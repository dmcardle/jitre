use std::ffi::CString;
use std::os::raw::c_char;

use crate::linear_collections::{LinMultiMap, LinSet};
use crate::nfa::Dfa;

/// LabelId is analogous to an assembly language labels. Using an integer rather
/// than a string to avoid paying the runtime cost of string checking.
pub type LabelId = i32;

pub enum SimpleOp {
    Label(LabelId),
    JumpToLabel(LabelId),
    JumpToLabelIfEq(LabelId, u8),
    LoadByte,
    LoadImm(u8),
    Return,
}

fn assemble(instructions: &[SimpleOp]) -> Vec<u8> {
    // The first pass builds the lookup table from labels IDs to instruction
    // pointer (relative to the first instruction).
    let (label_to_ip, size) =
        instructions
            .iter()
            .fold((LinMultiMap::new(), 0), |(mut map, n), instr| match instr {
                SimpleOp::Label(k) => {
                    map.insert(k, n);
                    (map, n)
                }
                SimpleOp::JumpToLabel(_) => (map, n + 5),
                SimpleOp::JumpToLabelIfEq(_, _) => (map, n + 8),
                SimpleOp::LoadByte => (map, n + 6),
                SimpleOp::LoadImm(_) => (map, n + 2),
                SimpleOp::Return => (map, n + 1),
            });

    let mut out = Vec::with_capacity(size as usize);
    instructions.iter().for_each(|instr| {
        match instr {
            SimpleOp::Label(_) => {}
            SimpleOp::JumpToLabel(k) => {
                let dest: i32 = *label_to_ip.get_first(&k).unwrap();
                let rel: i32 = dest - out.len() as i32 - 5;
                // jmp rel32
                out.push(0xe9);
                out.extend_from_slice(&rel.to_le_bytes());
            }
            SimpleOp::JumpToLabelIfEq(label, byte_imm) => {
                let dest: i32 = *label_to_ip.get_first(&label).unwrap() as i32;
                let rel: i32 = dest - out.len() as i32 - 8;
                out.extend_from_slice(&[
                    // cmp al, ${byteImm}
                    0x3c, *byte_imm, // je ${relative offset to label}
                    0x0f, 0x84,
                ]);
                out.extend_from_slice(&rel.to_le_bytes());
            }
            SimpleOp::LoadByte => {
                // Dereference RDI to load one byte, then increment RDI.
                out.extend_from_slice(&[
                    // movzx eax, byte [rdi]
                    0x0f, 0xb6, 0x07, // inc rdi
                    0x48, 0xff, 0xc7,
                ]);
            }
            SimpleOp::LoadImm(byte_imm) => {
                // mov al, ${byteImm}
                out.extend_from_slice(&[0xb0, *byte_imm]);
            }
            SimpleOp::Return => out.push(0xc3),
        }
    });

    out
}

/// Compile a DFA to X86 instructions.
///
/// For example:
///
/// ```asm
/// start:
///   xor AX, AX
///
/// state_0:         // The start state MUST be written immediately after start.
///   mov (DI), SI   // This is repeated once per state.
///   add DI, 1
///
///   cmp SI, 'a'    // On 'a', go to state 3.
///   je state_3
///
///   cmp SI, 'b'    // On 'b', go to state 2.
///   je state_2
///
///   cmp SI, 'c'    // On 'c', go to accept state.
///   je accept
///
///   ret            // Implicitly reject by returning.
///
/// state_1:
///   // ...
///
/// accept:
///   mov AX, 1
///   ret
///
/// ```
pub fn dfa_to_simple_ops(dfa: &Dfa<u16, u8>) -> Vec<SimpleOp> {
    const LABEL_ACCEPT: LabelId = -1;
    const LABEL_REJECT: LabelId = -2;

    let mut ops: Vec<SimpleOp> = Vec::new();

    ops.push(SimpleOp::JumpToLabel(dfa.start_state.into()));

    // TODO: calculate the size of each instruction to determine the label
    // value. Then use the function hooking technique from the iced_tea readme
    // to reencode the instructions at a different IP offset.

    let mut states = LinSet::new();
    let mut transition_table = LinMultiMap::new();
    for ((from, on), to) in dfa.transition.iter() {
        states.insert(*from);
        transition_table.insert(*from, (*on, *to));
    }

    for state in states {
        ops.push(SimpleOp::Label(state as i32));
        ops.push(SimpleOp::LoadByte);

        // TODO: if the loaded byte is zero, jump to the reject state.

        for (on, to) in transition_table.get_all(&state) {
            // TODO: compare the loaded byte to `on`. If they match, then jump
            // to the state with label `to`. If `to` is an accept state, instead
            // jump to `LABEL_ACCEPT`.

            ops.push(SimpleOp::JumpToLabelIfEq(*to as i32, *on));
        }

        ops.push(SimpleOp::JumpToLabelIfEq(
            if dfa.accept_states.contains(&state) {
                LABEL_ACCEPT
            } else {
                LABEL_REJECT
            },
            b'\0',
        ));

        ops.push(SimpleOp::JumpToLabel(LABEL_REJECT));
    }

    ops.push(SimpleOp::Label(LABEL_ACCEPT));
    // TODO: push something like SimpleOp::SetReturnTrue
    ops.push(SimpleOp::Return);

    // Prepend a jump to the start state.

    ops
}

// Writes |code| to a buffer and then executes it. Super mega unsafe!
// Adapted from https://make-a-demo-tool-in-rust.github.io/1-3-jit.html.
#[cfg(any(target_os = "linux", target_os = "macos"))]
fn run_machine_code(code: &[u8], line: &str) -> i32 {
    const PAGE_SIZE: usize = 4096;
    // TODO try to eliminate this copy
    let c_string = CString::new(line).unwrap();
    unsafe {
        let mut raw_addr: *mut libc::c_void = std::mem::zeroed();
        libc::posix_memalign(&mut raw_addr, PAGE_SIZE, code.len());
        libc::mprotect(
            raw_addr,
            code.len(),
            libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
        );
        // TODO try to eliminate this copy
        libc::memcpy(raw_addr, std::mem::transmute(code.as_ptr()), code.len());
        let func: unsafe extern "C" fn(*const c_char) -> i32 = std::mem::transmute(raw_addr);
        // TODO remove PROT_WRITE before calling `func`. For reasons I do not
        // understand, calling `libc::mprotect`` a second time seems to cause a
        // segfault.
        let result = func(c_string.into_raw());
        std::mem::drop(raw_addr);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_machine_code() {
        // This assembly function returns zero in $rax iff the string pointed to
        // by $rdi begins with "fo".
        let code = [
            0x80, 0x3f, 0x66, // cmp BYTE PTR [rdi], 'f'
            0xb8, 0x01, 0x00, 0x00, 0x00, //
            0x75, 0x09, // jne PC+9
            0x31, 0xc0, // xor eax, eax
            0x80, 0x7f, 0x01, 0x6f, // cmp BYTE PTR [rdi+1],'o'
            0x0f, 0x95, 0xc0, // setne al
            0xc3, // ret
        ];
        let result = run_machine_code(&code, &"foobar");
        assert_eq!(result, 0);

        let result = run_machine_code(&code, &"barfoo");
        assert_ne!(result, 0);
    }

    #[test]
    fn test_assemble_simple() {
        // Build a SimpleOp machine that matches /f(o|b)(o|b)*/.
        const REJECT_STATE: i32 = -1;
        const ACCEPT_STATE: i32 = 0;
        let instructions = [
            // --- State 1. Match 'f'.
            SimpleOp::Label(1),
            SimpleOp::LoadByte,
            SimpleOp::JumpToLabelIfEq(2, b'f'),
            // Reject if none of the cases matched. Note that this implicitly
            // covers the input string's null terminator.
            SimpleOp::JumpToLabel(REJECT_STATE),
            // --- State 2. Match 'o' or 'b'.
            SimpleOp::Label(2),
            SimpleOp::LoadByte,
            SimpleOp::JumpToLabelIfEq(3, b'o'),
            SimpleOp::JumpToLabelIfEq(3, b'b'),
            SimpleOp::JumpToLabel(REJECT_STATE),
            // --- State 3. Match 'o' or 'b', repeated.
            SimpleOp::Label(3),
            SimpleOp::LoadByte,
            // If we see 'o' or 'b', loop back to this same state. Note that
            // this backwards jump tests that we correctly encode a negative
            // relative JE instruction.
            SimpleOp::JumpToLabelIfEq(3, b'o'),
            SimpleOp::JumpToLabelIfEq(3, b'b'),
            SimpleOp::JumpToLabelIfEq(ACCEPT_STATE, b'\0'),
            SimpleOp::JumpToLabel(REJECT_STATE),
            // --- "Reject" State.
            SimpleOp::Label(REJECT_STATE),
            SimpleOp::LoadImm(0),
            SimpleOp::Return,
            // --- "Accept" State.
            SimpleOp::Label(ACCEPT_STATE),
            SimpleOp::LoadImm(1),
            SimpleOp::Return,
        ];

        let code = assemble(&instructions);

        assert_eq!(1, run_machine_code(&code, &"fo"));
        assert_eq!(1, run_machine_code(&code, &"fb"));
        assert_eq!(1, run_machine_code(&code, &"fooboo"));
        assert_eq!(0, run_machine_code(&code, &"go"));
        assert_eq!(0, run_machine_code(&code, &"fx"));
        assert_eq!(0, run_machine_code(&code, &"f"));
        assert_eq!(0, run_machine_code(&code, &""));
    }
}
