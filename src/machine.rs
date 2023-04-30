use std::ffi::CString;
use std::os::raw::c_char;

use crate::nfa::Dfa;

pub enum X64Reg {
    Rdi,
    Rsi,
    Rdx,
    Rcx,
    R8,
    R9,
    Rax,
}

pub type LabelName = String;

pub enum X64Instr {
    Label(LabelName), // Not technically an instruction.
    Xor(X64Reg, X64Reg),
    CmpDeref(X64Reg, u64), // Dereference the left register.
    Cmp(X64Reg, X64Reg),
    Je(LabelName),
    Jne(LabelName),
    Jmp(LabelName),
}

pub fn dfa_to_x64(dfa: Dfa<u16, u8>) -> Vec<X64Instr> {
    panic!("Not implemented")
}

fn machine_lower(instrs: &[X64Instr]) -> Vec<u8> {
    panic!("Not implemented")
}

// Writes |code| to a buffer and then executes it. Super mega unsafe!
// Adapted from https://make-a-demo-tool-in-rust.github.io/1-3-jit.html.
#[cfg(any(target_os = "linux", target_os = "macos"))]
unsafe fn run_machine_code(code: &[u8], line: &str) -> i32 {
    const PAGE_SIZE: usize = 4096;
    let mut raw_addr: *mut libc::c_void = std::mem::zeroed();
    libc::posix_memalign(&mut raw_addr, PAGE_SIZE, code.len());
    libc::mprotect(
        raw_addr,
        code.len(),
        libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
    );
    libc::memcpy(raw_addr, std::mem::transmute(code.as_ptr()), code.len());
    let func: unsafe extern "C" fn(*const c_char) -> i32 = std::mem::transmute(raw_addr);
    let c_string = CString::new(line).unwrap();
    let result = func(c_string.into_raw());
    println!("asm returned {}", result);
    std::mem::drop(raw_addr);
    result
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
        unsafe {
            let result = run_machine_code(&code, &"foobar");
            assert_eq!(result, 0);

            let result = run_machine_code(&code, &"barfoo");
            assert_ne!(result, 0);
        }
    }
}
