/// A Vec-backed multi-map from `K` to `V` with O(n) lookups. Each key can
/// correspond to 0 or more values.
pub struct LinMultiMap<K, V> {
    backing: Vec<(K, V)>,
}

impl<K: Eq + Copy, V: Eq + Copy> LinMultiMap<K, V> {
    pub fn new() -> LinMultiMap<K, V> {
        LinMultiMap::<K, V> {
            backing: Vec::new(),
        }
    }
    pub fn insert(&mut self, k: K, v: V) {
        self.backing.push((k, v));
    }
    pub fn get<'a>(&'a self, k: &K) -> impl Iterator<Item = &'a V> {
        let owned_k = k.clone();
        self.backing
            .iter()
            .filter(move |(k1, _)| k1 == &owned_k)
            .map(|(_, v)| v)
    }
    pub fn get_all<'a>(&'a self, k: &K) -> Vec<&'a V> {
        self.get(k).collect()
    }
    pub fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.backing.iter()
    }
}

pub struct LinSet<V> {
    backing: Vec<V>,
    len: usize,
    cursor: usize, // used by iterator
}

impl<V: Eq + Copy> LinSet<V> {
    pub fn new() -> LinSet<V> {
        LinSet {
            backing: Vec::new(),
            len: 0,
            cursor: 0,
        }
    }
    pub fn clear(&mut self) {
        self.backing.clear();
        self.len = 0;
    }
    pub fn insert(&mut self, v: V) {
        if !self.contains(&v) {
            self.backing.push(v);
        }
        self.len += 1;
    }
    pub fn contains(&self, v: &V) -> bool {
        self.backing.contains(v)
    }
    pub fn len(&self) -> usize {
        self.len
    }
    pub fn iter(&self) -> impl Iterator<Item = &V> {
        self.backing.iter()
    }
    pub fn is_disjoint(&self, other: &LinSet<V>) -> bool {
        self.iter().all(|v| !other.contains(v))
    }
}

impl<V: Copy> Iterator for LinSet<V> {
    type Item = V;
    fn next(&mut self) -> Option<Self::Item> {
        let ret = match self.backing.get(self.cursor) {
            Some(v) => Some(*v),
            None => None,
        };
        self.cursor += 1;
        ret
    }
}

impl<V: Eq + Copy> std::iter::FromIterator<V> for LinSet<V> {
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        let mut c = LinSet::new();
        for i in iter {
            c.insert(i);
        }
        c
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linmultimap_simple() {
        let mut m = LinMultiMap::<u64, u64>::new();

        assert_eq!(m.get_all(&1).len(), 0);

        m.insert(1, 2);
        assert_eq!(m.get_all(&1), vec![&2]);

        m.insert(1, 3);
        assert_eq!(m.get_all(&1), vec![&2, &3]);

        m.insert(2, 3);
        assert_eq!(m.get_all(&1), vec![&2, &3]);
        assert_eq!(m.get_all(&2), vec![&3]);

        // Check that the multimap supports multiple instances of a value.
        m.insert(1, 3);
        assert_eq!(m.get_all(&1), vec![&2, &3, &3]);
    }

    #[test]
    fn test_linset_simple() {
        let mut s = LinSet::<u64>::new();
        assert!(!s.contains(&1));

        s.insert(42);
        assert!(!s.contains(&1));
        assert!(s.contains(&42));

        s.insert(42);
        assert!(!s.contains(&1));
        assert!(s.contains(&42));

        // Despite being inserted twice, 42 should only appear once.
        assert_eq!(s.iter().collect::<Vec<&u64>>(), vec![&42]);

        s.insert(123);
        assert_eq!(s.iter().collect::<Vec<&u64>>(), vec![&42, &123]);
    }
}
