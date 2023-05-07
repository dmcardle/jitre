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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
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
}
