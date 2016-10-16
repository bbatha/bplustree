use std::ops::{Index, IndexMut};
use std::fmt::Debug;

const ORDER: usize = 4; // Must be at least 2
const BRANCHING_FACTOR: usize = ORDER - 1;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
struct InnerIdx(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
struct LeafIdx(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
enum NodeIndex {
    Inner(InnerIdx),
    Leaf(LeafIdx),
}

impl From<InnerIdx> for NodeIndex {
    fn from(idx: InnerIdx) -> Self {
        return NodeIndex::Inner(idx);
    }
}

impl From<LeafIdx> for NodeIndex {
    fn from(idx: LeafIdx) -> Self {
        return NodeIndex::Leaf(idx);
    }
}


// None can safely act like its copy
macro_rules! option_arr {
    ( $ty: ty; $size: ident ) => {
        unsafe {
            let mut data: [Option<$ty>; $size] = std::mem::uninitialized();
            for d in &mut data {
                std::ptr::write(d, None);
            }
            data
        }
    };
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
struct Inner<K> {
    parent: Option<InnerIdx>,
    keys: [Option<K>; BRANCHING_FACTOR],
    pointers: [Option<NodeIndex>; BRANCHING_FACTOR],
    right: Option<NodeIndex>,
}

impl<K: Ord + Copy + Debug> Inner<K> {
    fn new() -> Inner<K> {
        Inner {
            parent: None,
            keys: [None; BRANCHING_FACTOR],
            pointers: [None; BRANCHING_FACTOR],
            right: None,
        }
    }

    fn find_node_index(&self, key: K) -> NodeIndex {
        for (k, p) in self.keys.iter().zip(self.pointers.iter()) {
            match (*k, *p) {
                (Some(k), Some(p)) if key <= k => return p,
                (None, Some(p)) => panic!(format!("pointer: {:?} is missing its key", p)),
                (Some(k), None) => panic!(format!("key: {:?} is missing its pointer", k)),
                (_, _) => continue,
            }
        }

        self.right.expect("key is greater than all contained keys")
    }

    // splits the node and returns a new one if there was no room in the
    // node
    fn insert(&mut self, key: K, pointer: NodeIndex) -> Option<Inner<K>> {
        let mut insert_key = Some(key);
        let insert_ptr = Some(pointer);
        // TODO push key into right location
        for (k, p) in self.keys.iter_mut().zip(self.pointers.iter_mut()) {
            if k.is_none() {
                *k = insert_key;
                *p = insert_ptr;
                return None;
            } else if k >= &mut insert_key {
                *p = insert_ptr;
                *k = insert_key;
            }
        }

        match (insert_ptr, insert_key) {
            (Some(ptr), Some(key)) => {
                let mut new = self.split(insert_ptr);
                assert!(new.insert(key, ptr).is_none(),
                        "Split should always have room for new key");
                Some(new)
            }
            (Some(ptr), None) => panic!("{:?} has no associated data", ptr),
            (None, key @ Some(_)) => {
                self.keys.last_mut().map(|k| *k = key);
                None
            }
            (None, None) => None,
        }
    }

    fn split(&mut self, ptr: Option<NodeIndex>) -> Inner<K> {
        let mut new = Inner::new();
        new.parent = self.parent;

        let len = self.keys.len() + 1; // Non-Lexical Lifetime's can't come fast enough
        let (_, ref mut old_keys) = self.keys.split_at_mut(len / 2);
        for (old, new) in old_keys.iter_mut().zip(new.keys.iter_mut()) {
            *new = old.take();
        }

        let (_, ref mut old_ptrs) = self.pointers.split_at_mut(len / 2);
        for (old, new) in old_ptrs.iter_mut().zip(new.pointers.iter_mut()) {
            let old = old.take();
            // Leaf most inner nodes have all keys pointing to the same leaf
            if let Some(NodeIndex::Leaf(_)) = ptr {
                *new = ptr;
            } else {
                *new = old;
            }
        }

        new
    }
}

#[derive(Default, Debug)]
struct Inners<K>(Vec<Inner<K>>);

impl<K: Ord + Copy + Debug> Inners<K> {
    /// Finds the index of leaf node that most closely matches key
    fn find_leaf_index(&self, prev: InnerIdx, key: K) -> LeafIdx {
        if self.0.is_empty() {
            return LeafIdx(0); // to handle lazy alloc of inners
        }

        let mut prev = prev;
        loop {
            match self[prev].find_node_index(key) {
                NodeIndex::Inner(x) => prev = x,
                NodeIndex::Leaf(x) => return x,
            };
        }
    }

    fn get<'a>(&'a self, InnerIdx(idx): InnerIdx) -> Option<&'a Inner<K>> {
        self.0.get(idx)
    }

    fn get_mut<'a>(&'a mut self, InnerIdx(idx): InnerIdx) -> Option<&'a mut Inner<K>> {
        self.0.get_mut(idx)
    }
}

impl<K: Copy + Ord + Debug> Index<InnerIdx> for Inners<K> {
    type Output = Inner<K>;

    fn index<'a>(&'a self, idx: InnerIdx) -> &'a Self::Output {
        self.get(idx).unwrap()
    }
}

impl<K: Copy + Ord + Debug> IndexMut<InnerIdx> for Inners<K> {
    fn index_mut<'a>(&'a mut self, idx: InnerIdx) -> &'a mut Self::Output {
        self.get_mut(idx).unwrap()
    }
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
struct Leaf<K, V> {
    parent: Option<InnerIdx>,
    keys: [Option<K>; BRANCHING_FACTOR],
    data: [Option<V>; BRANCHING_FACTOR],
    next: Option<LeafIdx>,
}

impl<K: Ord + Copy + Debug, V: Debug> Leaf<K, V> {
    fn new(next: Option<LeafIdx>) -> Leaf<K, V> {
        Leaf {
            parent: None,
            keys: [None; BRANCHING_FACTOR],
            data: option_arr![V; BRANCHING_FACTOR],
            next: next,
        }
    }

    fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        self.keys
            .iter()
            .position(|k| &Some(key) == k)
            .and_then(|i| self.data.get(i).and_then(|v| v.as_ref()))
    }

    fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        self.keys
            .iter()
            .position(|k| &Some(key) == k)
            .and_then(move |i| self.data.get_mut(i).and_then(|v| v.as_mut()))
    }

    // returns Some(Leaf<K, V>) if the node splits on insert, Some(V) if a value was overwriten
    fn insert(&mut self,
              key: K,
              data: V,
              index: Option<LeafIdx>)
              -> (Option<Leaf<K, V>>, Option<V>) {
        let mut insert_key = Some(key);
        let mut insert_data = Some(data);
        for (k, p) in self.keys.iter_mut().zip(self.data.iter_mut()) {
            if k.is_none() {
                *k = insert_key;
                *p = insert_data;
                return (None, None);
            } else if k == &mut insert_key {
                std::mem::swap(p, &mut insert_data);
                assert!(insert_data.is_some(), "Key missing data pair");
                return (None, insert_data);
            }
        }

        match (insert_key, insert_data) {
            (Some(key), Some(data)) => {
                let mut new = self.split();
                self.next = index;
                if let (None, None) = new.insert(key, data, None) {
                } else {
                    panic!("New leaf shouldn't have to split");
                }
                (Some(new), None)
            }
            (None, None) => (None, None),
            (_, _) => panic!("Incomplete key data pair"),
        }
    }

    fn split(&mut self) -> Leaf<K, V> {
        let mut new = Leaf::new(self.next);
        new.parent = self.parent;

        let len = self.keys.len() + 1; // Non-Lexical Lifetime's can't come fast enough
        let (_, ref mut old_keys) = self.keys.split_at_mut(len / 2);
        for (old, new) in old_keys.iter_mut().zip(new.keys.iter_mut()) {
            *new = old.take();
        }

        let (_, ref mut old_data) = self.data.split_at_mut(len / 2);
        for (old, new) in old_data.iter_mut().zip(new.data.iter_mut()) {
            *new = old.take();
        }

        new
    }

    fn get_pair<'a>(&'a mut self, offset: usize) -> Option<(&'a K, &'a V)> {
        match (self.keys.get(offset).and_then(Option::as_ref),
               self.data.get(offset).and_then(Option::as_ref)) {
            (Some(k), Some(d)) => Some((k, d)),
            (_, _) => None,
        }
    }

    fn get_pair_mut<'a>(&'a mut self, offset: usize) -> Option<(&'a K, &'a mut V)> {
        match (self.keys.get(offset).and_then(Option::as_ref),
               self.data.get_mut(offset).and_then(Option::as_mut)) {
            (Some(k), Some(d)) => Some((k, d)),
            (_, _) => None,
        }
    }
}

#[derive(Debug)]
struct Leaves<K, V>(Vec<Leaf<K, V>>);

impl<K: Ord + Copy + Debug, V: Debug> Leaves<K, V> {
    // if the leaf is full the key of the inserted value must be inserted into the parent
    // returns (parent, new node idx, replaced)
    fn insert(&mut self,
              key: K,
              value: V,
              target: LeafIdx)
              -> (Option<InnerIdx>, Option<NodeIndex>, Option<V>) {
        if self.0.is_empty() {
            assert_eq!(target,
                       LeafIdx(0),
                       "should only be empty and receive a target 0");
            let mut leaf = Leaf::new(None);
            if let (None, None) = leaf.insert(key, value, None) {
            } else {
                panic!("New leaf shouldn't have to split");
            }
            let parent = leaf.parent;
            self.0.push(leaf);
            return (parent, None, None);
        }

        let last = LeafIdx(self.0.len());
        let (new, replaced) = self[target].insert(key, value, Some(last));
        if let Some(new) = new {
            let parent = new.parent;
            self.0.push(new);
            (parent, Some(NodeIndex::Leaf(last)), replaced)
        } else {
            (self[target].parent, None, replaced)
        }
    }

    fn get<'a>(&'a self, LeafIdx(idx): LeafIdx) -> Option<&'a Leaf<K, V>> {
        self.0.get(idx)
    }

    fn get_mut<'a>(&'a mut self, LeafIdx(idx): LeafIdx) -> Option<&'a mut Leaf<K, V>> {
        self.0.get_mut(idx)
    }
}

impl<K: Copy + Ord + Debug, V: Debug> Index<LeafIdx> for Leaves<K, V> {
    type Output = Leaf<K, V>;

    fn index<'a>(&'a self, idx: LeafIdx) -> &'a Self::Output {
        self.get(idx).unwrap()
    }
}

impl<K: Copy + Ord + Debug, V: Debug> IndexMut<LeafIdx> for Leaves<K, V> {
    fn index_mut<'a>(&'a mut self, idx: LeafIdx) -> &'a mut Self::Output {
        self.get_mut(idx).unwrap()
    }
}

// TODO: parameterize branching factor
#[derive(Debug)]
pub struct BPlusTree<K, V> {
    inners: Inners<K>,
    leaves: Leaves<K, V>,
    root: NodeIndex,
}

impl<K: Copy + Ord + Debug, V: Debug> Default for BPlusTree<K, V> {
    fn default() -> BPlusTree<K, V> {
        Self::new()
    }
}

impl<K: Copy + Ord + Debug, V: Debug> BPlusTree<K, V> {
    pub fn new() -> BPlusTree<K, V> {
        BPlusTree {
            root: NodeIndex::Leaf(LeafIdx(0)),
            inners: Inners(Vec::new()),
            leaves: Leaves(Vec::new()),
        }
    }

    fn find_leaf_index(&self, key: K) -> LeafIdx {
        match self.root {
            NodeIndex::Leaf(x) => x,
            NodeIndex::Inner(x) => self.inners.find_leaf_index(x, key),
        }
    }

    pub fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        self.leaves[self.find_leaf_index(key)].get(key)
    }

    pub fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        let idx = self.find_leaf_index(key);
        self.leaves[idx].get_mut(key)
    }

    pub fn clear(&mut self) {
        self.inners.0.clear();
        self.leaves.0.clear();
    }

    pub fn contains_key(&self, key: K) -> bool {
        // TODO can short circuit -- keys can be duplicated
        self.get(key).is_some()
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let leaf_idx = self.find_leaf_index(key);
        let (mut parent, new_node_idx, replaced) = self.leaves.insert(key, value, leaf_idx);
        let mut new_node_idx = if let Some(idx) = new_node_idx {
            idx
        } else {
            return replaced;
        };

        let mut last = NodeIndex::Leaf(leaf_idx);
        while let Some(p) = parent {
            let new = self.inners[p].insert(key, new_node_idx);
            if let Some(new) = new {
                // we had a split, shuffle to the parent
                last = new_node_idx;
                new_node_idx = NodeIndex::Inner(InnerIdx(self.inners.0.len()));
                parent = new.parent;
                self.inners.0.push(new);
            } else {
                // it fit, we are done inserting
                return replaced;
            }
        }

        // single leaf is the root
        if self.leaves.0.len() == 1 {
            return replaced;
        }

        let mut new_root = Inner::new();
        new_root.right = Some(new_node_idx);
        self.inners.0.push(new_root);
        let new_root_idx = InnerIdx(self.inners.0.len() - 1);
        self.root = NodeIndex::Inner(new_root_idx);

        match (new_node_idx, last) {
            (NodeIndex::Leaf(new), NodeIndex::Leaf(last)) => {
                self.leaves[last].parent = Some(new_root_idx);
                self.leaves[new].parent = Some(new_root_idx);
            }
            (NodeIndex::Inner(new), NodeIndex::Inner(last)) => {
                self.inners[last].parent = Some(new_root_idx);
                self.inners[new].parent = Some(new_root_idx);
            }
            (_, _) => panic!("mismatched node index types"),
        }
        replaced
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
        let mut first_leaf = self.root;
        while let NodeIndex::Inner(x) = first_leaf {
            first_leaf = self.inners[x].pointers[0].expect("should always have at least one key");
        }

        if let NodeIndex::Leaf(x) = first_leaf {
            Iter {
                leaf_index: x,
                offset: 0,
                tree: self,
            }
        } else {
            unreachable!()
        }
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, K, V> {
        let mut first_leaf = self.root;
        while let NodeIndex::Inner(x) = first_leaf {
            first_leaf = self.inners[x].pointers[0].expect("should always have at least one key");
        }

        if let NodeIndex::Leaf(x) = first_leaf {
            IterMut {
                leaf_index: x,
                offset: 0,
                tree: self,
            }
        } else {
            unreachable!()
        }
    }
}

impl<K: Copy + Ord + Debug, V: Debug> Index<K> for BPlusTree<K, V> {
    type Output = V;

    fn index<'a>(&'a self, key: K) -> &'a Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Copy + Ord + Debug, V: Debug> IndexMut<K> for BPlusTree<K, V> {
    fn index_mut<'a>(&'a mut self, key: K) -> &'a mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    leaf_index: LeafIdx,
    offset: usize,
    tree: &'a BPlusTree<K, V>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
    where K: 'a + Copy + Ord + Debug,
          V: 'a + Debug
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(leaf) = self.tree.leaves.get(self.leaf_index) {
            if let item @ Some(_) = leaf.get_pair(self.offset) {
                self.offset += 1;
                return item;
            } else {
                self.leaf_index.0 += 1
            }
        }
        None
    }
}

pub struct IterMut<'a, K: 'a, V: 'a> {
    leaf_index: LeafIdx,
    offset: usize,
    tree: &'a mut BPlusTree<K, V>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
    where K: 'a + Copy + Ord + Debug,
          V: 'a + Debug
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(leaf) = self.tree.leaves.get_mut(self.leaf_index) {
            if let item @ Some(_) = leaf.get_pair_mut(self.offset) {
                self.offset += 1;
                return item;
            } else {
                self.leaf_index.0 += 1
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smoke() {
        let mut tree = BPlusTree::new();
        for i in 0..10 {
            tree.insert(i, i);
            assert_eq!(tree[i], i);
            assert_eq!(tree.insert(i, i + 1), Some(i));
            assert_eq!(tree[i], i + 1);
        }
    }
}