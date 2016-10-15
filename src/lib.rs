#![allow(dead_code)]

use std::ops::{Index, IndexMut};
use std::fmt::Debug;

const ORDER: usize = 4; // Must be at least 2
const BRANCHING_FACTOR: usize = ORDER - 1;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
enum NodeIndex {
    Inner(usize),
    Leaf(usize),
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
    parent: Option<usize>,
    keys: [Option<K>; BRANCHING_FACTOR],
    pointers: [Option<NodeIndex>; ORDER],
}

impl<K: Ord + Copy> Inner<K> {
    fn new() -> Inner<K> {
        Inner {
            parent: None,
            keys: [None; BRANCHING_FACTOR],
            pointers: [None; ORDER],
        }
    }

    fn find_node_index(&self, key: K) -> NodeIndex {
        for (k, p) in self.keys.iter().zip(self.pointers.iter()) {
            if k.map_or(false, |k| key <= k ) {
                return p.expect("Keys should always have a data pair");
            }
        }
        self.pointers.last().unwrap().unwrap()
    }

    // splits the node and returns a new one if there was no room in the
    // node
    fn insert(&mut self, key: K, pointer: NodeIndex) -> Option<Inner<K>> {
        let mut insert_key = Some(key);
        let mut insert_ptr = Some(pointer);
        for (k, p) in self.keys.iter_mut().zip(self.pointers.iter_mut()) {
            if k.is_none() {
                *k = insert_key;
                *p = insert_ptr;
                return None;
            } else if k < &mut insert_key {
                std::mem::swap(p, &mut insert_ptr);
                std::mem::swap(k, &mut insert_key);
            }
        }

        match (insert_ptr, insert_key) {
            (Some(ptr), Some(key)) => {
                let mut new = self.split();
                new.insert(key, ptr).expect("Split should always have room for new key");
                Some(new)
            },
            (Some(ptr), None) => panic!("{:?} has no associated data", ptr),
            (None, key@Some(_)) => {
                self.keys.last_mut().map(|k| *k = key);
                None
            },
            (None, None) => None,
        }
    }

    fn split(&mut self) -> Inner<K> {
        let mut new = Inner::new();
        new.parent = self.parent;

        let len = self.keys.len(); // Non-Lexical Lifetime's can't come fast enough
        let (_, ref mut old_keys) = self.keys.split_at_mut(len / 2);
        for (ref mut old, ref mut new) in old_keys.iter_mut().zip(new.keys.iter_mut()) {
            std::mem::swap(old, new);
        }

        let (_, ref mut old_data) = self.pointers.split_at_mut(len/ 2);
        for (ref mut old, ref mut new) in old_data.iter_mut().zip(new.pointers.iter_mut()) {
            std::mem::swap(old, new);
        }

        new
    }
}


#[derive(Default, Debug)]
struct Inners<K>(Vec<Inner<K>>);


impl<K: Ord + Copy> Inners<K> {
    /// Finds the index of leaf node that most closely matches key
    fn find_leaf_index(&self, prev: usize, key: K) -> usize {
        if self.0.is_empty() {
            return 0; // to handle lazy alloc of inners
        }

        let mut prev = NodeIndex::Inner(prev);
        while let NodeIndex::Inner(x) = prev {
            prev = self.0[x].find_node_index(key);
        }

        match prev {
            NodeIndex::Inner(_) => unreachable!(),
            NodeIndex::Leaf(x) => x,
        }
    }

    // returns a new root if there is one
    fn insert(&mut self, key: K, target: usize, pointer: NodeIndex) -> Option<usize> {
        if self.0.is_empty() {
            println!("first alloc");
            let mut inner = Inner::new();
            assert_eq!(target, 0, "0 may mean the inners vec has been allocated yet");
            assert!(inner.insert(key, pointer).is_none(), "New node shouldn't split");
            self.0.push(inner);
            println!("inserted into leaves");
            return None;
        }

        let (mut target, mut idx, mut root) = (target, NodeIndex::Leaf(target), None);
        while let Some(new) = self.0[target].insert(key, idx) {
            root = new.parent;
            self.0.push(new);
            target = self.0.len();
            idx = NodeIndex::Inner(target);
        }
        return root;
    }
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
struct Leaf<K, V> {
    parent: usize,
    keys: [Option<K>; BRANCHING_FACTOR],
    data: [Option<V>; BRANCHING_FACTOR],
    next: Option<usize>,
}

impl<K: Ord + Copy, V> Leaf<K, V> {
    fn new(next: Option<usize>) -> Leaf<K, V> {
        Leaf {
            parent: 0,
            keys: [None; BRANCHING_FACTOR],
            data: option_arr![V; BRANCHING_FACTOR],
            next: next,
        }
    }

    // NOTE: does not apply at root node
    fn full(&self) -> bool {
        self.keys.iter().all(Option::is_some)
    }

    fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        self.keys.iter().position(|k| &Some(key) == k)
            .and_then(|i| self.data.get(i).and_then(|v| v.as_ref()))
    }

    fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        self.keys.iter().position(|k| &Some(key) == k)
            .and_then(move |i| self.data.get_mut(i).and_then(|v| v.as_mut()))
    }

    // returns Some(Leaf<K, V>) if the node splits on insert, Some(V) if a value was overwriten
    fn insert(&mut self, key: K, data: V, index: Option<usize>) -> (Option<Leaf<K, V>>, Option<V>) {
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
                let mut new = self.split(index);
                if let (None, None) = new.insert(key, data, None) { } else {
                    panic!("New leaf shouldn't have to split");
                }
                (Some(new), None)
            },
            (None, None) => (None, None),
            (_, _) => panic!("Incomplete key data pair"),
        }
    }

    fn split(&mut self, next: Option<usize>) -> Leaf<K, V> {
        let mut new = Leaf::new(next);
        new.parent = self.parent;

        let len = self.keys.len(); // Non-Lexical Lifetime's can't come fast enough
        let (_, ref mut old_keys) = self.keys.split_at_mut(len / 2);
        for (ref mut old, ref mut new) in old_keys.iter_mut().zip(new.keys.iter_mut()) {
            std::mem::swap(old, new);
        }

        let (_, ref mut old_data) = self.data.split_at_mut(len/ 2);
        for (ref mut old, ref mut new) in old_data.iter_mut().zip(new.data.iter_mut()) {
            std::mem::swap(old, new);
        }

        new
    }
}

#[derive(Debug)]
struct Leaves<K, V>(Vec<Leaf<K, V>>);

impl<K: Ord + Copy, V> Leaves<K, V> {
    // if the leaf is full the key of the inserted value must be inserted into the parent
    // returns (parent, node idx, replaced)
    fn insert(&mut self, key: K, value: V, target: usize) -> (usize, Option<NodeIndex>, Option<V>) {
        if self.0.is_empty() {
            let mut leaf = Leaf::new(None);
            if let (None, None) = leaf.insert(key, value, None) { } else {
                panic!("New leaf shouldn't have to split");
            }
            let parent = leaf.parent;
            self.0.push(leaf);
            return (parent, None, None);
        }

        let next = self.0.len()+1;
        let (new, replaced) = self.0[target].insert(key, value, Some(next));
        if let Some(new) = new {
            let parent = new.parent;
            self.0.push(new);
            (parent, Some(NodeIndex::Leaf(next)), replaced)
        } else {
            (self.0[target].parent, None, replaced)
        }
    }
}

// TODO: parameterize branching factor
#[derive(Debug)]
pub struct BPlusTree<K, V> {
    inners: Inners<K>,
    leaves: Leaves<K, V>,
    root: usize,
}

impl<K: Copy + Ord, V> Default for BPlusTree<K, V> {
    fn default() -> BPlusTree<K, V> { Self::new() }
}

impl<K: Copy + Ord, V> BPlusTree<K, V> {
    pub fn new() -> BPlusTree<K, V> {
        BPlusTree {
            root: 0,
            inners: Inners(Vec::new()),
            leaves: Leaves(Vec::new()),
        }
    }

    fn find_leaf_index(&self, key: K) -> usize {
        self.inners.find_leaf_index(self.root, key)
    }

    pub fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        println!("leaf: {:?}", self.find_leaf_index(key));
        self.leaves.0[self.find_leaf_index(key)].get(key)
    }

    pub fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        let idx = self.find_leaf_index(key);
        self.leaves.0[idx].get_mut(key)
    }
}

impl<K: Copy + Ord + Debug, V: Debug> BPlusTree<K, V> {
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
        let (parent, idx, val) = self.leaves.insert(key, value, leaf_idx);
        if let Some(idx) = idx {
            println!("too big for inners {:?} {:?}", parent, idx);
            if let Some(root) = self.inners.insert(key, parent, idx) {
                self.root = root;
                // TODO split root if more than half full
            }
            None
        } else {
            val
        }
    }
}

impl<K: Copy + Ord, V> Index<K> for BPlusTree<K, V> {
    type Output = V;

    fn index<'a>(&'a self, key: K) -> &'a Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Copy + Ord, V> IndexMut<K> for BPlusTree<K, V> {
    fn index_mut<'a>(&'a mut self, key: K) -> &'a mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smoke() {
        let mut tree = BPlusTree::new();
        tree.insert(1, 1);
        tree.insert(1, 2);
        println!("tree: {:#?}", tree);
        println!("get 1: {:?}", tree[1]);
        tree.insert(2, 2);
        tree.insert(3, 3);
        println!("get 3: {:?}", tree[3]);

        tree.insert(4, 4);
        println!("tree after 4: {:#?}", tree);
        println!("get 4: {:?}", tree[4]);
        tree.insert(5, 5);
        println!("tree after 5: {:#?}", tree);
        assert_eq!(tree[5], 5);
    }
}