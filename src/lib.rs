#![allow(dead_code)]

use std::ops::{Index, IndexMut};

const ORDER: usize = 4; // Must be at least 2
const BRANCHING_FACTOR: usize = ORDER - 1;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
enum NodeIndex {
    Inner(usize),
    Leaf(usize),
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
struct Node<K, V, N> {
    keys: [Option<K>; BRANCHING_FACTOR],
    data: [Option<V>; BRANCHING_FACTOR],
    next: N,
}

type Inner<K> = Node<K, NodeIndex, NodeIndex>;
type Leaf<K, V> = Node<K, V, Option<NodeIndex>>;

impl<K: Copy + Ord, V, N: Default> Default for Node<K, V, N> {
    fn default() -> Self {
        Self::new()
    }
}

// None can safely act like its copy
macro_rules! none_arr {
    ( $ty: ty; $size: ident ) => {
        unsafe {
            let mut data: [$ty; $size] = std::mem::uninitialized();
            for d in &mut data {
                std::ptr::write(d, None);
            }
            data
        }
    };
}

impl<K: Ord + Copy, V, N: Default> Node<K, V, N> {
    fn new() -> Node<K, V, N> {
        let data = none_arr![Option<V>; BRANCHING_FACTOR];

        Node {
            keys: [None; BRANCHING_FACTOR],
            data: data,
            next: N::default(),
        }
    }

    fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        if let Some(d) = self.keys.binary_search(&Some(key)).ok() {
            self.data.get(d).and_then(|v| v.as_ref())
        } else {
            None
        }
    }

    fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        if let Some(d) = self.keys.binary_search(&Some(key)).ok() {
            self.data.get_mut(d).and_then(|v| v.as_mut())
        } else {
            None
        }
    }

    // NOTE: does not apply at root node
    fn full(&self) -> bool {
        self.keys.iter().all(Option::is_some)
    }

    // NOTE: does not apply at root node
    fn has_room(&self) -> bool {
        self.keys.iter().filter(|&x| x.is_some()).count() < (ORDER + 1) / 2
    }

    // returns Some(V) if not inserted. Assumes data and keys are in key sorted order
    fn push(&mut self, key: K, data: V) -> Option<V> {
        if self.full() {
            return Some(data)
        }

        let mut insert_key = Some(key);
        let mut insert_data = Some(data);
        for (k, p) in self.keys.iter_mut().zip(self.data.iter_mut()) {
            if k.is_none() {
                *k = insert_key;
                *p = insert_data;
                return None;
            } else if k > &mut insert_key {
                std::mem::swap(p, &mut insert_data);
                std::mem::swap(k, &mut insert_key);
            }
        }
        assert!(insert_key.is_none() && insert_data.is_none(), "Attempted to push into a full node");
        None
    }

    fn contains_key(&self, key: K) -> bool {
        self.keys.contains(&Some(key))
    }

    fn split(&mut self) -> Node<K, V, N> {
        unimplemented!()
    }
}

impl<K: Copy + Ord> Inner<K> {
    /// Finds the index of node that most close matches key
    fn find_node_index<'a>(&'a self, key: K) -> NodeIndex {
        for (k, i) in self.keys.iter().zip(self.data.iter()) {
            match (*k, *i) {
                (Some(k), Some(i)) if k < key => return i,
                (Some(_), None) => panic!("Keys should always have associated data"),
                _ => break,
            }
        }
        self.next
    }
}

#[derive(Default, Debug)]
struct Inners<K>(Vec<Inner<K>>);


impl<K: Ord + Copy> Inners<K> {
    /// Finds the index of leaf node that most closely matches key
    fn find_leaf_index(&self, prev: NodeIndex, key: K) -> usize {
        let mut prev = prev;
        while let NodeIndex::Inner(x) = prev {
            prev = self.0[x].find_node_index(key);
        }

        match prev {
            NodeIndex::Inner(_) => unreachable!(),
            NodeIndex::Leaf(x) => x,
        }
    }
}

#[derive(Debug)]
struct Leaves<K, V>(Vec<Leaf<K, V>>);

// TODO: parameterize branching factor
#[derive(Debug)]
pub struct BPlusTree<K, V> {
    inners: Inners<K>,
    leaves: Leaves<K, V>,
    root: NodeIndex,
}

impl<K: Copy + Ord, V> Default for BPlusTree<K, V> {
    fn default() -> BPlusTree<K, V> { Self::new() }
}

impl<K: Copy + Ord, V> BPlusTree<K, V> {
    pub fn new() -> BPlusTree<K, V> {
        BPlusTree {
            root: NodeIndex::Leaf(0),
            inners: Inners(Vec::new()),
            leaves: Leaves(Vec::new()),
        }
    }

    pub fn clear(&mut self) {
        self.inners.0.clear();
        self.leaves.0.clear();
    }

    fn find_leaf_index(&self, key: K) -> usize {
        self.inners.find_leaf_index(self.root, key)
    }

    pub fn contains_key(&self, key: K) -> bool {
        self.get(key).is_some()
    }

    pub fn get<'a>(&'a self, key: K) -> Option<&'a V> {
        self.leaves.0[self.find_leaf_index(key)].get(key)
    }

    pub fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
        let idx = self.find_leaf_index(key);
        self.leaves.0[idx].get_mut(key)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // Grow to fit our first value
        if self.leaves.0.is_empty() {
            let mut leaf = Leaf::default();
            leaf.push(key, value);
            self.leaves.0.push(leaf);
            return None;
        }

        // if key is already in tree modify in place
        if let Some(old) = self.get_mut(key) {
            let mut value = value;
            std::mem::swap(old, &mut value);
            return Some(value)
        }

        let target_leaf_index = self.find_leaf_index(key);
        loop {
            let leaf = self.leaves.0.get_mut(target_leaf_index).unwrap();
            if leaf.full() {
                let split = leaf.split();
                //self.leaves.0.push(split);
                // TODO: insert key into parent node
            } else {
                leaf.push(key, value).expect("Leaf should have room for the key");
                return None;
            }
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