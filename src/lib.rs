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

impl<K: Ord + Copy + Debug> Inner<K> {
    fn new() -> Inner<K> {
        Inner {
            parent: None,
            keys: [None; BRANCHING_FACTOR],
            pointers: [None; ORDER],
        }
    }

    fn find_node_index(&self, key: K) -> NodeIndex {
        println!("Finding node index of {:?} when self: {:?}", key, self);
        for (i, p) in self.pointers
            .iter()
            .take_while(|p| p.is_some())
            .map(|p| p.unwrap())
            .enumerate() {
            match self.keys.get(i).and_then(|k| *k) {
                Some(k) if k >= key => {
                    println!("key is {:?} for p {:?}", k, p);
                    return p;
                }
                None => {
                    println!("No key for {:?}", p);
                    return p;
                }
                _ => continue,
            }
        }
        unreachable!();

        // for (k, p) in self.keys.iter().zip(self.pointers.iter()) {
        // if k.map_or(false, |k| key <= k) {
        // return p.expect("Keys should always have a data pair");
        // }
        // }
        // self.pointers
        // .iter()
        // .find(|x| x.is_some())
        // .and_then(|x| x.clone())
        // .expect("An inner node should always refer to at least one leaf")
        //
    }

    // splits the node and returns a new one if there was no room in the
    // node
    fn insert(&mut self, key: K, pointer: NodeIndex) -> Option<Inner<K>> {
        println!("Finding node index of {:?}", key);
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
                println!("before split: {:?}", self);
                let mut new = self.split(insert_ptr);
                println!("new: {:?}, old: {:?}", new, self);
                println!("going to insert {:?} {:?}", key, ptr);
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
        println!("splitting {:?}, {:?}", ptr, old_ptrs);
        for (old, new) in old_ptrs.iter_mut().zip(new.pointers.iter_mut()) {
            let old = old.take();
            // Leaf most inner nodes have all keys pointing to the same leaf
            if let Some(NodeIndex::Leaf(_)) = ptr {
                *new = ptr;
            } else {
                *new = old;
            }
        }
        println!("splitting {:?}, {:?}", ptr, old_ptrs);
        println!("splitting {:?}, {:?}", ptr, new.pointers);

        new
    }
}


#[derive(Default, Debug)]
struct Inners<K>(Vec<Inner<K>>);


impl<K: Ord + Copy + Debug> Inners<K> {
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
            assert_eq!(target,
                       0,
                       "0 may mean the inners vec has been allocated yet");
            assert!(inner.insert(key, pointer).is_none(),
                    "New node shouldn't split");
            self.0.push(inner);
            println!("inserted into leaves");
            return None;
        }

        let (mut target, mut last) = (target, pointer);
        while let Some(mut new) = self.0[target].insert(key, last) {
            let parent = new.parent;

            if let Some(p) = parent {
                self.0.push(new);
                last = NodeIndex::Inner(target);
                target = p;
            } else {
                println!("need new root");
                let mut root = Inner::new();
                let new_root_idx = Some(self.0.len() + 1);
                new.parent = new_root_idx;
                root.keys[0] = new.keys[0];
                root.pointers[0] = Some(NodeIndex::Inner(target));
                root.pointers[1] = Some(NodeIndex::Inner(self.0.len()));
                self.0[target].parent = new_root_idx;
                // fix right's new's children

                self.0.push(new);
                self.0.push(root);
                return new_root_idx;
            }
        }
        None
    }
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
struct Leaf<K, V> {
    parent: usize,
    keys: [Option<K>; BRANCHING_FACTOR],
    data: [Option<V>; BRANCHING_FACTOR],
    next: Option<usize>,
}

impl<K: Ord + Copy + Debug, V: Debug> Leaf<K, V> {
    fn new(next: Option<usize>) -> Leaf<K, V> {
        Leaf {
            parent: 0,
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
}

#[derive(Debug)]
struct Leaves<K, V>(Vec<Leaf<K, V>>);

impl<K: Ord + Copy + Debug, V: Debug> Leaves<K, V> {
    // if the leaf is full the key of the inserted value must be inserted into the parent
    // returns (parent, inserted node idx, replaced)
    fn insert(&mut self, key: K, value: V, target: usize) -> (usize, NodeIndex, Option<V>) {
        if self.0.is_empty() {
            assert_eq!(target, 0, "should only be empty and receive a target 0");
            let mut leaf = Leaf::new(None);
            if let (None, None) = leaf.insert(key, value, None) {
            } else {
                panic!("New leaf shouldn't have to split");
            }
            let parent = leaf.parent;
            self.0.push(leaf);
            return (parent, NodeIndex::Leaf(0), None);
        }

        let last = self.0.len();
        let (new, replaced) = self.0[target].insert(key, value, Some(last));
        if let Some(new) = new {
            let parent = new.parent;
            self.0.push(new);
            (parent, NodeIndex::Leaf(last), replaced)
        } else {
            (self.0[target].parent, NodeIndex::Leaf(target), replaced)
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

impl<K: Copy + Ord + Debug, V: Debug> Default for BPlusTree<K, V> {
    fn default() -> BPlusTree<K, V> {
        Self::new()
    }
}

impl<K: Copy + Ord + Debug, V: Debug> BPlusTree<K, V> {
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
        println!("Going to insert into {:?}", leaf_idx);
        let (parent, idx, val) = self.leaves.insert(key, value, leaf_idx);
        println!("Actually inserted into {:?}", idx);
        if let Some(root) = self.inners.insert(key, parent, idx) {
            self.root = root;
        };
        val
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn smoke() {
        let mut tree = BPlusTree::new();
        tree.insert(1, 1);
        println!("tree: {:#?}", tree);
        println!("get 1: {:?}", tree[1]);
        tree.insert(2, 2);
        println!("tree after 2: {:#?}", tree);
        tree.insert(3, 3);
        println!("tree after 3: {:#?}", tree);
        println!("get 3: {:?}", tree[3]);

        tree.insert(4, 4);
        println!("tree after 4: {:#?}", tree);
        println!("get 4: {:?}", tree[4]);
        tree.insert(5, 5);
        println!("tree after 5: {:#?}", tree);
        assert_eq!(tree[5], 5);
    }
}