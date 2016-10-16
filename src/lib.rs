use std::ops::{Index, IndexMut};
use std::fmt::Debug;
use std::slice;
use std::iter;

const ORDER: usize = 4; // Must be at least 2
const BRANCHING_FACTOR: usize = ORDER - 1;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
struct InnerIdx(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
struct LeafIdx(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
enum NodeIndex {
    Inner(InnerIdx),
    Leaf(LeafIdx),
}

impl NodeIndex {
    fn is_leaf(&self) -> bool {
        match self {
            &NodeIndex::Inner(_) => false,
            &NodeIndex::Leaf(_) => true,
        }
    }

    fn is_inner(&self) -> bool {
        !self.is_leaf()
    }
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

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
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

    fn get<'a>(&'a self, key: K) -> Option<&'a NodeIndex> {
        self.keys
            .iter()
            .position(|k| &Some(key) == k)
            .and_then(|i| self.pointers.get(i).and_then(|p| p.as_ref()))
    }

    fn get_mut<'a>(&'a mut self, key: K) -> Option<&'a mut NodeIndex> {
        self.keys
            .iter()
            .position(|k| &Some(key) == k)
            .and_then(move |i| self.pointers.get_mut(i).and_then(|p| p.as_mut()))
    }

    fn remove(&mut self, key: K) {
        // OPTIMIZE really dumb algo
        if let Some(i) = self.keys.iter().position(|k| &Some(key) == k) {
            self.keys[i].take();
            let data = self.pointers[i].take();
            assert!(data.is_some(), "keys should have data");
            self.keys.sort();
            use std::cmp::Ordering;
            self.pointers.sort_by(|a, b| {
                match (a, b) {
                    (&Some(_), &None) => Ordering::Greater,
                    (&None, &Some(_)) => Ordering::Less,
                    (_, _) => Ordering::Equal,
                }
            });
        }
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

    fn balanced(&self) -> bool {
        self.keys.iter().filter(|x| x.is_some()).count() > (self.keys.len() / 2)
    }

    fn redistribute(&mut self,
                    left: &mut Option<Self>,
                    right: &mut Option<Self>)
                    -> Option<(K, InnerIdx)> {
        unimplemented!()
    }

    fn merge(&mut self, left: &mut Option<Self>, right: &mut Option<Self>) -> Option<InnerIdx> {
        unimplemented!()
    }
}

impl<K: Copy + Ord + Debug> Index<K> for Inner<K> {
    type Output = NodeIndex;

    fn index<'a>(&'a self, key: K) -> &'a Self::Output {
        self.get(key).unwrap()
    }
}

impl<K: Copy + Ord + Debug> IndexMut<K> for Inner<K> {
    fn index_mut<'a>(&'a mut self, key: K) -> &'a mut Self::Output {
        self.get_mut(key).unwrap()
    }
}

#[derive(Default, Debug, PartialEq, PartialOrd, Ord, Eq, Hash)]
struct Inners<K>(Vec<Inner<K>>);

enum InnersBalanceResult<K> {
    Balanced,
    Redistributed(InnerIdx, K, InnerIdx),
    Merged(Option<InnerIdx>),
}

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

    fn balance(&mut self, target: InnerIdx, key: K) -> InnersBalanceResult<K> {
        if self[target].balanced() {
            return InnersBalanceResult::Balanced;
        }

        let (curr, left, right) = self.current_and_siblings_mut(target, key);
        if let Some((split_key, split_idx)) = curr.redistribute(left, right) {
            let parent = curr.parent.expect("cant redistribute root node");
            InnersBalanceResult::Redistributed(parent, split_key, split_idx)
        } else {
            InnersBalanceResult::Merged(curr.merge(left, right))
        }
    }

    fn current_and_siblings_mut<'a>
        (&'a mut self,
         target: InnerIdx,
         key: K)
         -> (&'a mut Inner<K>, &'a mut Option<Inner<K>>, &'a mut Option<Inner<K>>) {
        unimplemented!();
    }

    fn remove(&mut self, target: InnerIdx, key: K, last: NodeIndex) -> Option<NodeIndex> {
        let mut target = target;
        let mut last = last;
        loop {
            self[target].remove(key);
            match self.balance(target, key) {
                InnersBalanceResult::Balanced => return None,
                InnersBalanceResult::Redistributed(parent, split_key, split_idx) => {
                    self[parent][split_key] = NodeIndex::Inner(split_idx);
                    return None;
                }
                InnersBalanceResult::Merged(parent) => {
                    if let Some(parent) = parent {
                        self.0.remove(target.0);
                        last = NodeIndex::Inner(target);
                        target = parent;
                    } else {
                        return Some(last);
                    }
                }
            }
        }
    }

    fn clear(&mut self) {
        self.0.clear()
    }

    fn next_index(&mut self) -> InnerIdx {
        InnerIdx(self.0.len())
    }

    fn push(&mut self, new: Inner<K>) {
        self.0.push(new)
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

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
struct Leaf<K, V> {
    parent: Option<InnerIdx>,
    keys: [Option<K>; BRANCHING_FACTOR],
    data: [Option<V>; BRANCHING_FACTOR],
    next: Option<LeafIdx>,
}

type LeafIter<'a, K: 'a, V: 'a> = iter::Zip<slice::Iter<'a, Option<K>>, slice::Iter<'a, Option<V>>>;
type LeafIterMut<'a, K: 'a, V: 'a> = iter::Zip<slice::Iter<'a, Option<K>>,
                                               slice::IterMut<'a, Option<V>>>;

enum LeafInsertResult<K, V> {
    Split(Leaf<K, V>),
    Inserted(Option<V>),
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

    fn insert(&mut self, key: K, data: V, index: Option<LeafIdx>) -> LeafInsertResult<K, V> {
        let mut insert_key = Some(key);
        let mut insert_data = Some(data);
        for (k, p) in self.keys.iter_mut().zip(self.data.iter_mut()) {
            if k.is_none() {
                *k = insert_key;
                *p = insert_data;
                return LeafInsertResult::Inserted(None);
            } else if k == &mut insert_key {
                std::mem::swap(p, &mut insert_data);
                assert!(insert_data.is_some(), "Key missing data pair");
                return LeafInsertResult::Inserted(insert_data);
            }
        }

        match (insert_key, insert_data) {
            (Some(key), Some(data)) => {
                let mut new = self.split();
                self.next = index;
                match new.insert(key, data, None) {
                    LeafInsertResult::Inserted(None) => LeafInsertResult::Split(new),
                    _ => panic!("New leaf shouldn't have to split"),
                }
            }
            (None, None) => LeafInsertResult::Inserted(None),
            (_, _) => panic!("Incomplete key data pair"),
        }
    }

    fn remove(&mut self, key: K) -> Option<V> {
        // OPTIMIZE really dumb algo
        if let Some(i) = self.keys.iter().position(|k| &Some(key) == k) {
            self.keys[i].take();
            let data = self.data[i].take();
            assert!(data.is_some(), "keys should have data");
            self.keys.sort();
            use std::cmp::Ordering;
            self.data.sort_by(|a, b| {
                match (a, b) {
                    (&Some(_), &None) => Ordering::Greater,
                    (&None, &Some(_)) => Ordering::Less,
                    (_, _) => Ordering::Equal,
                }
            });
            data
        } else {
            None
        }
    }

    fn is_empty(&self) -> bool {
        self.keys.iter().all(|x| x.is_none())
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

    fn iter<'a>(&'a self) -> LeafIter<'a, K, V> {
        self.keys.iter().zip(self.data.iter())
    }

    fn iter_mut<'a>(&'a mut self) -> LeafIterMut<'a, K, V> {
        self.keys.iter().zip(self.data.iter_mut())
    }

    fn balanced(&self) -> bool {
        self.keys.iter().filter(|x| x.is_some()).count() > (self.keys.len() / 2)
    }

    fn redistribute(&mut self,
                    left: &mut Option<Self>,
                    right: &mut Option<Self>)
                    -> Option<(K, LeafIdx)> {
        unimplemented!()
    }

    fn merge(&mut self, left: &mut Option<Self>, right: &mut Option<Self>) -> InnerIdx {
        unimplemented!()
    }
}

#[derive(Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
struct Leaves<K, V>(Vec<Leaf<K, V>>);

enum LeavesInsertResult<V> {
    Inserted(Option<V>),
    Split(Option<InnerIdx>, LeafIdx),
}

enum LeavesBalanceResult<K> {
    Balanced,
    Redistributed(InnerIdx, K, LeafIdx),
    Merged(InnerIdx),
}

impl<K: Ord + Copy + Debug, V: Debug> Leaves<K, V> {
    // if the leaf is full the key of the inserted value must be inserted into the parent
    // returns (parent, new node idx, replaced)
    fn insert(&mut self, key: K, value: V, target: LeafIdx) -> LeavesInsertResult<V> {
        if self.0.is_empty() {
            assert_eq!(target,
                       LeafIdx(0),
                       "should only be empty and receive a target 0");
            let mut leaf = Leaf::new(None);
            match leaf.insert(key, value, None) {
                LeafInsertResult::Inserted(_) => (),
                _ => panic!("New leaf shouldn't have to split"),
            };
            // let parent = leaf.parent;
            self.0.push(leaf);
            return LeavesInsertResult::Inserted(None);
        }

        let last = LeafIdx(self.0.len());
        match self[target].insert(key, value, Some(last)) {
            LeafInsertResult::Inserted(r) => LeavesInsertResult::Inserted(r),
            LeafInsertResult::Split(new) => {
                let parent = new.parent;
                self.0.push(new);
                LeavesInsertResult::Split(parent, last)
            }
        }
    }

    fn balance(&mut self, target: LeafIdx, key: K, inners: &Inners<K>) -> LeavesBalanceResult<K> {
        if self[target].balanced() {
            return LeavesBalanceResult::Balanced;
        }

        let (curr, left, right) = self.current_and_siblings_mut(target, key, inners);
        if let Some((split_key, split_idx)) = curr.redistribute(left, right) {
            let parent = curr.parent.expect("cant redistribute root node");
            LeavesBalanceResult::Redistributed(parent, split_key, split_idx)
        } else {
            LeavesBalanceResult::Merged(curr.merge(left, right))
        }
    }

    fn current_and_siblings_mut<'a>
        (&'a mut self,
         target: LeafIdx,
         key: K,
         inners: &Inners<K>)
         -> (&'a mut Leaf<K, V>, &'a mut Option<Leaf<K, V>>, &'a mut Option<Leaf<K, V>>) {
        // sigh this will involve abusing split_at or using unsafe
        unimplemented!()
    }

    fn remove(&mut self, i: LeafIdx) {
        assert!(!self[i].is_empty(),
                "attempted to remove a leaf with data in it");
        // TODO do nothing here, and add the index to a free list, which can be
        // used during compaction
        self.0.remove(i.0);
    }

    fn get<'a>(&'a self, LeafIdx(idx): LeafIdx) -> Option<&'a Leaf<K, V>> {
        self.0.get(idx)
    }

    fn get_mut<'a>(&'a mut self, LeafIdx(idx): LeafIdx) -> Option<&'a mut Leaf<K, V>> {
        self.0.get_mut(idx)
    }

    fn iter<'a>(&'a self, start: LeafIdx) -> LeavesIter<'a, K, V> {
        LeavesIter {
            leaves: &self.0,
            current: Some(start),
        }
    }

    fn iter_mut<'a>(&'a mut self, start: LeafIdx) -> LeavesIterMut<'a, K, V> {
        LeavesIterMut {
            leaves: &mut self.0,
            current: Some(start),
        }
    }

    fn clear(&mut self) {
        self.0.clear()
    }
}

struct LeavesIter<'a, K: 'a, V: 'a> {
    leaves: &'a [Leaf<K, V>],
    current: Option<LeafIdx>,
}

impl<'a, K, V> Iterator for LeavesIter<'a, K, V> {
    type Item = &'a Leaf<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(i) = self.current {
            let next = &self.leaves[i.0];
            self.current = next.next;
            Some(next)
        } else {
            None
        }
    }
}

struct LeavesIterMut<'a, K: 'a, V: 'a> {
    leaves: &'a mut [Leaf<K, V>],
    current: Option<LeafIdx>,
}

impl<'a, K, V> Iterator for LeavesIterMut<'a, K, V> {
    type Item = &'a mut Leaf<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(LeafIdx(i)) = self.current {
            unsafe {
                let leaf_ptr = self.leaves.as_mut_ptr();
                if i < self.leaves.len() {
                    Some(leaf_ptr.offset(i as isize).as_mut().expect("no null elems"))
                } else {
                    None
                }
            }
        } else {
            None
        }
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

#[derive(Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
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
        self.inners.clear();
        self.leaves.clear();
    }

    pub fn contains_key(&self, key: K) -> bool {
        // TODO can short circuit -- keys can be duplicated
        self.get(key).is_some()
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let leaf_idx = self.find_leaf_index(key);
        let (mut parent, new_node_idx) = match self.leaves.insert(key, value, leaf_idx) {
            LeavesInsertResult::Inserted(r) => return r,
            LeavesInsertResult::Split(p, n) => (p, n),
        };

        let mut last = NodeIndex::Leaf(leaf_idx);
        let mut new_node_idx = NodeIndex::Leaf(new_node_idx);
        while let Some(p) = parent {
            let new = self.inners[p].insert(key, new_node_idx);
            if let Some(new) = new {
                // we had a split, shuffle to the parent
                last = new_node_idx;
                new_node_idx = NodeIndex::Inner(self.inners.next_index());
                parent = new.parent;
                self.inners.push(new);
            } else {
                // it fit, we are done inserting
                return None;
            }
        }

        // whole tree is one leaf node, do not need to insert into inners
        if self.root.is_leaf() {
            return None;
        }

        let mut new_root = Inner::new();
        new_root.right = Some(new_node_idx);
        let new_root_idx = self.inners.next_index();
        self.inners.push(new_root);
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
        None
    }

    pub fn remove(&mut self, key: K) -> Option<V> {
        let target = self.find_leaf_index(key);
        let removed = self.leaves[target].remove(key);

        match self.leaves.balance(target, key, &self.inners) {
            LeavesBalanceResult::Balanced => (),
            LeavesBalanceResult::Redistributed(parent, split_key, split_idx) => {
                self.inners[parent][split_key] = NodeIndex::Leaf(split_idx);
            }
            LeavesBalanceResult::Merged(parent) => {
                if let Some(root) = self.inners.remove(parent, key, NodeIndex::Leaf(target)) {
                    self.root = root;
                }
            }
        };
        removed
    }

    fn leftmost_leaf(&self) -> LeafIdx {
        let mut first_leaf = self.root;
        while let NodeIndex::Inner(x) = first_leaf {
            first_leaf = self.inners[x].pointers[0].expect("should always have at least one key");
        }

        if let NodeIndex::Leaf(x) = first_leaf {
            x
        } else {
            unreachable!()
        }
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
        Iter(self.leaves.iter(self.leftmost_leaf()).flat_map(Leaf::iter))
    }

    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, K, V> {
        let start = self.leftmost_leaf();
        IterMut(self.leaves.iter_mut(start).flat_map(Leaf::iter_mut))
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

// impl trait methods would be killer here
pub struct Iter<'a, K: 'a, V: 'a>(iter::FlatMap<LeavesIter<'a, K, V>,
                                                LeafIter<'a, K, V>,
                                                fn(&'a Leaf<K, V>) -> LeafIter<'a, K, V>>);

impl<'a, K, V> Iterator for Iter<'a, K, V>
    where K: 'a + Copy + Ord + Debug,
          V: 'a + Debug
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().and_then(|(k, d)| {
            match (k, d) {
                (&Some(ref k), &Some(ref d)) => Some((k, d)),
                (_, _) => None,
            }
        })
    }
}


pub struct IterMut<'a, K: 'a, V: 'a>(iter::FlatMap<LeavesIterMut<'a, K, V>,
                                                   LeafIterMut<'a, K, V>,
                                                   fn(&'a mut Leaf<K, V>) -> LeafIterMut<'a, K, V>>);

impl<'a, K, V> Iterator for IterMut<'a, K, V>
    where K: 'a + Copy + Ord + Debug,
          V: 'a + Debug
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().and_then(|(k, d)| {
            match (k, d) {
                (&Some(ref k), &mut Some(ref mut d)) => Some((k, d)),
                (_, _) => None,
            }
        })
    }
}

impl<K, V> std::iter::FromIterator<(K, V)> for BPlusTree<K, V>
    where K: Copy + Ord + Debug,
          V: Debug
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut tree = BPlusTree::new();
        for (k, v) in iter {
            tree.insert(k, v);
        }

        tree
    }
}

impl<K, V> Extend<(K, V)> for BPlusTree<K, V>
    where K: Copy + Ord + Debug,
          V: Debug
{
    fn extend<T>(&mut self, iter: T)
        where T: IntoIterator<Item = (K, V)>
    {
        for (k, v) in iter {
            self.insert(k, v);
        }
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

        for i in 0..10 {
            assert_eq!(tree.remove(i), Some(i + 1));
        }
    }
}