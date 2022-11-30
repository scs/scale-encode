use std::sync::Arc;

// A simple singly-linked `Send`-able linked list
// implementation to allow fairly cheap path cloning
// and appending. This is used as part of our `Context`
// type and is not a part of the public API.
#[derive(Debug, Clone)]
pub struct LinkedList<T>(Option<Arc<Inner<T>>>);

#[derive(Debug)]
struct Inner<T> {
    item: T,
    prev: LinkedList<T>
}

impl <T> LinkedList<T> {
    pub fn new() -> Self {
        Self(None)
    }
    pub fn push(self, item: T) -> Self {
        Self(Some(Arc::new(Inner{ item, prev: self })))
    }
    pub fn len(&self) -> usize {
        self.iter_back().count()
    }
    pub fn iter_back(&self) -> LinkedListIter<'_, T> {
        LinkedListIter { list: self }
    }
}

impl <T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct LinkedListIter<'a, T> {
    list: &'a LinkedList<T>
}

impl <'a, T> Iterator for LinkedListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        match &self.list.0 {
            None => {
                None
            },
            Some(list) => {
                let item = &list.item;
                self.list = &list.prev;
                Some(item)
            }
        }
    }
}