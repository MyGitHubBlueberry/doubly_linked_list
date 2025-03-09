use std::{cell::RefCell, rc::{Rc, Weak}};

type StrongNode<T> = Option<Rc<RefCell<Node<T>>>>; 
type WeakNode<T> = Option<Weak<RefCell<Node<T>>>>; 

pub struct List<T: Clone + PartialEq> {
    pub length: usize,
    head: StrongNode<T>,
    tail: StrongNode<T>,
}

impl<T: Clone + PartialEq> Iterator for List<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(head) = self.head.clone() {
            let item = head.as_ref().borrow().val.borrow().clone();
            self.length -= 1;
            self.head = head.as_ref().borrow().next.clone();
            if self.length == 0 {
                self.tail = None;
            }
            return Some(item);
        }
        None
    }

}

impl<T: Clone + PartialEq> List<T> {
    pub fn new() -> Self {
        Self {
            length: 0,
            head: None,
            tail: None,
        }
    }

    pub fn append(&mut self, item: T) {
        let node = Rc::new(RefCell::new(Node::new(item, None, None)));

        if self.length == 0 {
            self.head = Some(Rc::clone(&node));
        } else {
            let tail = self.tail.take().unwrap();
            tail.borrow_mut().next = Some(Rc::clone(&node));
            node.borrow_mut().prev = Some(Rc::downgrade(&tail));
        }

        self.tail = Some(node);
        self.length += 1;
    }

    pub fn prepend(&mut self, item: T) {
        let node = Rc::new(RefCell::new(Node::new(item, None, None)));

        if self.length == 0 {
            self.tail = Some(Rc::clone(&node));
        } else {
            let head = self.head.take().unwrap();
            head.borrow_mut().prev = Some(Rc::downgrade(&node));
            node.borrow_mut().next = Some(head);
        }

        self.head = Some(node);
        self.length += 1;
    }

    pub fn insert_at(&mut self, item: T, index: usize) {
        if index == 0 {
            return self.prepend(item);
        } else if index >= self.length {
            return self.append(item);
        }

        let node = Rc::new(RefCell::new(Node::new(item, None, None)));
        let mut prev = self.head.as_ref().unwrap().clone();

        for _ in 1..index {
            prev = prev.clone().borrow().next.as_ref().unwrap().clone();
        }

        let next = prev.borrow_mut().next.take().unwrap();

        node.borrow_mut().next = Some(Rc::clone(&next));
        node.borrow_mut().prev = Some(Rc::downgrade(&prev));

        next.borrow_mut().prev = Some(Rc::downgrade(&node));
        prev.borrow_mut().next = Some(node);
        
        self.length += 1;

        return;
    }

    pub fn get(&self, index: usize) -> Option<Rc<RefCell<T>>> {
        if self.length == 0 {
            return None;
        }
        if index >= self.length - 1 {
            Some(self.tail.as_ref()?.borrow().val.clone());
        }

        let mut curr = Rc::downgrade(self.head.as_ref()?);

        for _ in 0..index {
            curr = Rc::downgrade(curr.upgrade()?.borrow().next.as_ref()?);
        }

        return Some(curr.upgrade()?.as_ref().borrow().val.clone());
    }

    pub fn remove(&mut self, item: T) -> Option<T> {
        if self.length == 0 {
            return None;
        }
        let mut curr = self.head.clone();
        let mut idx = 0;
        while let Some(node) = curr {
            if *node.borrow().val.borrow() == item {
                let prev = node.borrow_mut().prev.take();
                let next = node.borrow_mut().next.take();
                let val = node.borrow().val.borrow().clone();
                if self.length == 1 {
                    self.head = None;
                    self.tail = None;
                }
                else if idx == 0 {
                    self.head = next;
                }
                else if idx == self.length - 1 {
                    self.tail = prev.unwrap().upgrade();
                }
                else {
                    prev.as_ref().unwrap().upgrade().unwrap().borrow_mut().next = next.clone();
                    next.as_ref().unwrap().borrow_mut().prev = prev.clone();
                }

                self.length -= 1;

                return Some(val);
            }
            curr = node.clone().borrow().next.as_ref().cloned();
            idx += 1;
        }
        return None;
    }

    pub fn remove_at(&mut self, index: usize) -> Option<T> {
        if self.length == 0 || index >= self.length {
            return None;
        }

        let mut curr = self.head.as_ref().unwrap().clone();

        for _ in 0..index {
            curr = curr.clone().borrow().next.as_ref().unwrap().clone();
        }

        if index == 0 {
            self.head = None;
            self.head = curr.borrow().next.clone();
        }
        if index == self.length - 1 {
            self.tail = None;
            if let Some(prev) = &curr.borrow().prev {
                self.tail = prev.upgrade();
            }
        }

        let prev = curr.borrow_mut().prev.take();
        let next = curr.borrow_mut().next.take();
        if let Some(next) = &next {
            next.borrow_mut().prev = prev.clone();
        }
        if let Some(prev) = prev {
            prev.upgrade().unwrap().borrow_mut().next = next;
        };

        self.length -= 1;
        return Some(curr.as_ref().borrow().val.as_ref().borrow().clone());
    }
}

#[derive(Debug)]
struct Node<T: Clone + PartialEq> {
    val: Rc<RefCell<T>>,
    next: StrongNode<T>,
    prev: WeakNode<T>,
}

impl<T: Clone + PartialEq> Node<T> {
    fn new(val: T, next: StrongNode<T>, prev: WeakNode<T>) -> Self {
        Self {
            val: Rc::new(RefCell::new(val)),
            next,
            prev,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_list() {
        let list: List<i32> = List::new();
        assert_eq!(list.length, 0);
        assert!(list.head.is_none());
        assert!(list.tail.is_none());
    }

    #[test]
    fn test_append() {
        let mut list = List::new();
        list.append(10);
        assert_eq!(list.length, 1);
        assert_eq!(*list.head.as_ref().unwrap().borrow().val.borrow(), 10);
        assert_eq!(*list.tail.as_ref().unwrap().borrow().val.borrow(), 10);
        
        list.append(20);
        assert_eq!(list.length, 2);
        assert_eq!(*list.tail.as_ref().unwrap().borrow().val.borrow(), 20);
    }

    #[test]
    fn test_prepend() {
        let mut list = List::new();
        list.prepend(10);
        assert_eq!(list.length, 1);
        assert_eq!(*list.head.as_ref().unwrap().borrow().val.borrow(), 10);

        list.prepend(5);
        assert_eq!(list.length, 2);
        assert_eq!(*list.head.as_ref().unwrap().borrow().val.borrow(), 5);
    }

    #[test]
    fn test_insert_at() {
        let mut list = List::new();
        list.append(10);
        list.append(30);
        list.insert_at(20, 1);

        assert_eq!(list.length, 3);
        assert_eq!(*list.get(1).unwrap().borrow(), 20);
    }

    #[test]
    fn test_get() {
        let mut list = List::new();
        assert!(list.get(0).is_none());
        
        list.append(10);
        list.append(20);
        list.append(30);
        
        assert_eq!(*list.get(0).unwrap().borrow(), 10);
        assert_eq!(*list.get(1).unwrap().borrow(), 20);
        assert_eq!(*list.get(2).unwrap().borrow(), 30);
        assert!(list.get(3).is_none());
    }

    #[test]
    fn test_remove() {
        let mut list = List::new();
        assert_eq!(list.remove(10), None);
        
        list.append(10);
        list.append(20);
        list.append(30);
        
        assert_eq!(list.remove(20), Some(20));
        assert_eq!(list.length, 2);
        assert_eq!(list.get(1).unwrap().borrow().clone(), 30);
        assert_eq!(list.remove(40), None);
    }

    #[test]
    fn test_remove_at() {
        let mut list = List::new();
        assert_eq!(list.remove_at(0), None);
        
        list.append(10);
        list.append(20);
        list.append(30);
        
        assert_eq!(list.remove_at(1), Some(20));
        assert_eq!(list.length, 2);
        assert_eq!(list.get(1).unwrap().borrow().clone(), 30);
        
        assert_eq!(list.remove_at(10), None);
    }

    #[test]
    fn test_insert_at_boundaries() {
        let mut list = List::new();
        list.insert_at(10, 0);
        assert_eq!(list.length, 1);
        assert_eq!(*list.head.as_ref().unwrap().borrow().val.borrow(), 10);
        
        list.insert_at(20, 1);
        assert_eq!(list.length, 2);
        assert_eq!(*list.tail.as_ref().unwrap().borrow().val.borrow(), 20);
        
        list.insert_at(15, 1);
        assert_eq!(list.length, 3);
        assert_eq!(*list.get(1).unwrap().borrow(), 15);
    }

    #[test]
    fn test_multiple_appends_and_prepends() {
        let mut list = List::new();
        list.append(20);
        list.append(30);
        list.prepend(10);
        list.prepend(5);
        
        assert_eq!(list.length, 4);
        assert_eq!(*list.get(0).unwrap().borrow(), 5);
        assert_eq!(*list.get(1).unwrap().borrow(), 10);
        assert_eq!(*list.get(2).unwrap().borrow(), 20);
        assert_eq!(*list.get(3).unwrap().borrow(), 30);
    }

    #[test]
    fn test_reverse_iteration() {
        let mut list = List::new();
        list.append(10);
        list.append(20);
        list.append(30);
        
        let mut values = vec![];
        let mut current = list.tail.clone();
        while let Some(node) = current {
            values.push(*node.borrow().val.borrow());
            current = node.borrow().prev.as_ref().and_then(|weak| weak.upgrade());
        }
        assert_eq!(values, vec![30, 20, 10]);
    }

    #[test]
    fn test_complex_removal_sequence() {
        let mut list = List::new();
        list.append(10);
        list.append(20);
        list.append(30);
        list.append(40);
        list.append(50);
        
        assert_eq!(list.remove(30), Some(30));
        assert_eq!(list.length, 4);
        assert_eq!(list.get(2).unwrap().borrow().clone(), 40);

        assert_eq!(list.remove_at(3), Some(50));
        assert_eq!(list.length, 3);
        assert!(list.get(3).is_none());
    }
}
