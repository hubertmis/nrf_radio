use super::linked_list::{LinkedList, ListItem};

pub struct Iter<'iter, 'list, T> {
    next: &'iter Option<&'list mut ListItem<'list, T>>,
}

impl<'iter, 'list, T> Iter<'iter, 'list, T> {
    /// Create new iterator.
    ///
    /// This function is to be used by ['LinkedList.iter()'](LinkedList::iter).
    pub(super) fn new(list: &'iter LinkedList<'list, T>) -> Self {
        Self {
            next: list.get_first(),
        }
    }
}

impl<'iter, T> Iterator for Iter<'iter, '_, T> {
    type Item = &'iter T;

    fn next(&mut self) -> Option<Self::Item> {
        let following = match self.next {
            Some(item_ref) => item_ref.get_next(),
            None => &None,
        };
        let next = self.next;

        self.next = following;

        Some(next.as_ref()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_iterator_in_scope_smaller_than_list() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(1);
        list.push(&mut item);

        {
            let mut iter = Iter::new(&list);
            assert_eq!(iter.next(), Some(&1));
            assert_eq!(iter.next(), None);
        }

        let mut item2 = ListItem::new(2);
        list.push(&mut item2);

        let mut iter = Iter::new(&list);
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_for_loop() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(1);
        list.push(&mut item);
        let mut item2 = ListItem::new(2);
        list.push(&mut item2);

        let iter = Iter::new(&list);
        let mut cnt = 0usize;

        for _int_ref in iter {
            cnt += 1;
        }

        assert_eq!(cnt, 2);
    }
}
