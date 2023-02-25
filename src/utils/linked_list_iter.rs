use super::linked_list::{LinkedList, ListItem};
use core::ops::Deref;

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

        Some(next.as_ref()?.deref().deref())
    }
}

/*
 * This IterMut was a nice rust learning excercise, but I don't think it should be available for
 * LinkedList. IterMut would allow anyone with access to LinkedList to modify content of items
 * pushed to the list by other users. Only a user owning a token should be allowed to modify it.
 */
pub struct IterMut<'iter, 'list, T> {
    next: Option<&'iter mut Option<&'list mut ListItem<'list, T>>>,
}

impl<'iter, 'list, T> IterMut<'iter, 'list, T> {
    /// Create new mutable iterator.
    ///
    /// This function is to be used by ['LinkedList.iter_mut()'](LinkedList::iter_mut).
    pub(super) fn new(list: &'iter mut LinkedList<'list, T>) -> Self {
        Self {
            next: Some(list.get_mut_first()),
        }
    }
}

impl<'iter, 'list, T> Iterator for IterMut<'iter, 'list, T> {
    type Item = &'iter mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let tmp: Option<&'iter mut Option<&'list mut ListItem<'list, T>>> = self.next.take();
        let (next, following): (
            Option<&'iter mut T>,
            Option<&'iter mut Option<&'list mut ListItem<'list, T>>>,
        ) = match tmp {
            Some(Some(item_ref)) => {
                let (next, following) = item_ref.get_mut_item_and_next();
                (Some(next), Some(following))
            }
            Some(None) | None => (None, None),
        };

        self.next = following;
        next
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

    #[test]
    fn test_create_mut_iterator_in_scope_smaller_than_list() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(1);
        list.push(&mut item);

        {
            let mut iter = IterMut::new(&mut list);
            let item = iter.next();
            assert_eq!(item, Some(&mut 1));

            // Modify item - mutable iterator allows it
            *(item.unwrap()) = 3;

            assert_eq!(iter.next(), None);
        }

        let mut item2 = ListItem::new(2);
        list.push(&mut item2);

        let mut iter = IterMut::new(&mut list);
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 3));
        assert_eq!(iter.next(), None);
    }
}
