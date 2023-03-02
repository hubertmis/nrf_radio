//! Generic heapless linked list with unlimited number of items
//!
//! Heapless linked list is useful as a data structure in system programming where heap is not
//! available.
//!
//! This implementation of linked list allows unlimited number of items, because memory for list
//! items is allocated by the list users. The list implementation is responsible for setting
//! correct links between the items, but not for the memory management. The implication of such
//! design is required lifetime of list items, which must be at least as long as the list itself.

use super::linked_list_iter::Iter;
use core::ops::{Deref, DerefMut};

/// Errors reported by the methods in this module
#[derive(Debug, Eq, PartialEq)]
pub enum Error<'list, T> {
    /// Item represented by given [token](ListItemToken) was not found in the list. The ownership
    /// of the token is returned to the caller.
    NotFound(ListItemToken<'list, T>),
}

/// Generic item which can be stored in a [linked list](LinkedList)
///
/// This is a smart pointer dereferending to the stored generic type.
///
/// An item can be added to single linked list at a time.
///
/// While an item is added to a list you can't modify the item, because it is exclusively borrowed
/// by the list.
///
/// # Examples
///
/// ```
/// use nrf_radio::utils::linked_list::ListItem;
///
/// let list_item = ListItem::new(5i32);
/// assert_eq!(*list_item, 5i32);
/// ```
#[derive(Debug, PartialEq)]
pub struct ListItem<'item, T> {
    item: T,
    next: Option<&'item mut ListItem<'item, T>>,
}

impl<'item, T> ListItem<'item, T> {
    /// Create a new item which can be stored in a [linked list](LinkedList)
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::ListItem;
    ///
    /// let list_item = ListItem::new(Vec::<usize>::new());
    /// ```
    pub fn new(item: T) -> Self {
        Self { item, next: None }
    }

    /// Get a reference to data stored by this list item
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::ListItem;
    ///
    /// let list_item = ListItem::new("data");
    ///
    /// assert_eq!(list_item.get_data(), &"data");
    /// ```
    pub fn get_data(&self) -> &T {
        &self.item
    }

    /// Insert this item to a list just behind passed item.
    ///
    /// The item passed as `existing` must be in a list.
    ///
    /// Using this function requires some access to mutable references of the items in a list. Such
    /// access is restricted to this and neghbor modules, so this function is also restricted.
    pub(super) fn insert_behind(
        &'item mut self,
        existing: &mut ListItem<'item, T>,
    ) -> ListItemToken<'item, T> {
        if self.next.is_some() {
            panic!("Next link of an item is set indicating it is added to a list. But if it is added to a list it's user shall not have access to mutable reference to an item to call this function.");
        }

        let following = existing.next.take();
        self.next = following;

        let token = ListItemToken { ptr: self };

        existing.next.replace(self);

        token
    }

    /// Get reference to the next item in the list
    ///
    /// This method is intended to be used by the list iterator implementation.
    pub(super) fn get_next(&self) -> &Option<&'item mut ListItem<'item, T>> {
        &self.next
    }

    /// Get reference to the data kept by this item and reference to the next item in the list
    ///
    /// This method is intended to be used by the list mutable iterator implementation.
    pub(super) fn get_mut_data_and_next(
        &mut self,
    ) -> (&mut T, &mut Option<&'item mut ListItem<'item, T>>) {
        (&mut self.item, &mut self.next)
    }
}

impl<'item, T> Deref for ListItem<'item, T> {
    type Target = T;

    fn deref(&self) -> &<Self as Deref>::Target {
        &self.item
    }
}

impl<'item, T> DerefMut for ListItem<'item, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}

/// Token representing a list item.
///
/// When a linked list user adds an item to the linked list it mutably borrows the item to the list
/// for the list's lifetime. Because of this the list user cannot use mutable or immutable
/// reference to an item while the item is linked with the list. To be able to represent an item in
/// the [linked list](LinkedList) API in some other way than by a reference to an item, this token
/// is used.
///
/// The token is returned when an item is successfully added to a list.
///
/// The token can be exchanged for a mutable reference to the list item by removing the item from
/// the list. In such operation the list returns previously mutably borrowed reference.
///
/// More on the token usage in the linked list's methods using token.
#[derive(Debug, Eq, PartialEq)]
pub struct ListItemToken<'item, T> {
    ptr: *mut ListItem<'item, T>,
}

/// The type representing a linked list.
#[derive(Default)]
pub struct LinkedList<'list, T> {
    first: Option<&'list mut ListItem<'list, T>>,
}

impl<'list, T> LinkedList<'list, T> {
    /// Create an empty linked list
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::LinkedList;
    ///
    /// let list = LinkedList::<usize>::new();
    /// ```
    pub fn new() -> Self {
        Self { first: None }
    }

    /// Add an item at the head of the list
    ///
    /// An item must be mutable to be added to a list.
    ///
    /// When an item is added, the [`LinkedList`] mutably borrows the item for as long as the item
    /// is in the list. You can't use mutable or immutable reference to the item while it is added
    /// to the list (because of this exclusive borrow). To represent the added item while
    /// interacting with the [`LinkedList`] you must use other object, which created when you add
    /// an item: a [token](ListItemToken). When an item is added to the list, the list exclusively
    /// borrows the item from you, however in exchange you get a [token](ListItemToken), like in a
    /// cloakroom. You can use the token to get the exclusively borrowed item back.
    ///
    /// # Examples
    /// ```
    /// use nrf_radio::utils::linked_list::{LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.push(&mut item);
    /// ```
    pub fn push(&mut self, item: &'list mut ListItem<'list, T>) -> ListItemToken<'list, T> {
        if item.next.is_some() {
            panic!("Next link of an item is set indicating it is added to a list. But if it is added to a list it's user shall not have access to mutable reference to an item to call this function.");
        }

        let next = self.first.take();
        item.next = next;

        // Token must be created after item is modified to make miri happy, but after it is moved
        // to self.first to make borrow checker happy.
        let token = ListItemToken { ptr: item };

        self.first.replace(item);

        token
    }

    /// Get an item from the head of the list
    ///
    /// This action removes the retrieved item from the list.
    /// Actually, you don't get an owenrship of the item, but you exclusively borrows the item from
    /// its owner (the borrow is passed from the list to you).
    ///
    /// You don't need a [token](ListItemToken) to pop an item from the list. Tokens are needed to
    /// precisely identify one item, but popping gets any item that happens to be at the head.
    ///
    /// # Examples
    /// ```
    /// use nrf_radio::utils::linked_list::{LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.push(&mut item);
    ///
    /// let item_option = list.pop();
    /// assert!(item_option.is_some());
    /// let item_ref = item_option.unwrap();
    /// assert_eq!(**item_ref, "Hello");
    ///
    /// let item_option = list.pop();
    /// assert!(item_option.is_none());
    /// ```
    pub fn pop(&mut self) -> Option<&'list mut ListItem<'list, T>> {
        let mut item = self.first.take();

        if let Some(item) = item.as_mut() {
            self.first = item.next.take();
        }

        item
    }

    /// Exchange a token for mutable referenece to an item
    ///
    /// # Safety
    ///
    /// Call this function only when you know that the item represented by this function was already
    /// removed from the list (e.g. with the [`pop`](LinkedList::pop) function) and dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::{LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.push(&mut item);
    ///
    /// {
    ///   let item_option = list.pop();
    ///   assert!(item_option.is_some());
    ///   let item_ref = item_option.unwrap();
    ///   assert_eq!(**item_ref, "Hello");
    ///
    ///   // The popped reference is dropped at the end of this block.
    /// }
    ///
    /// unsafe {
    ///   // Item was already popped from the list, and it's reference is dropped.
    ///   // get_unchecked() can be safely used.
    ///
    ///   let item_ref = list.get_unchecked(token);
    ///   assert_eq!(**item_ref, "Hello");
    /// }
    /// ```
    pub unsafe fn get_unchecked(
        &mut self,
        token: ListItemToken<'list, T>,
    ) -> &'list mut ListItem<'list, T> {
        token.ptr.as_mut().unwrap()
    }

    /// Remove an element from this list
    ///
    /// Remove from the list an element represented by passed [token](ListItemToken).
    ///
    /// # Examples
    ///
    /// If the element is found in the list, exclusive borrow is returned to you.
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::{LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.push(&mut item);
    ///
    /// let remove_result = list.remove(token);
    /// assert!(remove_result.is_ok());
    /// let item_ref = remove_result.unwrap();
    /// assert_eq!(**item_ref, "Hello");
    /// ```
    ///
    /// If the element is missing in the list, the token is returned to you.
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::{Error, LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.push(&mut item);
    ///
    /// list.pop();
    ///
    /// let remove_result = list.remove(token);
    /// let remove_error_option = remove_result.err();
    /// assert!(remove_error_option.is_some());
    /// let remove_error = remove_error_option.unwrap();
    ///
    /// match remove_error {
    ///   Error::NotFound(token) => {
    ///     // token can be stored for further usage
    ///   }
    ///   _ => panic!("Unexpected error"),
    /// }
    /// ```
    pub fn remove(
        &mut self,
        token: ListItemToken<'list, T>,
    ) -> Result<&'list mut ListItem<'list, T>, Error<'list, T>> {
        enum PrevItem<'list, T> {
            ListHead(*mut LinkedList<'list, T>),
            ListItem(*mut ListItem<'list, T>),
        }

        let mut curr_item_option: *mut Option<&'list mut ListItem<'list, T>> = &mut self.first;
        let mut prev_item = PrevItem::ListHead(self);

        // Safety:
        //  There are no races, because this function takes mutable reference to self, so no
        //  other function can modify the list while this is being executed.
        //  item_option pointer is never dangling, becaust it points the self.first option which is
        //  valid through the lifetime of self (whole function code).
        //  prev_item pointers are never dangling. ListHead points only to self which is valid
        //  through whole function code. ListItem points to items from the list: each of the
        //  items in the list must have 'list lifetime, so at least as long as self.
        //  item_ptr is never dangling, because it points to an item from the list
        //  Is there any other reason why this function could be unsound?
        //
        //  Moreover, now miri claims it's fine
        unsafe {
            // TODO: create an iterator instead?
            while let Some(curr_item) = &mut *curr_item_option {
                let curr_item_ptr: *mut ListItem<'list, T> = *curr_item;
                if curr_item_ptr == token.ptr {
                    match prev_item {
                        PrevItem::ListHead(list) => (*list).first = curr_item.next.take(),
                        PrevItem::ListItem(prev_item) => (*prev_item).next = curr_item.next.take(),
                    }
                    return Ok(&mut *curr_item_ptr);
                } else {
                    prev_item = PrevItem::ListItem(curr_item_ptr);
                    curr_item_option = &mut (*curr_item_ptr).next;
                }
            }
            Err(Error::NotFound(token))
        }
    }

    /// Returns an iterator over the list.
    ///
    /// The iterator yields all linked items.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::{LinkedList, ListItem};
    ///
    /// let mut list = LinkedList::new();
    /// let mut item1 = ListItem::new(1);
    /// let mut item2 = ListItem::new(2);
    ///
    /// list.push(&mut item1);
    /// list.push(&mut item2);
    ///
    /// let sum: i32 = list.iter().sum();
    /// assert_eq!(sum, 3);
    /// ```
    pub fn iter(&self) -> Iter<'_, 'list, T> {
        Iter::new(self)
    }

    /// Returns reference to the first item in the list or None if the list is empty.
    ///
    /// This method is intended to be used by an iterator implementation.
    pub(super) fn get_first(&self) -> &Option<&'list mut ListItem<'list, T>> {
        &self.first
    }

    /// Returns mutable reference to the first item in the list or None if the list is empty.
    ///
    /// This method is intended to be used by a mutable iterator implementation.
    pub(super) fn get_mut_first(&mut self) -> &mut Option<&'list mut ListItem<'list, T>> {
        &mut self.first
    }
}

// Cannot impl<'list, T> IntoIterator for LinkedList<'list, T>, because LinkedList does not own T.
// It owns only &'list mut T.

impl<'iter, 'list, T> IntoIterator for &'iter LinkedList<'list, T> {
    type Item = &'iter T;
    type IntoIter = Iter<'iter, 'list, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_and_pop_single_list_item() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(5);

        list.push(&mut item);
        let retrieved_item = list.pop().unwrap();

        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, 5);

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_push_and_pop_multiple_integers() {
        const N: usize = 100;
        let mut list = LinkedList::new();
        let mut items = Vec::new();

        for i in 0..N {
            items.push(ListItem::new(i));
        }

        for item in items.iter_mut() {
            list.push(item);
        }

        for i in 0..N {
            let retrieved_item = list.pop().unwrap();

            let retrieved_value = **retrieved_item;
            assert_eq!(retrieved_value, N - 1 - i);
        }

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_push_and_remove_single_list_item() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(5);

        let token = list.push(&mut item);
        let retrieved_item = list.remove(token).unwrap();

        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, 5);

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_push_and_remove_already_removed_item() {
        let mut list = LinkedList::new();
        let mut item = ListItem::new(5);

        let token = list.push(&mut item);
        let token_ptr = token.ptr;
        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, 5);

        let retrieve_result = list.remove(token);
        assert_eq!(
            retrieve_result,
            Err(Error::NotFound(ListItemToken { ptr: token_ptr }))
        );
    }

    #[test]
    fn test_remove_head() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut middle = ListItem::new("middle");
        let mut tail = ListItem::new("tail");

        list.push(&mut tail);
        list.push(&mut middle);
        let token = list.push(&mut head);

        let retrieved_item = list.remove(token).unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "middle");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "tail");

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_remove_tail() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut middle = ListItem::new("middle");
        let mut tail = ListItem::new("tail");

        let token = list.push(&mut tail);
        list.push(&mut middle);
        list.push(&mut head);

        let retrieved_item = list.remove(token).unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "tail");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "middle");

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_remove_middle() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut middle = ListItem::new("middle");
        let mut tail = ListItem::new("tail");

        list.push(&mut tail);
        let token = list.push(&mut middle);
        list.push(&mut head);

        let retrieved_item = list.remove(token).unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "middle");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "tail");

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_iter() {
        let mut list = LinkedList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);
        let mut item3 = ListItem::new(3);

        list.push(&mut item1);
        list.push(&mut item2);
        list.push(&mut item3);

        let iter = list.iter();
        assert_eq!(iter.sum::<u32>(), 6u32);
    }

    #[test]
    fn test_into_iter() {
        let mut list = LinkedList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);
        let mut item3 = ListItem::new(3);

        list.push(&mut item1);
        list.push(&mut item2);
        list.push(&mut item3);

        let mut cnt = 0;

        for _item in &list {
            cnt += 1;
        }

        assert_eq!(cnt, 3);
    }

    #[test]
    fn test_insert_behind_the_only_element() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut new = ListItem::new("new");

        list.push(&mut head);

        let existing = list.get_mut_first().as_mut().unwrap();

        new.insert_behind(existing);

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "new");

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_insert_behind_the_tail() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut tail = ListItem::new("tail");
        let mut new = ListItem::new("new");

        list.push(&mut tail);
        list.push(&mut head);

        let head = list.get_mut_first().as_mut().unwrap();
        let (_, tail) = head.get_mut_data_and_next();
        let tail = tail.as_mut().unwrap();

        new.insert_behind(tail);

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "tail");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "new");

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_insert_behind_the_head() {
        let mut list = LinkedList::new();
        let mut head = ListItem::new("head");
        let mut tail = ListItem::new("tail");
        let mut new = ListItem::new("new");

        list.push(&mut tail);
        list.push(&mut head);

        let head = list.get_mut_first().as_mut().unwrap();

        new.insert_behind(head);

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "head");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "new");

        let retrieved_item = list.pop().unwrap();
        let retrieved_value = **retrieved_item;
        assert_eq!(retrieved_value, "tail");

        assert!(list.pop().is_none());
    }
}
