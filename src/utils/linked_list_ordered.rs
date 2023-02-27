//! [`LinkedList`] variants maintaining items in the list in order

use super::linked_list::{Error, LinkedList, ListItem, ListItemToken};

/// [`LinkedList`] variant keeping items in ascending order
///
/// This structure is implemented as a wrapper around [`LinkedList`] to prevent users from using
/// functions which could mess with the order like [`LinkedList::push`].
///
/// # Example
///
/// ```
/// use nrf_radio::utils::linked_list::ListItem;
/// use nrf_radio::utils::linked_list_ordered::AscendingList;
///
/// let mut list = AscendingList::new();
///
/// let mut item1 = ListItem::new(1);
/// let mut item2 = ListItem::new(2);
/// let mut item3 = ListItem::new(3);
///
/// list.insert(&mut item1);
/// list.insert(&mut item3);
/// list.insert(&mut item2);
///
/// let retrieved_ref = list.pop().unwrap();
/// assert_eq!(retrieved_ref.get_data(), &1);
///
/// let retrieved_ref = list.pop().unwrap();
/// assert_eq!(retrieved_ref.get_data(), &2);
///
/// let retrieved_ref = list.pop().unwrap();
/// assert_eq!(retrieved_ref.get_data(), &3);
///
/// assert!(list.pop().is_none());
/// ```
pub struct AscendingList<'list, T: Ord>(LinkedList<'list, T>);

impl<'list, T> AscendingList<'list, T>
where
    T: Ord,
{
    /// Creates a new instance with an empty list
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list_ordered::AscendingList;
    ///
    /// let mut list = AscendingList::<usize>::new();
    /// ```
    pub fn new() -> Self {
        Self(LinkedList::new())
    }

    /// Removes and returns the first item in the linked list, if any.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list_ordered::AscendingList;
    ///
    /// let mut list = AscendingList::<&str>::new();
    ///
    /// let result = list.pop();
    /// assert!(result.is_none());
    /// ```
    pub fn pop(&mut self) -> Option<&'list mut ListItem<'list, T>> {
        self.0.pop()
    }

    /// Inserts a new item into the linked list, maintaining the ascending order.
    ///
    /// The `new` parameter is a mutable reference to the item to be inserted. Returns a
    /// [`ListItemToken`] that can be used to remove the inserted item from the linked list.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::ListItem;
    /// use nrf_radio::utils::linked_list_ordered::AscendingList;
    ///
    /// let mut list = AscendingList::new();
    /// let mut item = ListItem::new("Hello");
    ///
    /// let token = list.insert(&mut item);
    /// ```
    pub fn insert(&mut self, new: &'list mut ListItem<'list, T>) -> ListItemToken<'list, T> {
        let mut prev_option = self.0.get_mut_first();

        if let Some(first) = prev_option {
            if first.get_data() >= new {
                return self.0.push(new);
            }
        }

        // TODO: Can I use some kind of iterator instead, with peek option?
        //       So far my attempts with an iterator returning a mutable reference to the
        //       consecutive ListItems resulted in Undefined Behavior according to miri. I tend to
        //       agree with this judgement.
        //       It is hard, because when iterator's user would get a mutable reference to a
        //       ListItem instance with iterator's lifetime, it could modify the instance while the
        //       iterator is progressing, breaking iteration coherency. Maybe the returned iterator
        //       should be not Send to prevent "while" part of the statement. And then it could be
        //       safely implemented on raw pointers to share a mutable reference with certain
        //       constrains showed by API and traits?
        //       Anyway, such improvement seems an overkill and I'll leave the implementation as it
        //       is right now.
        while let Some(prev) = prev_option {
            let next_option = prev.get_next();
            if let Some(next) = next_option {
                if next.get_data() >= new {
                    return new.insert_behind(prev);
                }
            } else {
                // Insert as the last element in the list
                return new.insert_behind(prev);
            }

            (_, prev_option) = prev.get_mut_data_and_next();
        }

        self.0.push(new)
    }

    /// Removes the item represented by the provided `token` from the linked list.
    ///
    /// Returns a mutable reference to the removed item on success, or an `Error` if the
    /// `token` is invalid or points to a different list.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::utils::linked_list::ListItem;
    /// use nrf_radio::utils::linked_list_ordered::AscendingList;
    ///
    /// let mut list = AscendingList::new();
    /// let mut item1 = ListItem::new("Hello");
    /// let mut item2 = ListItem::new("world");
    ///
    /// let token1 = list.insert(&mut item1);
    /// let token2 = list.insert(&mut item2);
    ///
    /// let result = list.remove(token1);
    /// assert!(result.is_ok());
    ///
    /// let item1_ref = result.unwrap();
    /// assert_eq!(item1_ref.get_data(), &"Hello");
    /// ```
    pub fn remove(
        &mut self,
        token: ListItemToken<'list, T>,
    ) -> Result<&'list mut ListItem<'list, T>, Error<'list, T>> {
        self.0.remove(token)
    }
}

impl<T> Default for AscendingList<'_, T>
where
    T: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_greater_int_first() {
        let mut list = AscendingList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);

        list.insert(&mut item2);
        list.insert(&mut item1);

        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 1);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 2);

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_insert_lower_int_first() {
        let mut list = AscendingList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);

        list.insert(&mut item1);
        list.insert(&mut item2);

        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 1);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 2);

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_insert_middle_int_first() {
        let mut list = AscendingList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);
        let mut item3 = ListItem::new(3);

        list.insert(&mut item2);
        list.insert(&mut item1);
        list.insert(&mut item3);

        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 1);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 2);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 3);

        assert!(list.pop().is_none());
    }

    #[test]
    fn test_insert_middle_int_last() {
        let mut list = AscendingList::new();
        let mut item1 = ListItem::new(1);
        let mut item2 = ListItem::new(2);
        let mut item3 = ListItem::new(3);

        list.insert(&mut item1);
        list.insert(&mut item3);
        list.insert(&mut item2);

        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 1);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 2);
        let item_ref = list.pop().unwrap();
        assert_eq!(**item_ref, 3);

        assert!(list.pop().is_none());
    }
}
