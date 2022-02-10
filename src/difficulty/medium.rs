pub fn say_hello(name: &str) {
    println!("Hello {}, I'm feeling particularly rusty today!", name);
}

/*
2. Add Two Numbers
https://leetcode.com/problems/add-two-numbers/

You are given two non-empty linked lists representing two non-negative integers.
The digits are stored in reverse order, and each of their nodes contains a single digit.
Add the two numbers and return the sum as a linked list.

You may assume the two numbers do not contain any leading zero, except the number 0 itself.

Constraints:

The number of nodes in each linked list is in the range [1, 100].
0 <= Node.val <= 9
It is guaranteed that the list represents a number that does not have leading zeros.
*/

//Definition for singly-linked list.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }

    fn add_next(&mut self, val: i32) {
        self.next = ListNode::wrap(val);
    }

    fn wrap(val: i32) -> Option<Box<ListNode>> {
        Some(Box::new(ListNode::new(val)))
    }

    fn new_from_vect(vals: Vec<i32>) -> Self {
        if vals.is_empty() {
            panic!("Input vector cannot be empty");
        }
        let mut head = ListNode::new(*vals.first().unwrap());
        let mut tail = &mut head;
        for i in 1..vals.len() {
            tail.add_next(vals[i]);
            tail = Option::as_deref_mut(&mut tail.next).unwrap();
        }

        head
    }
}

pub fn add_two_numbers(
    l1: Option<Box<ListNode>>,
    l2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    todo!()
}

#[cfg(test)]
mod tests {

    use super::*;

    // -----------------------
    // 2. Add Two Numbers
    // -----------------------

    #[test]
    #[should_panic]
    fn test_list_node_new_from_empty_vect_should_panic() {
        let vals: Vec<i32> = Vec::new();
        ListNode::new_from_vect(vals);
    }

    #[test]
    fn test_list_node_new_from_vect() {
        let vals = vec![2, 4, 3];
        let list_node = ListNode::new_from_vect(vals);
        assert_eq!(list_node.val, 2);
        assert!(list_node.next.is_some());

        let next = list_node.next.unwrap();
        assert_eq!(next.val, 4);
        assert!(next.next.is_some());

        let next = next.next.unwrap();
        assert_eq!(next.val, 3);
        assert!(next.next.is_none());
    }

    #[test]
    fn test_add_two_numbers_example_1() {
        // Input: l1 = [2,4,3], l2 = [5,6,4]
        // Output: [7,0,8]
        // Explanation: 342 + 465 = 807.

        // let l1 = Some(
        //     Box::new(ListNode::node(
        //     2,
        //     Some(Box::new(ListNode::new(4, Some(Box::new(ListNode::new(3)))))),
        // )));

        // let b1 = Some(Box::new(ListNode::new(5)));
        // let b2 = Some(Box::new(ListNode::new(6)));
        // let b3 = Some(Box::new(ListNode::new(4)));
    }

    #[test]
    fn test_add_two_numbers_example_2() {
        // Input: l1 = [0], l2 = [0]
        // Output: [0]
    }

    #[test]
    fn test_add_two_numbers_example_3() {
        // Input: l1 = [9,9,9,9,9,9,9], l2 = [9,9,9,9]
        // Output: [8,9,9,9,0,0,0,1]
    }
}
