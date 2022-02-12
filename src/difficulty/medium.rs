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
}

impl ListNode {
    fn add_next(&mut self, val: i32) {
        self.next = ListNode::create_from_value(val);
    }

    fn create_from_value(val: i32) -> Option<Box<ListNode>> {
        Some(Box::new(ListNode::new(val)))
    }

    fn create_from_vect(vals: Vec<i32>) -> Option<Box<ListNode>> {
        if vals.is_empty() {
            panic!("Input vector cannot be empty");
        }
        let mut head = ListNode::new(*vals.first().unwrap());
        let mut tail = &mut head;
        for i in 1..vals.len() {
            tail.add_next(vals[i]);
            tail = tail.next.as_deref_mut().unwrap();
        }

        Some(Box::new(head))
    }
}

pub fn add_two_numbers(
    l1: Option<Box<ListNode>>,
    l2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    let mut result_head = ListNode::new(0);
    let mut result_tail = &mut result_head;

    let mut a1 = &l1;
    let mut a2 = &l2;

    let mut remainder = 0;
    loop {
        let addend1 = match a1 {
            Some(v) => {
                a1 = &a1.as_deref().unwrap().next;
                v.as_ref().val
            }
            _ => 0,
        };

        let addend2 = match a2 {
            Some(v) => {
                a2 = &a2.as_deref().unwrap().next;
                v.as_ref().val
            }
            _ => 0,
        };

        let partial_sum = add_addends(addend1, addend2, remainder);

        result_tail.add_next(partial_sum.0);
        result_tail = result_tail.next.as_deref_mut().unwrap();

        remainder = partial_sum.1;

        if a1.is_none() && a2.is_none() {
            if remainder > 0 {
                result_tail.add_next(remainder);
            }
            break;
        }
    }

    result_head.next
}

/// Used to implement the partial sum of two number plus the remainder of a previous one
/// Return a tuple containing the unit part and the remainder for the next addiction
fn add_addends(addend1: i32, addend2: i32, remainder: i32) -> (i32, i32) {
    assert!(addend1 >= 0 && addend1 <= 9);
    assert!(addend2 >= 0 && addend2 <= 9);
    assert!(remainder >= 0 && remainder <= 9);

    let tmp_sum = addend1 + addend2 + remainder;
    let res = tmp_sum % 10; // extract the unit part
    let rem = (tmp_sum - res) % 9; // extract the ten part

    (res, rem)
}

#[cfg(test)]
mod tests {

    use super::*;

    // -----------------------
    // 2. Add Two Numbers
    // -----------------------
    #[test]
    fn test_add_addends_with_no_input_remainder_no_out_remainder() {
        let result = add_addends(4, 5, 0);
        assert_eq!(result, (9, 0))
    }

    #[test]
    fn test_add_addends_with_in_remainder_no_out_remainder() {
        let result = add_addends(3, 2, 1);
        assert_eq!(result, (6, 0))
    }

    #[test]
    fn test_add_addends_with_in_remainder_and_out_remainder() {
        let result = add_addends(6, 5, 1);
        assert_eq!(result, (2, 1))
    }

    #[test]
    fn test_add_addends_with_in_remainder_and_out_remainder_max() {
        let result = add_addends(9, 9, 9);
        assert_eq!(result, (7, 2))
    }

    #[test]
    #[should_panic]
    fn test_add_addend_with_two_digits_addend1() {
        add_addends(10, 9, 9);
    }

    #[test]
    #[should_panic]
    fn test_add_addend_with_two_digits_addend2() {
        add_addends(9, 10, 9);
    }

    #[test]
    #[should_panic]
    fn test_add_addend_with_two_digits_remainder() {
        add_addends(9, 9, 10);
    }

    #[test]
    #[should_panic]
    fn test_list_node_new_from_empty_vect_should_panic() {
        let vals: Vec<i32> = Vec::new();
        ListNode::create_from_vect(vals);
    }

    #[test]
    fn test_list_node_new_from_vect() {
        let vals = vec![2, 4, 3];
        let list_nodes = ListNode::create_from_vect(vals);

        let list_node = list_nodes.unwrap();

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
        let l1 = ListNode::create_from_vect(vec![2, 4, 3]);
        let l2 = ListNode::create_from_vect(vec![5, 6, 4]);

        // Output: [7,0,8]
        let result = add_two_numbers(l1, l2);
        assert_eq!(result, ListNode::create_from_vect(vec![7, 0, 8]));
    }

    #[test]
    fn test_add_two_numbers_example_2() {
        // Input: l1 = [0], l2 = [0]
        let l1 = ListNode::create_from_vect(vec![0]);
        let l2 = ListNode::create_from_vect(vec![0]);

        // Output: [0]
        let result = add_two_numbers(l1, l2);
        assert_eq!(result, ListNode::create_from_vect(vec![0]));
    }

    #[test]
    fn test_add_two_numbers_example_3() {
        // Input: l1 = [9,9,9,9,9,9,9], l2 = [9,9,9,9]
        let l1 = ListNode::create_from_vect(vec![9, 9, 9, 9, 9, 9, 9]);
        let l2 = ListNode::create_from_vect(vec![9, 9, 9, 9]);

        // Output: [8,9,9,9,0,0,0,1]
        let result = add_two_numbers(l1, l2);
        assert_eq!(
            result,
            ListNode::create_from_vect(vec![8, 9, 9, 9, 0, 0, 0, 1])
        );
    }
}
