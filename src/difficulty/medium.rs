use std::cmp;
use std::collections::{HashSet, LinkedList};

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

/*
3. Longest Substring Without Repeating Characters
https://leetcode.com/problems/longest-substring-without-repeating-characters/

Given a string s, find the length of the longest substring without repeating characters.

Constraints:

0 <= s.length <= 5 * 10^4
s consists of English letters, digits, symbols and spaces.
*/
pub fn length_of_longest_substring(s: String) -> i32 {
    // TODO - Implement with BTreeMap
    let mut dict: HashSet<char> = HashSet::new();
    let mut llist: LinkedList<char> = LinkedList::new();

    let mut max = 0;

    for c in s.chars() {
        if dict.insert(c) {
            // found a new char in the sequence
            llist.push_back(c);
        } else {
            // found a repeated char in the sequence
            max = cmp::max(max, llist.len());
            llist.push_back(c);

            // readjusting the current sequence
            loop {
                let front = llist.pop_front();
                if front.is_none() {
                    break;
                }

                let tmp_c = front.unwrap();
                if tmp_c == c {
                    break;
                }
                dict.remove(&tmp_c);
            }
        }
    }

    cmp::max(max, llist.len()) as i32
}

/*
8. String to Integer (atoi)
https://leetcode.com/problems/string-to-integer-atoi/

Implement the myAtoi(string s) function, which converts a string to a 32-bit signed integer (similar to C/C++'s atoi function).

The algorithm for myAtoi(string s) is as follows:

Read in and ignore any leading whitespace.
Check if the next character (if not already at the end of the string) is '-' or '+'.
Read this character in if it is either.
This determines if the final result is negative or positive respectively.
Assume the result is positive if neither is present.
Read in next the characters until the next non-digit character or the end of the input is reached.
The rest of the string is ignored.
Convert these digits into an integer (i.e. "123" -> 123, "0032" -> 32).
If no digits were read, then the integer is 0.
Change the sign as necessary (from step 2).
If the integer is out of the 32-bit signed integer range [-2^31, 2^31 - 1], then clamp the integer so that it remains in the range.
Specifically, integers less than -2^31 should be clamped to -2^31, and integers greater than 2^31 - 1 should be clamped to 2^31 - 1.
Return the integer as the final result.

Note:
Only the space character ' ' is considered a whitespace character.
Do not ignore any characters other than the leading whitespace or the rest of the string after the digits.

Constraints:

0 <= s.length <= 200
s consists of English letters (lower-case and upper-case), digits (0-9), ' ', '+', '-', and '.'
*/
pub fn my_atoi(s: String) -> i32 {
    if s.is_empty() {
        return 0;
    }

    let mut sign: i32 = 1;
    let mut number: i32 = 0;
    let mut current_state = AtoiParseState::new();

    for c in s.chars() {
        current_state = current_state.consume(c);
        match current_state {
            AtoiParseState::Trailing => (),
            AtoiParseState::Sign(s) => sign = s,
            AtoiParseState::Number(n) => {
                if sign < 0 && number > 0 {
                    number *= sign;
                }
                number = number.saturating_mul(10);
                number = number.saturating_add(n * sign);
            }
            AtoiParseState::End => break,
        }
    }

    number
}

#[derive(Debug, PartialEq, Eq)]
enum AtoiParseState {
    Trailing,
    Sign(i32),
    Number(i32),
    End,
}

impl AtoiParseState {
    fn new() -> AtoiParseState {
        AtoiParseState::Trailing
    }

    fn consume(&self, c: char) -> AtoiParseState {
        match self {
            AtoiParseState::Trailing => {
                if c == ' ' {
                    AtoiParseState::Trailing
                } else if c == '+' {
                    AtoiParseState::Sign(1)
                } else if c == '-' {
                    AtoiParseState::Sign(-1)
                } else if c.is_ascii_digit() {
                    AtoiParseState::Number(c.to_digit(10).unwrap() as i32)
                } else {
                    AtoiParseState::End
                }
            },
            AtoiParseState::Sign(_) => {
                if c.is_ascii_digit() {
                    AtoiParseState::Number(c.to_digit(10).unwrap() as i32)
                } else {
                    AtoiParseState::End
                }
            },
            AtoiParseState::Number(_) => {
                if c.is_ascii_digit() {
                    AtoiParseState::Number(c.to_digit(10).unwrap() as i32)
                } else {
                    AtoiParseState::End
                }
            },
            AtoiParseState::End => AtoiParseState::End,
        }
    }
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

    // -----------------------
    // 3. Longest Substring Without Repeating Characters
    // -----------------------

    #[test]
    fn test_length_of_longest_substring_example_1() {
        let input = String::from("abcabcbb");
        let output = length_of_longest_substring(input);
        assert_eq!(output, 3);
    }

    #[test]
    fn test_length_of_longest_substring_example_2() {
        let input = String::from("bbbbb");
        let output = length_of_longest_substring(input);
        assert_eq!(output, 1);
    }

    #[test]
    fn test_length_of_longest_substring_example_3() {
        let input = String::from("pwwkew");
        let output = length_of_longest_substring(input);
        assert_eq!(output, 3);
    }

    #[test]
    fn test_length_of_longest_substring_wrong_answer_1() {
        let input = String::from("dvdf");
        let output = length_of_longest_substring(input);
        assert_eq!(output, 3);
    }

    // -----------------------
    // 8. String to Integer (atoi)
    // -----------------------

    #[test]
    fn test_my_atoi_example_1() {
        let result = my_atoi(String::from("42"));
        assert_eq!(result, 42);
    }

    #[test]
    fn test_my_atoi_example_1_1() {
        let result = my_atoi(String::from("+42"));
        assert_eq!(result, 42);
    }

    #[test]
    fn test_my_atoi_example_2() {
        let result = my_atoi(String::from("   -42"));
        assert_eq!(result, -42);
    }

    #[test]
    fn test_my_atoi_example_3() {
        let result = my_atoi(String::from("4193 with words"));
        assert_eq!(result, 4193);
    }

    #[test]
    fn test_my_atoi_all_trailing_spaces_input() {
        let result = my_atoi(String::from("       "));
        assert_eq!(result, 0);
    }

    #[test]
    fn test_my_atoi_trailing_spaces_and_sign_input() {
        let result = my_atoi(String::from("       +"));
        assert_eq!(result, 0);
    }

    #[test]
    fn test_my_atoi_trailing_spaces_sign_letters_input() {
        let result = my_atoi(String::from("       +foobar"));
        assert_eq!(result, 0);
    }

    #[test]
    fn test_my_atoi_trailing_spaces_as_zeroes_input() {
        assert_eq!(0, my_atoi(String::from("  00")));
        assert_eq!(0, my_atoi(String::from("  -00")));
        assert_eq!(666, my_atoi(String::from("  00666")));
        assert_eq!(666, my_atoi(String::from("00666")));
        assert_eq!(-666, my_atoi(String::from("  -00666")));
        assert_eq!(666, my_atoi(String::from("  00666foo")));
    }

    #[test]
    fn test_my_atoi_integer_overflow() {
        assert_eq!(i32::MIN, my_atoi(String::from("-91283472332")));
        assert_eq!(i32::MAX, my_atoi(String::from("91283472332")));
    }
}
