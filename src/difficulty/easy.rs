use std::collections::HashMap;

pub fn say_hello() {
    println!("Hello, I'm feeling particularly rusty today!");
}

/*
01 - https://leetcode.com/problems/two-sum/

Given an array of integers nums and an integer target,
return indices of the two numbers such that they add up to target.

You may assume that each input would have exactly one solution,
and you may not use the same element twice.

Constraints:

2 <= nums.length <= 10^4
-10^9 <= nums[i] <= 10^9
-10^9 <= target <= 10^9
Only one valid answer exists.

*/
pub fn two_sum(nums: Vec<i32>, target: i32) -> Vec<i32> {
    //k=num value, v=num index in nums
    let mut addends: HashMap<i32, i32> = HashMap::new();

    for (i, val) in nums.iter().enumerate() {
        // calculate the necessary addend
        let difference = target - val;
        if let Some(e) = addends.get(&difference) {
            //found
            let mut result = vec![i as i32, *e];
            result.sort();
            return result;
        } else {
            addends.insert(*val, i as i32);
        }
    }

    vec![]
}

/*
9. Palindrome Number
https://leetcode.com/problems/palindrome-number/

Given an integer x, return true if x is palindrome integer.

An integer is a palindrome when it reads the same backward as forward.

For example, 121 is a palindrome while 123 is not.

Constraints:

-2^31 <= x <= 2^31 - 1

*/
pub fn is_palindrome(x: i32) -> bool {
    let s = x.to_string();
    let r: String = s.chars().rev().collect();
    s == r
}

/*
13. Roman to Integer
https://leetcode.com/problems/roman-to-integer/

Roman numerals are represented by seven different symbols: I, V, X, L, C, D and M.

Symbol       Value
I             1
V             5
X             10
L             50
C             100
D             500
M             1000

For example, 2 is written as II in Roman numeral, just two one's added together.
12 is written as XII, which is simply X + II.
The number 27 is written as XXVII, which is XX + V + II.

Roman numerals are usually written largest to smallest from left to right.
However, the numeral for four is not IIII.
Instead, the number four is written as IV.
Because the one is before the five we subtract it making four.
The same principle applies to the number nine, which is written as IX.

There are six instances where subtraction is used:

I can be placed before V (5) and X (10) to make 4 and 9.
X can be placed before L (50) and C (100) to make 40 and 90.
C can be placed before D (500) and M (1000) to make 400 and 900.

GOAL:
Given a roman numeral, convert it to an integer.

*/
pub fn roman_to_int(s: String) -> i32 {
    let i = RomanGliph::new('I', None, 1);
    let v = RomanGliph::new('V', Some(Box::new(&i)), 5);
    let x = RomanGliph::new('X', Some(Box::new(&i)), 10);
    let l = RomanGliph::new('L', Some(Box::new(&x)), 50);
    let c = RomanGliph::new('C', Some(Box::new(&x)), 100);
    let d = RomanGliph::new('D', Some(Box::new(&c)), 500);
    let m = RomanGliph::new('M', Some(Box::new(&c)), 1000);

    let mut dictionary: HashMap<char, &RomanGliph> = HashMap::new();
    dictionary.insert(i.symbol, &i);
    dictionary.insert(v.symbol, &v);
    dictionary.insert(x.symbol, &x);
    dictionary.insert(l.symbol, &l);
    dictionary.insert(c.symbol, &c);
    dictionary.insert(d.symbol, &d);
    dictionary.insert(m.symbol, &m);

    let mut sum = 0;
    let mut prev: Option<char> = None;
    for c in s.chars() {
        let current_gliph = match dictionary.get(&c) {
            Some(v) => v,
            _ => panic!(),
        };

        sum += current_gliph.value;
        if prev.is_some() {
            let prev_gliph = prev.unwrap();
            if current_gliph.get_prev_symbol() == prev_gliph {
                sum -= current_gliph.get_prev_value() * 2;
            }
        }

        prev = Some(c);
    }

    sum
}

struct RomanGliph<'a> {
    symbol: char,
    prev: Option<Box<&'a RomanGliph<'a>>>,
    value: i32,
}

impl<'a> RomanGliph<'a> {
    fn new(symbol: char, prev: Option<Box<&'a RomanGliph>>, value: i32) -> RomanGliph<'a> {
        RomanGliph {
            symbol,
            prev,
            value,
        }
    }

    fn get_prev_symbol(&self) -> char {
        match &self.prev {
            Some(v) => v.as_ref().symbol,
            None => '_',
        }
    }

    fn get_prev_value(&self) -> i32 {
        match &self.prev {
            Some(v) => v.as_ref().value,
            None => 0,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_two_sum_example_1() {
        let nums = vec![2, 7, 11, 15];
        let target = 9;

        let result = two_sum(nums, target);
        assert_eq!(result, vec![0, 1]);
    }

    #[test]
    fn test_two_sum_example_2() {
        let nums = vec![3, 2, 4];
        let target = 6;

        let result = two_sum(nums, target);
        assert_eq!(result, vec![1, 2]);
    }

    #[test]
    fn test_two_sum_example_3() {
        let nums = vec![3, 3];
        let target = 6;

        let result = two_sum(nums, target);
        assert_eq!(result, vec![0, 1]);
    }

    // -----------------------

    #[test]
    fn test_is_palindrome_example_1() {
        let x = 121;
        let result = is_palindrome(x);
        assert!(result == true)
    }

    #[test]
    fn test_is_palindrome_example_2() {
        let x = -121;
        let result = is_palindrome(x);
        assert!(result == false)
    }

    #[test]
    fn test_is_palindrome_example_3() {
        let x = 10;
        let result = is_palindrome(x);
        assert!(result == false)
    }

    // -----------------------

    #[test]
    fn test_roman_gliph_new() {
        let i = RomanGliph::new('I', None, 1);
        assert_eq!('I', i.symbol);
        assert_eq!(1, i.value);
        assert_eq!('_', i.get_prev_symbol());
        assert_eq!(0, i.get_prev_value());

        let v = RomanGliph::new('V', Some(Box::new(&i)), 5);
        assert_eq!('V', v.symbol);
        assert_eq!(5, v.value);
        assert_eq!('I', v.get_prev_symbol());
        assert_eq!(1, v.get_prev_value());
    }

    #[test]
    fn test_roman_to_int_example_1() {
        assert_eq!(3, roman_to_int("III".to_string()));
    }

    #[test]
    fn test_roman_to_int_example_2() {
        assert_eq!(58, roman_to_int("LVIII".to_string()));
    }

    #[test]
    fn test_roman_to_int_example_3() {
        assert_eq!(1994, roman_to_int("MCMXCIV".to_string()));
    }
}
