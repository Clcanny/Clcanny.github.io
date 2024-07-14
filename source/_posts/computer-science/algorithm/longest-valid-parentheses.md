---
layout: post
title: Longest Valid Parentheses
date: 2024-07-14 22:26:19
categories:
  - [Computer Science, Algorithm]
---

## Introduction

This blog documents my thoughts on solving the [Longest Valid Parentheses](https://leetcode.com/problems/longest-valid-parentheses/description/) problem:

> Given a string containing just the characters `'('` and `')'`, return the length of the longest valid (well-formed) parentheses substring.
>
> Example 1:
>
> Input: s = "(()"
>
> Output: 2
>
> Explanation: The longest valid parentheses substring is "()".
>
> Example 2:
>
> Input: s = ")()())"
>
> Output: 4
>
> Explanation: The longest valid parentheses substring is "()()".
>
> Example 3:
>
> Input: s = ""
>
> Output: 0

It is easy to diagnose that this problem can be solved using dynamic programming. I typically approach dynamic programming problems with the following steps:

1. Visualize the problem as a table-filling game.
2. Find a way to use already calculated values (representing subproblems) to avoid redundant calculations and control complexity.
3. Refine the boundary conditions.

## Visualize as a Table-Filling Game

At first, I naturally thought that the table would be two-dimensional, with columns representing the substring's beginning index (inclusive) and rows representing the substring's ending index (exclusive). The value in each cell represents the longest valid parentheses substring (denoted by `s[b..e)`) within the substring `s[begin..end)`.

|            | begin index |     0     | 1 | ... | length - 1 |
|     -      |      -      |     -     | - |  -  |     -      |
| end index  |             |           |   |     |            |
|     0      |             |           |   |     |            |
|     1      |             |           |   |     |            |
|    ...     |             |           |   |     |            |
| length - 1 |             |           |   |     |            |
|   length   |             | `s[x..y)` |   |     |            |

According to this two-dimensional table, I can divide the problem into subproblems in the following way. The longest valid parentheses in `s[i..j)` can be:

1. The longest valid parentheses in `s[(i+1)..(j-1))`.
2. If we can find a longest valid parentheses substring starting from `i+1` and extend it one to the left and right of that substring. Formally speaking, `s[i..(k+1))` if there is a substring `s[(i+1)..k)` that is the longest valid parentheses beginning from `i+1`, where `(i+1) <= k < (j-1)`, and `s[i] == s[k+1]`.
3. If we can find a longest valid parentheses substring ending at `j`, and extend it one to the left and right of that substring...

To solve case 2, I need a rightmost index table. `rightmost_index_table_[i]` is an exclusive index such that `s[i..rightmost_index_table_[i])` is the longest valid parentheses substring starting from `i`.

Take `")()())"` as an example. `rightmost_index_table_[0]` is 0 because `s[0]` is `)` and there is no valid parentheses substring starting from 0. `rightmost_index_table_[1]` is 5 because the longest valid parentheses substring starting from 1 is `s[1..5)`, which is `"()()"`.

|                             |  `i`   |  0  |  1  |  2  |  3  |  4  |  5  |
|              -              |   -    |  -  |  -  |  -  |  -  |  -  |  -  |
|                             | `s[i]` | `)` | `(` | `)` | `(` | `)` | `)` |
| `rightmost_index_table_[i]` |        |  0  |  5  |  2  |  5  |  4  |  5  |

The interesting part is that once I have a rightmost index table, the longest valid parentheses problem is also solved. I can calculate the length of the longest valid parentheses substring starting from every position, and the maximum length is the answer. In conclusion, I need a one-dimensional rightmost index table to solve the longest valid parentheses problem.

## Find a Way to Reuse Grid Values

The following picture illustrates how to reuse previous values when calculating `rightmost_index_table_`. When calculating `rightmost_index_table_[i]`, we first find the longest valid parentheses starting from `i+1` (the yellow part), then check if the next character (the gray part) pairs with `s[i]`. Finally, we look for another valid parentheses substring that follows (the green part).

![An Illustration of How to Reuse Grid Values](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/longest-valid-parentheses/an-illustration-of-how-to-reuse-grid-values.png)

## Refine the Boundary Conditions

I actually spent a lot of time refining the boundary conditions, but I won't bore you with the details. Here is the code:

```cpp
class LongestValidParenthesesSolver {
 public:
  LongestValidParenthesesSolver(std::string_view str)
      : str_(str), rightmost_index_table_(str_.size(), -1) {
    assert(rightmost_index_table_.size() == str_.size());
  }

  int64_t find_longest_valid_parentheses_length() {
    int64_t max_length = 0;
    for (int64_t left_inclusive_index = str_.size() - 1;
         left_inclusive_index >= 0; left_inclusive_index--) {
      int64_t rightmost_exclusive_index =
          find_rightmost_valid_parenthesis_exclusive_index(
              left_inclusive_index);
      int64_t length = rightmost_exclusive_index - left_inclusive_index;
      max_length = std::max(max_length, length);
    }
    return max_length;
  }

  int64_t find_rightmost_valid_parenthesis_exclusive_index(
      int64_t left_inclusive_index) {
    assert(left_inclusive_index >= 0 && left_inclusive_index < str_.size());
    int64_t& rightmost_exclusive_index =
        rightmost_index_table_[left_inclusive_index];
    assert(rightmost_exclusive_index == -1);

    rightmost_exclusive_index = left_inclusive_index;
    if (rightmost_exclusive_index + 1 < str_.size()) {
      int64_t next_rightmost_exclusive_index =
          rightmost_index_table_[rightmost_exclusive_index + 1];
      assert(next_rightmost_exclusive_index != -1);
      assert(next_rightmost_exclusive_index >= rightmost_exclusive_index + 1);
      assert(next_rightmost_exclusive_index <= str_.size());
      if (str_[left_inclusive_index] == '(' &&
          (next_rightmost_exclusive_index < str_.size() &&
           str_[next_rightmost_exclusive_index] == ')')) {
        rightmost_exclusive_index = next_rightmost_exclusive_index + 1;
      } else {
        return rightmost_exclusive_index;
      }
    }

    if (rightmost_exclusive_index < str_.size()) {
      int64_t next_rightmost_exclusive_index =
          rightmost_index_table_[rightmost_exclusive_index];
      assert(next_rightmost_exclusive_index != -1);
      assert(next_rightmost_exclusive_index >= rightmost_exclusive_index);
      assert(next_rightmost_exclusive_index <= str_.size());
      if (next_rightmost_exclusive_index != rightmost_exclusive_index) {
        rightmost_exclusive_index = next_rightmost_exclusive_index;
      }
    }
    return rightmost_exclusive_index;
  }

 private:
  std::string_view str_;
  std::vector<int64_t> rightmost_index_table_;
};

class Solution {
 public:
  int longestValidParentheses(string s) {
    return LongestValidParenthesesSolver(s)
        .find_longest_valid_parentheses_length();
  };
};
```
