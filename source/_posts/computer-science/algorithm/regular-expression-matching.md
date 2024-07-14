---
layout: post
title: Regular Expression Matching
date: 2024-07-13 22:18:41
categories:
  - [Computer Science, Algorithm]
---

## Introduction

This blog documents my thoughts on solving the [Regular Expression Matching](https://leetcode.com/problems/regular-expression-matching/description/) problem:

> Given an input string `s` and a pattern `p`, implement regular expression matching with support for `'.'` and `'*'` where:
>
> `'.'` Matches any single character.​​​​
> `'*'` Matches zero or more of the preceding element.
> The matching should cover the entire input string (not partial).

It is easy to diagnose that this problem can be solved using dynamic programming. I typically approach dynamic programming problems with the following steps:

1. Visualize the problem as a table-filling game.
2. Find a way to use already calculated values (representing subproblems) to avoid redundant calculations and control complexity.
3. Refine the boundary conditions.

## Visualize as a Table-Filling Game

Considering there are only two inputs (`s` and `p`), it is natural for the table to be two-dimensional: each column represents an index of `s`, and each row represents an index of `p`. The value of each grid represents whether the substring of `s` from index 0 to the current index (inclusive) matches the substring of `p` from index 0 to the current index (inclusive). The value is T for yes, F for no, and NULL as the initial value for unknown.

|                  | `s`'s index | 0 | 1 |  2   | ... | `s`'s length - 1 |
|        -         |      -      | - | - |  -   |  -  |        -         |
|   `p`'s index    |             |   |   |      |     |                  |
|        0         |             | T | F | NULL |     |                  |
|        1         |             |   |   |      |     |                  |
|        2         |             |   |   |      |     |                  |
|       ...        |             |   |   |      |     |                  |
| `p`'s length - 1 |             |   |   |      |     |                  |

## Find a Way to Reuse Grid Values

Let's denote `pi` as the index of `p`, `p[pi]` as the corresponding character of `p`, and `p[0..pi]` as the substring of `p` from 0 (inclusive) to `pi` (inclusive).

1. When `p[pi]` is a normal character, `table[pi][si] = table[pi-1][si-1] && p[pi] == s[si]`.
2. When `p[pi]` is `.`, `table[pi][si] = table[pi-1][si-1]`.
3. When `p[pi]` is `*` and `p[pi-1]` is `.`, the case is more complex: `p[0..pi]` can match `s[0..si]` if any of the following conditions are met:
    a. `p[pi]` matches 0 characters, and `p[0..(pi-1)]` matches `s[0..si]`.
    b. `p[pi]` matches 1 character, and `p[0..(pi-1)]` matches `s[0..(si-1)]`.
    c. `p[pi]` matches 2 characters, and `p[0..(pi-1)]` matches `s[0..(si-2)]`.
    d. ...
4. When `p[pi]` is `*` and `p[pi-1]` is a normal character, this case is the most complicated:
    a. `p[pi]` matches 0 characters, and `p[0..(pi-1)]` matches `s[0..si]`.
    b. If `s[si]` equals the normal character, `p[pi]` can match 1 character, and `p[0..(pi-1)]` matches `s[0..(si-1)]`.
    d. ... continue until `s[x]` does not equal the normal character.

## Refine the Boundary Conditions

The most important boundary condition is the initial condition. For example, consider `p = "a"` and `s = "a"`. The initial condition is `table[0][0] == table[-1][-1] && "a" == "a"` after one deduction, which means that when `pi == -1` and `si == -1`, they match.

```cpp
enum class RegexCharType {
  kNormal = 0,
  kDot = 1,
  kNormalStar = 2,
  kDotStar = 3,
};
struct RegexChar {
  RegexCharType type;
  char character;
};

class RegexMatcher {
 public:
  RegexMatcher(std::string_view str, std::string_view regex) : str_(str) {
    for (int64_t i = regex.size() - 1; i >= 0; i--) {
      if (regex[i] == '.') {
        regex_.insert(regex_.begin(), RegexChar{RegexCharType::kDot});
      } else if (regex[i] == '*') {
        assert(i > 0);
        if (regex[i - 1] == '.' || regex[i - 1] == '*') {
          regex_.insert(regex_.begin(), RegexChar{RegexCharType::kDotStar});
        } else {
          regex_.insert(regex_.begin(),
                        RegexChar{RegexCharType::kNormalStar, regex[i - 1]});
        }
        i--;
      } else {
        regex_.insert(regex_.begin(),
                      RegexChar{RegexCharType::kNormal, regex[i]});
      }
    }
    is_matched_table_.resize(str_.size());
    for (auto i = 0L; i < str_.size(); i++) {
      is_matched_table_[i].resize(regex_.size());
    }
  }

  bool is_match() { return is_match(str_.size() - 1, regex_.size() - 1); }

  bool is_match(int64_t str_index, int64_t regex_index) {
    assert(str_index >= -1);
    assert(regex_index >= -1);
    if (str_index == -1 && regex_index == -1) {
      return true;
    }
    if (str_index == -1) {
      for (auto i = regex_index; i >= 0; i--) {
        if (regex_[i].type == RegexCharType::kNormal ||
            regex_[i].type == RegexCharType::kDot) {
          return false;
        }
      }
      return true;
    }
    if (regex_index == -1) {
      return false;
    }

    assert(str_index < is_matched_table_.size());
    assert(regex_index < is_matched_table_[str_index].size());
    auto &is_matched = is_matched_table_[str_index][regex_index];
    if (is_matched.has_value()) {
      return *is_matched;
    }

    if (regex_[regex_index].type == RegexCharType::kNormal ||
        regex_[regex_index].type == RegexCharType::kDot) {
      is_matched = (regex_[regex_index].type == RegexCharType::kDot ||
                    str_[str_index] == regex_[regex_index].character) &&
                   is_match(str_index - 1, regex_index - 1);
      return *is_matched;
    }
    assert(regex_[regex_index].type == RegexCharType::kNormalStar ||
           regex_[regex_index].type == RegexCharType::kDotStar);
    for (auto i = str_index + 1;
         i >= 0 && (i == str_index + 1 ||
                    regex_[regex_index].type == RegexCharType::kDotStar ||
                    str_[i] == regex_[regex_index].character);
         i--) {
      if (is_match(i - 1, regex_index - 1)) {
        is_matched = true;
        return true;
      }
    }
    is_matched = false;
    return false;
  }

 private:
  std::string str_;
  std::vector<RegexChar> regex_;
  std::vector<std::vector<std::optional<bool>>> is_matched_table_;
};

class Solution {
 public:
  bool isMatch(string s, string p) { return RegexMatcher(s, p).is_match(); }
};
```
