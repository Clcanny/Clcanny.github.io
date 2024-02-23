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
