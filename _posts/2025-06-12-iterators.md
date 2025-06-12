---
title: "Lean has iterators now"
date: 2025-06-12T07:00:00+02:00
categories:
  - blog
tags:
  - Lean
  - human-eval-lean
---

Lean 4.22 (to be released in early August) will ship with the first version of
the new iterators library, allowing for efficient streaming, combining and
collecting of data. This library was designed and implemented by
[Paul](https://github.com/datokrat), and he has put a lot of thought into making
sure that iterators are compiled into efficient code (like in Rust), and he has
worked even harder to ensure that it's easy to prove things about iterators
(even when iterating monadically).

To celebrate this occasion, let's do one of the `human-eval-lean` tasks using
the new iterators (see [my previous post]({% post_url 2025-06-09-the-largest-divisor %})
for context about `human-eval-lean`).

HumanEval problem 11 asks us to take two lists of booleans and combine them into
one list using the xor operation at each position. The is easily done using
`List.zip` followed by `List.map`, but that would allocate a list of pairs as
an intermediate result, which is inefficient. We could write a recursive function,
but that sounds like a lot of work. `Iter.zip` to the rescue!

What follows is the entire code, including proofs.

```lean
import Std.Data.Iterators

def stringXor (a b : List Bool) : List Bool :=
  ((a.iter).zip b.iter)
    |>.map (fun p => Bool.xor p.1 p.2)
    |>.toList

@[simp, grind]
theorem length_stringXor {a b : List Bool} : (stringXor a b).length = min a.length b.length := by
  simp [stringXor]

theorem getElem_stringXor {a b : List Bool} {i : Nat} {hia : i < a.length} {hib : i < b.length} :
    (stringXor a b)[i]'(by grind) = Bool.xor a[i] b[i] := by
  simp [stringXor]
```

Three simple lines of stream processing, and the proofs are trivial one-liners
using what's available in the standard library. Superfast code and easy proofs -
this is how I want my Lean. I love it!

