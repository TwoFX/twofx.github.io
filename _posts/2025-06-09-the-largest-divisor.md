---
title: "The largest divisor"
date: 2025-06-09T20:00:00+02:00
categories:
  - blog
tags:
  - Lean
  - human-eval-lean
---

A few weeks ago I started the [`human-eval-lean`](https://github.com/TwoFX/human-eval-lean)
project, an effort to collect hand-written solutions to the famous HumanEval
(AI) programming benchmark, written in the programming language [Lean](https://lean-lang.org/).
The twist is that Lean is not just a programming language, but also a proof assistant,
and all solutions in `human-eval-lean` come with machine-checked formal proofs that the code is
correct.

The idea is shamelessly copied from [`human-eval-verus`](https://github.com/secure-foundations/human-eval-verus),
which does the same thing in [Verus](https://github.com/verus-lang/verus), a verification
platform for Rust programs. The fact that both `human-eval-lean` and `human-eval-verus`
exists is great because it makes it possible to directly compare the two systems and more
generally the verification paradigms they represent (interactive theorem proving for Lean
and Dafny-style SMT-solver-backed verification for Verus).

The `human-eval-verus` contributors have already solved dozens of the 160-or-so HumanEval
problems, which is very impressive. The Lean effort has only just started and we have only
done a handful of the problems so far, but there have been some nice contributions from
Marcus Rossel and Johannes Tantow, including a solution for [task 109](https://github.com/TwoFX/human-eval-lean/blob/master/HumanEvalLean/HumanEval109.lean),
which is notable because it has not been completed in Verus yet.

For the rest of this post, I'd like to quickly discuss my solution to HumanEval task 24, which
asks to write a function that takes as input an integer $$n$$ and returns the largest proper
divisor of $$n$$.

The HumanEval problems come with model solutions. Often, these are not very good, as is
the case here. The model solution just loops downwards from $$n - 1$$ and returns the
first divisor that it finds. This is wasteful: the first number that 
has a chance of being a proper divisor of $$n$$ is on the order of $$n/2$$, so this
implementation will, on every input without exception, do useless work for about $$n/2$$
steps before it starts checking numbers that even have a change of being a divisor.

Here is a better approach: loop upwards from $$2$$, looking for the _smallest_ divisor
$$d$$, and return $$n/d$$. If no divisor is found after looking for candidates until
$$\sqrt{n}$$, return $$1$$.

This works because whenever $$d$$ is a divisor of $$n$$, so is $$n/d$$, and this correspondence
reverses the order of the divisors. It shows that the largest divisor of $$n$$ can be
found in time proportional to the square root of $$n$$ rather than time proportional to
$$n$$, which is much better even on fairly small inputs.

Here is an implementation of this approach in Lean:

```lean
def largestDivisor (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if n < i * i then
      1
    else if n % i = 0 then
      n / i
    else
      go (i + 1)
```

it is written in a functional style, using tail recursion instead of a loop. Lean
also supports imperative constructs like `for` loops, but currently the support
for proving properties of functional programs is still better than for proving
properties of imperative programs.

One detail is that Lean will not accept the code as written above. In Lean, all
functions must terminate. In almost all cases, Lean is able to prove on its own
that a recursive function always reaches the base case, but in this case, we need
to help Lean a bit with the following code:

```lean
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega
```

We're saying: the recursion always terminates because the number $$n - i$$ keeps getting
smaller with each recursive call, but never goes below zero. For this to be true, we
need $$i < n$$ whenever we do a recursive call. The slightly tricky part about this is that we
only check for $$i^2 \le n$$, so we need to spell out to Lean that this implies $$i < n$$.

Now that Lean has accepted our program, we can run it and notice that it returns the
right results, but we can also state the correctness property for our function:

```lean
theorem largestDivisor_eq_iff {n i : Nat} (hn : 1 < n) :
    largestDivisor n = i ↔ i < n ∧ n % i = 0 ∧ ∀ j, j < n → n % j = 0 → j ≤ i :=
  -- Proof omitted
```

This reads as follows: as long as $$n > 1$$, the `largestDivisor` function applied to a
number $$n$$ returns $$i$$ if and only if three things hold:

* $$i$$ is less than $$n$$,
* $$n$$ modulo $$i$$ is zero (so $$i$$ is a divisor of $$n$$), and
* if $$j$$ is any other proper divisor of $$n$$, then $$j \le i$$.

In total, this means that $$i$$ is the greatest proper divisor of $$n$$.

The proof of this claim is a few dozen lines of code. Click [here](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FTwoFX%2Fhuman-eval-lean%2Frefs%2Fheads%2Fmaster%2FHumanEvalLean%2FHumanEval24.lean) to be dropped into the Lean web editor with the proof loaded in. You
can have a look around and place your cursor in various places. The bar on the right
will show the current state of the proof at that point.

The high-level idea of the proof is to break it up into two parts: the first part
consists of establishing the "loop invariant" of the "loop" function `go` and the
second part consists of showing that this invariant implies the claim. This works
well because it means we can separate the "computer science" (analyzing the program)
from the mathematics (arguing that mapping $$d$$ to $$n/d$$ makes a correspondence between
small and large divisors).

This also shows the strength of Lean: as an interative theorem prover, it is very
well-suited to express the mathematical reasoning that underpins the faster algorithm. Its
standard library also comes with many thousands of helper results about natural
numbers (and many other things like data structures) which are useful in the proof.
For example, in the proof it is very useful to have results characterizing exactly
how division, multiplication and the ordering on natural numbers interact.

For comparison, the [corresponding entry](https://github.com/secure-foundations/human-eval-verus/blob/main/tasks/human_eval_024.rs)
in `human-eval-verus` uses the naive linear-time algorithm. It has no problem establishing
the loop invariant in that case, but it is less clear how well it would work to adapt and
extend the verification to include the additional reasoning required for the faster
algorithm. If any Verus user is reading this, I would be very interested to see a Verus
implementation!

If you'd like to join the fun, feel free to have a look at the [`human-eval-lean`](https://github.com/TwoFX/human-eval-lean)
repo and have a look at the open tasks!
