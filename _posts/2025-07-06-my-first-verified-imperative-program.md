---
title: "My first verified (imperative) program"
date: 2025-07-06T13:00:00+02:00
categories:
  - blog
tags:
  - Lean
  - human-eval-lean
---

One of the many exciting new features in the upcoming Lean 4.22 release is a
preview of the new verification infrastructure for proving properties of imperative
programs. In this post, I'll take a first look at this feature, show a simple
example of what it can do, and compare it to similar tools.

## Guiding example

We will use the following simple programming task as an example throughout the
post: given a list of integers, determine if there are two integers at distinct
positions in the list that sum to zero.

For example, given the list `[1, 0, 2, -1]`, the result should be `true`, because
$$1 + (-1) = 0$$, and given the list `[0, 0]`, the result should also be `true`,
but given the list `[1, 0, -2]`, the result should be `false`.

The simplest way to solve this is to use two nested loops to iterate over all
pairs of distinct positions. This takes quadratic time, which is inefficient. There are
several ways to improve upon this. Here is the one we will use: iterate over the
list, and keep all elements we have seen so far in a set data structure. When
encountering a number $$x$$, efficiently check if we have seen $$-x$$ before. If
so, the answer is positive. If we reach the end of the list, the answer is negative.
This takes expected time $$O(n)$$ when using a hash set, or worst-case time $$O(n \log n)$$
when using a binary search tree. In Lean, both are available, under the names
`Std.HashSet` and `Std.TreeSet`, respectively.

## Local imperativity

Lean is a functional programming language, but it has good support for imperative
(stateful) programming both locally within a single function (via `do` notation)
and across functions (via monad transformers). In this post, we will use local
imperativity only.

Using local imperativity, it is easy to write down the set-based algorithm described
above:

```lean
def pairsSumToZero (l : List Int) : Id Bool := do
  let mut seen : HashSet Int := ∅

  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x

  return false
```

The `Id` and `do` in the first line of the code tell Lean that we would like to
work in "locally imperative" mode. Then we have access to a Python-like syntax
with the usual affordances of imperative programming, such as mutable state,
`for` loops and early returns[^1].

## Proving properties of locally imperative programs

Local imperativity is very useful when writing programs, and indeed much of Lean
itself is implemented in Lean using this style. However, Lean is not just a
programming language, but also an interactive theorem prover, and one of the
core features of Lean is that you can prove that your programs are correct.

Traditionally, proving properties about locally imperative programs was difficult
except in very simple cases, so if you were interested in proofs, it was usually
easiest to write your programs in a functional style, similarly to how you would
do it in a language like Haskell.

Lean 4.22 previews a new framework, called `Std.Do` after the place where it
lives in the Lean standard library, that aims to make verified imperative programming
(both local and global) easy.

The main thing that is still missing is documentation (and this post will not
change that in any meaningful way), but with a bit of digging we can already do
some initial experiments.

The foundation of `Std.Do` is given by the classic idea of *Hoare triples*. This
means that assertions about imperative programs are always of the form
"if $$P$$ is true, and I run the command $$C$$, then $$Q$$ is true". For example,
if a given variable is at least $$1$$, and I decrement it, then the variable
will be at least $$0$$.

The nice thing about Hoare triples is that they are composable. A large program
will be composed of many small functions that might operate on global state or
have other side effects, and Hoare triples allow stating properties that can
easily be reused when proving properties of larger programs using smaller programs.
Since our example only consists of a single function, this part isn't important
for our example, but it hints at the generality of `Std.Do` which I might explore
in a future post.

As Lean is an interactive system, the walkthrough that follows is easiest to follow
by having Lean open. Click [here](https://live.lean-lang.org/#url=https%3A%2F%2Fgist.githubusercontent.com%2FTwoFX%2Fbcdb6202fa8d8024b6a766a4d9df3f30%2Fraw%2Fe9263dddd43e868985614f689456a0adea50a3ee%2Fimperative.lean)
to open the online Lean playground pre-filled
with the proof. You can place your cursor inside the various places in the proof
to see what Lean has to say at that point.

The Lean syntax for Hoare triples is `⦃Precondition⦄ Command ⦃Postcondition⦄`. Using
this, let's state the correctness property of our `pairsSumToZero` function:

```lean
theorem pairsSumToZero_spec (l : List Int) :
    ⦃⌜True⌝⦄ pairsSumToZero l ⦃⇓r => r = true ↔ l.ExistsPair (fun a b => a + b = 0)⦄
```

In our case, there are no preconditions, so we use the always-true proposition `True`
as the precondition. The postcondition reads as "the function returns `true` if
and only if there is a pair of distinct positions in `l` such that the corresponding
values sum to $$0$$".

Now, Lean is an interactive theorem prover, so it expects us to tell it why this
Hoare triple is in fact true. To do this, `Std.Do` provides a piece of proof automation
called `mvcgen` (for "monadic verification condition generator") which analyzes locally
imperative programs and tells us what we need to do to prove the triple. After
starting the proof of `pairsSumToZero_spec`, we can invoke 

```lean
mvcgen [pairsSumToZero] --  generate verification conditions for the imperative code.
```

Lean then tells us that as a next step it wants us to provide a *loop invariant* for
the `for` loop in our code. This is a property that is true at the beginning of the
loop and is preserved by each loop iteration. Loop invariants are how we can deduce that something
is true after we exit the loop.

In our case, the control flow is slightly more complicated than the trivial examples
that you usually see for loop invariants, because our loop has an early return which we have to consider.
Here is the correct loop invariant:

> *Either* we have not taken the early return yet, and `seen` contains exactly those
> elements which are present in the prefix of the list we have traversed so far,
> and the prefix of the list we have traversed so far does not contain two elements
> that sum to zero,
>
> *or* we have taken the early return, and the list contains two elements which sum to zero.

Translating this to Lean in the form that `Std.Do` expects is a bit difficult without
documentation, but here is how it looks when done correctly:

```lean
case inv =>
  exact (fun (⟨earlyReturn?, seen⟩, traversalState) =>
    (earlyReturn? = none ∧ (∀ x, x ∈ seen ↔ x ∈ traversalState.rpref) ∧ ¬traversalState.pref.ExistsPair (fun a b => a + b = 0)) ∨
    (earlyReturn? = some true ∧ l.ExistsPair (fun a b => a + b = 0) ∧ l = traversalState.pref), ())
```

Here `earlyReturn?` is an optional value containing the value we returned early
if we returned early, `seen` is the `seen` from our program,
and `traversalState` contains information about where we are in the list. In
particular, `traversalState.pref` contains the prefix of the list that we have
already traversed, and `traversalState.rpref` is the reverse of that (which is
sometimes easier to reason about).

The third line is a fairly literal translation of the first case described in
prose above, and the fourth line is a translation of the second case, with the
slightly technical condition `l = traversalState.pref` thrown in, which asserts
that if we have taken the early return, we will not traverse the list any
further.

Now that we have provided the loop invariant, Lean tells us that we must prove
five things:

* If the loop invariant holds and we take the early return, the loop invariant still holds;
* if the loop invariant holds and we do not take the early return, the loop invariant still holds;
* the loop invariant is satisfied before we enter the loop;
* if we took the early return, the loop invariant implies the claimed property; and finally
* if we did not take the early return, the loop invariant implies the claimed property.

Now, to an experienced Lean user, proving these five things is not difficult, but
it is a bit tedious, because all of these are pretty obvious. Luckily, this is
where another big new feature from Lean 4.22 enters the picture: the `grind` tactic.
This is a new bit of proof automation which is able to make short work of many
"obvious" proofs like ours[^2]. This means that to dispatch the five proof obligations
above, it suffices to say

```lean
all_goals simp_all <;> grind
```

and Lean tells us `Goals accomplished!` to confirm that the proof is complete.
Behind the scenes, Lean has performed a detailed analysis of all cases, referring
to existing library results (for example that after inserting a new element into
a hash set, an element is contained if and only if it is equal to the new element
or was already contained in the original hash set) as appropriate.

For reference, here is the full program with the full proof:

```lean
/-!
# Imperative implementation
-/

def pairsSumToZero (l : List Int) : Id Bool := do
  let mut seen : HashSet Int := ∅

  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x

  return false

/-!
# Verification of imperative implementation
-/

theorem pairsSumToZero_spec (l : List Int) :
    ⦃⌜True⌝⦄ pairsSumToZero l ⦃⇓r => r = true ↔ l.ExistsPair (fun a b => a + b = 0)⦄ := by
  mvcgen [pairsSumToZero]

  case inv =>
    exact (fun (⟨earlyReturn?, seen⟩, traversalState) =>
      (earlyReturn? = none ∧ (∀ x, x ∈ seen ↔ x ∈ traversalState.rpref) ∧ ¬traversalState.pref.ExistsPair (fun a b => a + b = 0)) ∨
      (earlyReturn? = some true ∧ l.ExistsPair (fun a b => a + b = 0) ∧ l = traversalState.pref), ())

  all_goals simp_all <;> grind
```

## Why this excites me

I will explain why I was very happy when I saw this working for the first time.

Verified imperative programming in this style is not new. Technologies like Dafny
and Verus have been doing this for a long time. However, there are some key differences
between Dafny-style systems and Lean.

Dafny and Verus are primarily automated systems. They allow you to state properties
at various places in your programs. To make sure that these properties hold, the
system then encodes the properties into so-called verification conditions which they then
send to an external *automated* prover called an SMT solver. The SMT solver is very
good at proving these properties fully autonomously. This means that if everything
works out, you never have to worry about proofs, which is great! There are, however,
some significant downsides which all center around what happens when you leave that
happy path where everything works.

SMT solvers are very impressive, but they have their limits. For complex problems,
they can take a long time, so compile/checking times can become an issue. If they
time out or fail, it can be difficult to recover. Should I tweak my invariants in
the hope that the solver can do it? Is the problem just too hard for the solver?
Dafny and Verus allow you to add "lemmas", which are again proved by the SMT solver
and that you can then feed to the solver to reuse, but it's not always easy to tell
which lemma is
missing and the systems are not really designed for building up large libraries of lemmas
and proofs. In the worst case, this leads to a situation where you have built up
a medium-sized project when you run into a limitation that you just cannot overcome
with no way to recover, and no good way to introspect the solver to see what can
be done to make progress.

To make matters worse, the behaviour of SMT solvers can change subtly between versions, making it possible 
that proofs break for no real reason during version upgrades. In addition, SMT solvers
are large and complex software projects, and you're trusting that they're free of bugs
for your proofs to be correct.

Lean occupies a very different point in the design space: at its core, it is an
interactive system, where the user builds up the proof interactively. All of
Lean's tooling is
built around making the manual proving process as ergonomic as possible. Lean
has excellent editor support for interactive proving. It ships with a large library
of reusable concepts and lemmas, and it comes with powerful automation to make proofs
easy to write.

In our case, `grind` takes a role that is similar to the SMT solver in automated
systems. The difference is that when `grind` fails at some point, you can just do
the proof manually, and Lean is *really good* at making this easy.

From a trust perspective, Lean also has a good story: Lean is built to have a small
kernel, which is the only part that is relevant to whether Lean accepts a proof.
All of the automation that makes proving in Lean easy (including `grind`) generates
so-called proof terms that are fed to the small kernel. This means that while a bug in an
SMT solver might lead to Dafny accepting an incorrect program, a bug in `grind`
will at worst lead to Lean rejecting a correct program, which is much less bad.

Finally, the fact that Lean is focused on building theories means that large
libraries of proofs like [mathlib](https://github.com/leanprover-community/mathlib4)
are available for use in correctness proofs of programs, for example when verifying
cryptographic algorithms. This also means that Lean requires very little runtime
support for basic data types; unlike in Dafny, where the `set` type is built
into the system (implemented in C#, not Dafny) and its properties are essentially
taken as axioms, Lean's `Std.HashSet` and `Std.TreeSet` are
[fully implemented and verified in Lean](https://github.com/leanprover/lean4/tree/master/src/Std/Data).

For all of these reasons, I believe that Lean is in a very good position
to be a system that users can rely on and trust for real-world program verification
tasks.

## Bonus: verified functional programming

As a quick addendum, I will note that the functional implementation of `pairsSumToZero`
is also very easy to verify using `grind`. Here is the implementation:

```lean
def pairsSumToZero (l : List Int) : Bool :=
  go l ∅
where
  go (m : List Int) (seen : HashSet Int) : Bool :=
    match m with
    | [] => false
    | x::xs => if -x ∈ seen then true else go xs (seen.insert x)
```

Instead of the `for` loop, we have the tail-recursive helper function `go` which
takes the state as a parameter. Consequently, instead of writing down a loop
invariant, we give a correctness proof for the `go` function, which basically boils
down to the same thing:

```lean
theorem pairsSumToZero_go_iff (l : List Int) (seen : HashSet Int) :
    pairsSumToZero.go l seen = true ↔
      l.ExistsPair (fun a b => a + b = 0) ∨ ∃ a ∈ seen, ∃ b ∈ l, a + b = 0 := by
  fun_induction pairsSumToZero.go <;> simp_all <;> grind
```

The correctness statement is that `go`, when called with the state `seen` and
the yet-to-traverse suffix, returns true if and only if the suffix contains a
pair that sums to zero, or there is one element in `seen` and one in the suffix
that together sum to zero.
In the proof, instead of `mvcgen` for locally imperative programs, we rely on
`fun_induction` for the case analysis, and as before, `grind` does all of the proving work.

The correctness of `pairsSumToZero` is then an easy consequence:

```
theorem pairsSumToZero_iff (l : List Int) :
    pairsSumToZero l = true ↔ l.ExistsPair (fun a b => a + b = 0) := by
  simp [pairsSumToZero, pairsSumToZero_go_iff]
```


[^1]: If you would like to dig deep into how imperative programming inside a functional language works behind the scenes, there is [a paper](https://dl.acm.org/doi/pdf/10.1145/3547640) that describes the main ideas.

[^2]: I won't explain exactly what `grind` is or how it works here, but there is a comprehensive [reference manual entry](https://lean-lang.org/doc/reference/latest/The--grind--tactic/#grind) that should answer most of your questions.
