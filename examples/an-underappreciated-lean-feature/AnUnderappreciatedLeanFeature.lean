/-
Code for the blog post "An underappreciated Lean feature" (2026-07-14).

The introductory examples and the three left-pad implementations live in their
own wrapper namespaces (`Intro`, `FirstAttempt`, `SecondAttempt`,
`ThirdAttempt`) so that they can coexist in one module; the wrappers are
hidden from the rendered post via
`verso.externalExamples.suppressedNamespaces`.

The two `MyLibrary` examples from the end of the post are not part of this
module: one of them must fail to compile, so they are inline `lean` blocks in
the post itself instead. Only the (compiling) `MyLibrary.String.prependChar`
definition is replicated here so that the prose can refer to it with a hover.
-/

-- ANCHOR: dotNotation
example (l : List Nat) (isEven : Nat → Bool) :
    l.filter isEven = List.filter isEven l := rfl

example (l : List Nat) :
    l.eraseDups.sum = List.sum (List.eraseDups l) := rfl
-- ANCHOR_END: dotNotation

namespace Intro

/-
These definitions only exist so that the inline code in the introduction of
the post refers to real declarations and thus gets hovers. As with
`FirstAttempt` below, `open Intro` is needed because dot notation only
consults `open`ed namespaces, not the current one.
-/
open Intro

structure A where

def A.f (_ : A) : Nat := 0

-- ANCHOR: schematic
example (a : A) : a.f = A.f a := rfl
-- ANCHOR_END: schematic

-- ANCHOR: subsequences
/-- Computes all subsequences of a list. -/
def List.subsequences : List α → List (List α)
  | [] => [[]]
  | x :: xs => List.subsequences xs ++ (List.subsequences xs).map (x :: ·)

example (l : List Nat) : List (List Nat) := l.subsequences
-- ANCHOR_END: subsequences

-- ANCHOR: myList
structure MyList (α : Type) where
  elems : List α

def MyList.foo (l : MyList α) : Nat :=
  l.elems.length

def List.toMyList (l : List α) : MyList α :=
  ⟨l⟩

example (l : List Nat) : Nat := l.eraseDups.toMyList.foo
-- ANCHOR_END: myList

end Intro

namespace FirstAttempt

/-
Inside `FirstAttempt`, the `namespace String` below denotes
`FirstAttempt.String`, not `_root_.String`, so two `open`s are needed to make
the code elaborate as it would at the root: `open String` makes
`String.singleton` available by the name `singleton`, and `open FirstAttempt`
lets dot notation find `FirstAttempt.String.prependChar` (via the very feature
the post is about).
-/
open String
open FirstAttempt

-- ANCHOR: leftPadNaive
namespace String

/--
This is just an internal implementation detail which is
not considered part of the public API.
-/
def prependChar (c : Char) (s : String) : String :=
  singleton c ++ s

/-- Prepends `c` to `s` until `s` consists of at least `n` code points. -/
def leftPad (n : Nat) (c : Char := ' ') (s : String) : String := Id.run do
  let mut ans := s
  while ans.length < n do
    -- Dot notation, yay!
    ans := ans.prependChar c
  return ans

end String
-- ANCHOR_END: leftPadNaive

-- ANCHOR: leftPadNaiveCall
example (c : Char) (s : String) : String := s.prependChar c
-- ANCHOR_END: leftPadNaiveCall

end FirstAttempt

namespace SecondAttempt

-- ANCHOR: leftPadInternal
namespace LeftPad.Internal

open String

/--
This is just an internal implementation detail which is
not considered part of the public API.
-/
def String.prependChar (c : Char) (s : String) : String :=
  singleton c ++ s

end LeftPad.Internal

namespace String

open LeftPad.Internal

/-- Prepends `c` to `s` until `s` consists of at least `n` code points. -/
def leftPad (n : Nat) (c : Char := ' ') (s : String) : String := Id.run do
  let mut ans := s
  while ans.length < n do
    -- Dot notation, yay!
    ans := ans.prependChar c
  return ans

end String
-- ANCHOR_END: leftPadInternal

end SecondAttempt

namespace ThirdAttempt

/-
The "low-tech solution" from the post: `prependChar` renamed into a namespace
where it does not show up in autocompletion on `String`. The `section` limits
the `open` to the call-site example.
-/

-- ANCHOR: leftPadRenamed
/--
This is just an internal implementation detail which is
not considered part of the public API.
-/
def String.leftPad.Internal.prependChar (c : Char) (s : String) : String :=
  String.singleton c ++ s
-- ANCHOR_END: leftPadRenamed

section
open String.leftPad.Internal

-- ANCHOR: leftPadRenamedCall
example (c : Char) (s : String) : String := prependChar c s
-- ANCHOR_END: leftPadRenamedCall

end

end ThirdAttempt

/-
This namespace is deliberately *not* suppressed: the post's bonus section
refers to `MyLibrary.String.prependChar` inline, and the hover should show the
full name. Inline `lean` blocks in the post can't be used for this because the
inline `lean` *role* elaborates against the post module's environment, not the
example context's one.
-/
namespace MyLibrary

-- ANCHOR: myLibraryPrependChar
def String.prependChar (c : Char) (s : String) : String :=
  String.singleton c ++ s
-- ANCHOR_END: myLibraryPrependChar

end MyLibrary
