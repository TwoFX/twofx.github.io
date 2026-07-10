/-
Code for the blog post "An underappreciated Lean feature" (2026-07-07).
-/

-- ANCHOR: dotNotation
example (l : List Nat) (isEven : Nat → Bool) :
    l.filter isEven = List.filter isEven l := rfl

example (l : List Nat) :
    l.eraseDups.sum = List.sum (List.eraseDups l) := rfl
-- ANCHOR_END: dotNotation
