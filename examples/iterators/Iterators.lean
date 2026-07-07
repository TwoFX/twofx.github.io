/-
Code for the blog post "Lean has iterators now" (2025-06-12).
-/
-- ANCHOR: full
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
-- ANCHOR_END: full
