import VersoBlog

open Verso.Genre.Blog.Post

namespace Blog.Tag

/--
The tags used on the blog. The slugs match the anchors that the old
Jekyll/Minimal Mistakes site used on its `/tags/` page, so that old links of
the form `/tags/#lean` keep working.
-/
def lean : Category where
  name := "Lean"
  slug := "lean"

def humanEvalLean : Category where
  name := "human-eval-lean"
  slug := "human-eval-lean"

def mathlib : Category where
  name := "mathlib"
  slug := "mathlib"

def floats : Category where
  name := "Floating-point numbers"
  slug := "floating-point-numbers"
