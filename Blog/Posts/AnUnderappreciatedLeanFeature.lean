import VersoBlog
import Blog.Tags

open Verso Genre Blog
open Verso.Code.External
open Blog.Tag

set_option verso.exampleProject "examples/an-underappreciated-lean-feature"
set_option verso.exampleModule "AnUnderappreciatedLeanFeature"

set_option pp.rawOnError true

#doc (Post) "An underappreciated Lean feature" =>

%%%
authors := ["Julia Markus Himmel"]
date := {year := 2026, month := 7, day := 7}
categories := [lean]
%%%

One of Lean's staple features is _dot notation_, also known as _generalized field notation_ or
_extended field notation_. In short, this feature allows the short form `a.f` for the application
`A.f a`, where `a` is of type `A`. This is what allows us to write
{anchorTerm dotNotation}`l.filter isEven` instead of {anchorTerm dotNotation}`List.filter isEven l`
and {anchorTerm dotNotation}`l.eraseDups.sum` instead of
{anchorTerm dotNotation}`List.sum (List.eraseDups l)`. Code written this way is easy to read,
concise, familiar to users of imperative or object-oriented programming languages, and the Lean
language server gives helpful auto-complete when you type `l.`.

This is not a new idea: it has been known as _uniform function call syntax_ for more than 20
years. What makes this idea so powerful is that _anyone_ can write these functions, not just whoever "owns"
the type. Missing a `List.subsequences` function? Just write it yourself, and from that point on you
can write `l.subsequences`. This is also very useful for relating types defined upstream to types
from your own library: say you have defined a `MyList` type and a function `MyList.foo`, then you
can define a function `List.toMyList` to enable expressions such as `l.eraseDups.toMyList.foo`.

This is clearly extremely useful, but when I put on my library designer hat, it actually makes me a bit
uneasy. To explain why, let's say we're interested in building a library providing a `String.leftPad`
function. Here is a possible implementation of that library:

```
namespace String

/-- This is just an internal implementation detail which is not considered part of the public API. -/
def prependChar (c : Char) (s : String) : String :=
  singleton c ++ s

/-- Prepends `c` to `s` until `s` has length at least `n`. -/
def leftPad (n : Nat) (c : Char := ' ') (s : String) : String := Id.run do
  let mut ans := s
  while s.length < n do
    -- Dot notation, yay!
    ans := s.prependChar c
  return ans

end String
```

The problem is the `String.prependChar` function. As written, we export this function along with the
public `String.leftPad` function. Users of our library who invoke autocompletion on a `String` will
see the function, 
