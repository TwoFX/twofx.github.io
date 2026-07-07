import VersoBlog
import Blog.Tags

open Verso Genre Blog
open Blog.Tag

set_option pp.rawOnError true

#doc (Post) "Freyd-Mitchell and Gabriel-Popescu" =>

%%%
authors := ["Julia Markus Himmel"]
date := {year := 2025, month := 6, day := 21}
categories := [lean, mathlib]
%%%

Earlier this year, Jakob von Raumer, Paul Reichert and I finished a long project
adding the Freyd-Mitchell and Gabriel-Popescu theorems to mathlib, Lean's
mathematical library. This week, a blog post about the project went live on
the Lean community blog. [Click here to read it!](https://leanprover-community.github.io/blog/posts/abelian-categories/)
