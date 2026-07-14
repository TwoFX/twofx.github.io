import VersoBlog
import Blog.Tags

open Verso Genre Blog
open Verso.Code.External
-- `open Blog.Tag` would make the tag `Blog.Tag.lean` shadow the genre's
-- `lean` code block used below, so the category is qualified instead.

set_option verso.exampleProject "examples/an-underappreciated-lean-feature"
set_option verso.exampleModule "AnUnderappreciatedLeanFeature"
set_option verso.externalExamples.suppressedNamespaces "Intro FirstAttempt SecondAttempt ThirdAttempt"

set_option pp.rawOnError true

#doc (Post) "An underappreciated Lean feature" =>

%%%
authors := ["Julia Markus Himmel"]
date := {year := 2026, month := 7, day := 14}
categories := [Blog.Tag.lean]
%%%

Building large and interdependent libraries is the bread and butter of working with Lean, both on
the mathematics side and on the programming side of things. At the same time, the ecosystem is still
quite young, and we are still learning how to design APIs well, especially in situations where multiple
libraries interact. Many people building libraries have felt the following tension: I would like to locally extend an
upstream library without necessarily passing down the new material to my own users. How do I do this
in a convenient and safe way?

I recently learned about a useful Lean feature (“DNRO”) that has been part of the language for quite a while,
but that not many people know about. In this post,
I'd like to tell you about an API design problem I was facing and how the feature helped solve it.

# The problem

One of Lean's staple features is _dot notation_, more officially known as _generalized field notation_ or
_extended field notation_. In short, this feature allows the short form
{anchorTerm schematic}`a.f` for the application {anchorTerm schematic}`A.f a`, where
{anchorName schematic}`a` is of type {anchorName schematic}`A`. This is what allows us to write
{anchorTerm dotNotation}`l.filter isEven` instead of {anchorTerm dotNotation}`List.filter isEven l`
and {anchorTerm dotNotation}`l.eraseDups.sum` instead of
{anchorTerm dotNotation}`List.sum (List.eraseDups l)`. Code written this way is easy to read,
concise, familiar to users of imperative or object-oriented programming languages, and the Lean
language server gives helpful autocompletion when you type `l.`.

This is not a new idea: it has been known for more than 20 years, referred to as _uniform
function call syntax_ in some circles.
Resolving to the namespace of the type of the argument is a bit of a Lean specialty, however.
What makes this idea so powerful is that _anyone_ can write these functions, not just whoever “owns”
the type. Missing a {anchorName subsequences}`List.subsequences` function? Just write it yourself,
and from that point on you can write {anchorTerm subsequences}`l.subsequences`. This is also
nice for relating types defined upstream to types from your own library: say you have defined a
{anchorName myList}`MyList` type and a function {anchorName myList}`MyList.foo`, then you can define
a function {anchorName myList}`List.toMyList` to enable expressions such as
{anchorTerm myList}`l.eraseDups.toMyList.foo`.

This is clearly a helpful feature, but when I put on my library designer hat, it actually makes me a bit
uneasy. To explain why, let's say we're interested in building a library providing a
{anchorName leftPadNaive (show := String.leftPad)}`leftPad` function. Here is a possible implementation
of that library (note that discussing whether left-padding
a string is ever a good idea or how to do so efficiently is beside the point here). We introduce
a helper function {anchorName leftPadNaive (show := String.prependChar)}`prependChar`, and then
{anchorName leftPadNaive (show := String.leftPad)}`leftPad` applies this function in a loop, making
use of the nice dot notation feature in the loop body:

```anchor leftPadNaive
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
```

The problem is the {anchorName leftPadNaive (show := String.prependChar)}`prependChar` function. As
written, we export this function along with the
public {anchorName leftPadNaive (show := String.leftPad)}`leftPad` function. Users of our library who
invoke autocompletion on a `String` will
see the function, and unless they happen to look at the docstring (and who looks at the docstring
for _every_ library function they call?), they will assume that this is a public function supported
by one of their dependencies.

Clearly, we have miscommunicated the public API of our library here. The function is an internal
implementation detail which we do not want our users to interact with. I consider this an example of
_namespace pollution_: putting things in a publicly available namespace which should not be there.

# Attempts at a solution

To avoid this instance of namespace pollution, we need to either make sure that users do not import
the function, or move it to a different namespace that does not cause the function to appear
in autocompletion.

The way to prevent a function from being imported is to make it `private`. If we only call the function in
the file where it is defined, like in our {anchorName leftPadNaive}`leftPad` example, then this is
actually a perfectly workable solution.

If our library grows to multiple files, this no longer works because in general private functions
are not accessible after `import`ing a file. There are two ways we could try to use Lean's module
system to work around this. Both of these start by isolating the
{anchorName leftPadNaive (show := String.prependChar)}`prependChar` function into
its own file and then trying to control how that file is imported.

* We could make the function public, but only ever non-transitively
  import (i.e., `import` instead of `public import`) our internal function into modules which are
  part of the public API. This is brittle for two reasons. First, it is quite easy to get wrong by accident. Even worse,
  Lean sometimes forces us to use `public import` for boring technical reasons (in other words:
  transitivity of imports is a leaky abstraction. It is constrained by technical limitations which
  make it unsuitable as a vehicle for API design.), and if this
  happens even once, then we have already leaked the function. So this is not a watertight solution.
* We could also leave the function `private` and import its module using `import all` whenever we
  want to use it. This works, but in doing so we opt out of all of the advantages that the module
  system affords us, and it's also very coarse: for example, if the
  {anchorName leftPadNaive (show := String.prependChar)}`prependChar` function
  has its own helper functions that it would like to keep hidden inside its implementation file,
  then by visibility alone it will not be possible to tell which functions are meant for use outside
  of the module and which are not.

In short, the module system does not present us with a perfect solution here. This is not too
surprising given that solving this problem was not one of the goals of the module system.

The alternative is the low-tech
solution of renaming the function to something like
{anchorName leftPadRenamed}`String.leftPad.Internal.prependChar`. This
clearly communicates the intent. Of course, users can choose to ignore this communication and depend
on the implementation detail anyway, but [depending on the project setup](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#Lake___PackageConfig-allowImportAll),
not even the module system can prevent this. With this solution, we can enjoy all of the performance
benefits of the module system, we are not restricted in where we define the function relative to
the rest of the project, and we do not need to be super careful about which files are imported and
how.

So, problem solved? Not at all! We forgot about the reason why we were putting the function in such
a public position in the first place, namely the availability of dot notation. By renaming the function,
we have lost the ability to write {anchorTerm leftPadNaiveCall}`s.prependChar c`, and instead would
have to write {anchorTerm leftPadRenamedCall}`prependChar c s` (after `open`ing the relevant
namespaces).

# The solution

This is where the Lean feature that this blog post is about comes in: it turns out that *if
you `open` a namespace, then name resolution for dot notation takes this `open`ed namespace into
account*. For lack of a better term, I'll call this “dot-notation-respects-open”, or DNRO.
This means that we can do the following:

```anchor leftPadInternal
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
```

In this implementation, {anchorTerm leftPadInternal}`ans.prependChar c` looks for
{anchorName leftPadInternal}`String.prependChar` as before, but it will take
the `open`ed {anchorTerm leftPadInternal}`LeftPad.Internal` namespace into account. If there is a declaration
whose full name is `String.prependChar`, then it will use that. Otherwise, it will see that the namespace
{anchorTerm leftPadInternal}`LeftPad.Internal` is open, and try the name
{anchorName leftPadInternal (show := LeftPad.Internal.String.prependChar)}`String.prependChar`, which
indeed exists, so the dot notation resolves to a call to that function. On the
other hand, if the {anchorTerm leftPadInternal}`LeftPad.Internal` namespace is
not opened, then the {anchorName leftPadInternal (show := prependChar)}`String.prependChar` function is
not available via dot notation.

This is a good solution: we, as library authors, get to enjoy dot notation, but we do not pollute
the {anchorName leftPadNaive}`String` namespace with symbols we do not want to offer to our users.

DNRO was added by Kyle Miller in [November 2024](https://github.com/leanprover/lean4/pull/6189)
and released as part of Lean 4.15 to (as far as I can tell) relatively little fanfare. I certainly
didn't realize its importance at the time (if I saw it at all) and only really learned about it after
a friend told me about it quite recently. I think that
DNRO provides a good solution to a problem that many people have felt while working
on their libraries (namely, wanting to patch over API gaps in upstream libraries without implicitly
or explicitly intruding into that library's territory).

Another interesting opportunity arising from DNRO is that it lets a library provide additional
functions as an opt-in. For example, a library could choose to provide a “simple” API for
a type, which is available by default, and an “advanced” API, which only becomes available after
`open`ing something like `Library.Advanced`. Or, in the case of Lean itself, something like `open Lean`
might make additional functions on basic types (which are not part of the standard library canon but
nonetheless useful for metaprogramming) available via dot notation. It is a very flexible feature.

Really, the main difference from the low-tech solution described in the previous section is the organization
of namespaces. Since the `open` effectively only strips away namespace components from the front of the
name, the “dot-notation-enabling name” (like {anchorName leftPadInternal}`String.prependChar`) needs
to be a suffix of the full name, so we end up with names like
{anchorName leftPadInternal (show := LeftPad.Internal.String.prependChar)}`String.prependChar`. It
took me a while to get
used to this naming style, as previously there was no established convention of naming extensions to
upstream libraries as `DownstreamLibrary.UpstreamNamespace.functionName`, but it is a practice I hope
to see more of in the future.

The Lean distribution itself will be using DNRO to reduce the namespace pollution in the namespaces
belonging to Lean's basic types and its standard library. Our long-term goal is that all public functions on standard library types
should be part of the fully supported, high-quality, consistent standard library API, and all helpers and other non-public
declarations are either private or hidden in other namespaces.

# Bonus: a new linter

As I was working on increasing adoption of DNRO in the Lean core codebase, I noticed a
usability concern that will possibly be made worse by using DNRO more: merely adding a
declaration in a new namespace can break downstream code!

This is best illustrated using an example. Suppose we are building a library `MyLibrary`, and it
has code that looks something like this:

```leanInit myLib
-- This block initializes a Lean context
```

```lean myLib -show
-- The first command parsed in a fresh context gets the whole preceding file
-- attached as leading trivia (`ModuleParserState.hasLeading`), which the blog
-- genre would render. This hidden block absorbs that instead of the first
-- visible block.
--
-- The linter is disabled because `haystack`/`needle` in the deliberately broken `contains` below is
-- unused (its body fails to elaborate), and the warning would nag in editors.
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
```

```lean myLib -keep
namespace MyLibrary

open String

def has (haystack needle : String) : Bool :=
  contains haystack needle

end MyLibrary
```

This works fine. However, imagine now that before the `open String`, we add our
{anchorName leftPadNaive}`prependChar` function
from before. Suddenly, the definition of `has` no longer compiles:

```lean myLib +error -keep
namespace MyLibrary

def String.prependChar (c : Char) (s : String) : String :=
  String.singleton c ++ s

open String

def has (haystack needle : String) : Bool :=
  contains haystack needle

end MyLibrary
```

This looks quite puzzling. Can you see what the problem is?

It turns out that the problem is not with the `contains`, but with the `open` command before it!
Adding the new declaration silently changed which `String` the `open String` refers to.

To help debug this, in Lean 4.33, we added a new linter. Try hovering
over the linter warning on the `open String`:

```lean myLib -show
set_option linter.ambiguousOpen true
```

```lean myLib +error -keep
namespace MyLibrary

def String.prependChar (c : Char) (s : String) : String :=
  String.singleton c ++ s

open String

def has (haystack needle : String) : Bool :=
  contains haystack needle

end MyLibrary
```

The underlying problem here is that `open` inside a `namespace` only opens namespaces inside the
namespace we're in, _except if there are no such namespaces_, in which case it will open
namespaces outside the namespace we're in. In the initial snippet, there was no namespace which
starts in `MyLibrary` and ends in `String`, so we fell back to the global `String` namespace.
After adding the
{anchorName myLibraryPrependChar (show := MyLibrary.String.prependChar)}`String.prependChar`
function, there is now a `MyLibrary.String` namespace, so `open String` opens that, and no longer
opens the global `String` namespace, leading to `contains` no longer resolving to `String.contains`.

In this simple example, it's quite clear that the newly added function somehow has to be responsible.
In real examples, this scenario might occur after updating a dependency, so the new function is in
a completely different file that you might not even know exists, silently changing the behavior
of your downstream `open` command. With the new linter, you still get the breakage, but you get a
clear linter warning telling you what the correct fix is, namely disambiguating the `open` command
either by making it more specific, or, as in the following snippet, moving it to a different location:

```lean myLib

namespace MyLibrary

def String.prependChar (c : Char) (s : String) : String :=
  String.singleton c ++ s

end MyLibrary

open String -- writing `open _root_.String` in the same place as earlier would also have worked

namespace MyLibrary

def has (haystack needle : String) : Bool :=
  contains haystack needle

end MyLibrary
```

I expect that this situation will arise frequently if DNRO is adopted
more. Many projects will `open Std` inside `namespace MyLibrary`. This will break as soon as the
project decides to extend something from the standard library: under the new namespacing scheme,
the new material will live in the `MyLibrary.Std`
namespace, causing the `open Std` to refer to `MyLibrary.Std` instead of the global `Std`. I hope that
the new linter will make adjusting the `open` statements easier.
