import VersoBlog
import Blog.Tags

open Verso Genre Blog
open Blog.Tag

set_option pp.rawOnError true

#doc (Post) "Floats in Lean 4.33" =>

%%%
authors := ["Julia Markus Himmel"]
date := {year := 2026, month := 6, day := 19}
categories := [lean, floats]
%%%

Here is a little informal Q&A-style post about the changes to `Float` in Lean
4.33. The questions are meant to be read from top to bottom, not in arbitrary
order. This is not an "official" communication by the Lean FRO, whatever that
may mean.

# What is changing about floats in Lean 4.33?

Up until Lean 4.32, the `Float` type and all operations defined on it were
opaque to Lean's kernel. This means that it was possible to write programs
involving floats, and the compiler would happily compile them directly to C's
`double` type, but it was not possible to prove anything about the float
operations.

Starting in Lean 4.33, `Float`, and _some_ of the functions defined for floats,
now have a definition. `Float` is now (after
[#14091](https://github.com/leanprover/lean4/pull/14091)) a wrapper around a
new type `Float.Model` (which was added in
[#14079](https://github.com/leanprover/lean4/pull/14079)), and `Float.Model` is
a pure Lean implementation of 64-bit floating-point numbers with a subset of
the operations that are defined on `Float`. If you write code with `Float`, it
will continue to be compiled to native floating-point operations (in fact,
nothing changes at all from the perspective of the compiled code), but you can
now unfold the float operations in proofs and will see the implementation on
`Float.Model`.

Of course, everything I'm saying in this post about `Float` equally applies to
`Float32`, so there is also a `Float32.Model`.

In terms of implementation, `Float.Model` is a subtype of `UInt64` (forcing
representations of NaN to be canonical; see the question about correctness for
details), and
`Float32.Model` is a subtype of `UInt32`. Operations are implemented by
unpacking these bitvectors to an inductive `UnpackedFloat` which is shared
between the single- and double-precision worlds, performing the actual computation
and rounding there, and repacking afterwards.

You could, in theory, also write your code directly in terms of `Float.Model`,
which means that your program will then execute the model implementations
instead of using your CPU's native floating-point support. This way, you can
achieve a spectacular 200x speed-down on your code with the added bonus of far
fewer supported operations and an overall suboptimal experience.

# How can I use this?

The boring use case is that floating-point operations now execute in the
kernel, so that you can prove `0.1 + 0.2 != 0.3` with `rfl`. However, you should
be aware that it is not a goal to make these kinds of kernel computations for
floating-point numbers efficient, so you should not expect this to scale to
non-trivial examples.

The other, much more interesting, use case is that it is now, in principle,
possible to prove all kinds of properties about Lean programs involving the
`Float` type. This brings us to the important bit.

# The important bit

The `Float.Model` type and its associated theory are
*not* a fully-featured general-purpose floating-point library, and they will
never be one. Neither we, nor anyone else, should develop extensive theory
about the `Float.Model` type and prove lemmas directly about this type.

Instead, if you are interested in proving things about your programs involving
`Float`, here is what you should do:

* In a downstream library, develop a fully-featured general-purpose
  floating-point library, for example by porting Flocq, or by porting SymFPU,
  or by reading the IEEE-754 specification (and maybe the _Handbook of
  Floating-Point Arithmetic_) and writing something from scratch
* Prove that the `Float.Model` type is equivalent to your type corresponding to
  the IEEE binary64 format without NaN payloads, and that all of the operations
  commute with that equivalence
* Transfer lemmas about your nice downstream float type to `Float.Model` along
  that equivalence

Doing the verification layers separately like this is a good idea because the
development of `Float.Model` had very specific goals, namely to be simple,
concise, stable, and, above all, correct, specifically for the
`Float` and `Float32` types. In particular, if for example our rounding algorithm
turned out to be incorrect for 16-bit floats but correct for 32-bit floats and
64-bit floats, then it is quite possible that we would leave the bug unfixed in order
to avoid a breaking change. A proper floating-point library should cover many
more cases like smaller/larger floats, perhaps even fixed-point numbers. It
should also put more emphasis on ergonomics and of course verifiability. Even
if we planned to add a floating-point verification layer to the Lean standard
library, which we are not planning to do, we would make this entirely separate
from the construction of `Float.Model`.

# Are you going to ship lemmas about `Float` as part of the Lean distribution?

No, see above.

# Are you adding a general-purpose floating-point library to the Lean standard library?

No, see above. Note also that it would be quite difficult for us to do this,
because we don't have plans to add a real number type to the Lean distribution,
which is a prerequisite for a proper float verification layer.

# I am writing a pure proof development involving floating-point numbers and I have no plans to execute my code. Is the new material useful to me?

No.

# I have goals about `Float` or `Float32` that I want to bitblast and dispatch using `bv_decide`. Can I do this now?

Our model is not set up to allow this. However, you can connect `Float.Model`
to a library like [fp-lean](https://github.com/opencompl/fp-lean), transfer your
statement over to their bitblastable floats and then bitblast that.

# How was the model constructed?

While it is not a direct port, part of the code of the model we use
(specifically the `UnpackedFloat` type and the rounding logic) is quite
analogous to the `SpecFloat` construction in the Rocq standard library, which
is itself basically copied from `Flocq`. Our model extends this with a variety
of additional operations and also a packing/unpacking layer (Flocq probably also
has this, but our packing/unpacking code was developed independently). There are
several good reasons to stay true to the prior art here:

* Flocq is an excellent piece of software, and there is no reason to reinvent
  the wheel.
* Flocq has had many eyes on it, so by staying close to it we are increasing
  the likelihood that our model is correct.
* Realistically, it is very likely that whatever turns out to be the dominant
  Lean library for floats will be derived from Flocq. If our model is also
  derived from Flocq, then proving the two approaches equivalent should be an
  easier task.
* Since we are all bound by the IEEE specification, all implementations will be
  somewhat similar anyways.

It is safe to say that our model would not be as good if not for Flocq. I tried
to pay this forward by adding lots of documentation comments, which I hope will
make some of the things that personally puzzled me about floating-point
arithmetic and the rounding procedure in particular easier to learn.

Besides the implementation, various other resources were useful to me,
including:

* A blog post titled [Floating Point Numbers and
  Rounding](https://drilian.com/posts/2023.01.10-floating-point-numbers-and-rounding/)
  (though be aware that there are some typos in the calculations)
* The _Handbook of Floating-Point Arithmetic_.

# Where can I look at the model?

[Here](https://github.com/leanprover/lean4/blob/bc5f89f4abe82ee105ce7922a83e286fd7a67774/src/Init/Data/Float/Model/Float.lean)
is a link to the code.

# Is the model correct?

This question is more subtle than it may seem, because we first have to define
what it means to be "correct". The central goal of `Float.Model` is to behave
exactly like the runtime float functions behave when executed. Everything else
would effectively be a miscompilation, allowing for a proof of `False` using
`native_decide` or memory unsafety at runtime.

So, how do the runtime float
functions behave when executed? Since Lean compiles to C, we are effectively
governed by the C standard here. In typical C fashion, the semantics of
floating-point operations are a minefield of undefined behavior and
implementation-defined behavior. There is an article called [_The pitfalls of
verifying floating-point operations_](https://arxiv.org/pdf/cs/0701192) which
discusses many potential problems. For Lean, the short version is this: we
hardened the runtime a bit ([1](https://github.com/leanprover/lean4/pull/13872)
[2](https://github.com/leanprover/lean4/pull/13930)
[3](https://github.com/leanprover/lean4/pull/14012)), and now, _as long as code
called via FFI does not mess with the floating-point environment_, we can be
confident to observe the behavior required by IEEE 754. The conversions
between floats and integers are an exception, because for these the C standard
has its own opinion about
what should happen (namely, rounding towards zero instead of the
round-to-nearest-even convention which IEEE mandates for the other operations).
For the core operations, this implies that they have exactly (bit-for-bit)
specified behavior on all supported
platforms, and this is the behavior that our model must exhibit.

One small caveat here is that the C platform is extremely noncommittal about
NaN payloads, to the point where [copying a NaN may not preserve its bit
representation.](https://cppreference.com/cpp/types/numeric_limits/quiet_NaN)
This is not acceptable, of course, since the Lean runtime expects values to not
change when they are moved around. The way we address this is by making sure that
when asked for the bit representation of a float, the runtime always canonicalizes
whatever NaN it sees into a fixed canonical NaN. In turn, the logical model only
has a single NaN value without any payload.

Now that we know what "correct" means, how do we validate that our model
implementation is correct? The answer is that besides me having thought very
hard about every single line of code in the model, we do extensive testing.
Luckily, we are not the first people who had a need for difficult test cases
for floating-point implementations, and we were able to benefit from [Berkeley
TestFloat](https://www.jhauser.us/arithmetic/TestFloat.html) and
[UCBTest](https://netlib.org/fp/index.html). The test vectors generated by
these two programs are checked into our code base, and we run close to a
million test cases both on the model and on the native implementation as part
of our test suite. On the model, these tests take about 6.9 seconds, whereas
the native implementation runs them in 0.037 seconds, hence the 200x figure from
earlier.

Additionally, for decimal-to-float conversion, we test against the
[`parse-number-fxx-test-data` suite](https://github.com/nigeltao/parse-number-fxx-test-data).
That's another 5 million tests. We only run a small number (about 10,000) of
them as part of our CI, but it's easy to rerun the full suite after changing
the decimal-to-float routine.

As time progresses, hopefully people will show our model equivalent to their
models, which should further increase confidence.

# Which operations are supported?

As of writing: `add`, `sub`, `mul`, `div`, `sqrt`, `abs`, `neg`, `isNaN`,
`isInf`, `isFinite`, `le`, `lt`, `beq`, `ofInt`, `ofNat`, `ofIntX`, `ofUIntX`,
`toIntX`, `toUIntX`, `ofScientific`.

# Are you going to support more operations?

Yes, there are some more that we hope to get to in the short term (before the
release of 4.33 perhaps), such as `ceil`, `floor`, `round` and `scaleB`.

# Will you add my favorite operation?

It depends. As so often it is a question of how expensive it would be to add,
and how useful having it would be.

For some operations, such as the trigonometric functions, it is not currently
the case that we can safely assume that the C library will give consistent
results across all of our supported platforms.
The IEEE standard makes it a hard requirement to round the basic operations of
addition, subtraction, multiplication, division and square root correctly, but
for more advanced operations there is no such requirement, and in practice the
bit-by-bit behavior of implementations does differ.

So, giving a
logical model would entail pulling in an additional library for reproducible
results (whether these reproducible results are correct is another matter
entirely) and then copying exactly that algorithm into the logical model. This
would be quite expensive.

Even if we are able to give a logical model, it must be realistically possible
for us to validate the implementation. The test suites we are using so far
don't offer tests for many functions beyond those we already have, so ideally
we would need a different source for difficult test cases for the new function.

If you would benefit from having an additional model, you should contact me
and/or open an RFC. As with all feature suggestions to Lean, the ones that are
most likely to get acted on are those which unlock a relevant and real use case
instead of just being something that would be cool to have.

# Will you consider my pull request adding a model for a new operation?

No.

# Why not?

With all of the considerations described above and the fact that getting this
wrong is a miscompilation, reviewing a PR adding a new model is more expensive
than doing it ourselves.
