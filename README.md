# juliahimmel.de

The source of my blog, built with [Verso](https://github.com/leanprover/verso)
(and [SubVerso](https://github.com/leanprover/subverso) for the code samples).
It replaces the old Jekyll/Minimal Mistakes setup while keeping every URL
stable.

## Layout

```
Main.lean            The site definition and the generator (adapted blogMain):
                     stable post slugs, Atom feed, sitemap, 404 page, CNAME,
                     self-hosted KaTeX.
Blog/                Pages (Front, Now, ...) and posts (Blog/Posts/*),
                     written in Verso markup.
Blog/SiteTheme.lean  The theme: templates for pages/posts/archives and the
                     per-path overrides for /, /posts/ and /tags/.
Blog/Tags.lean       Tag definitions (slugs must match the old /tags/# anchors).
static-src/style.css The stylesheet (light & dark via prefers-color-scheme).
static/              Files copied verbatim into the site (images, ...).
examples/            One Lean project per code post, each pinned to the Lean
                     version the post was written against.
```

## Interactive code samples

Each post with code has a project under `examples/` with its own
`lean-toolchain`:

| project | Lean | post |
|---|---|---|
| `examples/largest-divisor` | v4.20.1 | The largest divisor |
| `examples/iterators` | v4.22.0 | Lean has iterators now |
| `examples/mvcgen` | v4.22.0 | My first verified (imperative) program |

The code in these projects is the *real, compiling* code from the posts.
Regions are marked with `-- ANCHOR: name` / `-- ANCHOR_END: name` comments and
quoted in the posts with ```` ```anchor name ```` code blocks; the build fails
if the quoted text does not match the source, and the rendered code gets
hover tooltips (types, docstrings, proof states) from the *era-correct*
compiler.

During a site build, Verso runs `elan run --install <toolchain> lake build`
inside each example project, so the right toolchains are downloaded
automatically (via the `subverso-extract-mod` executable and the
`:highlighted` module facet of the pinned SubVerso dependency).

Two things to know when touching the example projects:

* Each example project requires exactly the SubVerso version corresponding
  to the site's Verso tag — SubVerso publishes a `verso-vX.Y.Z` tag for every
  Verso tag `vX.Y.Z`, and its data format is an implementation detail with no
  compatibility guarantees between versions, so both sides must match.
  Projects whose Lean predates the module system (< 4.25) can't build that
  version directly, so they pin its automatically demodulized twin, tagged
  `no-modules/<commit>` after the commit that `verso-vX.Y.Z` points to.
* Always use `lake update --keep-toolchain` in the example projects —
  a plain `lake update` overwrites `lean-toolchain` with SubVerso's, which
  would defeat the whole point of per-post toolchains.

## Building

```sh
lake exe blog --output _site
```

The first build downloads and builds the example toolchains and is slow;
afterwards everything is cached. The result in `_site/` is fully static and
self-contained (KaTeX, tippy.js etc. are all served from `-verso-data/`, no
CDN), so any static file server can host it:

```sh
python3 -m http.server -d _site
```

## URL stability

The old site used the permalink `/:categories/:title/` ⇒ `/blog/<slug>/`.
The `postSlugs` table in `Main.lean` maps each post title to its old slug —
**never change existing entries**. New posts get a Jekyll-style slug derived
from the title; add an explicit entry if you need a different one.

Also kept alive: `/now/`, `/posts/`, `/tags/` (including the old
`/tags/#<slug>` anchors), `/feed.xml`, `/sitemap.xml`, `/404.html`. The About
page's content moved to the front page; `/about/` is a redirect to `/`.

## Writing a new post

Run `lake exe new-post` (from the repository root). It asks for the title,
date, authors, tags (creating new ones in `Blog/Tags.lean` if needed), the
URL slug and whether the post contains Lean code, and then does steps 1–3
below — including the example project and its `lake-manifest.json`, and a
`postSlugs` entry if a custom slug was chosen. The manual steps it automates:

1. Create `Blog/Posts/MyPost.lean` with `#doc (Post) "Title" =>`, a `%%%`
   metadata block (date, authors, categories) and the content in Verso markup.
2. If it contains Lean code, create `examples/my-post/` with the right
   `lean-toolchain`, the SubVerso require, and anchored code.
3. Import the module in `Blog.lean` and add it to the `site` definition in
   `Main.lean` (posts in the `"blog" ... with` block).
4. `lake exe blog --output _site` and check the result.

## Updating Lean/Verso

1. Set the new tag under the `verso` require in the root `lakefile.toml`
   (`rev = "vX.Y.Z"`) and run a plain `lake update` — here (and only here)
   the toolchain rewrite is what we want: it updates `lean-toolchain` to the
   Lean version Verso is built against.
2. Repin `subverso` in every `examples/*/lakefile.toml` to the corresponding
   SubVerso tag: `rev = "verso-vX.Y.Z"` for projects on a module-system Lean
   (≥ 4.25). Projects on an older Lean need the demodulized twin instead:
   `rev = "no-modules/<commit>"`, where `<commit>` is the commit that
   `verso-vX.Y.Z` points to — look it up with
   `git ls-remote https://github.com/leanprover/subverso refs/tags/verso-vX.Y.Z`.
3. In each example project, run
   `elan run --install $(cat lean-toolchain) lake update --keep-toolchain`
   to regenerate its manifest.
4. `lake exe blog --output _site` and check the result.

## Deployment

`.github/workflows/deploy.yml` builds the site with elan/lake and publishes
`_site/` to GitHub Pages on every push to `main` (the generated site includes
the `CNAME` for juliahimmel.de and a `.nojekyll`). The workflow caches
`~/.elan` and the `.lake` directories, since the first build compiles Verso
and three example toolchains.
