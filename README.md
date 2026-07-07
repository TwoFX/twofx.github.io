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

* The SubVerso revision is pinned in each `lakefile.toml` to a commit that
  still compiles with the old toolchains (newer SubVerso requires the Lean
  module system, ≥ 4.29). Verso's own test suite parses JSON produced by this
  revision, so it stays compatible with the site's Verso.
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

1. Create `Blog/Posts/MyPost.lean` with `#doc (Post) "Title" =>`, a `%%%`
   metadata block (date, authors, categories) and the content in Verso markup.
2. If it contains Lean code, create `examples/my-post/` with the right
   `lean-toolchain`, the SubVerso require, and anchored code.
3. Import the module in `Blog.lean` and add it to the `site` definition in
   `Main.lean` (posts in the `"blog" ... with` block).
4. `lake exe blog --output _site` and check the result.

## Deployment

`.github/workflows/deploy.yml` builds the site with elan/lake and publishes
`_site/` to GitHub Pages on every push to `main` (the generated site includes
the `CNAME` for juliahimmel.de and a `.nojekyll`). The workflow caches
`~/.elan` and the `.lake` directories, since the first build compiles Verso
and three example toolchains.
