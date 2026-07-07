import VersoBlog
import Verso.Output.Html.KaTeX
import Verso.Code.Highlighted.WebAssets

open Verso Doc Genre Blog Template
open Verso.Output Html

namespace Blog.SiteTheme

def siteName : String := "Julia Markus Himmel"

def siteUrl : String := "https://juliahimmel.de"

def siteDescription : String :=
  "Julia Markus Himmel's blog, mostly about formal verification, " ++
  "in particular in the programming language Lean."

/-! ## Helpers for working with the posts of the site -/

private def monthNames : Array String :=
  #["January", "February", "March", "April", "May", "June",
    "July", "August", "September", "October", "November", "December"]

def formatDate (d : Verso.Genre.Blog.Date) : String :=
  let m := monthNames[d.month - 1]? |>.getD (toString d.month)
  s!"{m} {d.day}, {d.year}"

partial def postsOfDir : Dir → Array BlogPost
  | .page _ _ _ contents => contents.foldl (fun acc d => acc ++ postsOfDir d) #[]
  | .blog _ _ _ posts => posts
  | .static .. => #[]

def allPosts (site : Site) : Array BlogPost :=
  match site with
  | .page _ _ contents => contents.foldl (fun acc d => acc ++ postsOfDir d) #[]
  | .blog _ _ posts => posts

def dateOf (p : BlogPost) : Int × Nat × Nat :=
  match p.contents.metadata with
  | .some md => (md.date.year, md.date.month, md.date.day)
  | .none => (0, 0, 0)

def dateLt (a b : Int × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- All posts of the site, newest first. -/
def sortedPosts (site : Site) : Array BlogPost :=
  (allPosts site).qsort fun a b => dateLt (dateOf b) (dateOf a)

partial def partWordCount (p : Part Post) : Nat :=
  p.content.foldl (fun acc b => acc + b.wordCount) 0 +
    p.subParts.foldl (fun acc s => acc + partWordCount s) 0

def readMinutes (p : BlogPost) : Nat :=
  max 1 ((partWordCount p.contents + 199) / 200)

def tagsOf (p : BlogPost) : List Post.Category :=
  p.contents.metadata.map (·.categories) |>.getD []

/-- All tags used by the given posts, sorted by name. -/
def allTags (posts : Array BlogPost) : Array Post.Category :=
  let cats := posts.foldl (fun acc p => acc ++ (tagsOf p).toArray) #[]
  let uniq := cats.foldl (init := (#[] : Array Post.Category)) fun acc c =>
    if acc.contains c then acc else acc.push c
  uniq.qsort (fun a b => a.name < b.name)

/-! ## Templates -/

def tagLinks (cats : List Post.Category) : Html :=
  if cats.isEmpty then .empty
  else {{
    <span class="post-tags">
      {{cats.toArray.map fun c => {{<a class="tag" href=s!"tags/#{c.slug}">{{c.name}}</a>" "}}}}
    </span>
  }}

/-- A single entry in a list of posts. -/
def postEntry (post : BlogPost) : TemplateM Html := do
  let name ← post.postName'
  let url := s!"blog/{name}/"
  let metaHtml : Html :=
    match post.contents.metadata with
    | .some md => {{
        <p class="post-entry-meta">
          <time class="post-date">{{formatDate md.date}}</time>
          " · " {{s!"{readMinutes post} minute read "}}
          {{tagLinks md.categories}}
        </p>
      }}
    | .none => .empty
  pure {{
    <li class="post-entry">
      <h3 class="post-entry-title"><a href={{url}}>{{post.contents.titleString}}</a></h3>
      {{metaHtml}}
    </li>
  }}

/--
The contents of `<head>` that are needed for the site to work. This is a copy
of `Verso.Genre.Blog.Template.builtinHeader` that self-hosts KaTeX and
marked.js (via the theme's CSS/JS files) instead of loading them from a CDN,
so that the generated site is fully self-contained.
-/
def selfContainedHeader : TemplateM Html := do
  let siteRoot := String.join ((← currentPath).toList.map fun _ => "../") ++ "./"
  let mut out := .empty
  out := out ++ {{<base href={{siteRoot}}/>}}
  out := out ++ {{<style>{{«verso-vars.css»}}</style>}}
  for style in (← read).builtInStyles do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← read).builtInScripts do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  for js in (← read).jsFiles do
    out := out ++ {{<script src=s!"-verso-data/{js}"></script>}}
  for css in (← read).cssFiles do
    out := out ++ {{<link rel="stylesheet" href=s!"-verso-data/{css}"/>}}
  for style in (← get).headerCss do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← get).headerJs do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  pure out

def primary : Template := do
  let path ← currentPath
  let titleStr : String ← param "title"
  let pageTitle := if path.toList.isEmpty then siteName else s!"{titleStr} - {siteName}"
  let postList : Html :=
    match (← param? "posts") with
    | .none => Html.empty
    | .some html => html
  let catList : Html :=
    match (← param? (α := Post.Categories) "categories") with
    | .none => Html.empty
    | .some ⟨cats⟩ =>
      if cats.isEmpty then Html.empty
      else {{
        <p class="category-list">
          "Tags: "
          {{cats.map fun (target, cat) => {{<a href={{target}}>{{Post.Category.name cat}}</a>" "}}}}
        </p>
      }}
  return {{
    <html lang="en">
      <head>
        <meta charset="utf-8"/>
        <meta name="viewport" content="width=device-width, initial-scale=1"/>
        <meta name="color-scheme" content="light dark"/>
        <meta name="description" content={{siteDescription}}/>
        <!-- Stop favicon requests -->
        <link rel="icon" href="data:,"/>
        <title>{{pageTitle}}</title>
        <link rel="me" href="https://hachyderm.io/@juhi"/>
        <link rel="alternate" type="application/atom+xml" title={{siteName}} href=s!"{siteUrl}/feed.xml"/>
        {{← selfContainedHeader}}
      </head>
      <body>
        <header class="site-header">
          <div class="site-header-inner">
            <a class="site-title" href=".">{{siteName}}</a>
            <nav class="site-nav">
              <a href="posts/">"Posts"</a>
              <a href="tags/">"Tags"</a>
              <a href="now/">"Now"</a>
            </nav>
          </div>
        </header>
        <main>
          {{← param "content"}}
          {{postList}}
          {{catList}}
        </main>
        <footer class="site-footer">
          <p>
            <a href="https://github.com/TwoFX">"GitHub"</a>
            " · "
            <a rel="me" href="https://hachyderm.io/@juhi">"Mastodon"</a>
            " · "
            <a href=s!"{siteUrl}/feed.xml">"Feed"</a>
          </p>
          <p>
            "© Julia Markus Himmel. Built with "
            <a href="https://lean-lang.org/">"Lean"</a>
            " and "
            <a href="https://github.com/leanprover/verso">"Verso"</a>
            "."
          </p>
        </footer>
      </body>
    </html>
  }}

def page : Template := do
  pure {{
    <article class="page">
      <h1 class="page-title">{{← param "title"}}</h1>
      {{← param "content"}}
    </article>
  }}

def post : Template := do
  let metaHtml : Html ←
    match (← param? "metadata") with
    | .none => pure Html.empty
    | .some (md : Post.PartMetadata) => do
      let readTime : Html :=
        match (← param? (α := String) "readtime") with
        | .some mins => {{ " · " {{s!"{mins} minute read "}} }}
        | .none => .empty
      pure {{
        <p class="post-meta">
          <time class="post-date">{{formatDate md.date}}</time>
          {{readTime}}
          {{tagLinks md.categories}}
        </p>
      }}
  pure {{
    <article class="post">
      <header>
        <h1>{{← param "title"}}</h1>
        {{metaHtml}}
      </header>
      {{← param "content"}}
    </article>
  }}

def category : Template := do
  let category : Post.Category ← param "category"
  pure {{
    <h1>{{category.name}}</h1>
    <p class="post-meta">"All posts tagged with “" {{category.name}} "”."</p>
  }}

def archiveEntry : Template := do
  let post : BlogPost ← param "post"
  postEntry post

/-! ## Per-path template overrides -/

/-- The front page: author card, intro text, and the list of posts. -/
def homePage : Template := do
  let posts := sortedPosts (← read).site
  let entries ← posts.mapM postEntry
  pure {{
    <div class="home">
      <section class="author-card">
        <img class="author-photo" src="static/images/bio-photo.jpg" alt="Photo of Julia Markus Himmel"/>
        <div class="author-info">
          <h1 class="author-name">{{siteName}}</h1>
          <p class="author-bio">"Mathematics and computer science"</p>
          <p class="author-links">
            <a href="https://juliahimmel.de">"Website"</a>
            <a href="https://github.com/TwoFX">"GitHub"</a>
            <a rel="me" href="https://hachyderm.io/@juhi">"Mastodon"</a>
          </p>
        </div>
      </section>
      <section class="home-intro">
        {{← param "content"}}
      </section>
      <section class="recent-posts">
        <h2>"Recent posts"</h2>
        <ul class="post-list">{{entries}}</ul>
      </section>
    </div>
  }}

/-- The `/posts/` page: all posts, grouped by year. Replaces the old Jekyll
"Posts by Year" archive at the same URL. -/
def postsByYear : Template := do
  let posts := sortedPosts (← read).site
  let years := posts.foldl (init := (#[] : Array Int)) fun acc p =>
    let y := (dateOf p).1
    if acc.contains y then acc else acc.push y
  let mut sections := Html.empty
  for y in years do
    let yearPosts := posts.filter fun p => (dateOf p).1 == y
    let entries ← yearPosts.mapM postEntry
    sections := sections ++ {{
      <section class="year-group">
        <h2 id=s!"{y}">{{toString y}}</h2>
        <ul class="post-list">{{entries}}</ul>
      </section>
    }}
  pure {{
    <article class="page">
      <h1 class="page-title">{{← param "title"}}</h1>
      {{sections}}
    </article>
  }}

/-- The `/tags/` page: all posts, grouped by tag. Replaces the old Jekyll
"Posts by Tag" archive at the same URL; the `id` attributes of the headers
match the anchors that Minimal Mistakes generated, so old deep links like
`/tags/#lean` keep working. -/
def tagsPage : Template := do
  let posts := sortedPosts (← read).site
  let tags := allTags posts
  let mut sections := Html.empty
  for tag in tags do
    let tagPosts := posts.filter fun p => (tagsOf p).contains tag
    let entries ← tagPosts.mapM postEntry
    sections := sections ++ {{
      <section class="tag-group">
        <h2 id={{tag.slug}}>{{tag.name}}</h2>
        <ul class="post-list">{{entries}}</ul>
      </section>
    }}
  pure {{
    <article class="page">
      <h1 class="page-title">{{← param "title"}}</h1>
      {{sections}}
    </article>
  }}

/-! ## The theme -/

def baseTheme : Theme where
  primaryTemplate := primary
  pageTemplate := page
  postTemplate := post
  categoryTemplate := category
  archiveEntryTemplate := archiveEntry
  cssFiles := #[
    ("style.css", include_str "../static-src/style.css"),
    ("katex/katex.min.css", Verso.Output.Html.katex.css)
  ]
  jsFiles := #[
    ("katex/katex.min.js", Verso.Output.Html.katex.js, false),
    ("marked.umd.min.js", Verso.Code.Highlighted.WebAssets.marked, false)
  ]

def theme : Theme :=
  baseTheme
  |>.override #[] ⟨homePage, id⟩
  |>.override #["posts"] ⟨postsByYear, id⟩
  |>.override #["tags"] ⟨tagsPage, id⟩

end Blog.SiteTheme

-- Note: static-src/style.css is embedded via include_str; edit this comment
-- (or use lake build --rehash) to force a rebuild after changing the CSS.
-- CSS revision: 4 (inline math is not code)
