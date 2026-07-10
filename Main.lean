import VersoBlog
import Blog

open Verso Genre Blog Site Syntax
open Verso.Output (Html)
open Blog.SiteTheme (theme siteName siteUrl siteDescription allPosts dateOf sortedPosts readMinutes)

/-!
# URL stability

The old Jekyll site used the permalink pattern `/:categories/:title/`, where
`:title` is the slug from the post's file name. All posts were in the `blog`
category, so posts live at `/blog/<slug>/`. The slugs below reproduce the old
slugs exactly; they must never change, or links out in the wild will break.
-/

def postSlugs : List (String × String) := [
  ("The largest divisor", "the-largest-divisor"),
  ("Lean has iterators now", "iterators"),
  ("Freyd-Mitchell and Gabriel-Popescu", "freyd-mitchell"),
  ("My first verified (imperative) program", "my-first-verified-imperative-program"),
  ("Floats in Lean 4.33", "float-qanda")
]

/-- Jekyll-style slug for future posts: lowercase, spaces become dashes, other
non-alphanumeric characters are dropped. No date prefix, matching the old
site's permalink structure. -/
def slugify (title : String) : String := Id.run do
  let mut slug := ""
  for c in title.toList do
    if c == ' ' then slug := slug.push '-'
    else if c.isAlpha || c.isDigit then slug := slug.push c.toLower
    else continue
  pure slug

def myPostName (_date : Verso.Genre.Blog.Date) (title : String) : String :=
  (postSlugs.lookup title).getD (slugify title)

/-!
# The site itself
-/

def theSite : Site := site Blog.Front /
  static "static" ← "static"
  "posts" Blog.PostsPage
  "tags" Blog.TagsPage
  "now" Blog.Now
  "blog" Blog.BlogIndex with
    Blog.Posts.AnUnderappreciatedLeanFeature
    Blog.Posts.FloatQanda
    Blog.Posts.Mvcgen
    Blog.Posts.FreydMitchell
    Blog.Posts.Iterators
    Blog.Posts.LargestDivisor

/-!
# Extra output files: feed, sitemap, 404 page

The old site served an Atom feed at `/feed.xml` (via jekyll-feed) and a
sitemap at `/sitemap.xml` (via jekyll-sitemap), and a 404 page at `/404.html`.
These are generated here to keep those URLs alive.
-/

def xmlEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

structure PostInfo where
  title : String
  slug : String
  date : Verso.Genre.Blog.Date

def postInfos (theSite : Site) : Array PostInfo :=
  sortedPosts theSite |>.map fun p =>
    let title := p.contents.titleString
    let date := p.contents.metadata.map (·.date) |>.getD ⟨1900, 1, 1⟩
    { title, slug := myPostName date title, date }

def feedXml (posts : Array PostInfo) : String := Id.run do
  let updated :=
    match posts[0]? with
    | some p => s!"{p.date.toIso8601String}T00:00:00Z"
    | none => "1900-01-01T00:00:00Z"
  let mut out := "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
  out := out ++ "<feed xmlns=\"http://www.w3.org/2005/Atom\">\n"
  out := out ++ s!"  <title>{xmlEscape siteName}</title>\n"
  out := out ++ s!"  <subtitle>{xmlEscape siteDescription}</subtitle>\n"
  out := out ++ s!"  <id>{siteUrl}/feed.xml</id>\n"
  out := out ++ s!"  <link href=\"{siteUrl}/feed.xml\" rel=\"self\"/>\n"
  out := out ++ s!"  <link href=\"{siteUrl}/\"/>\n"
  out := out ++ s!"  <updated>{updated}</updated>\n"
  out := out ++ s!"  <author><name>{xmlEscape siteName}</name></author>\n"
  for p in posts do
    let url := s!"{siteUrl}/blog/{p.slug}/"
    out := out ++ "  <entry>\n"
    out := out ++ s!"    <title>{xmlEscape p.title}</title>\n"
    out := out ++ s!"    <id>{url}</id>\n"
    out := out ++ s!"    <link href=\"{url}\"/>\n"
    out := out ++ s!"    <updated>{p.date.toIso8601String}T00:00:00Z</updated>\n"
    out := out ++ "  </entry>\n"
  out := out ++ "</feed>\n"
  pure out

def sitemapXml (posts : Array PostInfo) : String := Id.run do
  let pages := #["", "now/", "posts/", "tags/", "blog/"] ++
    posts.map (fun p => s!"blog/{p.slug}/")
  let mut out := "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
  out := out ++ "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">\n"
  for p in pages do
    out := out ++ s!"  <url><loc>{siteUrl}/{p}</loc></url>\n"
  out := out ++ "</urlset>\n"
  pure out

/-- The old site had an About page at `/about/`; its content now lives on the
front page. Keep the URL alive with a client-side redirect. -/
def aboutRedirectHtml : String := "<!doctype html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\">
<meta http-equiv=\"refresh\" content=\"0; url=/\">
<link rel=\"canonical\" href=\"" ++ siteUrl ++ "/\">
<title>" ++ siteName ++ "</title>
</head>
<body>
<p>This page has moved to <a href=\"/\">the front page</a>.</p>
</body>
</html>
"

def notFoundHtml : String := "<!doctype html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\">
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
<meta name=\"color-scheme\" content=\"light dark\">
<title>Page Not Found - " ++ siteName ++ "</title>
<style>
body { font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\", Roboto, \"Helvetica Neue\", Arial, sans-serif;
       max-width: 46rem; margin: 0 auto; padding: 3rem 1.25rem; line-height: 1.65;
       color: #3d4144; background: #fff; }
a { color: #2f7bbd; }
@media (prefers-color-scheme: dark) {
  body { color: #d4d8dc; background: #252a34; }
  a { color: #7cb8e8; }
}
</style>
</head>
<body>
<h1>Page Not Found</h1>
<p>Sorry, but the page you were trying to view does not exist.</p>
<p><a href=\"/\">Back to the front page</a></p>
</body>
</html>
"

/-!
# The generator

This is `Verso.Genre.Blog.blogMain`, adapted to
* use a custom `postName` function for stable URLs,
* write the extra output files described above, and
* self-host the KaTeX fonts (the CSS and JS are part of the theme).
-/

open Template in
def generateSite (theme : Theme) (siteToGen : Site) (options : List String)
    (extraParams : Multi.Path → Template.Params := fun _ => {}) : IO UInt32 :=
  withLogger fun logger => do
    let components : Components := by exact %registered_components
    let linkTargets : Code.LinkTargets TraverseContext := {}
    let cfg ← opts { postName := myPostName } options
    let (site', xref) ← siteToGen.traverse cfg components |>.run logger
    let initGenCtx : Generate.Context := {
      theme, «site» := site',
      ctxt := { path := .root, config := cfg, components },
      xref := xref,
      dir := cfg.destination,
      config := cfg,
      header := Html.doctype,
      linkTargets := linkTargets,
      components := components,
      extraParams := extraParams
    }
    let (((), st), _) ← site'.generate theme initGenCtx .empty {} |>.run logger

    -- Verso's supporting data (hover info, JS, CSS)
    FS.ensureDir (cfg.destination.join "-verso-data")
    FS.ensureDir (cfg.destination.join "-verso-data" |>.join "katex" |>.join "fonts")
    IO.FS.writeFile (cfg.destination.join "-verso-docs.json") (toString st.dedup.docJson)
    for (name, content, srcMap?) in xref.jsFiles do
      IO.FS.writeFile (cfg.destination.join "-verso-data" |>.join name) content
      if let some (mapName, mapContent) := srcMap? then
        IO.FS.writeFile (cfg.destination.join "-verso-data" |>.join mapName) mapContent
    for (name, content, _) in theme.jsFiles do
      IO.FS.writeFile (cfg.destination.join "-verso-data" |>.join name) content
    for (name, content) in theme.cssFiles ++ xref.cssFiles do
      IO.FS.writeFile (cfg.destination.join "-verso-data" |>.join name) content
    for (name, contents) in Verso.Output.Html.katexFonts do
      IO.FS.writeBinFile (cfg.destination.join "-verso-data" |>.join name) contents

    -- Extra outputs for URL stability and deployment
    let posts := postInfos siteToGen
    IO.FS.writeFile (cfg.destination.join "feed.xml") (feedXml posts)
    IO.FS.writeFile (cfg.destination.join "sitemap.xml") (sitemapXml posts)
    IO.FS.writeFile (cfg.destination.join "404.html") notFoundHtml
    FS.ensureDir (cfg.destination.join "about")
    IO.FS.writeFile (cfg.destination.join "about" |>.join "index.html") aboutRedirectHtml
    IO.FS.writeFile (cfg.destination.join "CNAME") "juliahimmel.de\n"
    IO.FS.writeFile (cfg.destination.join ".nojekyll") ""
where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--drafts"::more) => opts {cfg with showDrafts := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

def main (args : List String) : IO UInt32 := do
  -- Read time for each post, injected into the post pages' templates
  let readTimes : List (List String × String) :=
    (allPosts theSite).toList.map fun p =>
      let title := p.contents.titleString
      let date := p.contents.metadata.map (·.date) |>.getD ⟨1900, 1, 1⟩
      (["blog", myPostName date title], toString (readMinutes p))
  let extraParams : Multi.Path → Template.Params := fun path =>
    match readTimes.lookup path.toList with
    | some mins => Template.Params.ofList [("readtime", mins)]
    | none => {}
  generateSite theme theSite args extraParams
