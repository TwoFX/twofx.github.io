/-
`lake exe new-post` — interactive scaffolding for a new blog post.

This automates the "Writing a new post" section of the README:
1. creates `Blog/Posts/<Module>.lean` with the `#doc (Post)` header and the
   `%%%` metadata block,
2. if the post will contain Lean code, creates `examples/<dir>/` with a
   `lean-toolchain`, a require of the SubVerso version matching the site's
   Verso, and an anchored sample file,
3. imports the module in `Blog.lean` and adds it to the `site` definition in
   `Main.lean`,
4. if a custom URL slug is chosen, records it in `postSlugs` in `Main.lean`.
-/
import Std.Time

open Std.Time

def defaultAuthor : String := "Julia Markus Himmel"

/-! # Small helpers -/

def fileExists (p : String) : IO Bool :=
  System.FilePath.pathExists ⟨p⟩

def strip (s : String) : String :=
  s.trimAscii.toString

def escapeString (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\"
    | '"' => acc ++ "\\\""
    | c => acc.push c

/-- Must match `slugify` in `Main.lean`, which is what the generator applies
to posts without a `postSlugs` entry. -/
def slugify (title : String) : String := Id.run do
  let mut slug := ""
  for c in title.toList do
    if c == ' ' then slug := slug.push '-'
    else if c.isAlpha || c.isDigit then slug := slug.push c.toLower
    else continue
  pure slug

def moduleNameFor (title : String) : String := Id.run do
  let mut result := ""
  let mut newWord := true
  for c in title.toList do
    if c.isAlpha || c.isDigit then
      result := result.push (if newWord then c.toUpper else c)
      newWord := false
    else
      newWord := true
  pure result

def isValidIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c.isAlpha && cs.all fun c => c.isAlphanum || c == '\''

def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

/-! # Interaction -/

def ask (question : String) (default? : Option String := none) : IO String := do
  let stdout ← IO.getStdout
  match default? with
  | some d => stdout.putStr s!"{question} [{d}]: "
  | none => stdout.putStr s!"{question}: "
  stdout.flush
  let answer := strip (← (← IO.getStdin).getLine)
  if answer.isEmpty then
    pure (default?.getD "")
  else
    pure answer

partial def askRequired (question : String) : IO String := do
  let answer ← ask question
  if answer.isEmpty then
    IO.println "Please enter a value."
    askRequired question
  else
    pure answer

def askYesNo (question : String) (default : Bool) : IO Bool := do
  let answer ← ask question (if default then "Y/n" else "y/N")
  match answer.toLower with
  | "y" | "yes" => pure true
  | "n" | "no" => pure false
  | _ => pure default

structure Date where
  year : Nat
  month : Nat
  day : Nat

def Date.toIsoString (d : Date) : String :=
  s!"{d.year}-{pad2 d.month}-{pad2 d.day}"

def parseDate? (s : String) : Option Date := do
  match s.splitOn "-" with
  | [y, m, d] =>
    let y ← y.toNat?
    let m ← m.toNat?
    let d ← d.toNat?
    guard (1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ 31)
    pure ⟨y, m, d⟩
  | _ => none

partial def askDate (today : String) : IO Date := do
  let answer ← ask "Publication date (YYYY-MM-DD)" today
  match parseDate? answer with
  | some d => pure d
  | none =>
    IO.println "Please enter a date in the format YYYY-MM-DD."
    askDate today

partial def askModuleName (default : String) : IO String := do
  let answer ← ask "Module name (Blog/Posts/<Module>.lean)" default
  if !isValidIdent answer then
    IO.println s!"\"{answer}\" is not a valid Lean identifier."
    askModuleName default
  else if ← fileExists s!"Blog/Posts/{answer}.lean" then
    IO.println s!"Blog/Posts/{answer}.lean already exists."
    askModuleName default
  else
    pure answer

partial def askExampleDir (default : String) : IO String := do
  let answer ← ask "Example project directory (examples/<dir>)" default
  if answer.isEmpty || (answer.splitOn "/").length > 1 then
    IO.println "Please enter a plain directory name."
    askExampleDir default
  else if ← fileExists s!"examples/{answer}" then
    IO.println s!"examples/{answer} already exists."
    askExampleDir default
  else
    pure answer

/-! # Tags -/

/-- Extract the identifiers of the `Category` definitions in `Blog/Tags.lean`. -/
def parseTagIdents (tagsSrc : String) : List String :=
  tagsSrc.splitOn "\n" |>.filterMap fun line =>
    if line.startsWith "def " then
      match (line.drop 4).toString.splitOn " : Category" with
      | ident :: _ :: _ => some (strip ident)
      | _ => none
    else none

def appendTagDef (src ident name slug : String) : String :=
  let src := if src.endsWith "\n" then src else src ++ "\n"
  src ++ s!"\ndef {ident} : Category where\n  name := \"{escapeString name}\"\n  slug := \"{slug}\"\n"

/-! # Generated files -/

def postContent (title : String) (date : Date) (authors : List String)
    (tags : List String) (draft : Bool) (example? : Option String)
    (exampleModule : String) : String := Id.run do
  let mut out := "import VersoBlog\nimport Blog.Tags\n\nopen Verso Genre Blog\n"
  if example?.isSome then
    out := out ++ "open Verso.Code.External\n"
  out := out ++ "open Blog.Tag\n\n"
  if let some dir := example? then
    out := out ++ s!"set_option verso.exampleProject \"examples/{dir}\"\n"
    out := out ++ s!"set_option verso.exampleModule \"{exampleModule}\"\n\n"
  out := out ++ "set_option pp.rawOnError true\n\n"
  out := out ++ s!"#doc (Post) \"{escapeString title}\" =>\n\n"
  out := out ++ "%%%\n"
  out := out ++ s!"authors := [{", ".intercalate (authors.map fun a => s!"\"{escapeString a}\"")}]\n"
  out := out ++ s!"date := \{year := {date.year}, month := {date.month}, day := {date.day}}\n"
  out := out ++ s!"categories := [{", ".intercalate tags}]\n"
  if draft then
    out := out ++ "draft := true\n"
  out := out ++ "%%%\n\n"
  if example?.isSome then
    out := out ++ "Write your post here. Quote anchored code from the example project like this:\n\n```anchor hello\ndef hello := \"world\"\n```\n"
  else
    out := out ++ "Write your post here.\n"
  pure out

/--
The SubVerso revision for a new example project. SubVerso publishes a
`verso-vX.Y.Z` tag for every Verso tag `vX.Y.Z`, and the example projects
must use exactly the SubVerso version corresponding to the site's Verso —
the data format is an implementation detail with no compatibility guarantees
between versions. New posts are assumed to use a Lean version with the
module system (≥ 4.25), so they can use this tag directly; only projects on
older Leans need its demodulized `no-modules/<commit>` twin (see "Updating
Verso" in the README).
-/
def subversoRevForNewProject : IO String := do
  let src ← IO.FS.readFile ⟨"lakefile.toml"⟩
  let mut inVerso := false
  for line in src.splitOn "\n" do
    let line := strip line
    if line.startsWith "[[" then
      inVerso := false
    else if line == "name = \"verso\"" then
      inVerso := true
    else if inVerso && line.startsWith "rev = " then
      match line.splitOn "\"" with
      | _ :: tag :: _ =>
        unless tag.startsWith "v" do
          throw (IO.userError s!"the verso rev \"{tag}\" in lakefile.toml is not a version tag; \
            the site must be on a tagged Verso release so that the example project can use \
            the corresponding subverso tag")
        return s!"verso-{tag}"
      | _ => pure ()
  throw (IO.userError "could not find the verso require's rev in lakefile.toml")

def exampleLakefile (mod subversoRev : String) : String :=
  s!"name = \"examples\"\ndefaultTargets = [\"{mod}\"]\n\n[[require]]\nname = \"subverso\"\ngit = \"https://github.com/leanprover/subverso\"\n# The SubVerso version corresponding to the site's Verso tag (see \"Updating\n# Verso\" in the README).\nrev = \"{subversoRev}\"\n\n[[lean_lib]]\nname = \"{mod}\"\n"

def exampleModuleContent (title : String) (date : Date) : String :=
  s!"/-\nCode for the blog post \"{title}\" ({date.toIsoString}).\n-/\n\n-- ANCHOR: hello\ndef hello := \"world\"\n-- ANCHOR_END: hello\n"

/-! # Edits to existing files -/

/-- Add the post to the `"blog" ... with` block in `Main.lean` (newest first). -/
def addToSite (mainSrc mod : String) : Option String :=
  let anchor := "\"blog\" Blog.BlogIndex with"
  match mainSrc.splitOn anchor with
  | [pre, post] => some (pre ++ anchor ++ s!"\n    Blog.Posts.{mod}" ++ post)
  | _ => none

/-- Add an entry to the `postSlugs` table in `Main.lean`. -/
def addSlugOverride (mainSrc title slug : String) : Option String :=
  match mainSrc.splitOn "def postSlugs" with
  | [pre, post] =>
    match post.splitOn "\n]" with
    | first :: rest =>
      if rest.isEmpty then none
      else some <| pre ++ "def postSlugs" ++ first
        ++ s!",\n  (\"{escapeString title}\", \"{slug}\")"
        ++ "\n]" ++ String.intercalate "\n]" rest
    | [] => none
  | _ => none

def runLakeUpdate (dir toolchain : String) : IO Bool := do
  let child ← IO.Process.spawn {
    cmd := "elan"
    args := #["run", "--install", toolchain, "lake", "update", "--keep-toolchain"]
    cwd := some ⟨s!"examples/{dir}"⟩
  }
  pure ((← child.wait) == 0)

/-! # Main -/

def main : IO UInt32 := do
  unless (← fileExists "Main.lean") && (← fileExists "Blog.lean") do
    IO.eprintln "Please run this from the repository root (Main.lean and Blog.lean not found)."
    return 1

  IO.println "Scaffolding a new blog post. Press Enter to accept a [default]."
  IO.println ""

  let title ← askRequired "Title"
  let date ← askDate (← PlainDate.now).toSQLDateString

  let authorsRaw ← ask "Authors (comma-separated)" defaultAuthor
  let authors := authorsRaw.splitOn "," |>.map strip |>.filter (!·.isEmpty)

  -- Tags: offer the existing ones, create missing ones in Blog/Tags.lean
  let tagsSrc ← IO.FS.readFile ⟨"Blog/Tags.lean"⟩
  let mut knownTags := parseTagIdents tagsSrc
  IO.println s!"Existing tags: {", ".intercalate knownTags}"
  let tagsRaw ← ask "Tags (comma-separated, Enter for none)"
  let requestedTags := tagsRaw.splitOn "," |>.map strip |>.filter (!·.isEmpty)
  let mut tags : List String := []
  let mut newTagsSrc := tagsSrc
  let mut tagsModified := false
  for t in requestedTags do
    if knownTags.contains t then
      tags := tags ++ [t]
    else if !isValidIdent t then
      IO.println s!"Skipping tag \"{t}\": not a valid Lean identifier."
    else if ← askYesNo s!"Tag \"{t}\" does not exist yet. Add it to Blog/Tags.lean?" true then
      let name ← ask s!"Display name for \"{t}\"" t
      let slug ← ask s!"Slug for \"{t}\" (used as the /tags/#<slug> anchor)" (slugify name)
      newTagsSrc := appendTagDef newTagsSrc t name slug
      tagsModified := true
      knownTags := knownTags ++ [t]
      tags := tags ++ [t]
    else
      IO.println s!"Skipping tag \"{t}\"."

  let modName ← askModuleName (moduleNameFor title)

  let derivedSlug := slugify title
  let slug ← ask "URL slug (post will live at /blog/<slug>/)" derivedSlug

  let draft ← askYesNo "Mark as draft (only rendered with --drafts)?" false

  -- Optional example project for code samples
  let mut exampleDir? : Option String := none
  let mut toolchain := ""
  let mut ranLakeUpdate := false
  if ← askYesNo "Will the post contain Lean code examples?" false then
    let dir ← askExampleDir derivedSlug
    let repoToolchain := strip (← IO.FS.readFile ⟨"lean-toolchain"⟩)
    IO.println "The example project is pinned to the Lean version the post is written against."
    toolchain ← ask "Lean toolchain for the example project" repoToolchain
    exampleDir? := some dir

  -- Create everything
  IO.println ""

  if let some dir := exampleDir? then
    IO.FS.createDirAll ⟨s!"examples/{dir}"⟩
    IO.FS.writeFile ⟨s!"examples/{dir}/lean-toolchain"⟩ (toolchain ++ "\n")
    IO.FS.writeFile ⟨s!"examples/{dir}/lakefile.toml"⟩ (exampleLakefile modName (← subversoRevForNewProject))
    IO.FS.writeFile ⟨s!"examples/{dir}/{modName}.lean"⟩ (exampleModuleContent title date)
    IO.println s!"Created examples/{dir}/ (lean-toolchain, lakefile.toml, {modName}.lean)."
    if ← askYesNo "Generate its lake-manifest.json now (runs elan/lake, may download a toolchain)?" true then
      ranLakeUpdate ← runLakeUpdate dir toolchain
      if !ranLakeUpdate then
        IO.eprintln "Warning: lake update failed; run it manually (see next steps)."

  let postPath := s!"Blog/Posts/{modName}.lean"
  IO.FS.writeFile ⟨postPath⟩ (postContent title date authors tags draft exampleDir? modName)
  IO.println s!"Created {postPath}."

  if tagsModified then
    IO.FS.writeFile ⟨"Blog/Tags.lean"⟩ newTagsSrc
    IO.println "Added new tags to Blog/Tags.lean."

  let blogSrc ← IO.FS.readFile ⟨"Blog.lean"⟩
  let blogSrc := if blogSrc.endsWith "\n" then blogSrc else blogSrc ++ "\n"
  IO.FS.writeFile ⟨"Blog.lean"⟩ (blogSrc ++ s!"import Blog.Posts.{modName}\n")
  IO.println s!"Imported Blog.Posts.{modName} in Blog.lean."

  let mut mainSrc ← IO.FS.readFile ⟨"Main.lean"⟩
  let mut manualSteps : List String := []
  match addToSite mainSrc modName with
  | some updated =>
    mainSrc := updated
    IO.println s!"Added Blog.Posts.{modName} to the site definition in Main.lean."
  | none =>
    manualSteps := manualSteps ++
      [s!"add Blog.Posts.{modName} to the \"blog\" ... with block in Main.lean (not found automatically)"]
  if slug != derivedSlug then
    match addSlugOverride mainSrc title slug with
    | some updated =>
      mainSrc := updated
      IO.println s!"Added a postSlugs entry for the custom slug \"{slug}\" to Main.lean."
    | none =>
      manualSteps := manualSteps ++
        [s!"add (\"{title}\", \"{slug}\") to postSlugs in Main.lean (not found automatically)"]
  IO.FS.writeFile ⟨"Main.lean"⟩ mainSrc

  IO.println ""
  IO.println "Done! Next steps:"
  let mut n := 1
  for step in manualSteps do
    IO.println s!"{n}. {step}"
    n := n + 1
  if let some dir := exampleDir? then
    if !ranLakeUpdate then
      IO.println s!"{n}. in examples/{dir}: elan run --install {toolchain} lake update --keep-toolchain"
      IO.println "   (never plain `lake update` — it would overwrite lean-toolchain, see README)"
      n := n + 1
    IO.println s!"{n}. replace the sample anchor in examples/{dir}/{modName}.lean with real code"
    n := n + 1
  IO.println s!"{n}. write the post in {postPath}"
  IO.println s!"{n + 1}. lake exe blog --output _site  # and check the result"
  return 0
