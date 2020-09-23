# A medium for knowledge management and transfer (HTML5/JS/CSS only)

*The ability to "write" in a medium means you can _generate_ materials and tools for others. [...] In print writing, the materials and tools you generate are rhetorical; they demonstrate and convince. In computer writing, the tools you generate are processes; they simulate and decide.* -- Alan Kay in [User Interface: A Personal View (page 5)](https://numinous.productions/ttft/assets/Kay1989.pdf)

Crosscutt is the software that powers my personal blog. Here are the key facts you should know.

* It is in a very early stage.
* It runs on every server that is capable of serving static files.
* It requires client-side JavaScript.
* Articles are written using a special Markdown dialect.
* KaTeX formulas are supported.
* The blog comes with an integrated EPUB viewer and you can create deep links to every sentence in your E-Books (respect the copyright of the books, though).
* Each blog article is supposed to be an interactive tool. For example, it is possible to create collapsible sections.

## Getting Started

To use this software, you will need Node.js and a Node.js package manager. I use [Yarn](https://yarnpkg.com/) but it should be possible to use NPM, too.

Open a terminal and execute:
```sh
git clone https://github.com/datokrat/crosscutt.git
cd crosscutt
yarn
```

You can build your blog using
```sh
yarn build
```

## Creating Content

Please take a look at the file  [`data-seed.js`](./src/data-seed.js). Write your articles into an `article-*.txt` file and `import` it at the beginning of `data-seed.js`. Then add a new `Article` object to the list of articles.

It is also possible to include resources/"references" such as EPUB files. These may be added as `EpubReference` objects to the list of `references` and will be available under the URL `[root]/?reference/[ID of reference]`.

### Markdown features

Crosscutt Markdown currently supports five features: paragraphs, links, headings and collapsible sections.

#### Paragraphs

You can split your article into paragraphs using empty lines.

```
This is paragraph 1.

This is paragraph 2.
```

#### Links

You can create links whose target is either a URL or a reference (e.g., an `EpubReference`).

```
You can create links whose target is either a [[URL|https://example.org]] or a [[reference|reference:some reference ID]].
```

In the above example, the second link refers to the resource with ID `some refereqnce ID`.

#### Headings

As of today, there is only one type of heading. You can create headings between paragraphs using `# ` at the beginning of a line.

```
# Heading

Some paragraph under a heading
```

#### KaTeX Math Formulas

Delimit your inline formulas with `$` and your block formulas with `$$`.

```
If the group finite $G$ operates on the set finite set $M$, we can relate the cardinality of $M$ with the sizes of its orbits unter $G$ by
$$ \# G = \sum_{r \in R} \# ( G \bullet r ), $$
where $R$ is a system of representants of the orbits unter $G$.
```

##### Collapsible Sections

If you want some section of your article to be collapsible or exandible on demand, indent all of its lines (also empty lines!) using four spaces `    ` and precede it with a section header
```^ 
_ name of the section
```
if the section should be collapsed per default or
```
^ name of the section
```
if the section should be expanded per default.

There is a special type of link that can be used to toggle the visibility of a section. Here is a full example:
```
Please [[expand the following section|toggle:example section]] to read along.

_ example section
    Great! Now you know how collapsible sections work.
```

## Debugging

After installing the package `http-server` using
```
yarn global add http-server
```
you can execute
```
yarn run debug
```
from the root directory of the project to build the blog and serve all files from the `dist/` directory for debugging purposes.

## Deploying

After building the blog, just copy the `dist/` directory to your server.

## Vim Support

I use Vim for the development. My setup is based on [this great tutorial](https://freshman.tech/vim-javascript/). The most important plugin is ALE because it automatically gives me feedback regarding the style and formatting of my code and automatically fixes the formatting using `:ALEFix`.

In my `vimrc` file, I added some special key mappings for this repo. Those are:
```
function! SetupEnvironment()
  if filereadable(".vimsettings")
    if readfile(".vimsettings")[0] == "build=yarn-run"
      nnoremap <Leader>x :w<CR> :!yarn run debug<CR>
      nnoremap <Leader>f :ALEFix<CR>
    endif
  endif
endfunction

call SetupEnvironment()
```
They allow me to fix the formatting using `\f` and start the debug server using `\x` (in normal mode).

