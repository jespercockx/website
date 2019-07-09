---
date: 2019-07-09
title: Writing Agda blog posts in literate markdown
author: Jesper
---

So you got to admit all the cool kids are doing it nowadays: writing
blog posts in literate Agda. Do you want to join the club? Then you've
come to the right place! In this blog post I'll explain how to write a
blog post (or any literate Agda code, really) as a markdown file and
transform it into fancy highlighted and hyperlinked html. Don't worry,
it's easy!

```
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

plus1 : (x : Nat) → x + 1 ≡ suc x
plus1 zero                    = refl
plus1 (suc x) rewrite plus1 x = refl
```

# Writing the blog post

To start, you'll first need to install Agda 2.6.0 or newer and Pandoc
2.2 or newer. Both can be installed from Cabal with `cabal install
agda-2.6.0.1 pandoc-2.2.1` (these versions work well with GHC 8.0,
YMMV).

Next, create a file called `blogpost.lagda.md` and open it up in
Emacs. Here, you write your text using standard [markdown
syntax](https://daringfireball.net/projects/markdown/basics). Any Agda
code goes between triple backticks:

<pre><code>&#96;&#96;&#96;
-- write your Agda code here
&#96;&#96;&#96;</code></pre>

Bonus trick: to hide an Agda code block, just put it between html
comments (<&excl;&dash;&dash; and &dash;&dash;>).

You'll notice that the agda2-mode for emacs is not automatically
loaded when editing `.lagda.md` files. You can either load it manually
(using `M-x agda2-mode`) or fix the problem once and for all by adding
this line to your `.emacs` configuration:

```elisp
(add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))
```

# From markdown to html

Once you are finished with writing your blog post, first use Agda to
convert the code parts to html:

```bash
agda --html --html-highlight=code blogpost.lagda.md
```

Here, the `--html` flag tells Agda to generate html from the file, and
`--html-highlight=code` tells Agda not to touch the non-code parts of
the file (these will be processed by Pandoc). You should now have a
new directory called `html` containing the following:

- A file `blogpost.md`
- `.html` files for all the imported modules
- A css stylesheet `Agda.css`

To complete the process, run Pandoc on the `.md` file like so:

```bash
pandoc html/blogpost.md -o blogpost.html
```

This tells Pandoc to convert the markdown file to html (it won't touch
the code since that's already been converted by Agda).

If you want, you can go wild with any [Pandoc
extensions](https://pandoc.org/MANUAL.html#pandocs-markdown) you want
to use. Personally, I'm just using `tex_math_dollars`,
`tex_math_double_backslash` and `latex_macros` (for using LaTeX
commands in text).

# Integrating with Hakyll

Since I'm building my website with
[Hakyll](https://jaspervdj.be/hakyll/), I tried to integrate Agda into
the Hakyll pipeline. Unfortunately, this did not go quite as smoothly
as I expected: Hakyll is built around the paradigm of mapping one
input file to one output file, but this does not match with how
`agda --html` generates its output. For more details on the problem I
had, see [this
post](https://groups.google.com/forum/#!topic/hakyll/fLakSephFQ0).

Instead, I currently run `agda --html` on all Agda blog posts as a
preprocessing step to Hakyll. This does not work quite as seamlessly
as I hoped since Hakyll does not automatically detect changes when
running in `watch` mode, but it gets the job done. If you are also
running Hakyll and you want to steal my method, feel free to take a
look at it
[here](https://github.com/jespercockx/website/blob/master/site.hs). Also,
if you know of a better method please let me know!

I hope you enjoyed this blogpost about the *making of* this blog, next
time I will finally talk about the long-awaited topic of rewrite rules
in Agda (I promise!)
