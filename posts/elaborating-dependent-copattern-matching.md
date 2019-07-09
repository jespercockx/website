---
date: 2018-09-22
title: Elaborating Dependent (Co)pattern Matching
author: Jesper
---

It has been a while since my last (and first) post, so here is a
new one about this year's ICFP paper by Andreas Abel and me, titled
"Elaborating Dependent (Co)pattern Matching"
([pdf](/files/elaborating-dependent-copattern-matching.pdf)). Dependent
pattern matching and copattern matching is one of Agda's coolest
features. It is also a topic very close to my heart since I spend most
of my PhD years on the topic.

My goal in this blog post is not to go into the theoretical details,
you can find those in the paper. Instead, I want to go a bit more into
the reasons why I think this work is important and some unexpected
discoveries I made while working on the paper.

**Prerequisites.** I'll assume you have used a proof assistant with
  dependent pattern matching (such as Agda, Idris, or the Equations
  package for Coq) at least a few times, but I won't assume any
  knowledge about the Agda internals.

## How to trust your type system

When we use a typechecker or a proof assistant, it is fundamentally
because we don't trust ourselves enough (or we can't be bothered to)
to check whether all the details of a program or proof make sense.
Their usefulness thus depends directly on our ability to trust them.
But why do we believe we can in fact trust them: is it based on
**science** or on **faith**? I claim that currently, we are somewhere
in between these two. Let me explain why.

A typical dependently typed programming language / proof assistant (be
it Agda, Coq, Idris, or even Haskell) actually consists of two
languages: a high-level *surface language* and a lower-level *core
language*. The surface language usually has many convenience features
such as implicit arguments, named variables, pattern matching, a
tactic system, etc. On the other hand, the core language has none of
these and is kept as small as possible on purpose. These core
languages have often been studied in great detail for decades and
(while there are still many new discoveries to be made) they lie
firmly in the camp of **science**.

The process of translating from surface to core language is called
*elaboration*. It includes many steps such as scope checking, type
checking, higher-order unification for checking constraints and
figuring out implicit arguments, and running tactics. The goals of
elaboration are twofold:

1. to *check* that the user-written code (in the surface language) is
   correct, and

2. to *generate* the low-level program (in the core language) which
   can then be executed (if you are in the business of running your
   programs, that is).

In Agda, currently only a very small part of the core language can be
typechecked independently, so we need to trust the elaboration
process. This elaboration is a big, ugly mess of semi-imperative
Haskell code with lots of unsafe features and no real
specification. This is clearly not based on any rational science, only
**faith** enables us to use Agda while keeping our sanity.

In other languages---such as Coq---the generated core can be checked
independently, and in fact it *is* checked at every `qed` and
`defined`. So should Agda follow Coq and get a proper core language?
While I think this is a good idea (our paper actually takes a step in
that direction), I don't think that's *enough*.

Suppose in extremis that the elaborator would translate every type to
the unit type `⊤`, and every term to the trivial proof `tt`. Then all
the generated code is certainly type-correct, but it is as certainly
not what we want! Of course, in reality mistakes in the elaboration
process are never this blatant, but they still happen and may result
in type-correct yet meaningless code being generated.  The message is
thus:

  *Even with a trusted core language and double-checking of all
  generated code, the elaborator is still part of the trusted kernel!*

(If you're using Coq or Agda just as a theorem prover and you don't
care about the actual proof term, you still have to trust the
elaborator to preserve the meaning of the *theorem statement*, which
can be a complex expression itself).

So if we must rely on the correctness of elaboration, what can we do
to increase our trust in it? Well, eat our own dogfood and formally
verify it of course. Unfortunately, the current state of Agda is
pretty far from the point where it would be feasible to verify
anything about it (remember it doesn't even have a proper core
language?). So the first step will be more modest: take a small part
of the elaboration process, specify what properties it ought to have,
and prove that they are indeed satisfied by this small part.


## Elaborating pattern matching

Let's get to the actual topic of the paper: dependent pattern
matching. Dependent pattern matching provides a very convenient syntax
for defining new functions (and, through the Curry-Howard
correspondence, proofs) by case analysis and recursion. A big part of
the power of dependent pattern matching comes from the unification
algorithm it employs for specializing types to each specific case and
to rule out impossible cases. This unification algorithm was the main
topic of my PhD thesis, but here I want to talk about a different aspect.

Pattern matching is one of these features that are present in the
surface language but are translated away by elaboration. In
particular, the elaboration of a function by dependent pattern
matching proceeds in two steps: first, the clauses written by the user
are translated to a *case tree*, and then this case tree can be
further translated to the *primitive eliminators* provided by the core
language (for example CIC for Coq). Agda skips the second step and
uses case trees directly in its internal language instead.

The second step of this translation has been studied extensively in
the past: by Conor McBride, Healfdene Goguen and James McKinna for a
type theory with UIP (uniqueness of identity proofs) and by me and
Dominique Devriese in the general case. On the other hand, no-one ever
really formalized or proved anything about the first step. You guessed
it: that's exactly what we do in our new paper.

In order to prove anything about the elaboration process, we need to
formalize it in much greater detail than is usually done. Finding the
right judgement forms was actually the main challenge when writing the
paper; once we got them right most of the proofs followed naturally!
At the same time, having a very precise description of the elaboration
process helps a lot when actually implementing the algorithm for
Agda. So formalizing elaboration is a big win from both the
theoretical and the practical side of things!

For example, to prove that the case trees produced by elaboration are
well-typed, it is necessary to have typing rules for case trees in the
first place. However, this is not the case for the case trees
currently used internally by Agda! In fact, they do not contain
sufficient information to check them independently, which is one of
the major obstacles preventing us from having a proper core language
for Agda.  In the future, I would like to refactor the representation
of case trees in Agda to be closer to the well-typed case trees in our
paper.

## First-match semantics and the shortcut rule

An important goal in our paper is to prove that elaborating a
definition by pattern matching preserves the *meaning* of the
definition. In particular, if the arguments to the function match a
certain clause, and they didn't match any of the previous clauses,
then this clause should fire -- this is the so-called *first-match
semantics* of pattern matching. In our paper, prove that our
elaboration process preserves the first-match semantics of the clauses
written by the user.

In a dependently typed language, we expect stronger properties from
our programs than usual, in particular w.r.t. evaluation of open terms
(i.e. terms with free variables). This poses interesting new questions
when proving properties that involve evaluation. For example, consider
Berry's infamous `majority` function:

```agda
majority : Bool → Bool → Bool → Bool
majority true  true  true  = true
majority x     true  false = x
majority false y     true  = y
majority true  false z     = z
majority false false false = false
```

When evaluating `majority x true false`, can we safely skip the first
clause and apply the second clause to conclude `majority x true false
= x`? This so-called *shortcut rule* allows matching to proceed to the
next clause when there's a mismatch for one argument (in this case the
third) even when matching for another argument (here the first) is
still inconclusive.

However, it turns out this rule is not allowed if we want to preserve
the first-match semantics in the translation to a case tree! For
example, the obvious case tree for `majority` matches first on the
first argument, which means `majority x true false` is a stuck term
that does not evaluate to anything.

A more restricted version of the shortcut rule is *left-to-right
matching*, where the arguments are matched (you'd never guess) from
left to right, and a mismatch means going to the next clause
immediately. This semantics adequately describes the behaviour of the
case tree for `majority` and is the one that was (until recently)
the one implemented in Agda.

But this restricted shortcut rule is *also* not preserved by the
elaboration to a case tree.  Here is an example for which the *only*
valid case tree does not satisfy the first-match semantics with
left-to-right matching:

```agda
f : (A : Set) → A → (A ≡ Bool) → Bool
f .Bool true refl = true
f _     _    _    = false
```

The function matches on both its second and third argument, but in a
well-typed case tree the match on the third argument has to come
before the second. Hence `f Bool false p` for a variable `p` does not
evaluate to `false` but is stuck.

This actually caused a bug in Agda which allowed us to break subject
reduction (see [#2964](https://github.com/agda/agda/issues/2964)). I
only discovered this bug because I was writing the proof of
preservation of first-match semantics and failed to make it work!
Once we found the error, the problem was easy to fix by removing the
shortcut rule in all forms.

In effect, our theorem says that the first-match semantics (without
the shortcut rule) give a *lower bound* to the computational behaviour
of any case tree produced by elaboration: the case has at least this
computational behaviour, and possibly some more depending on the order
of case splits. On the other hand, we could also give an *upper bound*
to the computational behaviour of any case tree, in the form of some
*any-match* semantics. The definition of any-match semantics and the
proof that it is an upper bound is left as an exercise to the reader
;)


## Conclusion

This post is getting pretty long so I'm going to stop here. If you
cannot get enough, you're in luck since there's a whole
[paper](/files/elaborating-dependent-copattern-matching.pdf) for you!
One thing that's in the paper but I didn't talk about here at all is
*copattern matching*, as indicated by the `(co)' in the paper
title. Copatterns are very cool so maybe I'll write something about
them here later.

As always, if you have any questions or comments about this post, let
me know on the Agda mailing list. See you next time, where I'll
hopefully talk about one of Agda's most unsafe features: user-defined
rewrite rules!





