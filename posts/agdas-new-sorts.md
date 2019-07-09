---
date: 2018-05-03
title: The Agda's New Sorts
author: Jesper
---

In the last few weeks, Sandro Stucki has given a couple of excellent presentations on pure type systems (pts's) at the [initial types club](https://github.com/InitialTypes/Club) at Chalmers. Since I've been working on the implementation of Agda's sorts system, and the new implementation is closely based on the theory of pure type systems, I thought it would be interesting to talk a bit about the implementation of these concepts used by Agda. 

**Prerequisites**: a bit of experience with using Agda, basic knowledge of pure type systems (see section 5.2 of [Barendregt's classic](https://www.dropbox.com/s/pwg069e0lomhzie/Barendregt92_-_Lambda_Calculi_with_Types.pdf?dl=0)).

Note: this post started as my personal notes to prepare for a talk at the initial types club, but then I realized it could make a nice blog post. Since this is kind of an experiment, please let me know if there's something I can improve or if you're just eager to have more posts about the development of Agda!

Agda's universe hierarchy
-----------------
Sorts (aka universes) are types whose members themselves are again types. They are a central element of Martin-Löf's type theory and languages based on that theory, such as Agda. The prototypical example of a sort in Agda is `Set`, the universe of small types. Why do we need any sort other than `Set`, you ask? Well, to avoid inconsistency and undecidable typechecking we cannot have `Set : Set` (known as the **type-in-type** rule): Martin-Löf's original type theory had a rule like this, but Girard showed that this is inconsistent (this is called Girard's paradox). While Girard's original paradox is quite complex, it's easier to get a contradiction in Agda by (ab)using datatypes and structural recursion (example taken from a [post by Andreas Abel](https://lists.chalmers.se/pipermail/agda/2017/009337.html) on the Agda mailing list):

    {-# OPTIONS --type-in-type #-}

    data ⊥ : Set where

    data D : Set where
      c : (f : (A : Set) → A → A) → D

    empty : D → ⊥
    empty (c f) = empty (f D (c f))

    absurd : ⊥
    absurd = empty (c λ A x → x)

See also [this post by Liam O'Connor](http://liamoc.net/posts/2015-09-10-girards-paradox.html) for a direct encoding of a similar inconsistency with type-in-type, Russell's paradox (aka the Barber's paradox).

To avoid these inconsistencies, Agda has an infinite hierarchy of sorts `Set0` (= `Set`), `Set1`, `Set2`, ... such that `Set0 : Set1`, `Set1 : Set2`, ... Thus if we restrict Agda's type system to just the sorts `SetN` and dependent function types `(x : A) → B`, we can think of it as a pure type system with the sorts given by natural numbers, axioms `(n, n+1)` and rules `(m, n, m ⊔ n)` (where `⊔` indicates the maximum). Unlike Coq, Agda has *no* cumulativity, so we have `Set0 : Set1` and `Set1 : Set2` but not `Set0 : Set2`. I'll come back to the point of cumulativity at the end of this post.

Universe polymorphism
---------------------
In practice, of course, things aren't that simple. It turns out that defining the same functions and datatypes at different universe levels gets really old really quickly. To fix this, Agda has a feature called *universe polymorphism*. This feature exposes a new type `Level : Set` to the user, as well as primitive functions on levels `lzero : Level`, `lsuc  : Level → Level`, and `_⊔_ : Level → Level → Level`. For each `l : Level` we get a new universe `Set l`, with the obvious rules (`Set lzero = Set0`, `Set (lsuc lzero) = Set1`, ...) This allows us to define functions and datatypes for all universe levels at once, e.g. the polymorphic identity function:

    id : (l : Level)(A : Set l)(x : A) → A
    id l A x = x

This seems like a useful yet unexciting feature and indeed, if you've ever seen some non-trivial Agda code you have probably encountered it already. However, it has some big implications for Agda as a pure type system: it means that the *sort* of the codomain of a function type can now also depend on the *value* of the argument. This definitely does not fit into the framework of pure type systems anymore, so we're entering uncharted lands. It also raises a number of practical questions about Agda's sort system, such as:

- Levels are now no longer just natural numbers but they can be arbitrary *terms*, in particular a level can be neutral (i.e. contain free variables). So how do we determine when two levels are equal?
- The type of `id` is `(l : Level) (A : Set l) (x : A) → A`, but what is the sort of this type?

To answer the former question, Agda has a special-purpose solver to solve equalities and inequalities between arbitrary expressions of type `Level`, but I won't say more about it here. The second question is what interests us here: since the sort of this type cannot be `Set l` for any level `l`, Agda introduces a new sort `Setω` which is different from any `Set l`, and it tells us that `(l : Level) (A : Set l) (x : A) → A : Setω`. So `Setω` can be thought of as a sort that's bigger than `Set l` for any level `l`.

To extend the theory of pure type systems to universe polymorphism, we now need to consider 'dependent pts rules' of the form `(x : _ : s1, s2, s3)` where `s2` can depend on the variable `x`. We do not care about the type of `x`, but only about the fact that this type should be in `s1`. Concretely, the new dependent pts rule for `Setω` is  `(x : _ : s , s' , Setω)` whenever `s'` is dependent on `x`. On the other hand, when `s'` is not dependent on `x` we fall back to the regular 'non-dependent' pts rules.

Beyond the universe hierarchy
-------------------------------------------------

By introducing universe polymorphism, we also have a first example of a sort which is not in the universe hierarchy of `Set l`: `Setω`. It turns out that considering sorts different from any `Set l` can actually be very useful: we can encode some additional properties of a type in its sort, or we can restrict what the user is allowed to do with types of a certain sort by restricting the pts rules. Here are a few examples which I think would be very nice to have in Agda:

- We could add a `Prop` sort to Agda which consists of *definitionally proof-irrelevant* types (in contrast to `Prop` in Coq, which is at best propositionally proof-irrelevant). See [PropRezz.agda](https://gist.githubusercontent.com/jespercockx/d7e0885f2078e0c0a54de99117226ac4/raw/da623c143c8922a8459ba136075e6be506b6ba28/PropRezz.agda) for a quick demo of the possibilities.
- Sized types make use of a type `Size` to prove termination in a modular way, but there are some operations that are not permitted on function types ending in `Size`. These properties can be enforced by giving `Size` its own universe `SizeUniv`.
- We could have a new option `--omega-in-omega` which makes Agda inconsistent by adding the axiom `Setω : Setω`, similar to `--type-in-type` but without collapsing the whole universe hierarchy. This should make it easier to do some 'unsafe' things which require `--type-in-type` without destroying compatibility with standard universe-polymorphic Agda code.
- Similarly to `Prop`, we could also add a universe `SSet` of *strict sets*, i.e. types for which the identity type is a `Prop`. In particular, these types should satisfy the definitional `K` rule stating that any proof of `x ≡ x` is *definitionally* equal to `refl`.
- Finally (and most ambitiously) it would be very interesting to add a sort of *non-fibrant types* to make Agda into a two-level type theory like Voevodsky's Homotopy Type System (HTS). The basic idea is that the non-fibrant types serve as an internalization of the metatheory of the fibrant types, which allows us to do all kinds of crazy meta-level things in the language itself. In particular, the first level may satisfy univalence and the second level may satisfy UIP; by separating the sorts we can make sure that this doesn't lead to inconsistencies. You can read more about two-level type systems in [Formalisations Using Two-Level Type Theory](https://hott-uf.github.io/2017/abstracts/twoleveltt.pdf) by Danil Annenkov, Paolo Capriotti, and Nicolai Kraus.

Making room in Agda's architecture for all of these new sorts was the main motivation for me to start working on a new implementation of Agda's sort system.

Meta levels and meta sorts
-------------------------------------------
When typechecking an Agda program, we frequently have to check that some expression is a valid type without knowing what sort it has. Up until recently, Agda always assumed that any unknown sort was of the form `Set _l` for some metavariable `_l : Level`. You may have noticed that `Setω` is already not of this form, so there used to be some hacks to make this assumption work anyway (specifically, the metavariable `_l` was instantiated with the ill-typed solution `Setω` and there was a computation rule `Set Setω ---> Setω`. It was horrible.) 

To get rid of this assumption that any sort is of the form `Set _`, I added a new constructor to Agda's internal representation of sorts for a sort metavariable or **sort meta** for short, representing an as of yet unknown sort. These sort metas can then be solved by the constraint solver just like regular (term) metas. Nice and tidy.

However, there's a complication: we often have to determine the sort of a function type with domain in sort `s1` and codomain in sort `s2`, when `s1` and/or `s2` are still unknown. For example, what's the sort of `(l : Level) → Set (_1 l)` where `_1` is a metavariable of type `Level → Level`? It could be e.g. `Setω` if `_1` is the identity function, or `Set` if `_1` is the constant function `lzero`. Similarly, we may want to get the sort 'one level up' from a given sort `s`, but `s` is still unknown. Introducing more new sort metas in those cases is not ideal, as we actually use those operations **a lot**, so we would get insane numbers of metavariables. Also, it would be quite tricky to keep track of all the dependencies between the different sort metas.

Instead, I opted to introduce two extra constructors `PiSort s1 s2` and `UnivSort s` for the sort of a function type and the sort of another sort respectively (for the connoisseurs: `PiSort` is similar to the old `DLub` sort). These constructors do not represent new sorts but instead they *compute* to the right sort once their arguments are known. For example, `PiSort Level (\l. Set l)` evaluates to `Setω`, `PiSort (Set l) (\_. Set l')` evaluates to `Set (l ⊔ l')` and `UnivSort (Set l)` evaluates to `Set (lsuc l)`. Not every `PiSort` or `UnivSort` is well-defined, for example `Setω` does not have a `UnivSort` since there is no bigger sort than `Setω`. So the `PiSort` and `UnivSort` constructors are accompanied by two new *constraints* `HasBiggerSort s` and `HasPTSRule s1 s2`. Constraints are Agda's way of handling postponement of certain problems, such as the `ValueCmp` constraint which enforces two terms are equal. These two new constraints in particular ensure that no occurrence of `PiSort` or `UnivSort` will be stuck forever but each will compute to a proper sort eventually (or else Agda will report 'unsolved constraints').

So that's it: the design of Agda's new sort system. It has already been merged into the main Agda repository, so if you are still hungry for more details you can take a look there. Specifically:

- [Agda.Syntax.Internal](https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Internal.hs#L212): the Sort datatype used for the internal representation of sorts
- [Agda.TypeChecking.Substitute](https://github.com/agda/agda/blob/dbcee417486f52bd6e17315e15cbb26b17e485e4/src/full/Agda/TypeChecking/Substitute.hs#L1212): basic functions defining the axioms and rules of Agda's pts
- [Agda.TypeChecking.Conversion](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Conversion.hs#L1095): solving equalities and inequalities between sorts
- [Agda.TypeChecking.Monad.Base](https://github.com/agda/agda/blob/dbcee417486f52bd6e17315e15cbb26b17e485e4/src/full/Agda/TypeChecking/Monad/Base.hs#L793): two new constraints `HasBiggerSort` and `HasPTSRule` were added to the `Constraint` datatype
- [Agda.TypeChecking.Sort](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Sort.hs): functions for solving these constraints

At the moment I'm working on implementing `Prop` for Agda and hopefully more new sorts will follow after that, so stay tuned!

Towards cumulativity for Agda?
---------------------------------------------------
One of the most requested features for Agda is cumulativity, i.e. the subtyping rule `Set i <: Set j` for `i < j`, so it would be amiss to talk about sorts in Agda without mentioning it. And indeed, there are many cases where cumulativity would make writing Agda code a lot easier and less frustrating! However, as far as I can tell no-one has really figured out how to combine Agda-style universe polymorphism with cumulativity, so it is still an open problem.

The closest working example is Coq, which sports both a cumulative hierarchy of universes and universe polymorphism (see [this paper by Matthieu Sozeau and Nicolas Tabareau](https://www.irif.fr/~sozeau/research/publications/Universe_Polymorphism_in_Coq.pdf)). But there are some limitations compared to what we would want to have in Agda:

- Coq only allows top-level definitions to be quantified over levels, and thus it doesn't require a sort like `Setω`. But in Agda we can quantify over universe-polymorphic types which are in `Setω`! See [this code by Nils Anders Danielsson](http://www.cse.chalmers.se/~nad/listings/equality/Equality.html#3238) for an example where this is actually used.
- Coq doesn't guarantee the uniqueness of metavariable solutions, but this uniqueness is a core design principle of Agda. So we expect that simply adding cumulativity to Agda will result in lots and lots of unsolved metavariables, unless we have some way to mitigate this.

While my refactoring of the sort system certainly does not enable cumulativity directly, it allows for some new possibilities to experiment with. I'm planning to do some of this experimentation during the next [Agda meeting in Göteborg](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.AIMXXVII) 4 -- 9 June 2018. So if you're interested to work on this (or on any other part of Agda) you are very welcome to come and join us!