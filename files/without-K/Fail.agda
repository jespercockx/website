{-# OPTIONS --without-K #-}

module Fail where

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- Example 1: a direct definition of K by pattern matching (try splitting on e)
K : {A : Set} {x : A} (P : x ≡ x → Set) →
    P refl → (e : x ≡ x) → P e
K P p e = {!!}


-- Example 2: K vs. univalence
coerce : {A B : Set} → A ≡ B → A → B
coerce refl x = x

data Bool : Set where true false : Bool

-- (try splitting on e)
coerce-id : (e : Bool ≡ Bool) → coerce e true ≡ true
coerce-id e = {!!}


-- Example 3: Elimination rule for the heterogeneous equality
data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

-- (try splitting on e)
subst-≅ : {A : Set} {x y : A} (P : A → Set) → x ≅ y → P x → P y
subst-≅ P e p = {!!}


-- Example 4: uniqueness of equality proofs "one level up" (try splitting on e)
weak-K : {A : Set} {a b : A} (p q : a ≡ b) (α β : p ≡ q) → α ≡ β
weak-K refl .refl refl e = {!!}


-- Example 5: the reason why the indices need to be self-unifiable.
-- There is no need for A and a to be postulates for this example:
-- they can be anything as long as they don't contain free variables.
postulate A : Set
postulate a : A

-- Foo is defined such that "Foo e" is equivalent with "refl ≡ e"
data Foo : a ≡ a → Set where
  foo : Foo refl

-- (try splitting on e)
weaker-K : (e : foo ≡ foo) → e ≡ refl
weaker-K e = {!!}
