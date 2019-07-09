{-# OPTIONS --without-K #-}

module Examples where

-- Propositional equality
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- Transitivity
trans : {A : Set} (x y z : A) →
        x ≡ y → y ≡ z → x ≡ z
trans x .x .x refl refl = refl

-- Congruence
cong : {A B : Set} (f : A → B) → 
       {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  lz : (n : ℕ) → zero ≤ n
  ls : (m n : ℕ) → m ≤ n → suc m ≤ suc n

-- Antisymmetry of ≤ 
≤-antisym : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-antisym .zero    .zero    (lz .zero) (lz .zero)   = refl
≤-antisym .(suc m) .(suc n) (ls m n p) (ls .n .m q) = 
            cong suc (≤-antisym m n p q)

-- The standard J-eliminator for the propositional equality
J : ∀ {a} {A : Set a} {x : A} (P : (y : A) → x ≡ y → Set) →
    P x refl → {y : A} (e : x ≡ y) → P y e
J P p refl = p

data ⊤ : Set where tt : ⊤

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- This definition is not accepted by the default --without-K flag
≤-self : (m : ℕ) → m ≤ m → ⊤
≤-self .zero (lz .zero) = tt
≤-self .(suc m) (ls m .m p) = tt

-- This definition is accepted by --without-K ...
sum-left : (k l m : ℕ) → (k + l) ≡ m → ⊤
sum-left k l .(k + l) refl = tt

-- ... but this one isn't.
sum-right : (k l m : ℕ) → k ≡ (l + m) → ⊤
sum-right .(l + m) l m refl = tt

data Box (A : Set) : Set where
  [_] : A → Box A

-- This definition is also rejected by --without-K
box-injective : {A : Set} (x y : A) → [ x ] ≡ [ y ] → x ≡ y
box-injective x .x refl = refl

-- Desugaring the definition of ≤-antisym
module Desugaring where

  subst : ∀ {a} {A : Set a} {x : A} (P : A → Set) →
          {y : A} → x ≡ y → P x → P y
  subst P e p = J (λ y _ → P y) p e

  data ⊥ : Set where

  ⊥-elim : (A : Set) → ⊥ → A
  ⊥-elim A ()

  ℕ-elim : ∀ {p} (P : ℕ → Set p) 
           (mz : P zero) (ms : (n : ℕ) → P n → P (suc n)) → 
           (n : ℕ) → P n
  ℕ-elim P mz ms zero = mz
  ℕ-elim P mz ms (suc n) = ms n (ℕ-elim P mz ms n)

  ℕ-NoConf : ℕ → ℕ → Set
  ℕ-NoConf = ℕ-elim 
               (λ _ → ℕ → Set) 
               (ℕ-elim (λ _ → Set) ⊤ (λ _ _ → ⊥)) 
               (λ m _ → ℕ-elim (λ _ → Set) ⊥ (λ n _ → m ≡ n))

  ℕ-noConf : (m n : ℕ) → m ≡ n → ℕ-NoConf m n
  ℕ-noConf = λ m n → J 
               (λ n _ → ℕ-NoConf m n) 
               (ℕ-elim (λ m → ℕ-NoConf m m) tt (λ m _ → refl) m)

  ≤-elim : (P : (m n : ℕ) → m ≤ n → Set) → 
           (mz : (n : ℕ) → P zero n (lz n)) → 
           (ms : (m n : ℕ) (e : m ≤ n) → 
                 P m n e → P (suc m) (suc n) (ls m n e)) →
           (m n : ℕ) (e : m ≤ n) → P m n e
  ≤-elim P mz ms .zero n (lz .n) = mz n
  ≤-elim P mz ms .(suc m) .(suc n) (ls m n e) = ms m n e (≤-elim P mz ms m n e)

  ≤-antisym' : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
  ≤-antisym' = ≤-elim -- Case split on proof of m ≤ n
    (λ m n _ → n ≤ m → m ≡ n)
    -- Case 1: zero = m, zero ≤ n
    (λ n e → ≤-elim -- Case split on proof of n ≤ zero
      (λ n m _ → m ≡ zero → m ≡ n) 
      -- Case 1.1: zero = n, zero ≤ zero 
      (λ n e → e)
      -- Case 1.2: suc k = n, suc l = zero, k ≤ l 
      (λ k l _ _ e → ⊥-elim -- Absurdity: suc l = zero
        (suc l ≡ suc k) 
        (ℕ-noConf (suc l) zero e)) -- suc l = zero → ⊥
      n zero e refl)
    -- Case 2: suc m' = m, suc n' = n, m' ≤ n'
    (λ m n _ H q → cong suc
      (H -- Recursive call to prove m' ≡ n'
        (≤-elim -- suc n' ≤ suc m' → n' ≤ m'
          (λ k l _ → k ≡ suc n → l ≡ suc m → n ≤ m)
          -- Case 2.1: suc n' = zero, zero ≤ suc m'
          (λ _ e _ → ⊥-elim -- Absurdity: zero = suc n'
            (n ≤ m)
            (ℕ-noConf zero (suc n) e)) -- suc n' = zero → ⊥
          -- Case 2.2: suc k = suc n', suc l = suc m', k ≤ l
          (λ k l e _ p q → subst -- Substitute k for n' 
            (λ n → n ≤ m)
            (ℕ-noConf (suc k) (suc n) p) -- suc k = suc n' → k = n'
            (subst -- Substitute l for m'
              (λ m → k ≤ m) 
              (ℕ-noConf (suc l) (suc m) q) -- suc l = suc m' → l = m'
              e))
          (suc n) (suc m) q refl refl)))
