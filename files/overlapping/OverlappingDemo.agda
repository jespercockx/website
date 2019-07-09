module OverlappingDemo where

open import Relation.Binary.PropositionalEquality

-- Standard data types Bool and ℕ
data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- The obligatory overlapping definition of plus
overlapping
  _+_ : ℕ → ℕ → ℕ
  zero    + n       = n
  (suc m) + n       = suc (m + n)
  m       + zero    = m
  m       + (suc n) = suc (m + n)
  (suc m) + (suc n) = suc (suc (m + n))


-- For comparison
_+'_ : ℕ → ℕ → ℕ
zero    +' n = n
(suc m) +' n = suc (m +' n)

--  Example how this definition works
+-example : {m n : ℕ} → 
  (m + (zero + (suc n))) + suc zero ≡ suc (suc (m + n))
+-example = refl 

+'-example : {m n : ℕ} → (m +' (zero +' (suc n))) +' suc zero ≡ suc (suc (m +' n))
+'-example = {!!}

-- Overlapping definitions of ∧ and ∨
overlapping
  _∧_ : Bool → Bool → Bool
  x     ∧ false = false
  false ∧ y     = false
  x     ∧ true  = x
  true  ∧ y     = y

  _∨_ : Bool → Bool → Bool
  x ∨ true  = true
  true ∨ y  = true
  x ∨ false = x
  false ∨ y = y

overlapping
  deMorgan₁ : ∀ x y z → x ∧ (y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)
  deMorgan₁ true y z = refl
  deMorgan₁ false y z = refl
  
  deMorgan₂ : ∀ x y z → x ∨ (y ∧ z) ≡ (x ∨ y) ∧ (x ∨ z)
  deMorgan₂ true y z = refl
  deMorgan₂ false y z = refl

-- This definition is translated to a non-equivalent case tree ...
maj₁ : Bool → Bool → Bool → Bool
maj₁ true true true = true
maj₁ x true false = x
maj₁ false y true = y
maj₁ true false z = z
maj₁ false false false = false

-- ... making this lemma unprovable without pattern matching on b
lem₁ : {b : Bool} → maj₁ b true false ≡ b
lem₁ = {!!}

-- This definition is not ...
overlapping
  maj₂ : Bool → Bool → Bool → Bool
  maj₂ true true true = true
  maj₂ x true false = x
  maj₂ false y true = y
  maj₂ true false z = z
  maj₂ false false false = false

-- ... so this lemma is trivial to prove
lem₂ : {b : Bool} → maj₂ b true false ≡ b
lem₂ = λ {b} → refl

-- Vectors are lists indexed on length
data Vec (A : Set) : ℕ → Set where
  ε : Vec A zero
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- Overlapping definition of list concatenation
-- Makes use of the fact that m + 0 reduces to m
overlapping
  _++_ : {A : Set}{m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
  ε ++ w = w
  v ++ ε = v
  (cons a v) ++ w = cons a (v ++ w)

-- This is much easier ...
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero    n = refl
+-comm (suc m) n = cong suc (+-comm m n)

-- ... than before
--  m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
--  m+1+n≡1+m+n zero    n = refl
--  m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

--  +-comm : Commutative _+_
--  +-comm zero    n = sym $ proj₂ +-identity n
--  +-comm (suc m) n =
--    begin
--      suc m + n
--    ≡⟨ refl ⟩
--      suc (m + n)
--    ≡⟨ cong suc (+-comm m n) ⟩
--      suc (n + m)
--    ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
--      n + suc m
--    ∎

interleave : {A : Set} → (m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
interleave .zero    n ε              w = w
interleave .(suc m) n (cons {m} a v) w 
    rewrite (+-comm m n) 
  = cons a (interleave n m w v)

-- Previously, we needed a different version of +

--  _⋎_ : ∀ {a m n} {A : Set a} →
--        Vec A m → Vec A n → Vec A (m +⋎ n)
--  []       ⋎ ys = ys
--  (x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- Some more operations on natural numbers
overlapping
  _-_ : ℕ → ℕ → ℕ
  m     - zero  = m
  zero  - n     = zero
  suc m - suc n = m - n

-lemma : (m n : ℕ) → (m + n) - n ≡ m
-lemma m zero = refl
-lemma m (suc n) = -lemma m n

overlapping
  _*_ : ℕ → ℕ → ℕ
  zero  * n     = zero
  m     * zero  = zero
  suc m * n     = n + (m * n)
  m     * suc n = (m * n) + m
-- Unfortunately, the definition with this last clause is not confluent
-- However, we can prove it correct

+-assoc : (l m n : ℕ) → l + (m + n) ≡ (l + m) + n
+-assoc zero m n = refl
+-assoc (suc l) m n = cong suc (+-assoc l m n)

*-lemma : (m n : ℕ) → m * (suc n) ≡ (m * n) + m
*-lemma zero n = refl
*-lemma (suc m) n rewrite *-lemma m n = cong suc (+-assoc n (m * n) m)

overlapping
  _⊔_ : ℕ → ℕ → ℕ
  zero  ⊔ n     = n
  m     ⊔ zero  = m
  suc m ⊔ suc n = suc (m ⊔ n)

overlapping
  _⊓_ : ℕ → ℕ → ℕ
  zero  ⊓ n     = zero
  m     ⊓ zero  = zero
  suc m ⊓ suc n = suc (m ⊓ n)

-- Transitivity of the propositional equality
≡-trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
≡-trans refl q = q
≡-trans p refl = p

cong' : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong' f refl = refl