open import Basics


data Flavour : Type where
  chocolaty : Flavour
  cheesy    : Flavour

data Food : Type where
  moelleux : Food
  pizza    : Food
  sandwich : Food

flavour : Food → Flavour
flavour moelleux = chocolaty
flavour pizza = cheesy
flavour sandwich = cheesy



data Ingredient : Type where
  chocolate : Ingredient
  cheese    : Ingredient
  butter    : Ingredient
  eggs      : Ingredient
  flour     : Ingredient
  sugar     : Ingredient
  tomato    : Ingredient
  bread     : Ingredient

ingredients : Food → List Ingredient

ingredients moelleux =
  chocolate ∷
  butter    ∷
  flour     ∷
  eggs      ∷
  sugar     ∷ []

ingredients sandwich =
  bread      ∷
  {!cheese!}      ∷ []

ingredients pizza =
  flour     ∷
  tomato    ∷
  cheese    ∷
  chocolate ∷ []
