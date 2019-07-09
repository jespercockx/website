open import Basics


data Flavour : Type where
  chocolaty : Flavour
  cheesy    : Flavour

data _Food : Flavour → Type where
  moelleux  : chocolaty Food
  pizza     : cheesy Food
  _sandwich : ∀ (x : Flavour) → x Food



data _Ingredient : Flavour → Type where
  chocolate : chocolaty Ingredient
  cheese    : cheesy Ingredient
  butter    : chocolaty Ingredient
  eggs      : ∀ {x : Flavour}
            → x Ingredient
  flour     : ∀ {x : Flavour}
            → x Ingredient
  sugar     : chocolaty Ingredient
  tomato    : cheesy Ingredient
  bread     : ∀ {x : Flavour}
            → x Ingredient


ingredients : {x : Flavour} →
  x Food → List (x Ingredient)

ingredients moelleux =
  chocolate ∷
  butter    ∷
  flour     ∷
  eggs      ∷
  sugar     ∷ []

ingredients pizza =
  flour     ∷
  tomato    ∷
  cheese    ∷
  {!!}      ∷ []

ingredients (chocolaty sandwich)  =
  bread     ∷
  chocolate ∷ []

ingredients (cheesy sandwich) =
  bread     ∷
  cheese    ∷ []


amount-of-cheese :
  cheesy Food → Amount

amount-of-cheese x = {!!}
