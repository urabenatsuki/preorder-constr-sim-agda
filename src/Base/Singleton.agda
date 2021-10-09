module Base.Singleton where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Level using (Level)

----------------------------------------------------------------------
-- simple `inspect` to be used with `case_of_`
--
-- cf. https://agda.readthedocs.io/en/v2.6.0.1/language/with-abstraction.html#the-inspect-idiom

data Singleton {a : Level} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect' : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect' x = x with≡ refl
