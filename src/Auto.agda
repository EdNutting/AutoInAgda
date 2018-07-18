open import Function     using (const; id)
open import Auto.Core    using (IsHintDB; simpleHintDB; Rules; Rule; name2rule)
open import Data.List    using ([]; [_]; _++_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Reflection   using (Name; Term; TC)
open import Data.Unit    using (⊤)

module Auto where

  open import Auto.Extensible simpleHintDB public renaming (auto to auto')
  open import Reflection

  auto : ℕ → TC HintDB → Term → TC ⊤
  auto depth dbTC hole = bindTC dbTC λ db →
                         bindTC (inferType hole) λ goal →
                         bindTC (auto' (dfs) depth db goal) λ result →
                         unify hole result

  macro
    autoMacro = auto
