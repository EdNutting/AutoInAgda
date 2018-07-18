module Auto.Show where
  open import Agda.Builtin.String public
  open import Agda.Builtin.Word public
  open import Agda.Builtin.Float public
  open import Agda.Builtin.Reflection public
  
  open import Level using (Level) public
  open import Function public
  open import Data.Unit using (⊤) public
  open import Data.Nat renaming (ℕ to Nat; _≟_ to _≟ₙ_ ) public
  open import Data.Nat.Show renaming (show to showN) public
  open import Data.List public

  infixr 4 _#_
  _#_ : String → String → String
  _#_ = primStringAppend

  private
    showT : Term → String

  record Show {a} (A : Set a) : Set a where
    field
      show : A → String
  open Show {{...}} public

  instance
    ShowList : ∀ {a} {A : Set a} {{_ : Show A}} → Show (List A)
    show ⦃ ShowList ⦄ [] = "[]"
    show ⦃ ShowList ⦄ (x ∷ l) = (show x) # " :: " # (show l)

  instance
    ShowNat : Show Nat
    show ⦃ ShowNat ⦄ = showN

  instance
    ShowRelevance : Show Relevance
    show ⦃ ShowRelevance ⦄ relevant = "relevant"
    show ⦃ ShowRelevance ⦄ irrelevant = "irrelevant"

  instance
    ShowVisibility : Show Visibility
    show ⦃ ShowVisibility ⦄ visible = "visible"
    show ⦃ ShowVisibility ⦄ hidden = "hidden"
    show ⦃ ShowVisibility ⦄ instance′ = "instance"

  instance
    ShowName : Show Name
    show ⦃ ShowName ⦄ = primShowQName
 
  instance
    {-# TERMINATING #-}
    ShowArg : ∀ {A : Set} {{_ : Show A}} → Show (Arg A)
    show ⦃ ShowArg ⦄ (arg (arg-info v r) x) = "(arg (arg-info " # (show r) # " " # (show v) # ") " # (show x) # ")"

  instance
    ShowWord64 : Show Word64
    show ⦃ ShowWord64 ⦄ = show ∘ primWord64ToNat

  instance
    ShowFloat : Show Float
    show ⦃ ShowFloat ⦄ = primShowFloat

  instance
    ShowMeta : Show Meta
    show ⦃ ShowMeta ⦄ = primShowMeta

  instance
    {-# TERMINATING #-}
    ShowLit : Show Literal
    show ⦃ ShowLit ⦄ (nat n) = show n
    show ⦃ ShowLit ⦄ (word64 n) = show n
    show ⦃ ShowLit ⦄ (float x) = show x
    show ⦃ ShowLit ⦄ (char c) = primShowChar c
    show ⦃ ShowLit ⦄ (string s) = s
    show ⦃ ShowLit ⦄ (name x) = show x
    show ⦃ ShowLit ⦄ (meta x) = show x

  instance
    {-# TERMINATING #-}
    ShowPattern : Show Pattern
    show ⦃ ShowPattern ⦄ (con c ps) = "con (" # (show c) # " " # (show ps) # ")"
    show ⦃ ShowPattern ⦄ dot = "∙"
    show ⦃ ShowPattern ⦄ (var s) = "var " # s
    show ⦃ ShowPattern ⦄ (lit l) = "lit " # (show l)
    show ⦃ ShowPattern ⦄ (proj f) = "proj " # (show f)
    show ⦃ ShowPattern ⦄ absurd = "absurd"

  instance
    {-# TERMINATING #-}
    ShowClause : Show Clause
    show ⦃ ShowClause ⦄ (clause ps t) = "clause(" # (show ps) # ") " # (showT t)
    show ⦃ ShowClause ⦄ (absurd-clause ps) = "absurd-clause(" # (show ps) # ")"

  instance
    {-# TERMINATING #-}
    ShowAbs : {A : Set} {{_ : Show A}} → Show (Abs A)
    show ⦃ ShowAbs ⦄ (abs s x) = s # ", " # (show x)

  instance
    ShowSort : Show Sort
    show ⦃ ShowSort ⦄ (set t) = "Set " # (showT t)
    show ⦃ ShowSort ⦄ (lit n) = "Lit " # (show n)
    show ⦃ ShowSort ⦄ unknown = "Unknown"

  instance
    {-# TERMINATING #-}
    ShowTerm : Show Term
    show ⦃ ShowTerm ⦄ (var x args) = "(var " # (show x) # " (" # (show args) # "))"
    show ⦃ ShowTerm ⦄ (con c args) = "(con " # (show c) # " (" # (show args) # "))"
    show ⦃ ShowTerm ⦄ (def f args) = "(def " # (show f) # " (" # (show args) # "))"
    show ⦃ ShowTerm ⦄ (lam v t) = "(lam " # (show v) # (show t) # ")"
    show ⦃ ShowTerm ⦄ (pat-lam cs args) = "pattern lambda (" # (show cs) # ") (" # (show args) # ")"
    show ⦃ ShowTerm ⦄ (pi a b) = "(pi " # (show a) # " @ " # (show b) # ")"
    show ⦃ ShowTerm ⦄ (agda-sort s) = "agda-sort " # (show s)
    show ⦃ ShowTerm ⦄ (lit l) = "(lit " # (show l) # ")"
    show ⦃ ShowTerm ⦄ (meta x xs) = "(meta " # (show x) # ", " # (show xs) # ")"
    show ⦃ ShowTerm ⦄ unknown = "unknown"

  showT = show

  showGoal : String → Type → TC ⊤
  showGoal msg goal = typeError (strErr (msg # "\nGoal:\n" # (show goal)) ∷ [])
  
