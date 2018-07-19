open import Level                                 using (_⊔_)
open import Algebra                               using (module CommutativeSemiring; module DistributiveLattice)
open import Function                              using (id; const; _∘_; _$_)
open import Coinduction                           using (∞; ♯_; ♭)
open import Data.Fin        as Fin                using (Fin; suc; zero)
open import Data.List       as List               using (List; _∷_; []; [_]; _++_; length; concat; foldr; concatMap)
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Nat                              using (ℕ; suc; zero; _≤_; z≤n; s≤s)
open import Data.Nat.Properties                   using (commutativeSemiring; distributiveLattice; ≤-decTotalOrder)
open import Data.Product                          using (∃; _×_; _,_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Vec        as Vec                using (Vec; _∷_; []; fromList)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary                       using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Auto.Show using (Show; show)
open import Data.String using (String) renaming (primStringAppend to _⊹⊹_)

module ProofSearch
  (RuleName : Set) (ShowRuleName : Show RuleName)
  (TermName : Set) (_≟-TermName_ : (x y : TermName) → Dec (x ≡ y)) (ShowTermName : Show TermName)
  (Literal  : Set) (_≟-Literal_  : (x y : Literal)  → Dec (x ≡ y)) (ShowLit : Show Literal)
  where

  open import Unification TermName _≟-TermName_ ShowTermName Literal _≟-Literal_ ShowLit public hiding (_++_)


  ----------------------------------------------------------------------------
  -- * define rules and utility functions                                 * --
  ----------------------------------------------------------------------------

  private
    ∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (b ⊔ a)
    ∃-syntax = ∃
    syntax ∃-syntax (λ x → B) = ∃[ x ] B

  -- introduce rules
  record Rule (n : ℕ) : Set where
    constructor rule
    field
      name        : RuleName
      conclusion  : Term n
      premises    : List (Term n)

  open Rule using (name; conclusion; premises)


  -- alias for list of rules
  Rules : Set
  Rules = List (∃ Rule)

  instance
    ShowRule : {n : ℕ} → Show (Rule n)
    show ⦃ ShowRule ⦄ (rule name conclusion premises) = "rule " ⊹⊹ ((show ⦃ ShowRuleName ⦄ name) ⊹⊹ ((" conclusion:(" ⊹⊹ ((show conclusion) ⊹⊹ (") premises: (" ⊹⊹ ((show premises) ⊹⊹ ")"))))))

  instance
    Show∃Rule : Show (∃ Rule)
    show ⦃ Show∃Rule ⦄ (proj₁ , proj₂) = "∃ " ⊹⊹ ((show proj₁) ⊹⊹ (" " ⊹⊹ (show proj₂)))

  -- compute the arity of a rule
  arity : ∀ {n} (r : Rule n) → ℕ
  arity = length ∘ premises


  -- open instances relevant to definitions of difference, inject and raise
  open CommutativeSemiring commutativeSemiring using (_+_; +-comm)
  open DistributiveLattice distributiveLattice using (_∧_; ∧-comm)
  open DecTotalOrder       ≤-decTotalOrder       using (total)


  -- compute the difference between two natural numbers, given an
  -- ordering between them.
  Δ_ : ∀ {m n} → m ≤ n → ℕ
  Δ z≤n {k} = k
  Δ s≤s  p  = Δ p

  -- correctness proof of the difference operator Δ.
  Δ-correct : ∀ {m n} (p : m ≤ n) → n ≡ m + Δ p
  Δ-correct  z≤n    = refl
  Δ-correct (s≤s p) = cong suc (Δ-correct p)

  -- type class for injections in the fashion of Fin.inject+
  record Inject (T : ℕ → Set) : Set where
    field
      inject : ∀ {m} n → T m → T (m + n)

    inject≤ : ∀ {m n} → m ≤ n → T m → T n
    inject≤ {m} {n} p t = subst T (sym (Δ-correct p)) (inject (Δ p) t)

  open Inject {{...}} using (inject; inject≤)


  -- type class for raising in the fashion of Fin.raise
  record Raise (T : ℕ → Set) : Set where
    field
      raise : ∀ {m} n → T m → T (n + m)

    raise≤ : ∀ {m n} → m ≤ n → T m → T n
    raise≤ {m} {n} p t = subst T (sym (trans (Δ-correct p) (+-comm m (Δ p)))) (raise (Δ p) t)

  open Raise {{...}} using (raise; raise≤)


  -- instances for inject/raise for all used data types
  instance
    InjectFin   : Inject Fin
    InjectFin   = record { inject = Fin.inject+ }
    RaiseFin    : Raise  Fin
    RaiseFin    = record { raise  = Fin.raise }
    InjectTerm  : Inject Term
    InjectTerm  = record { inject = λ n → replace (var ∘ inject n) }
    RaiseTerm   : Raise  Term
    RaiseTerm   = record { raise  = λ m → replace (var ∘ raise m) }
    InjectTerms : Inject (List ∘ Term)
    InjectTerms = record { inject = λ n → List.map (inject n) }
    RaiseTerms  : Raise  (List ∘ Term)
    RaiseTerms  = record { raise  = λ m → List.map (raise m) }
    InjectGoals : ∀ {k} → Inject (λ n → Vec (Term n) k)
    InjectGoals = record { inject = λ n → Vec.map (inject n) }
    RaiseGoals  : ∀ {k} → Raise (λ n → Vec (Term n) k)
    RaiseGoals  = record { raise  = λ m → Vec.map (raise m) }
    InjectRule  : Inject Rule
    InjectRule  = record { inject = λ n → λ { (rule nm c p) → rule nm (inject n c) (inject n p) } }
    RaiseRule   : Raise Rule
    RaiseRule   = record { raise  = λ m → λ { (rule nm c p) → rule nm (raise m c) (raise m p) } }

  -- could rephrase inject/raise in terms of allowing modification by
  -- a function ℕ → ℕ, but really... why would I... it makes all the
  -- other instances much, much more obtuse
  injectSubst : ∀ {m n} (δ : ℕ) → Subst m n → Subst (m + δ) (n + δ)
  injectSubst _ nil = nil
  injectSubst δ (snoc s t x) = snoc (injectSubst δ s) (inject δ t) (inject δ x)


  private
    m≤n→m⊔n=n : ∀ {m n} → m ≤ n → m ∧ n ≡ n
    m≤n→m⊔n=n  z≤n    = refl
    m≤n→m⊔n=n (s≤s p) = cong suc (m≤n→m⊔n=n p)


  -- match indices of injectable data types
  match : ∀ {m n} {I J} {{i : Inject I}} {{j : Inject J}}
        → I m → J n → I (m ∧ n) × J (m ∧ n)
  match {m} {n} i j with total m n
  ... | inj₁ p rewrite              m≤n→m⊔n=n p = (inject≤ p i , j)
  ... | inj₂ p rewrite ∧-comm m n | m≤n→m⊔n=n p = (i , inject≤ p j)


  ----------------------------------------------------------------------------
  -- * define hint databases                                              * --
  ----------------------------------------------------------------------------

  record IsHintDB : Set₁ where
    field
      HintDB   : Set
      Hint     : ℕ → Set
      showHint : {n : ℕ} → Show (Hint n)

    Hints : Set
    Hints = List (∃ Hint)

    field
      getHints   : HintDB → Hints
      getRule    : ∀ {k} → Hint k → Rule k
      getTr      : ∀ {k} → Hint k → (HintDB → HintDB)
      ε          : HintDB
      _∙_        : HintDB → HintDB → HintDB
      return     : ∀ {k} → Rule k → HintDB

    fromRules : Rules → HintDB
    fromRules []             = ε
    fromRules ((k , r) ∷ rs) = return r ∙ fromRules rs

    instance
      Show∃Hint : Show (∃ Hint)
      show ⦃ Show∃Hint ⦄ (proj₁ , proj₂) = ((show proj₁) ⊹⊹ (" " ⊹⊹ (show ⦃ showHint ⦄ proj₂)))

    instance
      ShowHintDB : Show HintDB
      show ⦃ ShowHintDB ⦄ db = show (getHints db)


  ----------------------------------------------------------------------------
  -- * define simple hint databases                                       * --
  ----------------------------------------------------------------------------

  simpleHintDB : IsHintDB
  simpleHintDB = record
    { HintDB   = Rules
    ; Hint     = Rule
    ; showHint = ShowRule
    ; getHints = id
    ; getRule  = id
    ; getTr    = const id
    ; ε        = []
    ; _∙_      = _++_
    ; return   = λ r → [ _ , r ]
    }


  ----------------------------------------------------------------------------
  -- * define search trees, proofs and partial proofs                     * --
  ----------------------------------------------------------------------------

  -- simple alias to set apart the goal term
  Goal = Term

  -- search trees
  data SearchTree (A : Set) : Set where
    leaf : String → A → SearchTree A
    node : String → List (∞ (SearchTree A)) → SearchTree A

  -- representation of a failed branch
  fail : ∀ {A} → SearchTree A
  fail = node "fail" []

  data Proof : Set where
     con : (name : RuleName) (args : List Proof) → Proof

  instance
    {-# TERMINATING #-}
    ShowProof : Show Proof
    show ⦃ ShowProof ⦄ (con name args) = "con " ⊹⊹ ((show ⦃ ShowRuleName ⦄ name) ⊹⊹ (" " ⊹⊹ (show args)))

  -- representation of an incomplete proof
  Proof′ : ℕ → Set
  Proof′ m = ∃[ k ] (Vec (Goal m) k × (Vec Proof k → Proof))

  con′ : ∀ {n k} (r : Rule n) → Vec Proof (arity r + k) → Vec Proof (suc k)
  con′ {n} {k} r xs = head ∷ rest
    where
      head : Proof
      head = con (name r) (Vec.toList $ Vec.take (arity r) xs)
      rest : Vec Proof k
      rest = Vec.drop (arity r) xs


  ----------------------------------------------------------------------------
  -- * define proof search function                                       * --
  ----------------------------------------------------------------------------

  module Extensible (isHintDB : IsHintDB) where

    open IsHintDB isHintDB

    solve : ∀ {m} → Goal m → HintDB → SearchTree Proof
    solve {m} g = solveAcc {m} "[FIRST]" (1 , g ∷ [] , Vec.head)
      where
        solveAcc : ∀ {m} → String → Proof′ m → HintDB → SearchTree Proof
        solveAcc {m} s (0     ,     [] , p) _  = leaf ("(leaf " ⊹⊹ (s ⊹⊹ ")\n")) (p [])
        solveAcc {m} s (suc k , g ∷ gs , p) db = node ("(node " ⊹⊹ (s ⊹⊹ (" : " ⊹⊹ ((show g) ⊹⊹ ")\n")))) (steps (getHints db))
          where
            step : ∃[ δ ] (Hint δ) → ∞ (SearchTree Proof)
            step (δ , h) with unify (inject δ g) (raise m (conclusion (getRule h)))
            ... | nothing        = ♯ node ("fail-step : " ⊹⊹ hintInfo) [] -- fail
              where
                hintInfo : String
                hintInfo = ((show ⦃ showHint ⦄ h) ⊹⊹ "\n")
            ... | just (n , mgu) = ♯ solveAcc {n} ("step {" ⊹⊹ ((show n) ⊹⊹ ("} : " ⊹⊹ hintInfo))) prf (getTr h db)
              where
                hintInfo : String
                hintInfo = ((show ⦃ showHint ⦄ h) ⊹⊹ "\n")
                prf : Proof′ n
                prf = arity (getRule h) + k , gs′ , (p ∘ con′ (getRule h))
                  where
                    prm′ = raise m (Vec.fromList (premises (getRule h)))
                    gs′  = Vec.map (replace (sub mgu)) (prm′ Vec.++ inject δ gs)


            -- equivalent to `map step` due to termination checker
            steps : List (∃ Hint) → List (∞ (SearchTree Proof))
            steps []       = []
            steps (h ∷ hs) = step h ∷ steps hs

  ----------------------------------------------------------------------------
  -- * define various search strategies                                   * --
  ----------------------------------------------------------------------------

  Strategy : Set₁
  Strategy = ∀ {A} (depth : ℕ) → SearchTree A → String × List A

  dfs : Strategy
  dfs  zero    _        = "[End path]\n" , []
  dfs (suc k) (leaf s₁ x)  = s₁ , (x ∷ [])
  dfs (suc k) (node s₁ xs) = foldr (λ t p →
    let (s₂ , ts₁) = p
        (s₃ , ts₂) = dfs k (♭ t)
    in s₂ ⊹⊹ s₃ , ts₁ ++ ts₂)
    (s₁ , []) xs

--  dfs k (♭ x)

{-
  bfs : Strategy
  bfs depth t = concat (Vec.toList (bfsAcc depth t))
    where
      merge : ∀ {A : Set} {k} → (xs ys : Vec (List A) k) → Vec (List A) k
      merge [] [] = []
      merge (x ∷ xs) (y ∷ ys) = (x ++ y) ∷ merge xs ys

      empty : ∀ {A : Set} {k} → Vec (List A) k
      empty {k = zero}  = []
      empty {k = suc k} = [] ∷ empty

      bfsAcc : ∀ {A} (depth : ℕ) → SearchTree A → Vec (List A) depth
      bfsAcc  zero   _         = []
      bfsAcc (suc k) (leaf s x)  = (x ∷ []) ∷ empty
      bfsAcc (suc k) (node s xs) = [] ∷ foldr merge empty (List.map (λ x → bfsAcc k (♭ x)) xs)
-}
