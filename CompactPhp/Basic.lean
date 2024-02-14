import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Fintype.Card

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory

def hello := "world"

-- Completeness
#check isSatisfiable_iff_isFinitelySatisfiable
#print IsSatisfiable
#print IsFinitelySatisfiable
#print Theory
#print Nonempty
#print ModelType
#print Model
#print Sentence.Realize
#print Structure
#print Term
#print BoundedFormula
#print Fin

section NonStandard

inductive NS :=
| standard : ℕ → NS
| omega : NS

#check Unit
#check ℕ ⊕ Unit
#check (∀' (&0 =' &0))

#print Sequence₂
#print Language.empty
-- A first order language: first the type of function symbols, then the type of
-- relation symbols. Both are specified "per-arity"
#print Language
#print Language.mk₂

-- The language with all of ℕ as constants, and a single binary relation.
def Arith : Language := Language.mk₂ ℕ Empty Empty Empty Unit

-- The language with all of NS as constants, and a single binary relation.
def OmegaArith : Language := Language.mk₂ NS Empty Empty Empty Unit

lemma emptyFuncs : Arith.Functions (n + 1) → False :=
by
  cases' n with n; simp [Arith, Sequence₂]
  cases' n with n; simp [Arith, Sequence₂]
  simp [Arith, Sequence₂]

def liftConsts (n : ℕ) : Arith.Functions n → OmegaArith.Functions n :=
  match n with
  | 0 => NS.standard
  | .succ _ => λ h ↦ (emptyFuncs h).elim

def liftStandard : Arith →ᴸ OmegaArith := ⟨liftConsts, λ _ r ↦ r⟩

instance standardModel : Structure Arith ℕ :=
  Structure.mk₂ (λ c ↦ c)
    (λ h _ ↦ h.elim) (λ h _ _ ↦ h.elim) (λ h _ ↦ h.elim)
    (λ _ c₁ c₂ ↦ c₁ < c₂)

open Sentence
variable (φ : Sentence Arith)
#check (ℕ ⊨ φ)

def ArithTruths : Theory OmegaArith :=
  λ φ ↦ ∃ φ' : Sentence Arith, LHom.onSentence liftStandard φ' = φ ∧ ℕ ⊨ φ'

#check Term OmegaArith Empty
#print Term
#print Unit
#print PUnit

def lessThan : OmegaArith.Relations 2 := Unit.unit

def OmegaGreater : Theory OmegaArith :=
  λ φ ↦ ∃ n : ℕ,
   φ = lessThan.formula₂ (Constants.term (NS.standard n)) (Constants.term NS.omega)

def NonStandardLT := ArithTruths ∪ OmegaGreater

lemma NonStandardFinite : IsFinitelySatisfiable NonStandardLT :=
by
  simp [IsFinitelySatisfiable]
  intros T T_inc
  sorry

theorem NonStandardExists : IsSatisfiable NonStandardLT :=
by
  rw [isSatisfiable_iff_isFinitelySatisfiable]
  exact NonStandardFinite

end NonStandard

section FinitaryPHP

-- Infinite with infinite fiber
#check Finite.exists_infinite_fiber
-- Infinite with fiber > 2
#check Finite.exists_ne_map_eq_of_infinite
-- Finite with fiber > 2
#check Fintype.exists_ne_map_eq_of_card_lt
#print Set
#print Infinite
#print Finite



end FinitaryPHP
