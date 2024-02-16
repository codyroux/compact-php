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
    (λ h ↦ h.elim) (λ h ↦ h.elim) (λ h ↦ h.elim)
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

def omegaGtN (n : ℕ) : Sentence OmegaArith :=
  lessThan.formula₂ (Constants.term (NS.standard n)) (Constants.term NS.omega)

def OmegaGreater : Theory OmegaArith := λ φ ↦ ∃ n : ℕ, φ = omegaGtN n

def NonStandardLT := ArithTruths ∪ OmegaGreater

def NatWithFiniteOmega := ℕ deriving LT, Nonempty


def FinStruct' (omegaVal : ℕ): Structure OmegaArith NatWithFiniteOmega :=
  Structure.mk₂
    (λ c ↦ match c with | .standard n => n | .omega => omegaVal)
    (λ h ↦ h.elim)
    (λ h ↦ h.elim)
    (λ h ↦ h.elim)
    (λ _ c₁ c₂ ↦ c₁ < c₂)

#print Finset.max
#print Finset.map

noncomputable def getN (φ : Sentence OmegaArith) (isLt : φ ∈ OmegaGreater) : ℕ :=
  Classical.choose isLt

-- ugh a little awkard to define...
noncomputable def coefs (φs : Finset (Sentence OmegaArith)) : Finset ℕ :=
  Finset.image
  (λ φ ↦
  -- this is actually decidable...
  let _ : Decidable (φ ∈ OmegaGreater) := Classical.dec _
  if h : φ ∈ OmegaGreater then
    getN φ h
  else 0)
  φs


#print WithBot

noncomputable def maxOmegaVal (φs : Finset (Sentence OmegaArith)) : ℕ :=
  if h : (coefs φs).Nonempty then (coefs φs).max' h + 1 else 0

noncomputable def FinStruct (φs : Finset (Sentence OmegaArith)) : Structure OmegaArith NatWithFiniteOmega :=
FinStruct' (maxOmegaVal φs)

instance NormalArith : Structure Arith NatWithFiniteOmega :=
by
  simp [NatWithFiniteOmega]
  exact standardModel


#check Model

#print Structure

#check Formula.realize_rel₂
#check default
#print LHom.IsExpansionOn
#check Finset.le_max

lemma getNOmega : getN (omegaGtN n) isLt = n :=
by
  simp [getN]
  -- hmpf
  sorry

lemma FinStructModel {T : Finset (Sentence OmegaArith)} :
  ↑ T ⊆ OmegaGreater → S ⊆ ArithTruths → @Model _ _ (FinStruct T) (T ∪ S)
:=
by
  intros ltOmega ltArith
  apply (@Model.mk _ _ (FinStruct T))
  intros φ mem
  cases' mem with h h
  . have h' : φ ∈ OmegaGreater := by apply ltOmega; trivial
    unfold OmegaGreater at h'
    cases' h' with n h'
    rw [h'] at h
    rw [h']
    simp [omegaGtN, Realize]
    have inst : Structure OmegaArith NatWithFiniteOmega := FinStruct T
    rw [Formula.realize_rel₂]
    rw [Structure.relMap_apply₂]
    simp [Term.realize, maxOmegaVal]
    have nIsCoef : n ∈ coefs T :=
    by
      simp [coefs]
      exists (omegaGtN n)
      constructor
      . apply h
      . rw [dite_cond_eq_true] <;> try (simp; apply ltOmega; trivial)
        apply getNOmega
    have nonEmpty : (coefs T).Nonempty := by exists n
    rw [dite_cond_eq_true] <;> try (simp; trivial)
    suffices n ≤ (Finset.max' (coefs T)) nonEmpty
    by -- what is the one liner here!!!?
      apply Nat.lt_of_le_pred
      simp [Nat.pred]
      rw [Nat.pred_succ]
      trivial
    apply Finset.le_max'; trivial
  . have h' : φ ∈ ArithTruths := by apply ltArith; trivial
    unfold ArithTruths at h'
    cases' h' with φ' h'
    cases' h' with h₁ h₂
    rw [← h₁]
    have inst : Structure OmegaArith NatWithFiniteOmega := FinStruct T
    rw [LHom.realize_onSentence]
    sorry

#print ModelType

lemma FiniteOmageGreaterIsSat {T : Finset (Sentence OmegaArith)} :
  ↑ T ⊆ OmegaGreater → S ⊆ ArithTruths → IsSatisfiable (T∪S):=
by
  intros lt_om lt_arith
  constructor
  apply (@ModelType.mk _ _ _ (FinStruct T) (FinStructModel _ _))
  . trivial
  . trivial

lemma NonStandardFinite : IsFinitelySatisfiable NonStandardLT :=
by
  simp [IsFinitelySatisfiable]
  intros T T_inc
  simp [NonStandardLT] at T_inc
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
