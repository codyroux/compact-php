import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory
open Real

section NonStandard

-- The reals extended with a non-standard element
/-
Not that crazy. We are used to having such a type in interval arithmetic
Floats have +inf and -inf representable.
We could define normal addition,subtraction functions
over this stuff

for exmaple
def add x y :=
 match x,y with
  | +inf, _ => +inf
  | _, +inf => +inf
  | .standard x, .standard y => .standard (x + y)

-/
inductive NS :=
| standard : ℝ → NS
| omega : NS

/-
A goofy system for describing what function symbols we want
Probably arbitrary to do it this way and probably
designed around the good and bad of lean's facilities
and modelling style.
-/
inductive RelNames :=
| ltName : RelNames

inductive BinOpNames :=
| plusName : BinOpNames
| timesName : BinOpNames
| divName : BinOpNames

-- The language with all of ℕ as constants (0 arity fun symbols),
-- no single argument function symbols
-- a couple binary functions

def Arith : Language := Language.mk₂ ℕ Empty BinOpNames Empty RelNames

-- The language with all of NS as constants, and a single binary relation.
def OmegaArith : Language :=
⟨ λ n ↦ if n = 0 then NS else Arith.Functions n, Arith.Relations⟩

lemma emptyFuncs : Arith.Functions (n + 3) → False :=
by
  simp [Arith] -- we need simp to unfold Arith.

@[simp]
def liftConsts (n : ℕ) : Arith.Functions n → OmegaArith.Functions n :=
  match n with
  | 0 => λ (x : ℕ) ↦ NS.standard x
  | .succ m => λ (h : Arith.Functions (.succ m)) ↦ h -- how do I unfold the type here?

-- possibly should use whatever lean mechanism auto lifts N to R?
@[simp]
def liftStandard : Arith →ᴸ OmegaArith := ⟨liftConsts, λ _ r ↦ r⟩

@[simp]
noncomputable instance standardModel : Structure Arith ℝ :=
  Structure.mk₂ (λ c ↦ c)
    (λ h ↦ h.elim )
    (λ h ↦ match h with | .plusName => (. + .) | .timesName => (. * .) | .divName => (. / .))
    (λ h ↦ h.elim)
    (λ _ c₁ c₂ ↦ c₁ < c₂)

open Sentence

-- A "theory" is a set of formulas
#print Theory

-- https://en.wikipedia.org/wiki/True_arithmetic
-- The set of all nonstandard formulas such that
-- they are injected from arith formulas which
-- are satisfied in the standard model

-- This notion is dependent on Lean's notion of provability of satsifiability


def ArithTruths : Theory OmegaArith :=
  λ φ ↦ ∃ φ' : Sentence Arith, LHom.onSentence liftStandard φ' = φ ∧ ℝ ⊨ φ'

def lessThan : OmegaArith.Relations 2 := .ltName

-- n < omega
def omegaGtN (n : ℕ) : Sentence OmegaArith :=
lessThan.formula₂ (Constants.term (NS.standard n)) (Constants.term NS.omega)


-- { "n < omega" | n ∈ ℕ }
def OmegaGreater : Theory OmegaArith := omegaGtN '' (Set.univ : Set ℕ)
-- { omegaGtN n | n : ℕ }
-- λ φ ↦ ∃ n : ℕ, φ = omegaGtN n

#check Set.mem_image


def NonStandardLT := ArithTruths ∪ OmegaGreater

def NatWithFiniteOmega (_omegaVal : ℕ) := ℕ -- deriving LT, Nonempty fails

instance instLTNatOmega {n : ℕ}: LT (NatWithFiniteOmega n) := instLTNat

instance instNonemptyNatOmega {n : ℕ} : Nonempty (NatWithFiniteOmega n) :=
  ⟨(0 : ℕ)⟩

instance FinStruct' (omegaVal : ℕ): Structure OmegaArith (NatWithFiniteOmega omegaVal) :=
  Structure.mk₂
    (λ c ↦ match c with | .standard n => n | .omega => omegaVal)
    (λ h ↦ h.elim)
    (λ h ↦ h.elim)
    (λ h ↦ h.elim)
    (λ _ c₁ c₂ ↦ c₁ < c₂)

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


noncomputable def maxOmegaVal (φs : Finset (Sentence OmegaArith)) : ℕ :=
  if h : (coefs φs).Nonempty then (coefs φs).max' h + 1 else 0

noncomputable instance FinStruct {φs : Finset (Sentence OmegaArith)} :
  Structure OmegaArith (NatWithFiniteOmega (maxOmegaVal φs)) :=
FinStruct' (maxOmegaVal φs)

instance NormalArith : Structure Arith (NatWithFiniteOmega n) :=
by
  simp [NatWithFiniteOmega]
  exact standardModel


lemma omegaGtN_inj : omegaGtN n = omegaGtN m → n = m :=
by
  intros eq
  injection eq with hn hl hR hts
  rw [Function.funext_iff] at hts
  have := hts 0
  simp at this  -- this is bad style; `simp?`'s output would be better
  injection this


lemma getNOmega : getN (omegaGtN n) isLt = n :=
by
  simp [getN]
  -- hmpf
  unfold OmegaGreater at isLt
  simp [Membership.mem, Set.Mem] at isLt
  have h : omegaGtN n = omegaGtN (Classical.choose isLt) :=
  by
    apply @Classical.choose_spec _ (λ m ↦ omegaGtN n = omegaGtN m)
  apply omegaGtN_inj; rw [← h]

instance expantionFinOmega : LHom.IsExpansionOn liftStandard (NatWithFiniteOmega n) :=
by
  constructor
  . intros n; cases' n with n
    . simp [Arith, Sequence₂]
    . intros
      exfalso
      apply emptyFuncs; trivial
  . intros n; cases' n with n; simp [Arith, Sequence₂]
    cases' n with n; simp [Arith, Sequence₂]
    cases' n with n
    . simp [Arith, Sequence₂]
      intros; trivial
    . simp [Arith, Sequence₂]; intros R; simp at R
      cases R

lemma FinStructModel {T : Finset (Sentence OmegaArith)} :
  ↑ T ⊆ OmegaGreater → S ⊆ ArithTruths →
  NatWithFiniteOmega (maxOmegaVal T) ⊨ ↑T ∪ S :=
by
  intros ltOmega ltArith
  apply (@Model.mk _ _ (@FinStruct T))
  intros φ mem
  cases' mem with h h
  . have h' : φ ∈ OmegaGreater := by apply ltOmega; trivial
    unfold OmegaGreater at h'
    cases' h' with n h'
    rw [h'] at h
    rw [h']
    simp [omegaGtN, Realize, constantMap]
    unfold maxOmegaVal
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
    rw [LHom.realize_onSentence]
    simp [NatWithFiniteOmega]
    trivial

lemma FiniteOmegaGreaterIsSat {T : Finset (Sentence OmegaArith)} :
  ↑T ⊆ OmegaGreater → S ⊆ ArithTruths → IsSatisfiable (T ∪ S):=
by
  intros lt_om lt_arith
  constructor
  apply (@ModelType.mk _ _ _ (@FinStruct T) (FinStructModel _ _))
  . trivial
  . trivial

lemma NonStandardFinite : IsFinitelySatisfiable NonStandardLT :=
by
  simp [IsFinitelySatisfiable]
  intros T T_inc
  simp [NonStandardLT] at T_inc
  let _ : DecidablePred (. ∈ OmegaGreater) := Classical.decPred _
  let GT_T := T.filter (. ∈ OmegaGreater)
  let Arith_T := { φ ∈ ArithTruths | φ ∈ T }
  have is_union : ↑T = ↑GT_T ∪ Arith_T :=
  by
    apply Set.Subset.antisymm
    . intros φ inT
      simp
      by_cases φ ∈ OmegaGreater
      . left; constructor <;> trivial
      . right; constructor <;> try trivial
        have h : φ ∈ ArithTruths ∪ OmegaGreater := by apply T_inc; trivial
        cases h <;> trivial
    . intros φ union
      cases' union with _ h
      . apply @Finset.mem_of_mem_filter _ (. ∈ OmegaGreater)
        trivial
      . apply h.2
  rw [is_union]
  apply FiniteOmegaGreaterIsSat
  . simp [GT_T] -- adding Subset to this list causes a stack overflow!
    intro x; simp
  . simp [Arith_T]

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
