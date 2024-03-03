import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory
open Real

section NonStandard

-- The reals extended with a non-standard element
inductive NS :=
| standard : ℝ → NS
| ω : NS
-- ω
/-
A goofy system for describing what function symbols we want
Probably arbitrary to do it this way and probably
designed around the good and bad of lean's facilities
and modelling style.
-/
inductive RelNames :=
| ltName : RelNames

inductive UnOpNames :=
| negName : UnOpNames
| invName : UnOpNames

inductive BinOpNames :=
| plusName : BinOpNames
| timesName : BinOpNames

-- The language with all of ℚ as constants (0 arity fun symbols),
-- no single argument function symbols
-- a couple binary functions
def Arith : Language := Language.mk₂ ℚ UnOpNames BinOpNames Empty RelNames

-- The language with all of NS as constants, and a single binary relation.
def OmegaArith : Language :=
⟨ λ n ↦ if n = 0 then NS else Arith.Functions n, Arith.Relations⟩

lemma emptyFuncs : Arith.Functions (n + 3) → False :=
by
  simp only [Arith, mk₂_Functions, IsEmpty.forall_iff]

@[simp]
def liftConsts (n : ℕ) : Arith.Functions n → OmegaArith.Functions n :=
  match n with
  | 0 => λ (x : ℚ) ↦ NS.standard x
  | .succ m => λ (h : Arith.Functions (.succ m)) ↦ h

-- possibly should use whatever lean mechanism auto lifts N to R?
@[simp]
def liftStandard : Arith →ᴸ OmegaArith := ⟨liftConsts, λ _ r ↦ r⟩

@[simp]
noncomputable instance standardModel : Structure Arith ℝ :=
  Structure.mk₂ (λ c ↦ c)
    (λ h ↦ match h with
      | .negName => (- .)
      | .invName => (.⁻¹)
    )
    (λ h ↦ match h with
     | .plusName => (. + .)
     | .timesName => (. * .)
    )
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

-- n < ω
def omegaGtN (n : ℕ) : Sentence OmegaArith :=
lessThan.formula₂ (Constants.term (NS.standard n)) (Constants.term NS.ω)

-- { "n < ω" | n ∈ ℕ }
def OmegaGreater : Theory OmegaArith := Set.range omegaGtN
-- { omegaGtN n | n : ℕ }
-- λ φ ↦ ∃ n : ℕ, φ = omegaGtN n

def NonStandardLT := ArithTruths ∪ OmegaGreater

def RWithFiniteOmega (_omegaVal : ℝ) := ℝ -- deriving LT, Nonempty fails

-- These instances just come from the underlying type.
-- FIXME: how do we unfold the definition of `RWithFiniteOmega` to
-- automatically synthesize these instances?
instance instLTROmega {n : ℕ}: LT (RWithFiniteOmega n) := instLTReal

instance instNonemptyROmega {n : ℕ} : Nonempty (RWithFiniteOmega n) :=
  ⟨(0 : ℝ)⟩

noncomputable instance FinStruct' (omegaVal : ℝ): Structure OmegaArith (RWithFiniteOmega omegaVal) :=
  Structure.mk
  (λ {n} ↦ match n with
    | 0 => λ c _ ↦ match c with | .standard x => x | .ω => omegaVal
    -- kind of impressed it guesses here. Or am I wrong?
    | _+1 => standardModel.funMap)
  standardModel.RelMap

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


noncomputable def maxOmegaVal (φs : Finset (Sentence OmegaArith)) : ℝ :=
  if h : (coefs φs).Nonempty then (coefs φs).max' h + 1 else 0

noncomputable instance FinStruct {φs : Finset (Sentence OmegaArith)} :
  Structure OmegaArith (RWithFiniteOmega (maxOmegaVal φs)) :=
FinStruct' (maxOmegaVal φs)

noncomputable instance NormalArith : Structure Arith (RWithFiniteOmega n) :=
by
  simp only [RWithFiniteOmega]
  exact standardModel


lemma omegaGtN_inj : omegaGtN n = omegaGtN m → n = m :=
by
  intros eq
  injection eq with hn hl hR hts
  rw [Function.funext_iff] at hts
  have := hts 0
  simp only [Term.relabel, Term.func.injEq, heq_eq_eq, and_true, true_and] at this   -- this is bad style; `simp?`'s output would be better
  injection this with h
  revert h
  apply Nat.cast_injective


lemma getNOmega : getN (omegaGtN n) isLt = n :=
by
  simp [getN]
  -- hmpf. This is surely a lemma.
  have h : omegaGtN (Classical.choose isLt) = omegaGtN n:=
  by
    unfold OmegaGreater at isLt
    simp [Membership.mem, Set.Mem] at isLt
    unfold Set.range at isLt
    unfold setOf at isLt
    whnf at isLt
    apply (@Classical.choose_spec _ _ isLt)
  apply omegaGtN_inj; apply h

instance expantionFinOmega : LHom.IsExpansionOn liftStandard (RWithFiniteOmega n) :=
by
  constructor
  . intros n; cases' n with n
    . simp [Arith, Sequence₂, Structure.funMap]
    . cases' n with n
      . simp [Arith, Sequence₂]
        intros; trivial
      . cases' n with n
        . simp [Arith, Sequence₂]
          intros; trivial
        . simp [Arith]
  . intros n; cases' n with n; simp [Arith, Sequence₂]
    cases' n with n; simp [Arith, Sequence₂]
    cases' n with n
    . simp [Arith, Sequence₂]
      intros; trivial
    . simp [Arith, Sequence₂]; intros R; simp at R
      cases R

lemma FinStructModel {T : Finset (Sentence OmegaArith)} :
  ↑ T ⊆ OmegaGreater → S ⊆ ArithTruths →
  RWithFiniteOmega (maxOmegaVal T) ⊨ ↑T ∪ S :=
by
  intros ltOmega ltArith
  apply (@Model.mk _ _ (@FinStruct T))
  intros φ mem
  cases' mem with h h
  . have h' : φ ∈ OmegaGreater := by apply ltOmega; trivial
    unfold OmegaGreater at h'
    cases' h' with n h'
    cases' h' with _ h'
    simp [omegaGtN, Realize, constantMap, Structure.RelMap, Structure.funMap]
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
    suffices ↑n ≤ (Finset.max' (coefs T)) nonEmpty
    by -- what is the one liner here!!!?
      norm_cast
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
    simp [RWithFiniteOmega]
    trivial

lemma FiniteOmegaGreaterIsSat {T : Finset (Sentence OmegaArith)} :
  ↑T ⊆ OmegaGreater → S ⊆ ArithTruths → IsSatisfiable (T ∪ S):=
by
  intros lt_om lt_arith
  constructor
  apply (@ModelType.mk _ _ _ (@FinStruct T) (FinStructModel _ _) instNonemptyROmega)
  . trivial
  . trivial
  -- FIXME: make this a unification goal
  . exact 0

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

#print ModelType
#print IsSatisfiable
#print Nonempty

-- These are the (or at least some) actual non standard reals!
def NSR : Type :=
  let model := Classical.choice NonStandardExists;
  ↑model

#print Structure

noncomputable instance omegaArithNST : Structure OmegaArith NSR := by
  simp [NSR]
  exact (Classical.choice NonStandardExists).struc
  done

#print NSR

#check Term.realize
#check Sentence.Realize

#check Empty.elim

notation:50 "(|" φ "|)" => NSR ⊨ φ

#print Term

#print OmegaArith
#print Structure
#print Language.Constants

-- #eval OmegaArith.Constants

#check (NS.standard 0 : OmegaArith.Constants)

def myzero : OmegaArith.Constants := NS.standard 0

#check Constants.term myzero

#check
  @Term.realize OmegaArith NSR _ _
   ((λ h ↦ h.elim) : Empty → NSR)
   (Constants.term myzero)

#print Model
#print Theory
#print Realize

open Sentence

instance modelsNS : NSR ⊨ NonStandardLT := (Classical.choice NonStandardExists).is_model

-- Fixme: make this a coercion?
noncomputable def QtoNS : ℚ → NSR := λ q ↦ @constantMap OmegaArith _ _ $ NS.standard q

noncomputable def negNS : NSR → NSR :=
  λ x ↦ @Structure.funMap OmegaArith _ _ 1 UnOpNames.negName ![x]

noncomputable def invNS : NSR → NSR :=
  λ x ↦ @Structure.funMap OmegaArith _ _ 1 UnOpNames.invName ![x]

noncomputable def addNS : NSR → NSR → NSR :=
  λ x y ↦ @Structure.funMap OmegaArith _ _ 2 BinOpNames.plusName ![x, y]

noncomputable def mulNS : NSR → NSR → NSR :=
  λ x y ↦ @Structure.funMap OmegaArith _ _ 2 BinOpNames.timesName ![x, y]

#print RatCast

#check Term.realize_constants
#check Term.realize_con

#check constantMap
#check Structure.funMap

#print Field
#check Model.realize_of_mem

#print OmegaArith
#check OmegaArith.Constants

def zero : Language.Constants OmegaArith := NS.standard 0

#check Constants.term zero =' Constants.term (NS.standard 0)

#check NSR ⊨ Constants.term zero =' Constants.term (NS.standard 0)
#check (| Constants.term zero =' Constants.term (NS.standard 0) |)
#check (| ∀' (Constants.term zero =' &0) |)

lemma modelSatisfies : φ ∈ NonStandardLT → NSR ⊨ φ :=
by
  apply (@Model.realize_of_mem _ _ _ _ modelsNS)

-- This is gonna be pretty darn useful
theorem overspill : ∀ φ : Sentence Arith,
  ℝ ⊨ φ → NSR ⊨ LHom.onSentence liftStandard φ :=
by
  intro φ satR
  apply modelSatisfies
  unfold NonStandardLT
  left; whnf
  exists φ

lemma interpTrue : ∀ φ : Sentence OmegaArith, NSR ⊨ φ → (| φ |) :=
by
  intros; trivial

#check func

def addSyn : Arith.Functions 2 := BinOpNames.plusName

#check congrArg₂

#print LHom.onTerm
#print Term.brecOn

lemma addNS_assoc : ∀ a b c : NSR, addNS (addNS a b) c = addNS a (addNS b c) :=
by
  let φ : Sentence Arith := ∀' ∀' ∀' (Functions.apply₂ addSyn (Functions.apply₂ addSyn &2 &1) (&0)
    =' Functions.apply₂ addSyn (&2) (Functions.apply₂ addSyn &1 &0))
  let φ' : Sentence OmegaArith := ∀' ∀' ∀' (Functions.apply₂ addSyn (Functions.apply₂ addSyn &2 &1) (&0)
    =' Functions.apply₂ addSyn (&2) (Functions.apply₂ addSyn &1 &0))
  have h : LHom.onSentence liftStandard φ = φ' :=
  by -- some pain here: how to alleviate?
    simp [φ]
    simp [LHom.onSentence, LHom.onFormula, Functions.apply₂]
    apply congrArg₂
    . apply congrArg₂; trivial
      repeat apply List.ofFn_inj.mp; simp
    . apply congrArg₂; trivial
      repeat apply List.ofFn_inj.mp; simp
  suffices
   (| φ' |)
    by -- bleaugh
      simp [Realize, Formula.Realize, addSyn, Structure.funMap, Fin.snoc, Structure.funMap] at this
      simp [addNS]
      intros; apply this
  rw [← h]
  apply overspill
  simp [Realize, Formula.Realize, addSyn, Fin.snoc]
  -- finally!
  intros; ring


-- They inherit the field structure from ℝ.
instance isNSField : Field NSR where
  add := addNS
  add_assoc := addNS_assoc
  zero := QtoNS 0
  zero_add := _
  add_zero := _
  add_comm := _
  mul := mulNS
  left_distrib := _
  right_distrib := _
  zero_mul := _
  mul_zero := _
  mul_assoc := _
  one := QtoNS 1
  one_mul := _
  mul_one := _
  neg := negNS
  add_left_neg := _
  mul_comm := _
  inv := invNS
  exists_pair_ne := _
  mul_inv_cancel := _
  inv_zero := _

end NonStandard
