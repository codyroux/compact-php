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
#print Structure
#print Term
#print BoundedFormula
#print Fin

section NonStandard

inductive NS :=
| Standard : ℕ → NS
| Omega : NS

#check Unit
#check ℕ ⊕ Unit
#check (∀' (&0 =' &0))

#print Sequence₂
#print Language.empty
-- A first order language: first the type of function symbols, then the type of
-- relation symbols. Both are specified "per-arity"
#print Language

def LTArith : Language := ⟨Sequence₂ NS Empty Empty, Sequence₂ Empty Empty Unit⟩

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
