import PaperProofs.PrimeAssignment
import Mathlib.Algebra.MvPolynomial.CommRing

namespace P0365Subquarter
open MvPolynomial
set_option pp.all true

#print sourcePoint
#print sourceReduction
#print polynomialValue
#print nonsingularSource
#print clearedValue
#print clearedPartial
#print selectedPartial
#print sourceWitness
#print goodSourcePrime
#print smoothResidues
#print firstGoodPrime
#print CF07ClearedIdentity
#print CF07ActualSourceWitness
#print CF08BertrandList
#print CF08FirstGoodAssignment
#print CF08SmoothLabelBudget
#print CF08RoundedSourceAssignment
#check (cleared_identity : CF07ClearedIdentity)
#check (actual_source_witness : CF07ActualSourceWitness)
#check (bertrand_list : CF08BertrandList)
#check (first_good_assignment : CF08FirstGoodAssignment)
#check (smooth_label_budget : CF08SmoothLabelBudget)
#check (rounded_source_assignment : CF08RoundedSourceAssignment)
#print axioms cleared_identity
#print axioms actual_source_witness
#print axioms bertrand_list
#print axioms first_good_assignment
#print axioms smooth_label_budget
#print axioms rounded_source_assignment

set_option pp.all false

-- Both ratio coordinates have their original orientation.
example : sourcePoint 2 1 6 17 = ![2, (17:ℚ)/6] := by
  ext i; fin_cases i <;> norm_num [sourcePoint]

-- An actual canonical 8/9 source lies smoothly on each of these two lines.
-- The second line requires the fallback partial: F_s=0, F_t=1.
example : nonsingularSource (X 0 - C 2) 2 1 1 3 := by
  constructor
  · norm_num [polynomialValue, sourcePoint, eval₂_sub, eval₂_X, eval₂_C]
  · exact ⟨0, by
      simp only [map_sub, pderiv_C, pderiv_X]
      norm_num [polynomialValue, Pi.single_apply]⟩
example : nonsingularSource (X 1 - C 3) 2 1 1 3 := by
  constructor
  · norm_num [polynomialValue, sourcePoint, eval₂_sub, eval₂_X, eval₂_C]
  · exact ⟨1, by
      simp only [map_sub, pderiv_C, pderiv_X]
      norm_num [polynomialValue, Pi.single_apply]⟩

-- Rational nonsingularity does not imply good reduction at every prime.
-- F=2(s-2) loses its derivative modulo 2, although the denominators are units.
private theorem even_line_not_smooth (z : Fin 2 → ZMod 2) :
    ¬ ∃ i : Fin 2, polynomialValue (pderiv i (C 2 * (X 0 - C 2))) z ≠ 0 := by
  rintro ⟨i, hi⟩
  simp only [pderiv_mul, pderiv_C, map_sub, pderiv_X, zero_mul] at hi
  fin_cases i <;> norm_num [polynomialValue, Pi.single_apply, eval₂_mul, eval₂_sub, eval₂_C] at hi
  exact hi (ZMod.natCast_self 2)
example : ¬ goodSourcePrime (C 2 * (X 0 - C 2)) 2 1 1 3 2 := by
  intro h
  exact even_line_not_smooth _ h.2.2
-- Nonzero integral F can have zero reduction: it still contributes no smooth labels.
example : smoothResidues (C 2 * (X 0 - C 2)) 2 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  simp only [smoothResidues, dite_eq_right (by decide : (2:ℕ) ≠ 0), Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  exact even_line_not_smooth z hz.2
-- The actual first partial vanishes, and the second must supply the witness.
example : clearedPartial (X 1 - C 3) 1 2 1 1 3 0 = 0 ∧
    clearedPartial (X 1 - C 3) 1 2 1 1 3 1 = 1 := by
  simp only [clearedPartial, map_sub, pderiv_C, pderiv_X]
  norm_num [Pi.single_apply, clearedValue]

-- A genuine denominator obstruction at the 288/289 source is bad.
example (F : SourcePolynomial) : ¬ goodSourcePrime F 2 1 6 17 3 := by
  intro h
  exact h.1 (by decide)

-- A zero polynomial has no smooth residues, including the total p=0 guard.
example (p : ℕ) : smoothResidues 0 p = ∅ := by
  classical
  unfold smoothResidues
  split_ifs
  · rfl
  · ext z
    simp [polynomialValue]
example (F : SourcePolynomial) : smoothResidues F 0 = ∅ := by
  simp [smoothResidues]

-- Empty lists cannot receive an assignment; they are accepted only by the
-- independent list existence theorem, never the positive-length final consumer.
example (F : SourcePolynomial) (b d u v : ℕ) : firstGoodPrime F b d u v ∅ = 0 := by
  simp [firstGoodPrime]
example (R : ℝ) (hR : 1 ≤ R) : ∃ s : Finset ℕ, s.card = 0 ∧
    ∀ p ∈ s, Nat.Prime p ∧ R ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2^(0+1) * R :=
  bertrand_list 0 R hR

end P0365Subquarter
