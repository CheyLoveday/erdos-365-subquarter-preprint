import PaperProofs.GenericCoarse

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04GenericBoundedIntegerRelation
#print CF04ActualUniformCoarsePolynomial
#check (generic_bounded_integer_relation : CF04GenericBoundedIntegerRelation)
#check (actual_uniform_coarse_polynomial : CF04ActualUniformCoarsePolynomial)
#print axioms generic_bounded_integer_relation
#print axioms actual_uniform_coarse_polynomial
set_option pp.all false

example : CF04GenericBoundedIntegerRelation := by
  intro H hH ι A L hL hentry hzero
  exact generic_bounded_integer_relation H hH ι A L hL hentry hzero

example : CF04ActualUniformCoarsePolynomial := by
  intro δ hδ hδ₁
  exact actual_uniform_coarse_polynomial δ hδ hδ₁

-- H=1, nonempty population, rank zero; the cofactor is the empty minor.
example : ∃ c : Fin 1 → ℤ, c≠0 ∧ (∀ j,|(c j:ℝ)|≤1) ∧
    ∀ _i : Unit,∑ j : Fin 1,(0:ℤ)*c j=0 := by
  obtain ⟨c,hc,hbound,hrel⟩ := generic_bounded_integer_relation 1 (by norm_num)
    Unit (fun _ _ => 0) 1 (by norm_num) (by intros; norm_num)
    (by intro f; simp)
  exact ⟨c,hc,by simpa using hbound,hrel⟩

-- Empty populations are covered without a supplied row or full-rank basis.
example : ∃ c : Fin 2 → ℤ,c≠0 ∧ (∀ j,|(c j:ℝ)|≤1) ∧
    ∀ _i : Empty,∑ j : Fin 2,(0:ℤ)*c j=0 := by
  obtain ⟨c,hc,hbound,hrel⟩ := generic_bounded_integer_relation 2 (by norm_num)
    Empty (fun _ _ => 0) 1 (by norm_num) (by intros; norm_num)
    (by intro f; exact isEmptyElim (f 0))
  exact ⟨c,hc,by simpa using hbound,hrel⟩

-- Repeated actual rows at rank one, with H=2.
example : ∃ c : Fin 2 → ℤ,c≠0 ∧ (∀ j,|(c j:ℝ)|≤1) ∧
    ∀ _i : Unit,∑ j : Fin 2,(if j=0 then (1:ℤ) else 0)*c j=0 := by
  obtain ⟨c,hc,hbound,hrel⟩ := generic_bounded_integer_relation 2 (by norm_num)
    Unit (fun _ j => if j=0 then 1 else 0) 1 (by norm_num)
    (by intro i j; split_ifs <;> norm_num)
    (by intro f; norm_num [Matrix.det_fin_two])
  exact ⟨c,hc,by simpa using hbound,hrel⟩

end
end P0365Subquarter
