import PaperProofs.ThueLevels

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print StewartPrimitiveThue
#print CF15HighFactorThueAdmissibility
#print CF15IrreducibleThueLevel
#print CF15HighFactorLevelBudget
#print CF15SelectedFactorLevelBudget
#print CF15ActualGraphLevelBudget
#check (high_factor_thue_admissibility : CF15HighFactorThueAdmissibility)
#check (irreducible_thue_level : CF15IrreducibleThueLevel)
#check (high_factor_level_budget : CF15HighFactorLevelBudget)
#check (selected_factor_level_budget : CF15SelectedFactorLevelBudget)
#check (actual_graph_level_budget : CF15ActualGraphLevelBudget)
#print axioms high_factor_thue_admissibility
#print axioms irreducible_thue_level
#print axioms high_factor_level_budget
#print axioms selected_factor_level_budget
#print axioms actual_graph_level_budget
set_option pp.all false

example : CF15HighFactorThueAdmissibility := by
  intro f hf hirr hd
  exact high_factor_thue_admissibility f hf hirr hd
example : CF15IrreducibleThueLevel := by
  intro hThue f hf hirr hd hdu h hh S hS
  exact irreducible_thue_level hThue f hf hirr hd hdu h hh S hS
example : CF15HighFactorLevelBudget := by
  intro hThue Q f hf hirr hd hdu hdiv h hh S hS
  exact high_factor_level_budget hThue Q f hf hirr hd hdu hdiv h hh S hS
example : CF15SelectedFactorLevelBudget := by
  intro hThue Q hdispatch h hh S hS
  exact selected_factor_level_budget hThue Q hdispatch h hh S hS
example : CF15ActualGraphLevelBudget := by
  intro hThue X D A B hX hg hd inverse Q h hh S hS
  exact actual_graph_level_budget hThue X D A B hX hg hd inverse h hh S hS

-- Unit negative levels keep both signs and pay no prime-support exponent.
example (hThue : StewartPrimitiveThue) (Q : SourcePolynomial) (f : Polynomial ℤ)
    (hf : f.IsPrimitive) (hi : Irreducible (rationalPolynomial f))
    (hd : 3≤f.natDegree) (hu : f.natDegree≤11) (hdiv : f.homogenize f.natDegree ∣ Q)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=(-1:ℤ)) :
    S.card≤61600 := by
  simpa [divisorCount,primeSupportCount] using
    high_factor_level_budget hThue Q f hf hi hd hu hdiv (-1) (by decide) S hS
example (hThue : StewartPrimitiveThue) (Q : SourcePolynomial) (hQ : binaryFactorDispatch Q)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=(-1:ℤ)) :
    S.card≤61616 := by
  simpa [divisorCount,primeSupportCount] using
    selected_factor_level_budget hThue Q hQ (-1) (by decide) S hS
-- The high-factor branch cannot substitute degree one or two.
example : ¬ 3≤(Polynomial.X:Polynomial ℤ).natDegree := by simp
example : ¬ 3≤((Polynomial.X:Polynomial ℤ)^2).natDegree := by simp
-- A scalar multiple of a cubic is not automatically primitive.
example : ¬ (Polynomial.C 2*(Polynomial.X:Polynomial ℤ)^3).IsPrimitive := by
  intro hp
  have hu := hp 2 (by exact ⟨Polynomial.X^3,rfl⟩)
  rcases Int.isUnit_eq_one_or hu with h | h <;> norm_num at h

end
end P0365Subquarter
