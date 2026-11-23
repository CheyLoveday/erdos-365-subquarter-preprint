import PaperProofs.RulingCounts

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print multiplierCubic
#print CF15MultiplierCubicAdmissibility
#print CF15FixedMultiplierRatioCount
#print CF15FixedKernelRatioCount
#print CF15CoordinateRulingCount
#print CF15RulingLogSubpower
#print CF15CoordinateRulingSubpower
#check (multiplier_cubic_admissibility : CF15MultiplierCubicAdmissibility)
#check (fixed_multiplier_ratio_count : CF15FixedMultiplierRatioCount)
#check (fixed_kernel_ratio_count : CF15FixedKernelRatioCount)
#check (coordinate_ruling_count : CF15CoordinateRulingCount)
#check (ruling_log_subpower : CF15RulingLogSubpower)
#check (coordinate_ruling_subpower : CF15CoordinateRulingSubpower)
#print axioms multiplier_cubic_admissibility
#print axioms fixed_multiplier_ratio_count
#print axioms fixed_kernel_ratio_count
#print axioms coordinate_ruling_count
#print axioms ruling_log_subpower
#print axioms coordinate_ruling_subpower
set_option pp.all false

example : CF15MultiplierCubicAdmissibility := by
  intro u v hu hv hcop f
  exact multiplier_cubic_admissibility u v hu hv hcop
example : CF15FixedMultiplierRatioCount := by
  intro hThue q S hS
  exact fixed_multiplier_ratio_count hThue q S hS
example : CF15FixedKernelRatioCount := by
  intro q N S hS
  exact fixed_kernel_ratio_count q N S hS
example : CF15CoordinateRulingCount := by
  intro hThue i q N S hS
  exact coordinate_ruling_count hThue i q N S hS
example : CF15RulingLogSubpower := by
  intro ε hε
  exact ruling_log_subpower ε hε
example : CF15CoordinateRulingSubpower := by
  intro hThue ε hε
  exact coordinate_ruling_subpower hThue ε hε

-- A reducible cubic remains admissible: no irreducibility premise was added.
example : (rationalPolynomial (multiplierCubic 1 1)).Separable := by
  obtain ⟨_,_,_,hs,_⟩ := multiplier_cubic_admissibility 1 1 (by decide) (by decide) (by decide)
  exact hs
example : rationalPolynomial (multiplierCubic 1 1)=
    (1-Polynomial.X)*(1+Polynomial.X+(Polynomial.X:Polynomial ℚ)^2) := by
  simp only [rationalPolynomial,multiplierCubic,map_pow]
  norm_num
  ring
-- Zero multipliers lose the necessary degree/separability conditions.
example : (multiplierCubic 0 1).natDegree=0 := by simp [multiplierCubic]
example : ¬ (rationalPolynomial (multiplierCubic 1 0)).Separable := by
  intro hs
  have h := Polynomial.Separable.eval₂_derivative_ne_zero (RingHom.id ℚ) hs (x:=0)
    (by norm_num [rationalPolynomial,multiplierCubic])
  norm_num [rationalPolynomial,multiplierCubic] at h
-- The genuine8/9 source gives cubic level1 at the positive primitive kernel.
example : MvPolynomial.eval ![(2:ℤ),1]
    ((multiplierCubic 1 3).homogenize (multiplierCubic 1 3).natDegree)=1 := by
  obtain ⟨_,_,_,_,he⟩ := multiplier_cubic_admissibility 1 3 (by decide) (by decide) (by decide)
  simpa using he 2 1
-- The natural cutoff includes zero; both coordinates share the same envelope.
example : Nat.log 2 (2*0+1)=0 := by decide
example (hThue : StewartPrimitiveThue) (i : Fin 2) (q : ℚ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, n≤0 ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧ sourcePoint b d u v i=q) :
    S.card≤8401 := by
  simpa using coordinate_ruling_count hThue i q 0 S hS

end
end P0365Subquarter
