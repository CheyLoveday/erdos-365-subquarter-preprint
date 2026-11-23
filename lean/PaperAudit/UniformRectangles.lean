import PaperProofs.UniformRectangles

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04UniformRectangleSlack
#print CF04ActualUniformMinorVanishing
#check (uniform_rectangle_slack : CF04UniformRectangleSlack)
#check (actual_uniform_minor_vanishing : CF04ActualUniformMinorVanishing)
#print axioms uniform_rectangle_slack
#print axioms actual_uniform_minor_vanishing
set_option pp.all false

example : CF04UniformRectangleSlack := by
  intro δ c₀ hδ hδ₁ hc₀ hc₀₁
  exact uniform_rectangle_slack δ c₀ hδ hδ₁ hc₀ hc₀₁
example : CF04ActualUniformMinorVanishing := by
  intro δ hδ hδ₁
  exact actual_uniform_minor_vanishing δ hδ hδ₁

-- An explicit nonempty numeric budget: S=T=B/8,a=B/2,delta=1/2,c0=1/8.
-- Degree choices precede the coefficient family and the eventual B threshold.
example : ∃ C Amax : ℕ, 1≤C ∧ ∃ B₀ : ℝ, 1≤B₀ ∧
    ∀ B : ℝ, B₀≤B → ∃ A : ℕ, A≤Amax ∧
      Real.exp (((Fintype.card (RectangularIndex A C):ℝ)/2)*
        ((A:ℝ)*(B/8)+(C:ℝ)*(B/8))-
        latticeDeterminantLower (Fintype.card (RectangularIndex A C)) (B/2) B)<1 := by
  obtain ⟨C,Amax,hC,hconstants⟩ := uniform_rectangle_slack (1/2) (1/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B₀,hB₀,hbound⟩ := hconstants (fun _ => 1) (by intros; norm_num)
  refine ⟨C,Amax,hC,B₀,hB₀,?_⟩
  intro B hB
  have hBp : 0<B := by linarith
  obtain ⟨A,hA,hstrict⟩ := hbound B (B/8) (B/8) (B/2) hB
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by nlinarith [sq_nonneg B])
  exact ⟨A,hA,by simpa only [one_mul] using hstrict⟩

end
end P0365Subquarter
