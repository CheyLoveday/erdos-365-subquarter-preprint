import PaperTargets.UpperHeightSources
import PaperProofs.ReussLogScale

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem multiplier_square (X S : ℝ) (hX : 0<X) (hS : 0<S) :
    (reussMultiplierScale X S)^2*S^3=X := by
  dsimp [reussMultiplierScale]
  rw [div_pow,←Real.rpow_mul_natCast hX.le (1/2) 2,
    ←Real.rpow_mul_natCast hS.le (3/2) 2]
  norm_num
  field_simp

private theorem multiplier_range (X S N a w : ℝ) (hX : 0<X) (hS : 0<S)
    (hN : X≤N) (hN' : N≤3*X) (ha : S≤a) (ha' : a≤2*S)
    (hw : 1≤w) (he : N=a^3*w^2) :
    1/2≤reussMultiplierScale X S ∧ reussMultiplierScale X S/4≤w ∧
      w≤2*reussMultiplierScale X S := by
  let W : ℝ := reussMultiplierScale X S
  have hW : 0<W := by dsimp [W,reussMultiplierScale]; positivity
  have hw₀ : 0≤w := by linarith
  have hS₃ : 0<S^3 := pow_pos hS _
  have hscale : W^2*S^3=X := multiplier_square X S hX hS
  have hlo : X≤8*S^3*w^2 := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (lt_of_lt_of_le hS ha).le ha' 3) (sq_nonneg w)
    rw [←he] at hh
    nlinarith only [hN,hh]
  have hhi : S^3*w^2≤3*X := by
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS.le ha 3) (sq_nonneg w)
    rw [←he] at hh
    exact hh.trans hN'
  have hW₈ : W^2≤8*w^2 := by
    apply (mul_le_mul_iff_right₀ hS₃).mp
    nlinarith only [hscale,hlo]
  have hw₃ : w^2≤3*W^2 := by
    apply (mul_le_mul_iff_right₀ hS₃).mp
    nlinarith only [hscale,hhi]
  have hwW : w≤2*W := by
    apply (pow_le_pow_iff_left₀ hw₀ (by positivity : 0≤2*W) (by decide : (2:ℕ)≠0)).mp
    nlinarith only [hw₃,sq_nonneg W]
  have hWw : W≤4*w := by
    apply (pow_le_pow_iff_left₀ hW.le (by positivity : 0≤4*w) (by decide : (2:ℕ)≠0)).mp
    nlinarith only [hW₈,sq_nonneg w]
  exact ⟨by linarith,by linarith,hwW⟩

/-- Original equations and inclusive boxes supply constant-factor multiplier
ranges; actual integer positivity controls every nominal lower scale. -/
theorem actual_multiplier_ranges : CF04ActualMultiplierRanges := by
  intro X B E hX hB hE n b d u v hs hbox
  rcases hbox with ⟨hXn,hn,hb,hb',hd,hd'⟩
  have hXp : 0<X := by linarith
  have hb₁ : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by have hh:=hs.1; omega)
  have hd₁ : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by have hh:=hs.2.1; omega)
  have hu₁ : (1:ℝ)≤u := by exact_mod_cast (show 1≤u by have hh:=hs.2.2.1; omega)
  have hv₁ : (1:ℝ)≤v := by exact_mod_cast (show 1≤v by have hh:=hs.2.2.2.1; omega)
  have he₀ : (n:ℝ)=(b:ℝ)^3*(u:ℝ)^2 := by exact_mod_cast hs.2.2.2.2.2.2.1
  have he₁ : (n:ℝ)+1=(d:ℝ)^3*(v:ℝ)^2 := by
    exact_mod_cast (additive_and_integer_source n b d u v hs).2.1
  obtain ⟨hU,hu,hu'⟩ := multiplier_range X B n b u hXp hB hXn (by linarith) hb hb' hu₁ he₀
  obtain ⟨hV,hv,hv'⟩ := multiplier_range X E ((n:ℝ)+1) d v hXp hE
    (by linarith) (by linarith) hd hd' hv₁ he₁
  exact ⟨by linarith,by linarith,hU,hV,hu,hu',hv,hv'⟩

private theorem four_times_log_product (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Real.log ((4*a)*(4*b))=Real.log (a*b)+Real.log 16 := by
  have he : (4*a)*(4*b)=16*(a*b) := by ring
  rw [he,Real.log_mul (by norm_num : (16:ℝ)≠0) (mul_pos ha hb).ne']
  ring

/-- The fixed product factor16 is paid by the proved Reuss log/slack budget.
Only nominal scales retain coupling; upper-height determinant assembly is open. -/
theorem actual_upper_height_log_budget : CF04ActualUpperHeightLogBudget := by
  intro δ hδ hδ₁
  obtain ⟨X₀,hX₀,hactual⟩ := actual_reuss_log_scale δ (Real.log 16) hδ hδ₁
    (Real.log_nonneg (by norm_num))
  refine ⟨X₀,hX₀,?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  have hX₁ : 1≤X := by linarith
  obtain ⟨ψ,hBE,hψlo,hψhi,_,_,_,_,hMlo,hMhi,hbudget⟩ :=
    hactual X hX B E hB hE n b d u v hs hbox hbd hq
  obtain ⟨hBh,hEh,hUh,hVh,_,hu,_,hv⟩ :=
    actual_multiplier_ranges X B E hX₁ hB hE n b d u v hs hbox
  rcases hbox with ⟨_,_,_,hb,_,hd⟩
  refine ⟨ψ,hBE,hψlo,hψhi,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith,by linarith,hMlo,hMhi,?_⟩
  rw [four_times_log_product B E hB hE,
    four_times_log_product (reussMultiplierScale X B) (reussMultiplierScale X E)
      (by linarith) (by linarith)]
  exact hbudget

end
end P0365Subquarter
