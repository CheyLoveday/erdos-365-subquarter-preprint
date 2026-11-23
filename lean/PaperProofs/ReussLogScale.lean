import PaperTargets.ReussLogScale
import PaperProofs.ResidualProfiles
import PaperProofs.RoundedProfiles

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Existing ceiling bounds leave half the construction slack to pay fixed
logarithmic errors uniformly over every compact residual profile. -/
theorem rounded_log_slack : CF04RoundedLogSlack := by
  intro δ κ hδ hδ₁ hκ
  let c : ℝ := (9/32)*profileTheta^2
  have hc : 0<c := by norm_num [c,profileTheta]
  let C : ℝ := 2*κ+κ^2
  have hC : 0≤C := by dsimp [C]; positivity
  let A : ℝ := max 1 (max (2*Real.log 2) (4*C/(δ*c)))
  refine ⟨max 32 (Real.exp A),le_max_left _ _,?_⟩
  intro X hX ψ hlo hhi
  have hX₃₂ : 32≤X := (le_max_left _ _).trans hX
  have hX₁ : 1≤X := by linarith
  have hXp : 0<X := by linarith
  have hLA : A≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos A) ((le_max_right _ _).trans hX)
    simpa only [Real.log_exp] using hh
  have hL₁ : 1≤Real.log X := (le_max_left _ _).trans hLA
  have hL : 0<Real.log X := by linarith
  have hL₂ : 2*Real.log 2≤Real.log X :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hLA
  have hpay : 4*C≤Real.log X*(δ*c) := by
    apply (div_le_iff₀ (mul_pos hδ hc)).mp
    exact (le_trans (le_max_right _ _) (le_max_right _ _)).trans hLA
  have ht : 0<profileTheta := by norm_num [profileTheta]
  have hψ₀ : 0≤ψ := by linarith
  have hψ₂ : ψ≤2/3 := by linarith
  have hψ₁ : ψ≤1 := by linarith
  let q : ℝ := 1-(3/2)*ψ
  have hqlo : profileTheta/2≤q := by dsimp [q]; linarith
  have hq₀ : 0≤q := by linarith
  have hq₁ : q≤1 := by dsimp [q]; linarith
  have hm₀ := profile_bounds ψ hψ₀ hψ₂
  have hclow : c≤profileM0 ψ := by
    have hh := mul_le_mul hlo hqlo (by positivity : (0:ℝ)≤profileTheta/2) hψ₀
    dsimp [c,profileM0]
    dsimp [q] at hh
    nlinarith only [hh]
  let m : ℝ := (1+δ)*profileM0 ψ
  have hmlo : c≤m := by
    dsimp [m]
    nlinarith only [hclow,mul_nonneg hδ.le hm₀.1]
  have hmhi : m≤3/8 := by
    have hh := mul_le_mul_of_nonneg_right hδ₁ hm₀.1
    dsimp [m]
    nlinarith only [hh,hm₀.2.1]
  obtain ⟨hM₁,hMlo,hMhi⟩ := rounded_height_bounds X ψ δ hX₁ hψ₀ hψ₂ hδ.le
  have hMpos : (0:ℝ)<roundedHeight X ψ δ := by linarith
  have hloglo := Real.log_le_log (Real.rpow_pos_of_pos hXp m) hMlo
  rw [Real.log_rpow hXp] at hloglo
  have hloghi := Real.log_le_log hMpos hMhi
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hXp m).ne',
    Real.log_rpow hXp] at hloghi
  have hlogMlo : c*Real.log X≤Real.log (roundedHeight X ψ δ:ℝ) :=
    (mul_le_mul_of_nonneg_right hmlo hL.le).trans hloglo
  have hlogMhi : Real.log (roundedHeight X ψ δ:ℝ)≤Real.log X := by
    have hh := mul_le_mul_of_nonneg_right hmhi hL.le
    linarith
  let a : ℝ := (9/8)*(1+δ/2)
  have ha₀ : 0≤a := by dsimp [a]; positivity
  have ha₂ : a≤2 := by dsimp [a]; linarith
  have hproduct : (ψ*Real.log X+κ)*(q*Real.log X+κ)/Real.log X≤
      ψ*q*Real.log X+C := by
    have hsum : ψ+q≤2 := by linarith
    have hh := mul_le_mul_of_nonneg_right hsum (mul_nonneg hκ hL.le)
    have hk := mul_le_mul_of_nonneg_left hL₁ (sq_nonneg κ)
    apply (div_le_iff₀ hL).mpr
    dsimp [C]
    nlinarith only [hh,hk]
  have hcost : a*C≤(δ/2)*profileM0 ψ*Real.log X := by
    calc
      a*C ≤ 2*C := mul_le_mul_of_nonneg_right ha₂ hC
      _ ≤ (δ/2)*c*Real.log X := by nlinarith only [hpay]
      _ ≤ (δ/2)*profileM0 ψ*Real.log X :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hclow (by positivity)) hL.le
  refine ⟨hlogMlo,hlogMhi,?_⟩
  change a*((ψ*Real.log X+κ)*(q*Real.log X+κ)/Real.log X)≤_
  calc
    _ ≤ a*(ψ*q*Real.log X+C) := mul_le_mul_of_nonneg_left hproduct ha₀
    _ ≤ m*Real.log X := by
      dsimp [a,q,m,profileM0] at hcost ⊢
      nlinarith only [hcost]
    _ ≤ Real.log (roundedHeight X ψ δ:ℝ) := hloglo

private theorem multiplier_product_log (X B E : ℝ) (hX : 0<X) (hB : 0<B) (hE : 0<E) :
    Real.log (reussMultiplierScale X B*reussMultiplierScale X E)=
      Real.log X-(3/2)*Real.log (B*E) := by
  have hXB : 0<reussMultiplierScale X B := by
    dsimp [reussMultiplierScale]; positivity
  have hXE : 0<reussMultiplierScale X E := by
    dsimp [reussMultiplierScale]; positivity
  rw [Real.log_mul hXB.ne' hXE.ne']
  dsimp [reussMultiplierScale]
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_rpow hX,Real.log_rpow hB,Real.log_rpow hE,
    Real.log_mul hB.ne' hE.ne']
  ring

/-- Actual residual boxes supply both comparable product logarithms at the
prescribed coupled scales and the same uniform rounded-M/slack threshold. -/
theorem actual_reuss_log_scale : CF04ActualReussLogScale := by
  intro δ κ hδ hδ₁ hκ
  obtain ⟨X₁,hX₁,hslack⟩ := rounded_log_slack δ κ hδ hδ₁ hκ
  obtain ⟨X₂,hX₂,hprofile⟩ := residual_compact_profile
  refine ⟨max X₁ X₂,hX₁.trans (le_max_left _ _),?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  have hX₁' := (le_max_left _ _).trans hX
  have hX₂' := (le_max_right _ _).trans hX
  have hXp : 0<X := by linarith
  have hL : 0<Real.log X := Real.log_pos (by linarith)
  obtain ⟨ψ,hBE,hψlo,hψhi,hqlo,_⟩ :=
    hprofile X hX₂' B E hB hE n b d u v hs hbox hbd hq
  obtain ⟨hMlo,hMhi,hbudget⟩ := hslack X hX₁' ψ hψlo hψhi
  have hlogBE : Real.log (B*E)=ψ*Real.log X := by
    rw [hBE,Real.log_rpow hXp]
  have hlogUV : Real.log (reussMultiplierScale X B*reussMultiplierScale X E)=
      (1-(3/2)*ψ)*Real.log X := by
    rw [multiplier_product_log X B E hXp hB hE,hlogBE]
    ring
  have ht : 0<profileTheta := by norm_num [profileTheta]
  have hψ₀ : 0≤ψ := by linarith
  have hψ₁ : ψ≤1 := by linarith
  refine ⟨ψ,hBE,hψlo,hψhi,?_,?_,?_,?_,hMlo,hMhi,?_⟩
  · rw [hlogBE]
    exact mul_le_mul_of_nonneg_right hψlo hL.le
  · rw [hlogBE]
    simpa using mul_le_mul_of_nonneg_right hψ₁ hL.le
  · rw [hlogUV]
    exact mul_le_mul_of_nonneg_right hqlo hL.le
  · rw [hlogUV]
    have hh : 1-(3/2)*ψ≤1 := by linarith
    simpa using mul_le_mul_of_nonneg_right hh hL.le
  · rwa [hlogBE,hlogUV]

end
end P0365Subquarter
