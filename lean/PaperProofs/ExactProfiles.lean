import PaperTargets.ExactProfiles
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! CF16 real algebra. No calculus, grid extension, Pell, external premise,
rounded height or source-count assertion. -/
namespace P0365Subquarter

set_option autoImplicit false

private theorem m0_square_identity (ψ : ℝ) :
    3 / 16 - profileM0 ψ = (3 / 16) * (3 * ψ - 1) ^ 2 := by
  unfold profileM0
  ring

private theorem error_gap_bounds (k : Fin 5) :
    0 ≤ (28 : ℝ) - (profileErrorWeight k : ℝ) ∧
      (28 : ℝ) - (profileErrorWeight k : ℝ) ≤ 16 := by
  fin_cases k <;> norm_num [profileErrorWeight]

theorem profile_bounds : CF16ProfileBounds := by
  intro ψ h0 h2
  have hf : 0 ≤ 1 - (3 / 2 : ℝ) * ψ := by linarith
  have hn : 0 ≤ profileM0 ψ :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 8) h0) hf
  have hu : profileM0 ψ ≤ 3 / 16 := by
    nlinarith only [sq_nonneg (3 * ψ - 1), m0_square_identity ψ]
  exact ⟨hn, hu, lt_of_le_of_lt hu (by norm_num [profileTheta])⟩

theorem chart_branches : CF16ChartBranches := by
  intro ψ
  constructor
  · intro h
    unfold profileW
    apply min_eq_left
    unfold profileCentre at h
    linarith
  · intro h
    unfold profileW
    apply min_eq_right
    unfold profileCentre at h
    linarith

theorem centre_values : CF16CentreValues := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [profileM0, profileCentre]
  · norm_num [profileW, profileCentre]
  · intro k
    fin_cases k <;> norm_num [profileBranch, profileW, profileCentre,
      profileM0, profileErrorWeight, profileCentreValue]
  · norm_num [profileBranch, profileW, profileCentre,
      profileM0, profileErrorWeight, profileTheta]

private theorem centre_branch_le (k : Fin 5) :
    profileBranch profileCentre k ≤ profileTheta := by
  rw [centre_values.2.2.1 k]
  fin_cases k <;> norm_num [profileCentreValue, profileTheta]

theorem profile_envelope : CF16Envelope := by
  intro ψ _h0 _h2 k
  let γ : ℝ := 28 - (profileErrorWeight k : ℝ)
  have hg0 : 0 ≤ γ := (error_gap_bounds k).1
  have hg16 : γ ≤ 16 := (error_gap_bounds k).2
  have hc := centre_branch_le k
  by_cases h : ψ ≤ profileCentre
  · have hw := (chart_branches ψ).1 h
    have ht : -(9 : ℝ) / 40 ≤ 9 / 20 - 27 * ψ / 16 := by
      unfold profileCentre at h
      linarith
    have hb : (12 : ℝ) / 5 ≤ 6 + γ * (9 / 20 - 27 * ψ / 16) := by
      have hh := mul_le_mul_of_nonneg_left ht hg0
      nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr h)
      (le_trans (by norm_num : (0 : ℝ) ≤ 12 / 5) hb)
    have hid : profileBranch profileCentre k - profileBranch ψ k =
        (profileCentre - ψ) * (6 + γ * (9 / 20 - 27 * ψ / 16)) / 28 := by
      dsimp only [profileBranch]
      rw [centre_values.2.1, hw]
      dsimp [profileM0, profileCentre, γ]
      ring
    have hh := div_nonneg hprod (by norm_num : (0 : ℝ) ≤ 28)
    rw [← hid] at hh
    linarith
  · have hright : profileCentre ≤ ψ := le_of_lt (lt_of_not_ge h)
    have hw := (chart_branches ψ).2 hright
    have ht : 9 / 20 - 27 * ψ / 16 ≤ (0 : ℝ) := by
      unfold profileCentre at hright
      linarith
    have hb : (14 : ℝ) ≤ 14 - γ * (9 / 20 - 27 * ψ / 16) := by
      have hh := mul_nonpos_of_nonneg_of_nonpos hg0 ht
      linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hright)
      (le_trans (by norm_num : (0 : ℝ) ≤ 14) hb)
    have hid : profileBranch profileCentre k - profileBranch ψ k =
        (ψ - profileCentre) * (14 - γ * (9 / 20 - 27 * ψ / 16)) / 28 := by
      dsimp only [profileBranch]
      rw [centre_values.2.1, hw]
      dsimp [profileM0, profileCentre, γ]
      ring
    have hh := div_nonneg hprod (by norm_num : (0 : ℝ) ≤ 28)
    rw [← hid] at hh
    linarith

theorem unrounded_slack : CF16UnroundedSlack := by
  intro ψ δ h0 h2 hd
  let m := (1 + δ) * profileM0 ψ
  let q := profileTheta + δ - m
  change profileRho + (13 / 16) * δ ≤ q ∧ 0 < q ∧ 0 < 25 * δ ∧
    (∀ k : Fin 5,
      25 * δ ≤ 28 * q - (profileW ψ - (k.val : ℝ) -
        (profileErrorWeight k : ℝ) * m) ∧
      0 < 28 * q - (profileW ψ - (k.val : ℝ) -
        (profileErrorWeight k : ℝ) * m)) ∧ m + q = profileTheta + δ
  have hm0 := profile_bounds ψ h0 h2
  have hq : profileRho + (13 / 16) * δ ≤ q := by
    have hh := mul_nonneg (by linarith : 0 ≤ 1 + δ) (sub_nonneg.mpr hm0.2.1)
    dsimp [q, m, profileTheta, profileRho]
    nlinarith
  have hqpos : 0 < q := by
    have hr : (0 : ℝ) < profileRho := by norm_num [profileRho]
    linarith
  have hd25 : 0 < 25 * δ := by linarith
  refine ⟨hq, hqpos, hd25, ?_, ?_⟩
  · intro k
    let γ : ℝ := 28 - (profileErrorWeight k : ℝ)
    have hg : γ ≤ 16 := (error_gap_bounds k).2
    have hb : γ * profileM0 ψ ≤ 3 := by
      have hh := mul_le_mul_of_nonneg_right hg hm0.1
      nlinarith [hm0.2.1]
    have he := profile_envelope ψ h0 h2 k
    have hres : 0 ≤ 28 * profileTheta -
        (profileW ψ - (k.val : ℝ) + γ * profileM0 ψ) := by
      dsimp [profileBranch] at he
      change 0 ≤ 28 * profileTheta -
        (profileW ψ - (k.val : ℝ) +
          (28 - (profileErrorWeight k : ℝ)) * profileM0 ψ)
      linarith
    have hid : 28 * q - (profileW ψ - (k.val : ℝ) -
        (profileErrorWeight k : ℝ) * m) =
        (28 * profileTheta - (profileW ψ - (k.val : ℝ) + γ * profileM0 ψ)) +
          δ * (28 - γ * profileM0 ψ) := by
      dsimp [q, m, γ]
      ring
    have hmargin : 25 * δ ≤ 28 * q - (profileW ψ - (k.val : ℝ) -
        (profileErrorWeight k : ℝ) * m) := by
      rw [hid]
      have hh := mul_nonneg hd.le (sub_nonneg.mpr hb)
      nlinarith
    exact ⟨hmargin, lt_of_lt_of_le hd25 hmargin⟩
  · dsimp [q]
    ring

theorem unrounded_strict_constraints : CF16UnroundedStrictConstraints := by
  intro ψ δ h0 h2 hd
  have hs := unrounded_slack ψ δ h0 h2 hd
  have hm0 := (profile_bounds ψ h0 h2).1
  refine ⟨mul_nonneg (by linarith : 0 ≤ 1 + δ) hm0, ?_, hs.2.2.2.2, ?_⟩
  · have hq := hs.1
    linarith
  · intro k
    have hh := (hs.2.2.2.1 k).2
    linarith

end P0365Subquarter
