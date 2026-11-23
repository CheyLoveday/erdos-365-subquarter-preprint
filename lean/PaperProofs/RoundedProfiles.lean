import PaperTargets.RoundedProfiles
import PaperProofs.ExactProfiles
import Mathlib.Algebra.Order.Floor.Semifield

/-! Numerical CF16/CF17 application bridge. All constants are fixed before
profiles; no actual determinant estimate or prime assignment is asserted. -/
namespace P0365Subquarter

set_option autoImplicit false

private theorem eventual_power_gt (c t : ℝ) (ht : 0 < t) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → c < x ^ t := by
  let b := max 1 (c + 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨max 1 (b ^ t⁻¹), le_max_left _ _, ?_⟩
  intro x hx
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hb _)
    ((le_max_right 1 (b ^ t⁻¹)).trans hx) ht.le
  rw [Real.rpow_inv_rpow hb ht.ne'] at hh
  have hc : c < b := by have h := le_max_right 1 (c + 1); dsimp [b]; linarith
  exact hc.trans_le hh

theorem rounded_height_bounds : CF16RoundedHeightBounds := by
  intro x ψ δ hx h0 h2 hd
  let m := (1 + δ) * profileM0 ψ
  have hm : 0 ≤ m := mul_nonneg (by linarith) (profile_bounds ψ h0 h2).1
  have hy : 1 ≤ x ^ m := Real.one_le_rpow hx hm
  change 1 ≤ (Nat.ceil (x ^ m) : ℝ) ∧ x ^ m ≤ (Nat.ceil (x ^ m) : ℝ) ∧
    (Nat.ceil (x ^ m) : ℝ) ≤ 2 * x ^ m
  exact ⟨hy.trans (Nat.le_ceil _), Nat.le_ceil _, Nat.ceil_le_two_mul (by linarith)⟩

private theorem scale_pos (x ψ δ : ℝ) (hx : 1 ≤ x)
    (h0 : 0 ≤ ψ) (h2 : ψ ≤ 2 / 3) (hd : 0 ≤ δ) :
    0 < roundedScale x ψ δ := by
  have hm := (rounded_height_bounds x ψ δ hx h0 h2 hd).1
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)

theorem rounded_prime_scale : CF17RoundedPrimeScale := by
  intro δ hd
  obtain ⟨x₀, hx₀, hgrow⟩ := eventual_power_gt 2 ((13 / 16 : ℝ) * δ) (by positivity)
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx ψ h0 h2
  have hx1 : 1 ≤ x := hx₀.trans hx
  have hxpos : 0 < x := by linarith
  let m := (1 + δ) * profileM0 ψ
  let q := profileTheta + δ - m
  let M : ℝ := roundedHeight x ψ δ
  have hM := rounded_height_bounds x ψ δ hx1 h0 h2 hd.le
  have hMpos : 0 < M := by have h := hM.1; dsimp [M]; linarith
  have hq := (unrounded_slack ψ δ h0 h2 hd).1
  have hpow : x ^ profileRho * x ^ ((13 / 16 : ℝ) * δ) ≤ x ^ q := by
    rw [← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hq
  have hg := mul_lt_mul_of_pos_left (hgrow x hx) (Real.rpow_pos_of_pos hxpos profileRho)
  have hlow : x ^ q / 2 ≤ roundedScale x ψ δ := by
    change x ^ q / 2 ≤ x ^ (profileTheta + δ) / M
    apply (le_div_iff₀ hMpos).2
    have hu := mul_le_mul_of_nonneg_left hM.2.2
      (show 0 ≤ x ^ q / 2 by positivity)
    have hid : x ^ q * x ^ m = x ^ (profileTheta + δ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      dsimp [q]
      ring
    change x ^ q / 2 * M ≤ x ^ (profileTheta + δ)
    calc
      x ^ q / 2 * M ≤ x ^ q / 2 * (2 * x ^ m) := hu
      _ = x ^ q * x ^ m := by ring
      _ = x ^ (profileTheta + δ) := hid
  have hh : x ^ profileRho ≤ x ^ q / 2 := by nlinarith
  exact hh.trans hlow

private theorem term_scale_identity (x ψ δ : ℝ) (hx : 0 < x)
    (hM : 0 < (roundedHeight x ψ δ : ℝ)) (k : Fin 5) :
    roundedMixedTerm x ψ δ k =
      (x ^ (profileW ψ - (k.val : ℝ) - 28 * (profileTheta + δ)) *
        (roundedHeight x ψ δ : ℝ) ^ (28 - (profileErrorWeight k : ℝ))) *
      roundedScale x ψ δ ^ (28 : ℕ) := by
  let M : ℝ := roundedHeight x ψ δ
  let s := profileTheta + δ
  let b := profileW ψ - (k.val : ℝ)
  let a : ℝ := profileErrorWeight k
  let γ := 28 - a
  have hr : roundedScale x ψ δ ^ (28 : ℕ) = x ^ (28 * s) / M ^ (28 : ℝ) := by
    change (x ^ s / M) ^ (28 : ℕ) = _
    rw [← Real.rpow_natCast (x ^ s / M) 28,
      Real.div_rpow (Real.rpow_nonneg hx.le _) hM.le, ← Real.rpow_mul hx.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm s (28 : ℝ)]
  have hxb : x ^ (b - 28 * s) * x ^ (28 * s) = x ^ b := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hMa : M ^ γ / M ^ (28 : ℝ) = M ^ (-a) := by
    rw [← Real.rpow_sub hM]
    congr 1
    dsimp [γ]
    ring
  change x ^ b / M ^ a = (x ^ (b - 28 * s) * M ^ γ) * _
  calc
    x ^ b / M ^ a = x ^ b * M ^ (-a) := by rw [Real.rpow_neg hM.le, div_eq_mul_inv]
    _ = (x ^ (b - 28 * s) * x ^ (28 * s)) * (M ^ γ / M ^ (28 : ℝ)) := by
      rw [hxb, hMa]
    _ = (x ^ (b - 28 * s) * M ^ γ) * (x ^ (28 * s) / M ^ (28 : ℝ)) := by ring
    _ = (x ^ (b - 28 * s) * M ^ γ) * roundedScale x ψ δ ^ (28 : ℕ) := by rw [hr]

theorem rounded_mixed_term_bound : CF17RoundedMixedTermBound := by
  intro x ψ δ hx h0 h2 hd k
  have hxpos : 0 < x := by linarith
  let M : ℝ := roundedHeight x ψ δ
  let m := (1 + δ) * profileM0 ψ
  let a : ℝ := profileErrorWeight k
  let γ := 28 - a
  let b := profileW ψ - (k.val : ℝ)
  let s := profileTheta + δ
  have hM := rounded_height_bounds x ψ δ hx h0 h2 hd.le
  have hMpos : 0 < M := by have h := hM.1; dsimp [M]; linarith
  have hg : 0 ≤ γ ∧ γ ≤ 16 := by
    fin_cases k <;> norm_num [γ, a, profileErrorWeight]
  have hp : M ^ γ ≤ (2 : ℝ) ^ γ * x ^ (m * γ) := by
    have hh := Real.rpow_le_rpow hMpos.le hM.2.2 hg.1
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hxpos.le _),
      ← Real.rpow_mul hxpos.le] at hh
    exact hh
  have htwo : (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (16 : ℕ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hg.2
  have he : b - 28 * s + m * γ ≤ -(25 * δ) := by
    have hh := ((unrounded_slack ψ δ h0 h2 hd).2.2.2.1 k).1
    dsimp [b, s, m, γ, a]
    nlinarith
  have hc : x ^ (b - 28 * s) * M ^ γ ≤
      (2 : ℝ) ^ (16 : ℕ) * x ^ (-(25 * δ)) := by
    calc
      x ^ (b - 28 * s) * M ^ γ ≤
          x ^ (b - 28 * s) * ((2 : ℝ) ^ γ * x ^ (m * γ)) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hxpos.le _)
      _ = (2 : ℝ) ^ γ * x ^ (b - 28 * s + m * γ) := by
        rw [Real.rpow_add hxpos]
        ring
      _ ≤ (2 : ℝ) ^ (16 : ℕ) * x ^ (-(25 * δ)) :=
        mul_le_mul htwo (Real.rpow_le_rpow_of_exponent_le hx he)
          (Real.rpow_nonneg hxpos.le _) (by positivity)
  rw [term_scale_identity x ψ δ hxpos hMpos k]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg (scale_pos x ψ δ hx h0 h2 hd.le).le 28)

theorem rounded_error_absorption : CF17RoundedErrorAbsorption := by
  intro δ C hd hC
  obtain ⟨x₀, hx₀, hgrow⟩ := eventual_power_gt (5 * C * (2 : ℝ) ^ (16 : ℕ))
    (25 * δ) (by positivity)
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx ψ h0 h2
  have hx1 : 1 ≤ x := hx₀.trans hx
  have hxpos : 0 < x := by linarith
  have hr := scale_pos x ψ δ hx1 h0 h2 hd.le
  have hsum : (∑ k : Fin 5, roundedMixedTerm x ψ δ k) ≤
      5 * ((2 : ℝ) ^ (16 : ℕ) * x ^ (-(25 * δ)) * roundedScale x ψ δ ^ (28 : ℕ)) := by
    calc
      _ ≤ ∑ _k : Fin 5,
          (2 : ℝ) ^ (16 : ℕ) * x ^ (-(25 * δ)) * roundedScale x ψ δ ^ (28 : ℕ) :=
        Finset.sum_le_sum (fun k _ => rounded_mixed_term_bound x ψ δ hx1 h0 h2 hd k)
      _ = _ := by simp
  have hratio : 5 * C * (2 : ℝ) ^ (16 : ℕ) / x ^ (25 * δ) < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hxpos _)).2 (hgrow x hx)
  calc
    C * (∑ k : Fin 5, roundedMixedTerm x ψ δ k) ≤
        C * (5 * ((2 : ℝ) ^ (16 : ℕ) * x ^ (-(25 * δ)) *
          roundedScale x ψ δ ^ (28 : ℕ))) := mul_le_mul_of_nonneg_left hsum hC
    _ = (5 * C * (2 : ℝ) ^ (16 : ℕ) / x ^ (25 * δ)) *
        roundedScale x ψ δ ^ (28 : ℕ) := by rw [Real.rpow_neg hxpos.le]; ring
    _ < 1 * roundedScale x ψ δ ^ (28 : ℕ) :=
      mul_lt_mul_of_pos_right hratio (pow_pos hr 28)
    _ = roundedScale x ψ δ ^ (28 : ℕ) := one_mul _

end P0365Subquarter
