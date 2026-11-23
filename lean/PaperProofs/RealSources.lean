import PaperTargets.RealSources
import PaperProofs.SmoothSources
import PaperProofs.RoundedProfiles

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem source_real_data (n b d u v : ℕ) (h : PairSource n b d u v) :
    0 < (n : ℝ) ∧ 0 < (b : ℝ) ∧ 0 < (d : ℝ) ∧ 0 < (u : ℝ) ∧ 0 < (v : ℝ) ∧
      (n : ℝ) = (b : ℝ)^3 * (u : ℝ)^2 ∧
      (d : ℝ)^3 * (v : ℝ)^2 = (n : ℝ) + 1 := by
  have hn := (additive_and_integer_source n b d u v h).1
  refine ⟨by exact_mod_cast hn, by exact_mod_cast h.1,
    by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1,
    by exact_mod_cast h.2.2.2.1, ?_, ?_⟩
  · exact_mod_cast h.2.2.2.2.2.2.1
  · have hh := h.2.2.2.2.2.2.2
    rw [← h.2.2.2.2.2.2.1] at hh
    exact_mod_cast hh

private theorem rpow_half_square (s : ℝ) (hs : 0 ≤ s) :
    (s ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = s ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

private theorem rpow_third_cube (t : ℝ) (ht : 0 ≤ t) :
    (t ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = t ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

/-- The exact additive source equation controls both real chart errors. -/
theorem actual_relative_errors : CF11ActualRelativeErrors := by
  intro n b d u v h
  obtain ⟨hn, hb, hd, hu, hv, hnid, heq⟩ := source_real_data n b d u v h
  let s : ℝ := (b : ℝ) / d
  let t : ℝ := (v : ℝ) / u
  have hs : 0 < s := div_pos hb hd
  have ht : 0 < t := div_pos hv hu
  have hrel : (n : ℝ) * t^2 = ((n : ℝ) + 1) * s^3 := by
    dsimp [s, t]
    field_simp
    nlinarith [heq]
  have hninv : 0 < 1 / (n : ℝ) := by positivity
  constructor
  · let r := t / s ^ (3 / 2 : ℝ)
    have hr : 0 < r := div_pos ht (Real.rpow_pos_of_pos hs _)
    have hr2 : r^2 = 1 + 1 / (n : ℝ) := by
      dsimp [r]
      rw [div_pow, rpow_half_square s hs.le]
      apply (div_eq_iff (ne_of_gt (pow_pos hs 3))).2
      apply (mul_left_cancel₀ hn.ne')
      calc
        (n : ℝ) * t^2 = ((n : ℝ) + 1) * s^3 := hrel
        _ = (n : ℝ) * ((1 + 1 / (n : ℝ)) * s^3) := by field_simp
    have hr1 : 1 ≤ r := by nlinarith
    change 0 ≤ r - 1 ∧ r - 1 ≤ 1 / (n : ℝ)
    constructor <;> nlinarith
  · let r := s / t ^ (2 / 3 : ℝ)
    have hr : 0 < r := div_pos hs (Real.rpow_pos_of_pos ht _)
    have hr3 : r^3 = (n : ℝ) / ((n : ℝ) + 1) := by
      dsimp [r]
      rw [div_pow, rpow_third_cube t ht.le]
      apply (div_eq_iff (ne_of_gt (pow_pos ht 2))).2
      apply (mul_left_cancel₀ (show (n : ℝ) + 1 ≠ 0 by positivity))
      calc
        ((n : ℝ) + 1) * s^3 = (n : ℝ) * t^2 := hrel.symm
        _ = ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) * t^2) := by field_simp
    have hrat : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).2 (by linarith)
    have hr1 : r ≤ 1 := by nlinarith [sq_nonneg (r - 1)]
    have hgap : 1 - r ≤ 1 / ((n : ℝ) + 1) := by
      have hh : 1 - r^3 = 1 / ((n : ℝ) + 1) := by rw [hr3]; field_simp; ring
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg r),
        mul_nonneg (sub_nonneg.mpr hr1) hr.le]
    have hrec : 1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) := by
      exact one_div_le_one_div_of_le hn (by linarith)
    change -(1 / (n : ℝ)) ≤ r - 1 ∧ r - 1 ≤ 0
    constructor <;> linarith

theorem actual_normalized_error : CF11ActualNormalizedError := by
  intro n b d u v h inverse a X ha hX hXn hz1 hz2
  have hn := (source_real_data n b d u v h).1
  have he : |realSourceError inverse b d u v| ≤ 1 / (n : ℝ) := by
    have hh := actual_relative_errors n b d u v h
    cases inverse <;> apply abs_le.2 <;> constructor <;> simp_all <;> linarith
  let z := realSourceCoordinate inverse b d u v / a
  have hz : 0 < z := by dsimp [z]; linarith
  have hell : realChartExponent inverse ≤ 2 := by cases inverse <;> norm_num [realChartExponent]
  have hp : |z ^ realChartExponent inverse| ≤ 4 := by
    rw [abs_of_nonneg (Real.rpow_nonneg hz.le _)]
    calc
      _ ≤ z ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz1 hell
      _ ≤ 4 := by rw [Real.rpow_two]; dsimp [z] at *; nlinarith
  have hrec : 1 / (n : ℝ) ≤ 1 / X := one_div_le_one_div_of_le hX hXn
  unfold realNormalizedError
  rw [abs_mul]
  calc
    _ ≤ 4 * (1 / (n : ℝ)) := mul_le_mul hp he (abs_nonneg _) (by norm_num)
    _ ≤ 4 / X := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrec (by norm_num : (0:ℝ) ≤ 4)

private theorem coordinate_pos (n b d u v : ℕ) (h : PairSource n b d u v)
    (inverse : Bool) : 0 < realSourceCoordinate inverse b d u v := by
  have hh := source_real_data n b d u v h
  cases inverse <;> simp only [realSourceCoordinate, Bool.false_eq_true, ite_false, ite_true]
  · exact div_pos hh.2.1 hh.2.2.1
  · exact div_pos hh.2.2.2.2.1 hh.2.2.2.1

private theorem real_row_identity (n b d u v : ℕ) (h : PairSource n b d u v)
    (inverse : Bool) (j : Fin 8) :
    (sourceIntegerRow inverse b d u v j : ℝ) =
      (sourceRowDenominator inverse d u : ℝ) *
        (realSourceCoordinate inverse b d u v ^ (j.val % 4) *
          (if j.val < 4 then 1 else realSourcePartner inverse b d u v)) := by
  have hd : (d : ℝ) ≠ 0 := ne_of_gt (source_real_data n b d u v h).2.2.1
  have hu : (u : ℝ) ≠ 0 := ne_of_gt (source_real_data n b d u v h).2.2.2.1
  cases inverse <;> fin_cases j <;>
    norm_num [sourceIntegerRow, sourceRowDenominator, realSourceCoordinate, realSourcePartner] <;>
    field_simp [hd, hu] <;> ring_nf <;> field_simp [hd, hu]

theorem actual_row_normalization : CF11ActualRowNormalization := by
  intro n b d u v h inverse a ha j
  let s := realSourceCoordinate inverse b d u v
  let t := realSourcePartner inverse b d u v
  let ell := realChartExponent inverse
  let z := s / a
  let β := realNormalizedError inverse a b d u v
  have hs : 0 < s := coordinate_pos n b d u v h inverse
  have hsp : s ^ ell ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs ell)
  have hap : a ^ ell ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha ell)
  have hzpow : z ^ ell = s ^ ell / a ^ ell := Real.div_rpow hs.le ha.le ell
  have hpartner : a ^ ell * (z ^ ell + β) = t := by
    dsimp [β, realNormalizedError, realSourceError]
    change a ^ ell * (z ^ ell + z ^ ell * (t / s ^ ell - 1)) = t
    rw [hzpow]
    field_simp
    ring
  have hpower : a ^ (j.val % 4) * z ^ (j.val % 4) = s ^ (j.val % 4) := by
    rw [← mul_pow]
    congr 1
    dsimp [z]
    field_simp
  have hnorm : realColumnScale inverse a j * realNormalizedRow inverse z β j =
      s ^ (j.val % 4) * (if j.val < 4 then 1 else t) := by
    unfold realColumnScale realNormalizedRow
    by_cases hj : j.val < 4
    · simpa [hj] using hpower
    · simp only [hj, ite_false]
      change (a ^ (j.val % 4) * a ^ ell) * (z ^ (j.val % 4) * (z ^ ell + β)) = _
      calc
        _ = (a ^ (j.val % 4) * z ^ (j.val % 4)) * (a ^ ell * (z ^ ell + β)) := by ring
        _ = _ := by rw [hpower, hpartner]
  rw [real_row_identity n b d u v h inverse j]
  change _ = (sourceRowDenominator inverse d u : ℝ) * realColumnScale inverse a j *
    realNormalizedRow inverse z β j
  rw [mul_assoc, hnorm]

theorem actual_minor_normalization : CF11ActualMinorNormalization := by
  intro n b d u v h inverse a ha
  have hm : (fun i j => (sourceIntegerRow inverse (b i) (d i) (u i) (v i) j : ℝ)) =
      (fun i j => (sourceRowDenominator inverse (d i) (u i) : ℝ) *
        (realColumnScale inverse a j * realNormalizedRow inverse
          (realSourceCoordinate inverse (b i) (d i) (u i) (v i) / a)
          (realNormalizedError inverse a (b i) (d i) (u i) (v i)) j)) := by
    funext i j
    rw [actual_row_normalization (n i) (b i) (d i) (u i) (v i) (h i) inverse a ha j]
    ring
  rw [hm]
  let A : Matrix (Fin 8) (Fin 8) ℝ := Matrix.of (fun i j => realNormalizedRow inverse
    (realSourceCoordinate inverse (b i) (d i) (u i) (v i) / a)
    (realNormalizedError inverse a (b i) (d i) (u i) (v i)) j)
  change (Matrix.of (fun i j => (sourceRowDenominator inverse (d i) (u i) : ℝ) *
    (realColumnScale inverse a j * A i j))).det = _
  erw [Matrix.det_mul_column]
  change _ * (Matrix.of (fun i j => realColumnScale inverse a j * A i j)).det = _
  erw [Matrix.det_mul_row]
  exact (mul_assoc _ _ _).symm

theorem real_scale_cancellation : CF11RealScaleCancellation := by
  intro B E U X hB hE hX
  rw [← hX]
  constructor <;> field_simp

theorem rounded_minor_vanishing : CF11RoundedMinorVanishing := by
  intro δ C hδ hC
  obtain ⟨X₀, hX₀, hg⟩ := rounded_error_absorption δ C hδ hC
  refine ⟨X₀, hX₀, ?_⟩
  intro X ψ hX hψ0 hψ2 F p n b d u v hp hscale hsource hcurve hgood hres inverse hbound
  let Δ : ℤ := Matrix.det (fun i j => sourceIntegerRow inverse (b i) (d i) (u i) (v i) j)
  have hdiv : (p : ℤ)^28 ∣ Δ :=
    actual_source_determinants F p n b d u v hp hsource hcurve hgood hres inverse
  have hnonneg : 0 ≤ roundedScale X ψ δ := by
    have hxpos : 0 < X := by have hh := hX₀.trans hX; linarith
    exact div_nonneg (Real.rpow_nonneg hxpos.le _) (Nat.cast_nonneg _)
  have hpow : roundedScale X ψ δ ^ (28 : ℕ) ≤ (p : ℝ)^28 :=
    pow_le_pow_left₀ hnonneg hscale 28
  have hsmall : |(Δ : ℝ)| < (p : ℝ)^28 := by
    have hcast : (Δ : ℝ) = (Matrix.of (fun i j =>
        (sourceIntegerRow inverse (b i) (d i) (u i) (v i) j : ℝ))).det := by
      exact Int.cast_det (Matrix.of (fun i j => sourceIntegerRow inverse (b i) (d i) (u i) (v i) j))
    rw [hcast]
    exact hbound.trans_lt ((hg X hX ψ hψ0 hψ2).trans_le hpow)
  by_contra hne
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hne
  have hleR : (((p : ℤ)^28).natAbs : ℝ) ≤ (Δ.natAbs : ℝ) := by exact_mod_cast hle
  have hle' : (p : ℝ)^28 ≤ |(Δ : ℝ)| := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] using hleR
  exact (not_le_of_gt hsmall) hle'

end
end P0365Subquarter
