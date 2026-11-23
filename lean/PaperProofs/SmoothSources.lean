import PaperTargets.SmoothSources
import PaperProofs.PrimeAssignment
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Field.ZMod

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

open Polynomial

/-- Divide the column polynomials by the monic polynomial of all eight nodes.
This works with repeated nodes and over rings with zero-divisors. -/
theorem polynomial_evaluation_determinant : CF10PolynomialEvaluationDeterminant := by
  intro R _ a ha z hz f
  classical
  cases subsingleton_or_nontrivial R with
  | inl h =>
      letI := h
      exact Subsingleton.elim _ _
  | inr h =>
    letI : Nontrivial R := h
    let Q : Polynomial R := ∏ i : Fin 8, (X - C (z i))
    have hmon : Q.Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))
    have hdegree : Q.natDegree = 8 := by
      dsimp [Q]
      rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (z i))]
      simp
    have hQone : Q ≠ 1 := by intro h; rw [h, natDegree_one] at hdegree; contradiction
    let rem (j : Fin 8) := f j %ₘ Q
    have hrem (j : Fin 8) : (rem j).natDegree < 8 := by
      simpa [rem, hdegree] using natDegree_modByMonic_lt (f j) hmon hQone
    have hroot (i : Fin 8) : Q.eval (z i) = 0 := by
      dsimp [Q]
      rw [eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    have heval (i j : Fin 8) : (rem j).eval (z i) = (f j).eval (z i) := by
      exact eval₂_modByMonic_eq_self_of_root (f := RingHom.id R) (hroot i)
    let B : Matrix (Fin 8) (Fin 8) R := fun k j => (rem j).coeff k
    have hmatrix : (fun i j => (f j).eval (z i)) = Matrix.vandermonde z * B := by
      ext i j
      rw [← heval i j, Matrix.mul_apply]
      simp only [Matrix.vandermonde_apply, B]
      rw [show (∑ k : Fin 8, z i ^ k.val * (rem j).coeff k.val) =
      ∑ k ∈ Finset.range 8, z i ^ k * (rem j).coeff k from
        Fin.sum_univ_eq_sum_range (fun k : ℕ => z i ^ k * (rem j).coeff k) 8]
      simpa only [mul_comm] using (eval_eq_sum_range' (hrem j) (z i))
    choose w hw using hz
    have hv : Matrix.vandermonde z =
        Matrix.of (fun i j : Fin 8 => a^(j.val) * Matrix.vandermonde w i j) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.vandermonde_apply, hw i, mul_pow]
    have hprod : (∏ j : Fin 8, a^j.val) = 0 := by
      rw [Finset.prod_pow_eq_pow_sum]
      have hn : (∑ j : Fin 8, j.val) = 28 := by decide
      rw [hn, ha]
    rw [hmatrix, Matrix.det_mul, hv, Matrix.det_mul_row, hprod, zero_mul, zero_mul]

private def chartPoint {R : Type*} (i : Fin 2) (t s : R) : Fin 2 → R :=
  fun j => if j = i then t else s

private theorem chartPoint_self {R : Type*} (i : Fin 2) (z : Fin 2 → R) :
    chartPoint i (z i) (z (otherCoordinate i)) = z := by
  ext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem value_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : SourcePolynomial) (z : Fin 2 → R) :
    φ (polynomialValue F z) = polynomialValue F (φ ∘ z) := by
  unfold polynomialValue
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  ext c
  simp

private def slice {R : Type*} [CommRing R] (F : SourcePolynomial)
    (i : Fin 2) (s : R) : Polynomial R :=
  polynomialValue F (chartPoint i X (C s))

private theorem slice_eval {R : Type*} [CommRing R] (F : SourcePolynomial)
    (i : Fin 2) (s t : R) : (slice F i s).eval t = polynomialValue F (chartPoint i t s) := by
  rw [slice, ← Polynomial.coe_evalRingHom, value_map]
  congr 1
  ext j
  by_cases h : j = i <;> simp [chartPoint, h]

private theorem slice_derivative {R : Type*} [CommRing R] (F : SourcePolynomial)
    (i : Fin 2) (s t : R) : (slice F i s).derivative.eval t =
      polynomialValue (MvPolynomial.pderiv i F) (chartPoint i t s) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
      simp only [slice, polynomialValue, MvPolynomial.eval₂_C, MvPolynomial.pderiv_C,
        MvPolynomial.eval₂_zero]
      change (C (c:R)).derivative.eval t = 0
      simp
  | add F G hF hG =>
      simpa only [slice, polynomialValue, MvPolynomial.eval₂_add, map_add,
        derivative_add, eval_add] using congrArg₂ (· + ·) hF hG
  | mul_X F j hF =>
      by_cases hj : j = i
      · subst j
        simp only [slice, polynomialValue, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          chartPoint, ite_true, derivative_mul, eval_add, eval_mul, derivative_X, eval_X,
          eval_one, mul_one, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
          MvPolynomial.eval₂_add, MvPolynomial.eval₂_one]
        change (slice F i s).derivative.eval t * t + (slice F i s).eval t = _
        rw [hF, slice_eval]
        rfl
      · simp only [slice, polynomialValue, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          chartPoint, ite_eq_right hj, derivative_mul, derivative_C, eval_add, eval_mul, eval_C,
          eval_zero, mul_zero, add_zero, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_X_of_ne hj, MvPolynomial.eval₂_add, MvPolynomial.eval₂_zero]
        change (slice F i s).derivative.eval t * s = _
        rw [hF]
        rfl

private theorem reduction_dvd (p : ℕ) (hp : p.Prime) (x : SmoothRing p) :
    smoothReduction p x = 0 ↔ (p : SmoothRing p) ∣ x := by
  let : NeZero (p^28) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  constructor
  · intro h
    have hd : p ∣ n := by
      apply (ZMod.natCast_eq_zero_iff n p).mp
      simpa [smoothReduction] using h
    obtain ⟨k, rfl⟩ := hd
    exact ⟨k, by simp⟩
  · rintro ⟨y, hy⟩
    rw [hy, map_mul]
    simp [smoothReduction]

private theorem unit_of_reduction (p : ℕ) (hp : p.Prime) (x : SmoothRing p)
    (hx : smoothReduction p x ≠ 0) : IsUnit x := by
  let : NeZero (p^28) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < (28:ℕ))).mpr
  intro h
  apply hx
  have hn := (ZMod.natCast_eq_zero_iff n p).mpr h
  simpa [smoothReduction] using hn

private theorem prime_power_zero (p : ℕ) : (p : SmoothRing p)^28 = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

private def implicitApprox {R : Type*} [CommRing R] (F : SourcePolynomial)
    (i : Fin 2) (z₀ : Fin 2 → R) (ai : R) : ℕ → Polynomial R
  | 0 => 0
  | k+1 =>
      let q := implicitApprox F i z₀ ai k
      q - C ai * polynomialValue F
        (chartPoint i (C (z₀ i) + q) (C (z₀ (otherCoordinate i)) + X))

private theorem approx_zero {R : Type*} [CommRing R] (F : SourcePolynomial)
    (i : Fin 2) (z₀ : Fin 2 → R) (ai : R) (hF : polynomialValue F z₀ = 0) (k : ℕ) :
    (implicitApprox F i z₀ ai k).eval 0 = 0 := by
  induction k with
  | zero => simp [implicitApprox]
  | succ k ih =>
      simp only [implicitApprox, eval_sub, eval_mul, eval_C]
      rw [← Polynomial.coe_evalRingHom, value_map]
      have hz : (Polynomial.evalRingHom (0:R)) ∘
          chartPoint i (C (z₀ i) + implicitApprox F i z₀ ai k)
            (C (z₀ (otherCoordinate i)) + X) = z₀ := by
        ext j
        by_cases h : j = i
        · subst j; simp [chartPoint, ih]
        · have hh := congrFun (chartPoint_self i z₀) j
          simp [chartPoint, h] at hh
          simpa [chartPoint, h] using hh
      rw [hz, hF, mul_zero, sub_zero]
      exact ih

private theorem approx_error (F : SourcePolynomial) (p : ℕ) (hp : p.Prime)
    (i : Fin 2) (z₀ : Fin 2 → SmoothRing p) (ai : SmoothRing p)
    (hai : ai * polynomialValue (MvPolynomial.pderiv i F) z₀ = 1)
    (z : Fin 2 → SmoothRing p) (hF : polynomialValue F z = 0)
    (hres : ∀ j, smoothReduction p (z j) = smoothReduction p (z₀ j)) (k : ℕ) :
    (p : SmoothRing p)^(k+1) ∣ z i - (z₀ i +
      (implicitApprox F i z₀ ai k).eval (z (otherCoordinate i) - z₀ (otherCoordinate i))) := by
  let φ := smoothReduction p
  let x := z (otherCoordinate i) - z₀ (otherCoordinate i)
  induction k with
  | zero =>
      simpa [implicitApprox, pow_one] using
        (reduction_dvd p hp (z i - z₀ i)).mp (by simp [map_sub, hres i])
  | succ k ih =>
      let q := implicitApprox F i z₀ ai k
      let t := z₀ i + q.eval x
      let e := z i - t
      have he : (p : SmoothRing p)^(k+1) ∣ e := ih
      have hep : (p : SmoothRing p) ∣ e := (dvd_pow_self _ (by omega : k+1 ≠ 0)).trans he
      have hφe : φ e = 0 := (reduction_dvd p hp e).mpr hep
      let f := slice F i (z (otherCoordinate i))
      obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add f t e
      have hte : t + e = z i := by dsimp [e]; ring
      have hpoint : chartPoint i (z i) (z (otherCoordinate i)) = z := chartPoint_self i z
      have hfzero : f.eval (t+e) = 0 := by rw [hte, slice_eval, hpoint]; exact hF
      have hφt : φ t = φ (z₀ i) := by
        have hh : φ (z i) - φ t = 0 := by simpa [e, map_sub] using hφe
        rw [hres i] at hh
        exact (sub_eq_zero.mp hh).symm
      have hder : φ (f.derivative.eval t) = φ (polynomialValue (MvPolynomial.pderiv i F) z₀) := by
        rw [slice_derivative, value_map, value_map]
        congr 1
        ext j
        by_cases hj : j = i
        · subst j; simpa [chartPoint] using hφt
        · have hh := congrFun (chartPoint_self i z₀) j
          simp only [chartPoint, ite_eq_right hj] at hh
          simp only [Function.comp_apply, chartPoint, ite_eq_right hj]
          rw [hres (otherCoordinate i), hh]
      let m : SmoothRing p := 1 - ai * f.derivative.eval t - ai * c * e
      have hφm : φ m = 0 := by
        have hh := congrArg φ hai
        dsimp [m]
        simp only [map_sub, map_mul, map_one, hφe, mul_zero, sub_zero, hder]
        simp only [map_mul, map_one] at hh
        rw [hh]
        exact sub_self _
      have hm : (p : SmoothRing p) ∣ m := (reduction_dvd p hp m).mp hφm
      have hnew : z i - (z₀ i + (implicitApprox F i z₀ ai (k+1)).eval x) = m * e := by
        have hvalue : (polynomialValue F
            (chartPoint i (C (z₀ i) + q) (C (z₀ (otherCoordinate i)) + X))).eval x = f.eval t := by
          rw [← Polynomial.coe_evalRingHom, value_map, slice_eval]
          congr 1
          ext j
          by_cases hj : j = i <;> simp [chartPoint, hj, t, x]
        change z i - (z₀ i + (q - C ai * _).eval x) = m * e
        rw [eval_sub, eval_mul, eval_C, hvalue]
        rw [hfzero] at hc
        dsimp [m, e, t] at *
        linear_combination ai * hc
      rw [hnew, show (p : SmoothRing p)^(k+1+1) = (p : SmoothRing p) * p^(k+1) by ring]
      exact mul_dvd_mul hm he

theorem finite_implicit_polynomial : CF09FiniteImplicitPolynomial := by
  intro F p hp z₀ hF hsmooth
  obtain ⟨i, hi⟩ := hsmooth
  obtain ⟨ai, hai⟩ := (unit_of_reduction p hp _ hi).exists_left_inv
  refine ⟨i, implicitApprox F i z₀ ai 27, hi, approx_zero F i z₀ ai hF 27, ?_⟩
  intro z hz hres
  have hh := approx_error F p hp i z₀ ai hai z hz hres 27
  norm_num only at hh
  rw [prime_power_zero] at hh
  have he := zero_dvd_iff.mp hh
  exact sub_eq_zero.mp he

private theorem denominator_units (p d u : ℕ) (hp : p.Prime) (hden : ¬p∣d*u) :
    IsUnit (d : SmoothRing p) ∧ IsUnit (u : SmoothRing p) := by
  have hd : ¬p∣d := fun h => hden (dvd_mul_of_dvd_left h u)
  have hu : ¬p∣u := fun h => hden (dvd_mul_of_dvd_right h d)
  exact ⟨(ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < (28:ℕ))).mpr hd,
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < (28:ℕ))).mpr hu⟩

private theorem reduction_inv (p : ℕ) (hp : p.Prime) (a : SmoothRing p) (ha : IsUnit a) :
    smoothReduction p a⁻¹ = (smoothReduction p a)⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  have hh := congrArg (smoothReduction p) (ZMod.mul_inv_of_unit a ha)
  simp only [map_mul, map_one] at hh
  have hne : smoothReduction p a ≠ 0 := by intro h; rw [h, zero_mul] at hh; exact zero_ne_one hh
  apply mul_left_cancel₀ hne
  rw [hh, mul_inv_cancel₀ hne]

private theorem lift_reduction (p b d u v : ℕ) (hp : p.Prime) (hden : ¬p∣d*u) :
    (smoothReduction p) ∘ sourceLift b d u v p = sourceReduction b d u v p := by
  obtain ⟨hd, hu⟩ := denominator_units p d u hp hden
  ext i
  fin_cases i
  · change smoothReduction p ((b : SmoothRing p) * (d : SmoothRing p)⁻¹) =
      (b : ZMod p) * (d : ZMod p)⁻¹
    rw [map_mul, reduction_inv p hp _ hd]
    simp
  · change smoothReduction p ((v : SmoothRing p) * (u : SmoothRing p)⁻¹) =
      (v : ZMod p) * (u : ZMod p)⁻¹
    rw [map_mul, reduction_inv p hp _ hu]
    simp

private theorem clear_unit_power {R : Type*} [CommRing R] (b d di : R) (D e : ℕ)
    (hd : d*di = 1) (he : e ≤ D) :
    b^e * d^(D-e) = d^D * (b*di)^e := by
  have hD : d^D = d^e * d^(D-e) := by rw [← pow_add, Nat.add_sub_of_le he]
  symm
  rw [hD, mul_pow]
  calc
    _ = b^e * d^(D-e) * (d*di)^e := by rw [mul_pow]; ring
    _ = _ := by rw [hd, one_pow, mul_one]

private theorem cleared_lift (F : SourcePolynomial) (D b d u v p : ℕ)
    (hD : F.totalDegree ≤ D) (hd : IsUnit (d : SmoothRing p)) (hu : IsUnit (u : SmoothRing p)) :
    (clearedValue F D b d u v : SmoothRing p) =
      (d : SmoothRing p)^D * (u : SmoothRing p)^D * polynomialValue F (sourceLift b d u v p) := by
  classical
  simp only [clearedValue, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    polynomialValue, MvPolynomial.eval₂_eq', Fin.prod_univ_two, sourceLift, sourceReduction,
    Matrix.cons_val_zero, Matrix.cons_val_one, Int.coe_castRingHom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have he0 : e 0 ≤ D := (MvPolynomial.monomial_le_degreeOf 0 he).trans
    ((MvPolynomial.degreeOf_le_totalDegree F 0).trans hD)
  have he1 : e 1 ≤ D := (MvPolynomial.monomial_le_degreeOf 1 he).trans
    ((MvPolynomial.degreeOf_le_totalDegree F 1).trans hD)
  have h0 := clear_unit_power (b : SmoothRing p) d (d : SmoothRing p)⁻¹ D (e 0)
    (ZMod.mul_inv_of_unit _ hd) he0
  have h1 := clear_unit_power (v : SmoothRing p) u (u : SmoothRing p)⁻¹ D (e 1)
    (ZMod.mul_inv_of_unit _ hu) he1
  calc
    _ = (F.coeff e : SmoothRing p) * ((b : SmoothRing p)^e 0 * d^(D-e 0)) *
      ((v : SmoothRing p)^e 1 * u^(D-e 1)) := by ring
    _ = _ := by rw [h0,h1]; ring

private theorem source_lift_curve (F : SourcePolynomial) (p n b d u v : ℕ)
    (hp : p.Prime) (hs : PairSource n b d u v)
    (hF : polynomialValue F (sourcePoint b d u v) = 0) (hden : ¬p∣d*u) :
    polynomialValue F (sourceLift b d u v p) = 0 := by
  obtain ⟨hd, hu⟩ := denominator_units p d u hp hden
  have hQ := cleared_identity F F.totalDegree b d u v le_rfl hs.2.1 hs.2.2.1
  rw [hF, mul_zero] at hQ
  have hZ : clearedValue F F.totalDegree b d u v = 0 := by exact_mod_cast hQ
  have hR := cleared_lift F F.totalDegree b d u v p le_rfl hd hu
  rw [hZ, Int.cast_zero] at hR
  exact ((hd.pow _).mul (hu.pow _)).mul_right_eq_zero.mp hR.symm

private theorem lift_smooth (F : SourcePolynomial) (p b d u v : ℕ)
    (hp : p.Prime) (hgood : goodSourcePrime F b d u v p) :
    ∃ i : Fin 2, smoothReduction p
      (polynomialValue (MvPolynomial.pderiv i F) (sourceLift b d u v p)) ≠ 0 := by
  obtain ⟨i, hi⟩ := hgood.2.2
  refine ⟨i, ?_⟩
  rw [value_map, lift_reduction p b d u v hp hgood.1]
  exact hi

theorem actual_source_implicit_polynomial : CF09ActualSourceImplicitPolynomial := by
  intro F p n₀ b₀ d₀ u₀ v₀ hp hs₀ hF₀ hg₀
  obtain ⟨i, q, hi, hq0, hq⟩ := finite_implicit_polynomial F p hp
    (sourceLift b₀ d₀ u₀ v₀ p) (source_lift_curve F p n₀ b₀ d₀ u₀ v₀ hp hs₀ hF₀ hg₀.1)
    (lift_smooth F p b₀ d₀ u₀ v₀ hp hg₀)
  refine ⟨i, q, hq0, ?_⟩
  intro n b d u v hs hF hg hres
  apply hq (sourceLift b d u v p) (source_lift_curve F p n b d u v hp hs hF hg.1)
  intro j
  have h1 := congrFun (lift_reduction p b d u v hp hg.1) j
  have h0 := congrFun (lift_reduction p b₀ d₀ u₀ v₀ hp hg₀.1) j
  exact h1.trans ((congrFun hres j).trans h0.symm)

theorem source_row_identity : CF10SourceRowIdentity := by
  intro p b d u v hp hden inverse
  obtain ⟨hd, hu⟩ := denominator_units p d u hp hden
  have hdinv := ZMod.mul_inv_of_unit (d : SmoothRing p) hd
  have huinv := ZMod.mul_inv_of_unit (u : SmoothRing p) hu
  constructor
  · cases inverse
    · simpa [sourceRowDenominator] using (hd.pow 3).mul hu
    · simpa [sourceRowDenominator] using hd.mul (hu.pow 3)
  · intro j
    have hk : j.val % 4 ≤ 3 := by omega
    have h0 := clear_unit_power (b : SmoothRing p) d (d : SmoothRing p)⁻¹ 3 (j.val%4) hdinv hk
    have h1 := clear_unit_power (v : SmoothRing p) u (u : SmoothRing p)⁻¹ 3 (j.val%4) huinv hk
    cases inverse
    · by_cases hj : j.val < 4
      · simp only [sourceIntegerRow, sourceRowDenominator, chartMonomial, sourceLift,
          sourceReduction, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, hj, Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_one]
        rw [h0]
        ring
      · simp only [sourceIntegerRow, sourceRowDenominator, chartMonomial, sourceLift,
          sourceReduction, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, hj, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [h0]
        calc
          _ = (d : SmoothRing p)^3 * ((b : SmoothRing p)*(d : SmoothRing p)⁻¹)^(j.val%4) * (v : SmoothRing p) * ((u : SmoothRing p)*(u : SmoothRing p)⁻¹) := by rw [huinv,mul_one]
          _ = _ := by ring
    · by_cases hj : j.val < 4
      · simp only [sourceIntegerRow, sourceRowDenominator, chartMonomial, sourceLift,
          sourceReduction, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, hj, Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_one]
        rw [mul_comm ((u : SmoothRing p)^(3-j.val%4)) ((v : SmoothRing p)^(j.val%4)), h1]
        ring
      · simp only [sourceIntegerRow, sourceRowDenominator, chartMonomial, sourceLift,
          sourceReduction, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, hj, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [mul_comm ((u : SmoothRing p)^(3-j.val%4)) ((v : SmoothRing p)^(j.val%4)), h1]
        calc
          _ = (u : SmoothRing p)^3 * ((v : SmoothRing p)*(u : SmoothRing p)⁻¹)^(j.val%4) * (b : SmoothRing p) * ((d : SmoothRing p)*(d : SmoothRing p)⁻¹) := by rw [hdinv,mul_one]
          _ = _ := by ring

private theorem chart_monomial_eval {R : Type*} [CommRing R] (inverse : Bool)
    (g : Fin 2 → Polynomial R) (x : R) (j : Fin 8) :
    (chartMonomial inverse g j).eval x = chartMonomial inverse ((Polynomial.evalRingHom x) ∘ g) j := by
  unfold chartMonomial
  rw [eval_mul, eval_pow]
  split_ifs <;> simp

theorem actual_source_determinants : CF10ActualSourceDeterminants := by
  intro F p n b d u v hp hsource hcurve hgood hres inverse
  let z₀ := sourceLift (b 0) (d 0) (u 0) (v 0) p
  let z (k : Fin 8) := sourceLift (b k) (d k) (u k) (v k) p
  obtain ⟨i, q, hq0, hq⟩ := actual_source_implicit_polynomial F p (n 0) (b 0) (d 0) (u 0) (v 0)
    hp (hsource 0) (hcurve 0) (hgood 0)
  let x (k : Fin 8) := z k (otherCoordinate i) - z₀ (otherCoordinate i)
  have hparam (k : Fin 8) : (p : SmoothRing p) ∣ x k := by
    apply (reduction_dvd p hp _).mp
    dsimp [x, z, z₀]
    rw [map_sub]
    have h1 := congrFun (lift_reduction p (b k) (d k) (u k) (v k) hp (hgood k).1) (otherCoordinate i)
    have h0 := congrFun (lift_reduction p (b 0) (d 0) (u 0) (v 0) hp (hgood 0).1) (otherCoordinate i)
    simp only [Function.comp_apply] at h1 h0
    rw [h1, h0, hres k, sub_self]
  let g : Fin 2 → Polynomial (SmoothRing p) :=
    chartPoint i (C (z₀ i) + q) (C (z₀ (otherCoordinate i)) + X)
  have hgraph (k : Fin 8) : (Polynomial.evalRingHom (x k)) ∘ g = z k := by
    ext j
    by_cases hj : j = i
    · subst j
      simp only [Function.comp_apply, g, chartPoint, ite_true, map_add, Polynomial.coe_evalRingHom, eval_add,
        eval_C, eval_X]
      exact (hq (n k) (b k) (d k) (u k) (v k) (hsource k) (hcurve k) (hgood k) (hres k)).symm
    · have hself := congrFun (chartPoint_self i (z k)) j
      simp only [chartPoint, ite_eq_right hj] at hself
      simp only [Function.comp_apply, g, chartPoint, ite_eq_right hj, map_add,
        Polynomial.coe_evalRingHom, eval_add, eval_C, eval_X]
      dsimp [x]
      rw [add_sub_cancel, hself]
  let columns (j : Fin 8) := chartMonomial inverse g j
  have hdet : Matrix.det (fun k j => chartMonomial inverse (z k) j) = 0 := by
    have hh := polynomial_evaluation_determinant (SmoothRing p) (p : SmoothRing p)
      (prime_power_zero p) x hparam columns
    have heq : (fun k j => (columns j).eval (x k)) =
        (fun k j => chartMonomial inverse (z k) j) := by
      ext k j
      exact (chart_monomial_eval inverse g (x k) j).trans (congrArg (fun z => chartMonomial inverse z j) (hgraph k))
    rwa [heq] at hh
  let A : Matrix (Fin 8) (Fin 8) ℤ := fun k j => sourceIntegerRow inverse (b k) (d k) (u k) (v k) j
  have hmatrix : (fun k j => (A k j : SmoothRing p)) = Matrix.of
      (fun k j => (sourceRowDenominator inverse (d k) (u k) : SmoothRing p) * chartMonomial inverse (z k) j) := by
    ext k j
    exact (source_row_identity p (b k) (d k) (u k) (v k) hp (hgood k).1 inverse).2 j
  have hzero : ((Matrix.det A : ℤ) : SmoothRing p) = 0 := by
    change (Int.castRingHom (SmoothRing p)) (Matrix.det A) = 0
    rw [RingHom.map_det]
    change Matrix.det (fun k j => (A k j : SmoothRing p)) = 0
    rw [hmatrix, Matrix.det_mul_column
      (fun k : Fin 8 => (sourceRowDenominator inverse (d k) (u k) : SmoothRing p))
      (fun k j : Fin 8 => chartMonomial inverse (z k) j), hdet, mul_zero]
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd (Matrix.det A) (p^28)).mp hzero
  simpa only [Nat.cast_pow] using hdiv

end
end P0365Subquarter
