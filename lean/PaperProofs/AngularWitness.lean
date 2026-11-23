import PaperTargets.DividedMinors
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Section 13's enlarged analytic witness.
Source: research/papers/p0365-subquarter-v1/manuscript/MANUSCRIPT.md, section 13,
at reviewed source head 651754fa88f0485db734456cb786f5e2dabbeb2f.
The polynomial identity holds for arbitrary fixed distinct real first-seven
nodes, with an arbitrary eighth node. The repeated-node corollary uses an
allowed eighth-node choice to realize the actual determinant for fixed nonzero
amplitudes. This supplement is independent of the counting theorem and asserts
no canonical arithmetic saturation or reciprocal-height saving. -/
namespace P0365Subquarter.AngularWitness
noncomputable section
open Polynomial Matrix
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

abbrev Index := Fin 7 ⊕ Fin 1

def indexEquiv : Index ≃ Fin 8 := finSumFinEquiv

def exponent (inverse : Bool) (j : Fin 8) : ℕ :=
  realRootOrder inverse * (j.val % 4) +
    if j.val < 4 then 0 else realRootPartnerOrder inverse

theorem smooth_eq_power {R : Type*} [CommRing R] (inverse : Bool) (w : R) (j : Fin 8) :
    rootSmoothRow inverse w j = w ^ exponent inverse j := by
  simp only [rootSmoothRow, exponent, pow_add]
  split_ifs <;> simp

def jet (inverse : Bool) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => if i.val < 7 then (Nat.choose (exponent inverse j) i.val : ℝ)
    else rootErrorRow inverse 1 j

private def directL : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, (1/2), 1, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, (1/4), (3/2), 1, 0, 0, 0;
    0, 0, 0, (3/4), 1, 1, 0, 0;
    0, 0, 0, (1/8), (1/6), (5/6), 1, 0;
    0, 0, 0, 0, (8/3), (-32/3), (160/7), 1]

private def directU : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 1, 1, 1, 1, 1, 1, 1;
    0, 2, 4, 6, 3, 5, 7, 9;
    0, 0, 4, 12, (3/2), (15/2), (35/2), (63/2);
    0, 0, 0, 8, (-1/2), (5/2), (35/2), (105/2);
    0, 0, 0, 0, (3/8), (-5/8), (35/8), (315/8);
    0, 0, 0, 0, 0, (-1/4), (7/2), (189/4);
    0, 0, 0, 0, 0, 0, (7/6), (63/2);
    0, 0, 0, 0, 0, 0, 0, -320]

theorem jet_direct : (jet false).det = 2240 := by
  have he : jet false = directL * directU := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jet, exponent, realRootOrder, realRootPartnerOrder, rootErrorRow, Nat.choose,
        directL, directU, Matrix.mul_apply, Fin.sum_univ_succ]
  have hl : (directL).IsLowerTriangular := by
    clear he
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [directL, Fin.lt_def] at *
  have hu : (directU).IsUpperTriangular := by
    clear he hl
    intro i j hij
    change j < i at hij
    fin_cases i <;> fin_cases j <;> norm_num [directU, Fin.lt_def] at *
  rw [he, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hl,
    Matrix.det_of_isUpperTriangular hu]
  norm_num [directL, directU, Fin.prod_univ_succ]

private def inverseL : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0;
    0, (1/3), 2, 1, 0, 0, 0, 0;
    0, 0, (5/3), 3, 1, 0, 0, 0;
    0, 0, (2/3), 4, 2, 1, 0, 0;
    0, 0, (1/9), 3, (5/3), (5/3), 1, 0;
    0, 0, 0, 0, (-3/7), (12/7), (-45/14), 1]

private def inverseU : Matrix (Fin 8) (Fin 8) ℝ :=
  !![1, 1, 1, 1, 1, 1, 1, 1;
    0, 3, 6, 9, 2, 5, 8, 11;
    0, 0, 9, 27, -1, 5, 20, 44;
    0, 0, 0, 27, (4/3), (-5/3), (40/3), (220/3);
    0, 0, 0, 0, (-7/3), (5/3), (-10/3), (110/3);
    0, 0, 0, 0, 0, 1, -4, 66;
    0, 0, 0, 0, 0, 0, -2, 66;
    0, 0, 0, 0, 0, 0, 0, (810/7)]

theorem jet_inverse : (jet true).det = 393660 := by
  have he : jet true = inverseL * inverseU := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [jet, exponent, realRootOrder, realRootPartnerOrder, rootErrorRow, Nat.choose,
        inverseL, inverseU, Matrix.mul_apply, Fin.sum_univ_succ]
  have hl : (inverseL).IsLowerTriangular := by
    clear he
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [inverseL, Fin.lt_def] at *
  have hu : (inverseU).IsUpperTriangular := by
    clear he hl
    intro i j hij
    change j < i at hij
    fin_cases i <;> fin_cases j <;> norm_num [inverseU, Fin.lt_def] at *
  rw [he, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ hl,
    Matrix.det_of_isUpperTriangular hu]
  norm_num [inverseL, inverseU, Fin.prod_univ_succ]


def coefficientMatrix (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ) :
    Matrix Index Index ℝ[X] := fun i j =>
  match i with
  | Sum.inl k => (1 + C (ξ k) * X) ^ exponent inverse (indexEquiv j)
  | Sum.inr _ => rootErrorRow inverse (1 + C ξ₇ * X) (indexEquiv j)

def coefficientPolynomial (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ) : ℝ[X] :=
  (coefficientMatrix inverse ξ ξ₇).det

def vandermondeProduct (ξ : Fin 7 → ℝ) : ℝ :=
  ∏ i : Fin 7, ∏ j ∈ Finset.Ioi i, (ξ j - ξ i)

private theorem coeff_node_power (x : ℝ) (e m : ℕ) :
    ((1 + C x * X : ℝ[X]) ^ e).coeff m = (e.choose m : ℝ) * x ^ m := by
  have h := (Polynomial.comp_C_mul_X_coeff (p := (1 + X : ℝ[X]) ^ e)
    (r := x) (n := m))
  simpa only [Polynomial.add_comp, Polynomial.one_comp, Polynomial.X_comp,
    Polynomial.pow_comp, Polynomial.coeff_one_add_X_pow] using h

private def block (ξ : Fin 7 → ℝ) : Matrix Index Index ℝ :=
  Matrix.fromBlocks (Matrix.vandermonde ξ) 0 0 1

private def invBlock (ξ : Fin 7 → ℝ) : Matrix Index Index ℝ :=
  Matrix.fromBlocks (Matrix.vandermonde ξ)⁻¹ 0 0 1

private theorem block_inverse (ξ : Fin 7 → ℝ) (hξ : Function.Injective ξ) :
    block ξ * invBlock ξ = 1 := by
  have hv := Matrix.mul_nonsing_inv (Matrix.vandermonde ξ)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hξ))
  simp [block, invBlock, Matrix.fromBlocks_multiply, hv, Matrix.fromBlocks_one]

private def rowOrder : Index → ℕ := Sum.elim Fin.val (fun _ => 0)

private theorem sum_rowOrder : (∑ i : Index, rowOrder i) = 21 := by
  norm_num [rowOrder, Fintype.sum_sum_type, Fin.sum_univ_succ]

private def transformed (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ) :
    Matrix Index Index ℝ[X] :=
  (invBlock ξ).map C * coefficientMatrix inverse ξ ξ₇

private theorem transformed_coeff (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (k : Fin 7) (j : Index) (m : Fin 7) :
    ((transformed inverse ξ ξ₇) (Sum.inl k) j).coeff m.val =
      (if k = m then 1 else 0) * (Nat.choose (exponent inverse (indexEquiv j)) m.val : ℝ) := by
  have hv := congrFun (congrFun (Matrix.nonsing_inv_mul (Matrix.vandermonde ξ)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hξ))) k) m
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] at hv
  simp only [transformed, Matrix.mul_apply, Fintype.sum_sum_type,
    invBlock, Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, coefficientMatrix, coeff_node_power]
  simp_rw [mul_left_comm _ (Nat.choose (exponent inverse (indexEquiv j)) m.val : ℝ)]
  rw [← Finset.mul_sum, hv, mul_comm]

private theorem transformed_low (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (i j : Index) (m : ℕ) (hm : m < rowOrder i) :
    ((transformed inverse ξ ξ₇) i j).coeff m = 0 := by
  cases i with
  | inl k =>
    change m < k.val at hm
    have hmk : (⟨m, lt_trans hm k.isLt⟩ : Fin 7) ≠ k := by
      intro he; have := congrArg Fin.val he; simp at this; omega
    simpa [hmk.symm] using transformed_coeff inverse ξ ξ₇ hξ k j ⟨m, lt_trans hm k.isLt⟩
  | inr k => simp [rowOrder] at hm

private theorem transformed_diagonal_coeff (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (i j : Index) :
    ((transformed inverse ξ ξ₇) i j).coeff (rowOrder i) =
      jet inverse (indexEquiv i) (indexEquiv j) := by
  cases i with
  | inl k =>
    have hj : jet inverse (indexEquiv (Sum.inl k)) (indexEquiv j) =
        (Nat.choose (exponent inverse (indexEquiv j)) k.val : ℝ) := by
      change (if k.val < 7 then _ else _) = _
      rw [ite_eq_left k.isLt]
      rfl
    rw [hj]
    simpa only [rowOrder, Sum.elim_inl, ite_true, mul_one, one_mul] using
      transformed_coeff inverse ξ ξ₇ hξ k j k
  | inr k =>
    fin_cases k
    change ((transformed inverse ξ ξ₇) (Sum.inr 0) j).coeff 0 =
      rootErrorRow inverse 1 (indexEquiv j)
    simp only [transformed, Matrix.mul_apply, Fintype.sum_sum_type, invBlock,
      Matrix.map_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.one_apply,
      ite_true, map_one, one_mul, coefficientMatrix]
    simp only [rootErrorRow]
    split_ifs <;> simp only [Polynomial.coeff_zero, coeff_node_power, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, one_pow]

private def normalizedMatrix (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) : Matrix Index Index ℝ[X] := fun i j =>
  Classical.choose (Polynomial.X_pow_dvd_iff.mpr (transformed_low inverse ξ ξ₇ hξ i j))

private theorem normalized_factor (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (i j : Index) :
    transformed inverse ξ ξ₇ i j = X ^ rowOrder i * normalizedMatrix inverse ξ ξ₇ hξ i j :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (transformed_low inverse ξ ξ₇ hξ i j))

private theorem normalized_zero (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (normalizedMatrix inverse ξ ξ₇ hξ).map (Polynomial.evalRingHom (0 : ℝ)) =
      Matrix.reindex indexEquiv.symm indexEquiv.symm (jet inverse) := by
  ext i j
  have h := congrArg (fun p : ℝ[X] => p.coeff (rowOrder i))
    (normalized_factor inverse ξ ξ₇ hξ i j)
  simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, Nat.sub_self] at h
  simpa only [Polynomial.coeff_zero_eq_eval_zero, Matrix.map_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Polynomial.coe_evalRingHom] using
    h.symm.trans (transformed_diagonal_coeff inverse ξ ξ₇ hξ i j)

private theorem determinant_row_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ[X]) (d : ι → ℝ[X])
    (h : ∀ i j, A i j = d i * B i j) : A.det = (∏ i, d i) * B.det := by
  calc
    A.det = Matrix.det (Matrix.of (fun i j => d i * B i j)) :=
      congrArg Matrix.det (funext (fun i => funext (h i)))
    _ = _ := Matrix.det_mul_column d B

private theorem transformed_det (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (transformed inverse ξ ξ₇).det = X ^ 21 * (normalizedMatrix inverse ξ ξ₇ hξ).det := by
  have h := determinant_row_factor (transformed inverse ξ ξ₇) (normalizedMatrix inverse ξ ξ₇ hξ)
    (fun i => X ^ rowOrder i) (normalized_factor inverse ξ ξ₇ hξ)
  have hp : (∏ i : Index, (X : ℝ[X]) ^ rowOrder i) = X ^ 21 := by
    rw [Finset.prod_pow_eq_pow_sum, sum_rowOrder]
  exact h.trans (congrArg (fun z : ℝ[X] => z * (normalizedMatrix inverse ξ ξ₇ hξ).det) hp)

private theorem determinant_of_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B M : Matrix ι ι ℝ[X]) (h : A * B = M) : M.det = A.det * B.det := by
  rw [← h, Matrix.det_mul]

private theorem matrix_reconstruct (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (block ξ).map C * transformed inverse ξ ξ₇ = coefficientMatrix inverse ξ ξ₇ := by
  rw [transformed, ← Matrix.mul_assoc, ← Matrix.map_mul,
    block_inverse ξ hξ, Matrix.map_one, Matrix.one_mul] <;> simp

private theorem constant_block_det (ξ : Fin 7 → ℝ) :
    ((block ξ).map C).det = C (vandermondeProduct ξ) := by
  have hmap : ((block ξ).map C).det = C (block ξ).det :=
    ((Polynomial.C : ℝ →+* ℝ[X]).map_det (block ξ)).symm
  have hr : (block ξ).det = vandermondeProduct ξ := by
    rw [block, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_vandermonde]
    rfl
  exact hmap.trans (congrArg C hr)

private theorem coefficient_det_factor (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    coefficientPolynomial inverse ξ ξ₇ =
      C (vandermondeProduct ξ) * (X ^ 21 * (normalizedMatrix inverse ξ ξ₇ hξ).det) := by
  have hf := determinant_of_product ((block ξ).map C) (transformed inverse ξ ξ₇)
    (coefficientMatrix inverse ξ ξ₇) (matrix_reconstruct inverse ξ ξ₇ hξ)
  exact hf.trans (congrArg₂ (fun a b : ℝ[X] => a * b)
    (constant_block_det ξ) (transformed_det inverse ξ ξ₇ hξ))

private theorem normalized_det_zero (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    ((normalizedMatrix inverse ξ ξ₇ hξ).det).coeff 0 = (jet inverse).det := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have he := (Polynomial.evalRingHom (0 : ℝ)).map_det (normalizedMatrix inverse ξ ξ₇ hξ)
  change eval 0 (normalizedMatrix inverse ξ ξ₇ hξ).det =
    ((normalizedMatrix inverse ξ ξ₇ hξ).map (Polynomial.evalRingHom (0 : ℝ))).det at he
  rw [normalized_zero inverse ξ ξ₇ hξ, Matrix.det_reindex_self] at he
  exact he

private theorem polynomial_split_21 (P : ℝ[X]) (a b : ℝ) (hP : P.coeff 0 = b) :
    ∃ R : ℝ[X], C a * (X ^ 21 * P) = X ^ 21 * C (a * b) + X ^ 22 * R := by
  obtain ⟨R, hR⟩ := Polynomial.X_dvd_iff.mpr (show (P - C b).coeff 0 = 0 by
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_zero, hP, sub_self])
  refine ⟨C a * R, ?_⟩
  have hh : P = C b + X * R := by linear_combination hR
  rw [hh, map_mul]
  ring

/-- Exact finite polynomial remainder, for every fixed seven distinct nodes.
The eighth node is arbitrary and affects only the remainder. -/
theorem polynomial_remainder (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    ∃ R : ℝ[X], coefficientPolynomial inverse ξ ξ₇ =
      X ^ 21 * C (vandermondeProduct ξ * (jet inverse).det) + X ^ 22 * R := by
  obtain ⟨R, hR⟩ := polynomial_split_21 (normalizedMatrix inverse ξ ξ₇ hξ).det
    (vandermondeProduct ξ) (jet inverse).det (normalized_det_zero inverse ξ ξ₇ hξ)
  exact ⟨R, (coefficient_det_factor inverse ξ ξ₇ hξ).trans hR⟩

/-- All coefficients below 21 vanish, for every distinct-node choice. -/
theorem coefficient_below (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (m : ℕ) (hm : m < 21) :
    (coefficientPolynomial inverse ξ ξ₇).coeff m = 0 := by
  obtain ⟨R, hR⟩ := polynomial_remainder inverse ξ ξ₇ hξ
  rw [hR, Polynomial.coeff_add]
  simp only [Polynomial.coeff_X_pow_mul', show ¬21 ≤ m by omega,
    show ¬22 ≤ m by omega, ite_false, add_zero]

theorem coefficient_at_21 (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (coefficientPolynomial inverse ξ ξ₇).coeff 21 =
      vandermondeProduct ξ * (jet inverse).det := by
  obtain ⟨R, hR⟩ := polynomial_remainder inverse ξ ξ₇ hξ
  simp only [hR, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    le_refl, ite_true, Nat.sub_self, Polynomial.coeff_C_zero,
    show ¬22 ≤ (21 : ℕ) by omega, ite_false, add_zero]

/-- The finite remainder is also a genuine analytic Big-O remainder at zero. -/
theorem remainder_isBigO (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (fun h : ℝ => (coefficientPolynomial inverse ξ ξ₇).eval h -
      h ^ 21 * (vandermondeProduct ξ * (jet inverse).det)) =O[𝓝 0]
      (fun h : ℝ => h ^ 22) := by
  obtain ⟨R, hR⟩ := polynomial_remainder inverse ξ ξ₇ hξ
  have hb := (R.continuous.tendsto 0).isBigO_one ℝ
  have hp := (Asymptotics.isBigO_refl (fun h : ℝ => h ^ 22) (𝓝 0)).mul hb
  convert hp using 1
  · funext h
    simp only [hR, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · funext h
    simp

/-- Ratio limit makes the precise angular order explicit. It is the coefficient
of lambda, and makes no assertion for a moving amplitude lambda(h). -/
theorem leading_ratio_limit (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    Filter.Tendsto (fun h : ℝ => (coefficientPolynomial inverse ξ ξ₇).eval h / h ^ 21)
      (𝓝[≠] 0) (𝓝 (vandermondeProduct ξ * (jet inverse).det)) := by
  obtain ⟨R, hR⟩ := polynomial_remainder inverse ξ ξ₇ hξ
  have he : (fun h : ℝ => (coefficientPolynomial inverse ξ ξ₇).eval h / h ^ 21) =ᶠ[𝓝[≠] 0]
      (fun h : ℝ => vandermondeProduct ξ * (jet inverse).det + h * R.eval h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hn : h ≠ 0 := hh
    simp only [hR, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    field_simp
  apply Filter.Tendsto.congr' he.symm
  have hc : Continuous (fun h : ℝ => vandermondeProduct ξ * (jet inverse).det + h * R.eval h) :=
    continuous_const.add (continuous_id.mul R.continuous)
  have ht := hc.tendsto (0 : ℝ)
  simpa using ht.mono_left nhdsWithin_le_nhds

def node (ξ : Fin 7 → ℝ) (ξ₇ : ℝ) : Index → ℝ := Sum.elim ξ (fun _ => ξ₇)

def smoothMatrix (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ h : ℝ) : Matrix Index Index ℝ :=
  fun i j => rootSmoothRow inverse (1 + h * node ξ ξ₇ i) (indexEquiv j)

/-- Actual root-normalized rows: errors are zero in the first seven rows, and
lambda in the eighth. The column order is exactly the maintained root row. -/
def witnessMatrix (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ h lam : ℝ) : Matrix Index Index ℝ :=
  fun i j => rootNormalizedRow inverse (1 + h * node ξ ξ₇ i)
    (Sum.elim (fun _ => 0) (fun _ => lam) i) (indexEquiv j)

/-- Exact affine dependence on lambda identifies the actual coefficient in the
8x8 determinant, rather than just a detached jet calculation. -/
theorem actual_determinant (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ h lam : ℝ) :
    (witnessMatrix inverse ξ ξ₇ h lam).det = (smoothMatrix inverse ξ ξ₇ h).det +
      lam * (coefficientPolynomial inverse ξ ξ₇).eval h := by
  let M := smoothMatrix inverse ξ ξ₇ h
  let q : Index → ℝ := fun j => rootErrorRow inverse (1 + h * ξ₇) (indexEquiv j)
  have hw : witnessMatrix inverse ξ ξ₇ h lam = M.updateRow (Sum.inr 0)
      (M (Sum.inr 0) + lam • q) := by
    ext i j
    cases i with
    | inl k => simp [witnessMatrix, rootNormalizedRow, M, smoothMatrix, Matrix.updateRow, Function.update, node]
    | inr k => fin_cases k; simp [witnessMatrix, rootNormalizedRow, M, q, smoothMatrix,
        Matrix.updateRow, Function.update, node]
  have hq : (coefficientMatrix inverse ξ ξ₇).map (Polynomial.evalRingHom h) =
      M.updateRow (Sum.inr 0) q := by
    ext i j
    cases i with
    | inl k =>
      change ((1 + C (ξ k) * X) ^ exponent inverse (indexEquiv j)).eval h =
        rootSmoothRow inverse (1 + h * ξ k) (indexEquiv j)
      rw [smooth_eq_power]
      simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      congr 1
      ring
    | inr k =>
      fin_cases k
      change (rootErrorRow inverse (1 + C ξ₇ * X) (indexEquiv j)).eval h =
        rootErrorRow inverse (1 + h * ξ₇) (indexEquiv j)
      simp only [rootErrorRow]
      split_ifs <;> simp only [Polynomial.eval_zero, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      all_goals congr 1 <;> ring
  have he := (Polynomial.evalRingHom h).map_det (coefficientMatrix inverse ξ ξ₇)
  change (coefficientPolynomial inverse ξ ξ₇).eval h =
    ((coefficientMatrix inverse ξ ξ₇).map (Polynomial.evalRingHom h)).det at he
  rw [hq] at he
  rw [hw, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, ← he]

/-- The allowed repeated eighth node kills the all-smooth determinant exactly. -/
theorem smooth_repeated_node (inverse : Bool) (ξ : Fin 7 → ℝ) (h : ℝ) :
    (smoothMatrix inverse ξ (ξ 0) h).det = 0 := by
  apply Matrix.det_zero_of_row_eq (i := Sum.inl (0 : Fin 7)) (j := Sum.inr (0 : Fin 1))
    (by simp)
  funext j
  rfl

/-- A concrete allowed choice of eighth node realizes the coefficient witness
in the actual determinant, with no all-smooth remainder to cancel it. -/
theorem actual_repeated_node (inverse : Bool) (ξ : Fin 7 → ℝ) (h lam : ℝ) :
    (witnessMatrix inverse ξ (ξ 0) h lam).det =
      lam * (coefficientPolynomial inverse ξ (ξ 0)).eval h := by
  rw [actual_determinant, smooth_repeated_node, zero_add]

/-- For a fixed amplitude, the actual repeated-node determinant has the same
ratio limit multiplied by that amplitude. The amplitude is fixed before h. -/
theorem actual_repeated_node_ratio (inverse : Bool) (ξ : Fin 7 → ℝ) (lam : ℝ)
    (hξ : Function.Injective ξ) :
    Filter.Tendsto (fun h : ℝ => (witnessMatrix inverse ξ (ξ 0) h lam).det / h ^ 21)
      (𝓝[≠] 0) (𝓝 (lam * (vandermondeProduct ξ * (jet inverse).det))) := by
  have ht := Filter.Tendsto.mul (tendsto_const_nhds (x := lam))
    (leading_ratio_limit inverse ξ (ξ 0) hξ)
  simpa only [actual_repeated_node, mul_div_assoc] using ht

/-- With a nonzero jet determinant, the coefficient has exact order 21:
all lower coefficients vanish and the coefficient at 21 is nonzero. -/
theorem exact_order (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) (hJ : (jet inverse).det ≠ 0) :
    (∀ m < 21, (coefficientPolynomial inverse ξ ξ₇).coeff m = 0) ∧
      (coefficientPolynomial inverse ξ ξ₇).coeff 21 ≠ 0 := by
  refine ⟨fun m hm => coefficient_below inverse ξ ξ₇ hξ m hm, ?_⟩
  rw [coefficient_at_21 inverse ξ ξ₇ hξ]
  apply mul_ne_zero _ hJ
  rw [vandermondeProduct, ← Matrix.det_vandermonde]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hξ

/-- The manuscript compact-node condition gives the original angular range. -/
theorem compact_node_range (x h : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hh : 0 ≤ h) :
    1 ≤ 1 + h*x ∧ 1 + h*x ≤ 1+h := by
  constructor <;> nlinarith

/-- Positive angular scale retains distinct nodes. -/
theorem scaled_nodes_injective (ξ : Fin 7 → ℝ) (hξ : Function.Injective ξ)
    (h : ℝ) (hh : h ≠ 0) : Function.Injective (fun i => 1+h*ξ i) := by
  intro i j hij
  apply hξ
  apply mul_left_cancel₀ hh
  linarith

/-- Both allowed signs have a nonzero amplitude within every positive cap. -/
theorem allowed_amplitude (inverse : Bool) (L : ℝ) (hL : 0 < L) :
    ∃ lam : ℝ, lam ≠ 0 ∧ |lam| ≤ L ∧ (if inverse then lam < 0 else 0 < lam) := by
  cases inverse
  · have hp : 0 < L/2 := by linarith
    refine ⟨L/2, ne_of_gt hp, ?_, ?_⟩
    · rw [abs_of_pos hp]
      linarith
    · change 0 < L/2
      exact hp
  · have hn : -L/2 < 0 := by linarith
    refine ⟨-L/2, ne_of_lt hn, ?_, ?_⟩
    · rw [abs_of_neg hn]
      linarith
    · change -L/2 < 0
      exact hn


/-- Both exact jet determinants, in the manuscript's ordered columns. -/
theorem jet_det (inverse : Bool) :
    (jet inverse).det = if inverse then (393660 : ℝ) else 2240 := by
  cases inverse
  · exact jet_direct
  · exact jet_inverse

/-- Complete section 13 coefficient witness for both charts, with the numerical
leading constants instantiated and no unproved determinant premise. -/
theorem section13_witness (inverse : Bool) (ξ : Fin 7 → ℝ) (ξ₇ : ℝ)
    (hξ : Function.Injective ξ) :
    (∃ R : ℝ[X], coefficientPolynomial inverse ξ ξ₇ =
      X ^ 21 * C (vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240)) + X ^ 22 * R) ∧
    (∀ m < 21, (coefficientPolynomial inverse ξ ξ₇).coeff m = 0) ∧
    (coefficientPolynomial inverse ξ ξ₇).coeff 21 =
      vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240) ∧
    (coefficientPolynomial inverse ξ ξ₇).coeff 21 ≠ 0 ∧
    ((fun h : ℝ => (coefficientPolynomial inverse ξ ξ₇).eval h -
      h ^ 21 * (vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240))) =O[𝓝 0]
      (fun h : ℝ => h ^ 22)) ∧
    Filter.Tendsto (fun h : ℝ => (coefficientPolynomial inverse ξ ξ₇).eval h / h ^ 21)
      (𝓝[≠] 0) (𝓝 (vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240))) := by
  have hJ : (jet inverse).det ≠ 0 := by
    rw [jet_det]
    cases inverse <;> norm_num
  refine ⟨?_, fun m hm => coefficient_below inverse ξ ξ₇ hξ m hm, ?_,
    (exact_order inverse ξ ξ₇ hξ hJ).2, ?_, ?_⟩
  · simpa only [jet_det] using polynomial_remainder inverse ξ ξ₇ hξ
  · simpa only [jet_det] using coefficient_at_21 inverse ξ ξ₇ hξ
  · simpa only [jet_det] using remainder_isBigO inverse ξ ξ₇ hξ
  · simpa only [jet_det] using leading_ratio_limit inverse ξ ξ₇ hξ

/-- Fixed nonzero amplitudes give an actual enlarged-model determinant with a
nonzero order-21 ratio limit, using the allowed eighth node ξ0. -/
theorem realized_witness (inverse : Bool) (ξ : Fin 7 → ℝ) (lam : ℝ)
    (hξ : Function.Injective ξ) (hlam : lam ≠ 0) :
    (∀ h : ℝ, (witnessMatrix inverse ξ (ξ 0) h lam).det =
      lam * (coefficientPolynomial inverse ξ (ξ 0)).eval h) ∧
    Filter.Tendsto (fun h : ℝ => (witnessMatrix inverse ξ (ξ 0) h lam).det / h ^ 21)
      (𝓝[≠] 0) (𝓝 (lam * (vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240)))) ∧
    lam * (vandermondeProduct ξ * (if inverse then (393660 : ℝ) else 2240)) ≠ 0 := by
  refine ⟨fun h => actual_repeated_node inverse ξ h lam, ?_, mul_ne_zero hlam ?_⟩
  · simpa only [jet_det] using actual_repeated_node_ratio inverse ξ lam hξ
  · have h := (section13_witness inverse ξ (ξ 0) hξ).2.2.2.1
    rw [(section13_witness inverse ξ (ξ 0) hξ).2.2.1] at h
    exact h

end
end P0365Subquarter.AngularWitness
