import PaperTargets.DividedMinors
import PaperProofs.RealSources
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open MvPolynomial

private abbrev RootPoly := MvPolynomial (Fin 8) ℝ

private def nodeSub (i j : Fin 8) : RootPoly →+* RootPoly :=
  eval₂Hom C (fun k => if k = i then X j else X k)

private theorem difference_dvd_sub (i j : Fin 8) (P : RootPoly) :
    X i - X j ∣ P - nodeSub i j P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [nodeSub]
  | add P Q hP hQ =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hP hQ
  | mul_X P k hP =>
    have hk : (X i - X j : RootPoly) ∣ X k - nodeSub i j (X k) := by
      by_cases h : k = i <;> simp [nodeSub, h]
    rw [map_mul]
    have hh := dvd_add (dvd_mul_of_dvd_left hP (X k))
      (dvd_mul_of_dvd_right hk (nodeSub i j P))
    convert hh using 1 <;> ring

private theorem difference_dvd_iff (i j : Fin 8) (hij : i ≠ j) (P : RootPoly) :
    X i - X j ∣ P ↔ nodeSub i j P = 0 := by
  constructor
  · intro h
    have hh := map_dvd (nodeSub i j) h
    simpa [nodeSub, hij, hij.symm] using hh
  · intro h
    simpa [h] using difference_dvd_sub i j P

private theorem difference_prime (i j : Fin 8) (hij : i ≠ j) :
    Prime (X i - X j : RootPoly) := by
  refine ⟨sub_ne_zero.mpr (MvPolynomial.X_injective.ne hij), ?_, ?_⟩
  · intro h
    have hh := h.map (nodeSub i j)
    have hz : IsUnit (0 : RootPoly) := by simp [nodeSub, hij, hij.symm] at hh
    exact not_isUnit_zero hz
  · intro P Q h
    rw [difference_dvd_iff i j hij, map_mul, mul_eq_zero] at h
    exact h.imp ((difference_dvd_iff i j hij P).2) ((difference_dvd_iff i j hij Q).2)

private def samePairs (S : Finset (Fin 8)) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ (ij.1 ∈ S ↔ ij.2 ∈ S))

private def mixedPoly (inverse : Bool) (S : Finset (Fin 8)) : RootPoly :=
  Matrix.det (Matrix.of (fun i j => if i ∈ S then rootErrorRow inverse (X i) j
    else rootSmoothRow inverse (X i) j))

private theorem difference_not_dvd (i j k l : Fin 8) (hij : i < j) (hkl : k < l)
    (hne : (i,j) ≠ (k,l)) : ¬ (X i - X j : RootPoly) ∣ X k - X l := by
  intro h
  rw [difference_dvd_iff i j hij.ne, nodeSub, map_sub] at h
  simp only [eval₂Hom_X', sub_eq_zero] at h
  have hh : (if k = i then j else k) = (if l = i then j else l) := by
    apply MvPolynomial.X_injective (R := ℝ)
    simpa only [apply_ite] using h
  by_cases hk : k = i
  · subst k
    have hl : l ≠ i := hkl.ne.symm
    simp only [ite_true, hl, ite_false] at hh
    exact hne (by simp [hh])
  · by_cases hl : l = i
    · subst l
      simp only [hk, ite_false, ite_true] at hh
      exact (not_lt_of_ge hij.le) (hh ▸ hkl)
    · simp only [hk, hl, ite_false] at hh
      exact hkl.ne hh

private theorem pair_single_dvd (inverse : Bool) (S : Finset (Fin 8))
    (ij : Fin 8 × Fin 8) (hij : ij ∈ samePairs S) :
    (X ij.1 - X ij.2 : RootPoly) ∣ mixedPoly inverse S := by
  obtain ⟨horder, hgroup⟩ := (Finset.mem_filter.mp hij).2
  rw [difference_dvd_iff ij.1 ij.2 horder.ne, mixedPoly, RingHom.map_det]
  apply Matrix.det_zero_of_row_eq horder.ne
  funext j
  by_cases hi : ij.1 ∈ S
  · have hj : ij.2 ∈ S := hgroup.mp hi
    by_cases hk : j.val < 4 <;>
      simp [rootErrorRow, rootSmoothRow, nodeSub, hi, hj, hk, horder.ne.symm]
  · have hj : ij.2 ∉ S := fun hj => hi (hgroup.mpr hj)
    by_cases hk : j.val < 4 <;>
      simp [rootErrorRow, rootSmoothRow, nodeSub, hi, hj, hk, horder.ne.symm]

private theorem pair_product_dvd (inverse : Bool) (S : Finset (Fin 8)) :
    (∏ ij ∈ samePairs S, (X ij.1 - X ij.2 : RootPoly)) ∣ mixedPoly inverse S := by
  have aux : ∀ T : Finset (Fin 8 × Fin 8), T ⊆ samePairs S →
      (∏ ij ∈ T, (X ij.1 - X ij.2 : RootPoly)) ∣ mixedPoly inverse S := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert ij T hnot ih =>
      intro hT
      have hi : ij ∈ samePairs S := hT (Finset.mem_insert_self _ _)
      have hT' : T ⊆ samePairs S := fun x hx => hT (Finset.mem_insert_of_mem hx)
      have horder := (Finset.mem_filter.mp hi).2.1
      have hp := difference_prime ij.1 ij.2 horder.ne
      obtain ⟨Q,hQ⟩ := ih hT'
      have hd := pair_single_dvd inverse S ij hi
      rw [hQ] at hd
      have hn : ¬ (X ij.1 - X ij.2 : RootPoly) ∣ ∏ kl ∈ T, (X kl.1 - X kl.2) := by
        apply hp.not_dvd_finsetProd
        intro kl hkl
        exact difference_not_dvd ij.1 ij.2 kl.1 kl.2 horder
          (Finset.mem_filter.mp (hT' hkl)).2.1 (by
            intro he
            have he' : ij = kl := by simpa using he
            exact hnot (by simpa only [he'] using hkl))
      obtain ⟨V,hV⟩ := (hp.dvd_mul.mp hd).resolve_left hn
      rw [Finset.prod_insert hnot]
      refine ⟨V, ?_⟩
      rw [hQ,hV]
      ring
  exact aux (samePairs S) (fun _ h => h)

set_option maxRecDepth 200000 in
private theorem pair_count : ∀ (S : Finset (Fin 8)) (k : Fin 5),
    S.card = k.val → (samePairs S).card = profileErrorWeight k := by decide

/-- A finite coefficient bound for a fixed polynomial on the root cube. -/
private def rootPolyBound (P : RootPoly) : ℝ :=
  ∑ d ∈ P.support, |P.coeff d| * ∏ i : Fin 8, (2 : ℝ) ^ d i

private theorem rootPolyBound_nonneg (P : RootPoly) : 0 ≤ rootPolyBound P := by
  unfold rootPolyBound
  positivity

private theorem eval_bound (P : RootPoly) (w : Fin 8 → ℝ) (hw : ∀ i, |w i| ≤ 2) :
    |eval w P| ≤ rootPolyBound P := by
  rw [eval_eq']
  calc
    _ ≤ ∑ d ∈ P.support, |P.coeff d * ∏ i, w i ^ d i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ P.support, |P.coeff d| * ∏ i, |w i| ^ d i := by
      simp only [abs_mul, Finset.abs_prod, abs_pow]
    _ ≤ rootPolyBound P := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hw i) _)

private theorem mixed_many_zero {R : Type*} [CommRing R]
    (inverse : Bool) (S : Finset (Fin 8)) (w : Fin 8 → R) (hS : 4 < S.card) :
    Matrix.det (Matrix.of (fun i j => if i ∈ S then rootErrorRow inverse (w i) j
      else rootSmoothRow inverse (w i) j)) = 0 := by
  classical
  rw [Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro σ hσ
  have hex : ∃ i : Fin 8, i.val < 4 ∧ σ i ∈ S := by
    by_contra hn
    have hsub : S.image σ.symm ⊆ Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hh
      exact hn ⟨σ.symm j, by omega, by simpa⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.symm.injective] at hc
    have hfour : (Finset.univ.filter (fun i : Fin 8 => 4 ≤ i.val)).card = 4 := by decide
    omega
  obtain ⟨i, hi, his⟩ := hex
  have hz : (∏ j : Fin 8, if σ j ∈ S then rootErrorRow inverse (w (σ j)) j
      else rootSmoothRow inverse (w (σ j)) j) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [his, rootErrorRow, hi]
  simp only [Matrix.of_apply, hz, mul_zero]

private theorem eval_mixedPoly (inverse : Bool) (S : Finset (Fin 8)) (w : Fin 8 → ℝ) :
    eval w (mixedPoly inverse S) = Matrix.det (Matrix.of (fun i j =>
      if i ∈ S then rootErrorRow inverse (w i) j else rootSmoothRow inverse (w i) j)) := by
  rw [mixedPoly, RingHom.map_det]
  congr 1
  ext i j
  by_cases hi : i ∈ S <;> by_cases hj : j.val < 4 <;>
    simp [hi, hj, rootErrorRow, rootSmoothRow]

/-- Exact polynomial divided differences, including repeated root nodes. -/
theorem mixed_root_determinants : CF11MixedRootDeterminants := by
  classical
  let Q (inverse : Bool) (S : Finset (Fin 8)) : RootPoly :=
    Classical.choose (pair_product_dvd inverse S)
  have hQ (inverse : Bool) (S : Finset (Fin 8)) : mixedPoly inverse S =
      (∏ ij ∈ samePairs S, (X ij.1 - X ij.2 : RootPoly)) * Q inverse S :=
    Classical.choose_spec (pair_product_dvd inverse S)
  let C : ℝ := 1 + ∑ inverse : Bool, ∑ S : Finset (Fin 8), rootPolyBound (Q inverse S)
  have hnonneg : 0 ≤ ∑ inverse : Bool, ∑ S : Finset (Fin 8), rootPolyBound (Q inverse S) := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => rootPolyBound_nonneg _))
  have hC : 0 < C := add_pos_of_pos_of_nonneg (by norm_num) hnonneg
  have hCQ (inverse : Bool) (S : Finset (Fin 8)) : rootPolyBound (Q inverse S) ≤ C := by
    have h₁ := Finset.single_le_sum (fun S (_ : S ∈ (Finset.univ : Finset (Finset (Fin 8)))) =>
      rootPolyBound_nonneg (Q inverse S)) (Finset.mem_univ S)
    have h₂ : (∑ T : Finset (Fin 8), rootPolyBound (Q inverse T)) ≤
        ∑ inv : Bool, ∑ T : Finset (Fin 8), rootPolyBound (Q inv T) :=
      Finset.single_le_sum (fun inv _ => Finset.sum_nonneg
        (fun T _ => rootPolyBound_nonneg (Q inv T))) (Finset.mem_univ inverse)
    exact (h₁.trans h₂).trans (le_add_of_nonneg_left (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro inverse S w h hh hw hdist
  constructor
  · exact mixed_many_zero inverse S w
  · intro k hk
    erw [← eval_mixedPoly, hQ, map_mul, abs_mul]
    have hprod : |eval w (∏ ij ∈ samePairs S, (X ij.1 - X ij.2 : RootPoly))| ≤
        h ^ profileErrorWeight k := by
      simp only [map_prod, map_sub, eval_X, Finset.abs_prod]
      calc
        _ ≤ ∏ _ij ∈ samePairs S, h :=
          Finset.prod_le_prod₀ (fun ij _ => abs_nonneg _) (fun ij _ => hdist _ _)
        _ = h ^ profileErrorWeight k := by simp [pair_count S k hk]
    have heval : |eval w (Q inverse S)| ≤ C :=
      (eval_bound _ w (fun i => (abs_of_nonneg (by linarith [(hw i).1])).trans_le (hw i).2)).trans (hCQ inverse S)
    calc
      _ ≤ h ^ profileErrorWeight k * C := mul_le_mul hprod heval (abs_nonneg _) (pow_nonneg hh _)
      _ = C * h ^ profileErrorWeight k := by ring

private theorem error_weight_le (k : Fin 5) : profileErrorWeight k ≤ 28 := by
  fin_cases k <;> norm_num [profileErrorWeight]

private theorem determinant_row_expansion {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : (A+B).det =
      ∑ S : Finset ι, (Matrix.of (S.piecewise A B)).det := by
  exact (Matrix.detRowAlternating (n := ι) (R := ℝ)).map_add_univ A B

private theorem mixed_expansion (inverse : Bool) (w β : Fin 8 → ℝ) :
    Matrix.det (Matrix.of (fun i j => rootNormalizedRow inverse (w i) (β i) j)) =
      ∑ S : Finset (Fin 8), (∏ i ∈ S, β i) *
        Matrix.det (Matrix.of (fun i j => if i ∈ S then rootErrorRow inverse (w i) j
          else rootSmoothRow inverse (w i) j)) := by
  let A (i : Fin 8) : Fin 8 → ℝ := fun j => rootSmoothRow inverse (w i) j
  let B (i : Fin 8) : Fin 8 → ℝ := fun j => β i * rootErrorRow inverse (w i) j
  have he := determinant_row_expansion (Matrix.of B) (Matrix.of A)
  have hfunc : Matrix.of B + Matrix.of A = Matrix.of (fun i j => rootNormalizedRow inverse (w i) (β i) j) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply, A, B, rootNormalizedRow]
    ring
  rw [hfunc] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro S hS
  have hm0 : Matrix.of (S.piecewise (Matrix.of B) (Matrix.of A)) =
      Matrix.of (fun i j => if i ∈ S then β i * rootErrorRow inverse (w i) j
        else rootSmoothRow inverse (w i) j) := by
    ext i j
    change (if i ∈ S then B i else A i) j =
      (if i ∈ S then β i * rootErrorRow inverse (w i) j else rootSmoothRow inverse (w i) j)
    by_cases hi : i ∈ S <;> simp [hi,A,B]
  rw [hm0]
  have hm : (Matrix.of (fun i j => if i ∈ S then β i * rootErrorRow inverse (w i) j
      else rootSmoothRow inverse (w i) j)) = Matrix.of (fun i j =>
        (if i ∈ S then β i else 1) *
          (if i ∈ S then rootErrorRow inverse (w i) j else rootSmoothRow inverse (w i) j)) := by
    ext i j; by_cases h : i ∈ S <;> simp [h]
  rw [hm]
  erw [Matrix.det_mul_column]
  rw [Finset.prod_ite_mem_eq]
  rfl

/-- Finite row expansion; the perturbations may vary independently by row. -/
theorem normalized_determinant_bound : CF11NormalizedDeterminantBound := by
  classical
  obtain ⟨C,hC,hroot⟩ := mixed_root_determinants
  let K := C * (8 : ℝ)^4 * (3 : ℝ)^28
  refine ⟨256 * K, by dsimp [K]; positivity, ?_⟩
  intro inverse X M w β hX hM hw hdist hβ
  have hXp : 0 < X := by linarith
  have hMp : 0 < M := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsum : 0 ≤ realErrorSum X M := by
    unfold realErrorSum; positivity
  erw [mixed_expansion]
  have hterm (S : Finset (Fin 8)) :
      |(∏ i ∈ S, β i) * Matrix.det (Matrix.of (fun i j =>
        if i ∈ S then rootErrorRow inverse (w i) j else rootSmoothRow inverse (w i) j))| ≤
        K * realErrorSum X M := by
    have hroots := hroot inverse S w (3/M) (by positivity) hw hdist
    by_cases hlarge : 4 < S.card
    · erw [hroots.1 hlarge, mul_zero, abs_zero]
      positivity
    · let k : Fin 5 := ⟨S.card, by omega⟩
      have hk : S.card = k.val := rfl
      have hD := hroots.2 k hk
      have hp : |∏ i ∈ S, β i| ≤ (8/X)^k.val := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _i ∈ S, 8/X := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
            (fun i _ => hβ i)
          _ = _ := by simp [hk, div_pow]
      have ha : profileErrorWeight k ≤ 28 := error_weight_le k
      have hc : C * (8:ℝ)^k.val * (3:ℝ)^profileErrorWeight k ≤ K := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega : k.val ≤ 4)) hC.le
        · exact pow_le_pow_right₀ (by norm_num) ha
        · positivity
        · positivity
      have hs : 1 / (X^k.val * M^profileErrorWeight k) ≤ realErrorSum X M := by
        unfold realErrorSum
        exact Finset.single_le_sum (f := fun j : Fin 5 => (1:ℝ) /
          (X^j.val * M^profileErrorWeight j)) (fun j _ => by positivity) (Finset.mem_univ k)
      rw [abs_mul]
      calc
        _ ≤ (8/X)^k.val * (C * (3/M)^profileErrorWeight k) :=
          mul_le_mul hp hD (abs_nonneg _) (by positivity)
        _ = (C * (8:ℝ)^k.val * (3:ℝ)^profileErrorWeight k) /
            (X^k.val * M^profileErrorWeight k) := by rw [div_pow,div_pow]; ring
        _ ≤ K / (X^k.val * M^profileErrorWeight k) := div_le_div_of_nonneg_right hc (by positivity)
        _ = K * (1 / (X^k.val * M^profileErrorWeight k)) := by ring
        _ ≤ K * realErrorSum X M := mul_le_mul_of_nonneg_left hs hK
  calc
    _ ≤ ∑ S : Finset (Fin 8), |(∏ i ∈ S, β i) * Matrix.det (Matrix.of (fun i j =>
        if i ∈ S then rootErrorRow inverse (w i) j else rootSmoothRow inverse (w i) j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S : Finset (Fin 8), K * realErrorSum X M := Finset.sum_le_sum (fun S _ => hterm S)
    _ = (256 * K) * realErrorSum X M := by simp; ring

private theorem source_data (n b d u v : ℕ) (h : PairSource n b d u v) :
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

private theorem source_coordinate_pos (n b d u v : ℕ) (h : PairSource n b d u v)
    (inverse : Bool) : 0 < realSourceCoordinate inverse b d u v := by
  have hh := source_data n b d u v h
  cases inverse <;> simp only [realSourceCoordinate, Bool.false_eq_true, ite_false, ite_true]
  · exact div_pos hh.2.1 hh.2.2.1
  · exact div_pos hh.2.2.2.2.1 hh.2.2.2.1

private theorem root_powers (inverse : Bool) (z : ℝ) (hz : 0 < z) :
    (z ^ (1 / (realRootOrder inverse : ℝ))) ^ realRootOrder inverse = z ∧
      (z ^ (1 / (realRootOrder inverse : ℝ))) ^ realRootPartnerOrder inverse =
        z ^ realChartExponent inverse := by
  constructor
  · have h : realRootOrder inverse ≠ 0 := by cases inverse <;> decide
    simpa only [one_div] using Real.rpow_inv_natCast_pow hz.le h
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    cases inverse <;> norm_num [realRootOrder,realRootPartnerOrder,realChartExponent]

private theorem root_row_identity (inverse : Bool) (z β : ℝ) (hz : 0 < z) (j : Fin 8) :
    realNormalizedRow inverse z β j = rootNormalizedRow inverse
      (z ^ (1 / (realRootOrder inverse : ℝ))) β j := by
  have hp := root_powers inverse z hz
  unfold realNormalizedRow rootNormalizedRow rootSmoothRow rootErrorRow
  by_cases hj : j.val < 4 <;>
    simp only [hj, ite_true, ite_false, pow_mul, hp.1, hp.2, mul_one, mul_zero, add_zero] <;> ring

private theorem source_ratio_square (n b d u v : ℕ) (h : PairSource n b d u v) :
    ((v : ℝ)/u)^2 = ((b : ℝ)/d)^3 * (1 + 1/(n : ℝ)) := by
  obtain ⟨hn,hb,hd,hu,hv,hnid,heq⟩ := source_data n b d u v h
  have hh : (n:ℝ) * ((v:ℝ)/u)^2 = ((n:ℝ)+1) * ((b:ℝ)/d)^3 := by
    field_simp
    nlinarith [heq]
  apply mul_left_cancel₀ hn.ne'
  calc
    _ = ((n:ℝ)+1) * ((b:ℝ)/d)^3 := hh
    _ = _ := by field_simp

/-- Both root nodes in fact lie in [1,1+1/M]; the target's 3/M is conservative. -/
theorem actual_interval_nodes : CF11ActualIntervalNodes := by
  intro n b d u v hs X M a hX hXn hM hMX ha hint
  have hn := (source_data n b d u v hs).1
  have hMp : 0 < M := by linarith
  have hspos := source_coordinate_pos n b d u v hs false
  have htpos := source_coordinate_pos n b d u v hs true
  let z : ℝ := (b:ℝ)/d/a
  let q : ℝ := 1+1/M
  have hzpos : 0 < z := div_pos hspos ha
  have hz1 : 1 ≤ z := (le_div_iff₀ ha).2 (by simpa using hint.1)
  have hzq : z ≤ q := (div_le_iff₀ ha).2 (by simpa [q,mul_comm] using hint.2)
  have hq1 : 1 ≤ q := by
    have hh : 0 ≤ 1/M := by positivity
    dsimp [q]
    linarith
  have hq2 : q ≤ 2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hM
    simp only [one_div_one] at hh
    dsimp [q]
    linarith
  have hnrec : 1+1/(n:ℝ) ≤ q := by
    have hh := one_div_le_one_div_of_le hMp (hMX.trans hXn)
    dsimp [q]; linarith
  have hwpos (inverse : Bool) : 0 < realIntervalNode inverse a b d u v := by
    unfold realIntervalNode
    apply Real.rpow_pos_of_pos
    apply div_pos (source_coordinate_pos n b d u v hs inverse)
    cases inverse <;> simp only [realIntervalScale, Bool.false_eq_true, ite_false, ite_true]
    · exact ha
    · exact Real.rpow_pos_of_pos ha _
  have hw0 : realIntervalNode false a b d u v ^ (2:ℕ) = z :=
    (root_powers false z hzpos).1
  have hzInv : 0 < ((v:ℝ)/u) / a^(3/2:ℝ) :=
    div_pos htpos (Real.rpow_pos_of_pos ha _)
  have hw3 : realIntervalNode true a b d u v ^ (3:ℕ) = ((v:ℝ)/u)/a^(3/2:ℝ) :=
    (root_powers true _ hzInv).1
  have ha2 : (a^(3/2:ℝ))^(2:ℕ) = a^3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
  have hw6 : realIntervalNode true a b d u v ^ (6:ℕ) = z^3*(1+1/(n:ℝ)) := by
    calc
      _ = (realIntervalNode true a b d u v ^ (3:ℕ))^2 := by ring
      _ = (((v:ℝ)/u)/a^(3/2:ℝ))^2 := by rw [hw3]
      _ = ((v:ℝ)/u)^2/a^3 := by rw [div_pow,ha2]
      _ = z^3*(1+1/(n:ℝ)) := by rw [source_ratio_square n b d u v hs]; dsimp [z]; rw [div_pow]; ring
  have hnodes (inverse : Bool) : 1 ≤ realIntervalNode inverse a b d u v ∧
      realIntervalNode inverse a b d u v ≤ q := by
    cases inverse
    · constructor
      · apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ)≤1) (hwpos false).le (by decide : (2:ℕ)≠0)).mp
        simpa [hw0] using hz1
      · apply (pow_le_pow_iff_left₀ (hwpos false).le (by linarith : 0≤q) (by decide : (2:ℕ)≠0)).mp
        rw [hw0]
        nlinarith
    · have hz3 : 1 ≤ z^3 := by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hz1 3
      constructor
      · apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ)≤1) (hwpos true).le (by decide : (6:ℕ)≠0)).mp
        rw [one_pow,hw6]
        calc
          (1:ℝ) = 1*1 := by ring
          _ ≤ z^3*(1+1/(n:ℝ)) := mul_le_mul hz3 (by
            have hh : 0 ≤ 1/(n:ℝ) := by positivity
            linarith) (by norm_num) (by linarith)
      · apply (pow_le_pow_iff_left₀ (hwpos true).le (by linarith : 0≤q) (by decide : (6:ℕ)≠0)).mp
        rw [hw6]
        calc
          _ ≤ q^3*q := mul_le_mul (pow_le_pow_left₀ hzpos.le hzq 3) hnrec (by positivity) (by positivity)
          _ = q^4 := by ring
          _ ≤ q^6 := pow_le_pow_right₀ hq1 (by norm_num)
  intro inverse
  have hw := hnodes inverse
  refine ⟨hw.1, hw.2.trans hq2, hw.2.trans ?_, ?_, ?_⟩
  · exact add_le_add (le_refl (1:ℝ)) (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤3) hMp.le)
  · have herr : |realSourceError inverse b d u v| ≤ 1/(n:ℝ) := by
      have hh := actual_relative_errors n b d u v hs
      cases inverse <;> apply abs_le.2 <;> constructor <;> simp_all <;> linarith
    have hscale : 0 < realIntervalScale inverse a := by
      cases inverse <;> simp only [realIntervalScale, Bool.false_eq_true, ite_false, ite_true]
      · exact ha
      · exact Real.rpow_pos_of_pos ha _
    have hp := (root_powers inverse _ (div_pos (source_coordinate_pos n b d u v hs inverse) hscale)).2
    have hpower : |realIntervalNode inverse a b d u v ^ realRootPartnerOrder inverse| ≤ 8 := by
      rw [abs_pow,abs_of_nonneg (hwpos inverse).le]
      calc
        _ ≤ (2:ℝ)^realRootPartnerOrder inverse := pow_le_pow_left₀ (hwpos inverse).le (hw.2.trans hq2) _
        _ ≤ 8 := by cases inverse <;> norm_num [realRootPartnerOrder]
    unfold realNormalizedError
    rw [abs_mul, ← hp]
    have hrec := one_div_le_one_div_of_le (by linarith : 0<X) hXn
    calc
      _ ≤ 8*(1/(n:ℝ)) := mul_le_mul hpower herr (abs_nonneg _) (by norm_num)
      _ ≤ 8/X := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrec (by norm_num : (0:ℝ)≤8)
  · intro j
    have hscale : 0 < realIntervalScale inverse a := by
      cases inverse <;> simp only [realIntervalScale, Bool.false_eq_true, ite_false, ite_true]
      · exact ha
      · exact Real.rpow_pos_of_pos ha _
    exact root_row_identity inverse _ _
      (div_pos (source_coordinate_pos n b d u v hs inverse) hscale) j

private theorem column_product (inverse : Bool) (a : ℝ) :
    (∏ j : Fin 8, realColumnScale inverse a j) = a^12 * (a^realChartExponent inverse)^4 := by
  norm_num [Fin.prod_univ_succ,realColumnScale]
  ring

private theorem interval_column_product (inverse : Bool) (a : ℝ) (ha : 0<a) :
    (∏ j : Fin 8, realColumnScale inverse (realIntervalScale inverse a) j) =
      a^(if inverse then 22 else 18 : ℕ) := by
  rw [column_product]
  cases inverse
  · change a^12*(a^(3/2:ℝ))^4 = a^18
    have hh : (a^(3/2:ℝ))^(4:ℕ) = a^6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
    rw [hh]; ring
  · change (a^(3/2:ℝ))^12*((a^(3/2:ℝ))^(2/3:ℝ))^4 = a^22
    have hh : (a^(3/2:ℝ))^(12:ℕ) = a^18 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]; norm_num
    have hh' : (a^(3/2:ℝ))^(2/3:ℝ) = a := by
      rw [← Real.rpow_mul ha.le]; norm_num
    rw [hh,hh']; ring

/-- The real estimate applies directly to the original eight integer rows. -/
theorem actual_box_determinant_bound : CF11ActualBoxDeterminantBound := by
  classical
  obtain ⟨C,hC,hN⟩ := normalized_determinant_bound
  let K : ℝ := (16:ℝ)^8 * (2:ℝ)^22
  refine ⟨K*C, by dsimp [K]; positivity, ?_⟩
  intro X M B E a hX hM hMX hB hE ha n b d u v hs hbox hint inverse
  have hXp : 0<X := by linarith
  let U : ℝ := (X/B^3)^(1/2:ℝ)
  have hUp : 0<U := Real.rpow_pos_of_pos (div_pos hXp (pow_pos hB 3)) _
  have hU2 : U^2 = X/B^3 := (root_powers false _ (div_pos hXp (pow_pos hB 3))).1
  have hUX : U^2*B^3 = X := by rw [hU2]; field_simp
  have hu (i : Fin 8) : (u i : ℝ) ≤ 2*U := by
    obtain ⟨hn,hb,hd,hui,hv,hnid,heq⟩ := source_data (n i) (b i) (d i) (u i) (v i) (hs i)
    obtain ⟨hni,hni',hbi,hbi',hdi,hdi'⟩ := hbox i
    have hh : (u i : ℝ)^2*B^3 ≤ (2*U^2)*B^3 := by
      calc
        _ ≤ (u i : ℝ)^2*(b i : ℝ)^3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB.le hbi 3) (sq_nonneg _)
        _ = (n i : ℝ) := by rw [hnid]; ring
        _ ≤ 2*X := hni'
        _ = _ := by rw [mul_assoc, hUX]
    have hh' : (u i : ℝ)^2 ≤ 2*U^2 := (mul_le_mul_iff_left₀ (pow_pos hB 3)).mp (by simpa [mul_comm] using hh)
    nlinarith
  have hacap : a ≤ 2*(B/E) := by
    obtain ⟨hn,hb,hd,hu0,hv,hnid,heq⟩ := source_data (n 0) (b 0) (d 0) (u 0) (v 0) (hs 0)
    obtain ⟨hni,hni',hbi,hbi',hdi,hdi'⟩ := hbox 0
    calc
      a ≤ (b 0 : ℝ)/d 0 := (hint 0).1
      _ ≤ (b 0 : ℝ)/E := div_le_div_of_nonneg_left hb.le hE hdi
      _ ≤ (2*B)/E := div_le_div_of_nonneg_right hbi' hE.le
      _ = 2*(B/E) := by ring
  let R : ℝ := if inverse then E*U^3 else E^3*U
  have hR : 0<R := by cases inverse <;> dsimp [R] <;> positivity
  have hD (i : Fin 8) : 0 ≤ (sourceRowDenominator inverse (d i) (u i) : ℝ) ∧
      (sourceRowDenominator inverse (d i) (u i) : ℝ) ≤ 16*R := by
    have hui := hu i
    have hdi := (hbox i).2.2.2.2.2
    have hi := source_data (n i) (b i) (d i) (u i) (v i) (hs i)
    cases inverse <;> simp only [sourceRowDenominator,R,Bool.false_eq_true,ite_false,ite_true,
      Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    · refine ⟨by positivity, ?_⟩
      calc
        _ ≤ (2*E)^3*(2*U) := mul_le_mul (pow_le_pow_left₀ hi.2.2.1.le hdi 3) hui hi.2.2.2.1.le (by positivity)
        _ = _ := by ring
    · refine ⟨by positivity, ?_⟩
      calc
        _ ≤ (2*E)*(2*U)^3 := mul_le_mul hdi (pow_le_pow_left₀ hi.2.2.2.1.le hui 3) (by positivity) (by positivity)
        _ = _ := by ring
  have hDP : 0 ≤ ∏ i : Fin 8, (sourceRowDenominator inverse (d i) (u i) : ℝ) :=
    Finset.prod_nonneg (fun i _ => (hD i).1)
  have hDPub : (∏ i : Fin 8, (sourceRowDenominator inverse (d i) (u i) : ℝ)) ≤ (16:ℝ)^8*R^8 := by
    calc
      _ ≤ ∏ _i : Fin 8, 16*R := Finset.prod_le_prod₀ (fun i _ => (hD i).1) (fun i _ => (hD i).2)
      _ = _ := by simp [mul_pow]
  let e : ℕ := if inverse then 22 else 18
  have he : e ≤ 22 := by cases inverse <;> decide
  have hCP : 0 ≤ ∏ j : Fin 8, realColumnScale inverse (realIntervalScale inverse a) j := by
    rw [interval_column_product inverse a ha]; positivity
  have hCPub : (∏ j : Fin 8, realColumnScale inverse (realIntervalScale inverse a) j) ≤
      (2:ℝ)^22*(B/E)^e := by
    rw [interval_column_product inverse a ha]
    change a^e ≤ _
    calc
      _ ≤ (2*(B/E))^e := pow_le_pow_left₀ ha.le hacap e
      _ = (2:ℝ)^e*(B/E)^e := mul_pow _ _ _
      _ ≤ (2:ℝ)^22*(B/E)^e := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) he) (by positivity)
  have hcancel : R^8*(B/E)^e = realBoxScale inverse X B E := by
    have hh := real_scale_cancellation B E U X hB hE hUX
    cases inverse
    · exact hh.1
    · exact hh.2
  have hboxnonneg : 0 ≤ realBoxScale inverse X B E := by
    cases inverse <;> dsimp [realBoxScale] <;> positivity
  have hpref : (∏ i : Fin 8, (sourceRowDenominator inverse (d i) (u i) : ℝ)) *
      (∏ j : Fin 8, realColumnScale inverse (realIntervalScale inverse a) j) ≤
        K*realBoxScale inverse X B E := by
    calc
      _ ≤ ((16:ℝ)^8*R^8)*((2:ℝ)^22*(B/E)^e) := mul_le_mul hDPub hCPub hCP (by positivity)
      _ = K*(R^8*(B/E)^e) := by dsimp [K]; ring
      _ = _ := by rw [hcancel]
  have hdata (i : Fin 8) := actual_interval_nodes (n i) (b i) (d i) (u i) (v i)
    (hs i) X M a hX (hbox i).1 hM hMX ha (hint i) inverse
  have hsize : |Matrix.det (Matrix.of (fun i j => realNormalizedRow inverse
      (realSourceCoordinate inverse (b i) (d i) (u i) (v i) / realIntervalScale inverse a)
      (realNormalizedError inverse (realIntervalScale inverse a) (b i) (d i) (u i) (v i)) j))| ≤ C*realErrorSum X M := by
    have heq : Matrix.of (fun i j => realNormalizedRow inverse
        (realSourceCoordinate inverse (b i) (d i) (u i) (v i) / realIntervalScale inverse a)
        (realNormalizedError inverse (realIntervalScale inverse a) (b i) (d i) (u i) (v i)) j) =
      Matrix.of (fun i j => rootNormalizedRow inverse (realIntervalNode inverse a (b i) (d i) (u i) (v i))
        (realNormalizedError inverse (realIntervalScale inverse a) (b i) (d i) (u i) (v i)) j) := by
      ext i j; exact (hdata i).2.2.2.2 j
    rw [heq]
    apply hN inverse X M _ _ hX hM
    · intro i; exact ⟨(hdata i).1,(hdata i).2.1⟩
    · intro i j; apply abs_le.2; constructor <;>
        linarith [(hdata i).1,(hdata i).2.2.1,(hdata j).1,(hdata j).2.2.1]
    · intro i; exact (hdata i).2.2.2.1
  have hscale : 0 < realIntervalScale inverse a := by
    cases inverse <;> dsimp [realIntervalScale] <;> positivity
  erw [actual_minor_normalization n b d u v hs inverse (realIntervalScale inverse a) hscale]
  rw [abs_mul,abs_mul,abs_of_nonneg hDP,abs_of_nonneg hCP]
  calc
    _ ≤ (K*realBoxScale inverse X B E)*(C*realErrorSum X M) :=
      mul_le_mul hpref hsize (abs_nonneg _) (mul_nonneg (by dsimp [K]; positivity) hboxnonneg)
    _ = _ := by ring

private theorem rounded_height_le_X (X ψ δ : ℝ) (hX : 4≤X)
    (hψ0 : 0≤ψ) (hψ2 : ψ≤2/3) (hδ : 0≤δ) (hδ1 : δ≤1) :
    (roundedHeight X ψ δ : ℝ) ≤ X := by
  have hX1 : 1≤X := by linarith
  have hXp : 0<X := by linarith
  have hp := profile_bounds ψ hψ0 hψ2
  have hm : (1+δ)*profileM0 ψ ≤ (1/2:ℝ) := by
    calc
      _ ≤ 2*profileM0 ψ := mul_le_mul_of_nonneg_right (by linarith) hp.1
      _ ≤ 2*(3/16:ℝ) := mul_le_mul_of_nonneg_left hp.2.1 (by norm_num)
      _ ≤ 1/2 := by norm_num
  let t := X^(1/2:ℝ)
  have ht : 0<t := Real.rpow_pos_of_pos hXp _
  have ht2 : t^2 = X := (root_powers false X hXp).1
  have htwo : (2:ℝ)≤t := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ)≤2) ht.le (by decide : (2:ℕ)≠0)).mp
    simpa only [ht2, show (2:ℝ)^2=4 by norm_num] using hX
  calc
    _ ≤ 2*X^((1+δ)*profileM0 ψ) := (rounded_height_bounds X ψ δ hX1 hψ0 hψ2 hδ).2.2
    _ ≤ 2*t := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hm) (by norm_num)
    _ ≤ X := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htwo)]

private theorem profile_box_scale (X ψ B E : ℝ) (hX : 0<X) (hBE : B*E=X^ψ) :
    realBoxScale (selectedRealChart ψ) X B E = X^profileW ψ := by
  by_cases hc : ψ≤profileCentre
  · rw [selectedRealChart,ite_eq_left hc]
    simp only [realBoxScale,Bool.false_eq_true,ite_false]
    rw [hBE,(chart_branches ψ).1 hc]
    rw [← Real.rpow_natCast X 4,← Real.rpow_natCast (X^ψ) 6,← Real.rpow_mul hX.le,
      ← Real.rpow_add hX]
    congr 1; ring
  · rw [selectedRealChart,ite_eq_right hc]
    simp only [realBoxScale,ite_true]
    rw [hBE,(chart_branches ψ).2 (le_of_lt (lt_of_not_ge hc))]
    rw [← Real.rpow_natCast X 12,← Real.rpow_natCast (X^ψ) 14,← Real.rpow_mul hX.le,
      ← Real.rpow_sub hX]
    congr 1; ring

private theorem rounded_error_sum_identity (X ψ δ : ℝ) (hX : 0<X) :
    X^profileW ψ * realErrorSum X (roundedHeight X ψ δ : ℝ) =
      ∑ k : Fin 5, roundedMixedTerm X ψ δ k := by
  unfold realErrorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [roundedMixedTerm,Real.rpow_sub hX,Real.rpow_natCast,Real.rpow_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- All real analytic size hypotheses are now conclusions for actual boxes. -/
theorem rounded_actual_determinant_bound : CF11RoundedActualDeterminantBound := by
  obtain ⟨C,hC,hboxbound⟩ := actual_box_determinant_bound
  refine ⟨C,hC,?_⟩
  intro X ψ δ B E a hX hψ0 hψ2 hδ hδ1 hB hE ha hBE n b d u v hs hbox hint
  have hX1 : 1≤X := by linarith
  have hM := rounded_height_bounds X ψ δ hX1 hψ0 hψ2 hδ
  have hh := hboxbound X (roundedHeight X ψ δ : ℝ) B E a hX1 hM.1
    (rounded_height_le_X X ψ δ hX hψ0 hψ2 hδ hδ1) hB hE ha n b d u v hs hbox hint (selectedRealChart ψ)
  rw [profile_box_scale X ψ B E (by linarith) hBE] at hh
  calc
    _ ≤ C*X^profileW ψ*realErrorSum X (roundedHeight X ψ δ : ℝ) := hh
    _ = _ := by rw [mul_assoc,rounded_error_sum_identity X ψ δ (by linarith)]

/-- CF10 and the proved actual real bound annihilate the SAME integer minor. -/
theorem rounded_actual_minor_vanishing : CF11RoundedActualMinorVanishing := by
  intro δ hδ hδ1
  obtain ⟨C,hC,hactual⟩ := rounded_actual_determinant_bound
  obtain ⟨X₀,hX₀,hzero⟩ := rounded_minor_vanishing δ C hδ hC.le
  refine ⟨max 4 X₀,le_max_left _ _,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p n b d u v hp hscale hs hbox hint hcurve hgood hres
  have hX4 : 4≤X := (le_max_left 4 X₀).trans hX
  have hX0 : X₀≤X := (le_max_right 4 X₀).trans hX
  apply hzero X ψ hX0 hψ0 hψ2 F p n b d u v hp hscale hs hcurve hgood hres (selectedRealChart ψ)
  exact hactual X ψ δ B E a hX4 hψ0 hψ2 hδ.le hδ1 hB hE ha hBE n b d u v hs hbox hint

end
end P0365Subquarter
