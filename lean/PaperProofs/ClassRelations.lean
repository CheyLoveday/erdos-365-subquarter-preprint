import PaperTargets.ClassRelations
import PaperProofs.DividedMinors
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Nat.Find

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem integer_det_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (H : ℝ) (hH : 0 ≤ H) (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    |((A.det : ℤ) : ℝ)| ≤ (n.factorial : ℝ)*H^n := by
  rw [Int.cast_det, Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
        |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (A (σ i) i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, |(A (σ i) i : ℝ)| := by
      simp only [abs_mul, abs_unit_intCast, one_mul, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), H^n := by
      apply Finset.sum_le_sum
      intro σ hσ
      calc
        _ ≤ ∏ _i : Fin n, H := Finset.prod_le_prod₀
          (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = H^n := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- Tag actual rows separately from coordinate rows, even when values coincide. -/
private def rowCompletion {ι : Type} (A : ι → Fin 8 → ℤ) (k : ℕ) : Prop :=
  ∃ (S : Finset (Fin 8)) (B : Matrix (Fin 8) (Fin 8) ℤ),
    S.card = k ∧ B.det ≠ 0 ∧ (∀ i ∈ S, ∃ x : ι, B i = A x) ∧
      ∀ i ∉ S, ∃ j : Fin 8, B i = Pi.single j 1

private theorem completion_zero {ι : Type} (A : ι → Fin 8 → ℤ) : rowCompletion A 0 := by
  refine ⟨∅,1,by simp,by simp,by simp,?_⟩
  intro i hi
  refine ⟨i,?_⟩
  ext j
  simp [Matrix.one_apply,Pi.single_apply,eq_comm]

/-- One cofactor column from a maximal actual/unit completion covers every row. -/
theorem bounded_integer_relation : CF12BoundedIntegerRelation := by
  classical
  intro ι A H hH hA hzero
  let q := Nat.findGreatest (rowCompletion A) 8
  obtain ⟨S,B,hcard,hdet,hrows,hunits⟩ :=
    Nat.findGreatest_spec (by norm_num : 0 ≤ 8) (completion_zero A)
  have hq : q ≤ 8 := Nat.findGreatest_le 8
  have hq8 : q < 8 := by
    by_contra hh
    have hS : S = Finset.univ := Finset.eq_univ_of_card S (by simpa [hcard] using (show q = 8 by omega))
    have hx (i : Fin 8) : ∃ x : ι, B i = A x := hrows i (by simp [hS])
    choose f hf using hx
    apply hdet
    have he : B = Matrix.of (fun i j => A (f i) j) := by
      ext i j
      exact congrFun (hf i) j
    rw [he]
    exact hzero f
  obtain ⟨r,hr⟩ : ∃ r : Fin 8, r ∉ S := by
    obtain ⟨r,_,hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show S.card < (Finset.univ : Finset (Fin 8)).card by simpa [hcard] using hq8)
    exact ⟨r,hr⟩
  let c : Fin 8 → ℤ := fun j => B.adjugate j r
  have hc : c ≠ 0 := by
    intro hz
    apply hdet
    rw [Matrix.det_eq_sum_mul_adjugate_row B r]
    have hz' (j : Fin 8) : B.adjugate j r = 0 := congrFun hz j
    simp [hz']
  have hBH (i j : Fin 8) : |(B i j : ℝ)| ≤ H := by
    by_cases hi : i ∈ S
    · obtain ⟨x,hx⟩ := hrows i hi
      rw [congrFun hx j]
      exact hA x j
    · obtain ⟨k,hk⟩ := hunits i hi
      rw [congrFun hk j]
      by_cases hj : j = k <;> simp [Pi.single_apply,hj,hH,le_trans (by norm_num : (0:ℝ)≤1) hH]
  refine ⟨c,hc,?_,?_⟩
  · intro j
    dsimp [c]
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    simpa only [show (Nat.factorial 7 : ℝ) = 5040 by norm_num [Nat.factorial]] using integer_det_bound (B.submatrix r.succAbove j.succAbove) H (by linarith)
      (fun i k => hBH _ _)
  · intro x
    have hz : (B.updateRow r (A x)).det = 0 := by
      by_contra hn
      have hp : rowCompletion A (q+1) := by
        refine ⟨insert r S,B.updateRow r (A x),?_,hn,?_,?_⟩
        · rw [Finset.card_insert_of_notMem hr,hcard]
        · intro i hi
          by_cases hir : i = r
          · subst i; exact ⟨x,Matrix.updateRow_self⟩
          · rw [Matrix.updateRow_ne hir]
            exact hrows i ((Finset.mem_insert.mp hi).resolve_left hir)
        · intro i hi
          have hir : i ≠ r := fun h => hi (by simp [h])
          rw [Matrix.updateRow_ne hir]
          exact hunits i (fun h => hi (Finset.mem_insert_of_mem h))
      exact Nat.findGreatest_is_greatest (show q < q+1 by omega)
        (show q+1 ≤ 8 by omega) hp
    have hadj (j : Fin 8) : (B.updateRow r (A x)).adjugate j r = B.adjugate j r := by
      simp only [Matrix.adjugate_apply,Matrix.updateRow_idem]
    rw [Matrix.det_eq_sum_mul_adjugate_row _ r] at hz
    simpa only [Matrix.updateRow_self,hadj] using hz


private theorem mixed_power_bound (a b L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (haL : a ≤ L) (hbL : b ≤ L) (k : ℕ) (hk : k ≤ 3) :
    a^k*b^(3-k) ≤ L^3 := by
  calc
    _ ≤ L^k*L^(3-k) := mul_le_mul (pow_le_pow_left₀ ha haL _)
      (pow_le_pow_left₀ hb hbL _) (pow_nonneg hb _) (pow_nonneg hL _)
    _ = _ := by rw [← pow_add,Nat.add_sub_of_le hk]

/-- The common sixth-root scale controls both original chart row heights. -/
theorem source_row_height : CF12SourceRowHeight := by
  intro X hX n b d u v hs hn inverse j
  have hXp : 0 < X := by linarith
  have hY : 1 ≤ 3*X := by linarith
  let W : ℝ := (3*X)^(1/6 : ℝ)
  have hW : 1 ≤ W := Real.one_le_rpow hY (by norm_num)
  have hW0 : 0 ≤ W := by linarith
  have hW6 : W^6 = 3*X := by
    dsimp [W]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 3*X)]
    norm_num
  have hn1 : (n : ℝ)+1 ≤ 3*X := by linarith
  obtain ⟨hb3,hu2,hd3,hv2⟩ := source_bounds n b d u v hs
  have hkernel (a : ℕ) (ha : (a : ℝ)^3 ≤ (n : ℝ)+1) : (a : ℝ) ≤ W^2 := by
    apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg a) (pow_nonneg hW0 2) (by decide : (3:ℕ) ≠ 0)).mp
    calc
      _ ≤ (n : ℝ)+1 := ha
      _ ≤ 3*X := hn1
      _ = (W^2)^3 := by rw [← pow_mul]; exact hW6.symm
  have hmult (a : ℕ) (ha : (a : ℝ)^2 ≤ (n : ℝ)+1) : (a : ℝ) ≤ W^3 := by
    apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg a) (pow_nonneg hW0 3) (by decide : (2:ℕ) ≠ 0)).mp
    calc
      _ ≤ (n : ℝ)+1 := ha
      _ ≤ 3*X := hn1
      _ = (W^3)^2 := by rw [← pow_mul]; exact hW6.symm
  have hb : (b : ℝ) ≤ W^2 := hkernel b (by
    have h : (b:ℝ)^3 ≤ (n:ℝ) := by exact_mod_cast hb3
    linarith)
  have hd : (d : ℝ) ≤ W^2 := hkernel d (by exact_mod_cast hd3)
  have hu : (u : ℝ) ≤ W^3 := hmult u (by
    have h : (u:ℝ)^2 ≤ (n:ℝ) := by exact_mod_cast hu2
    linarith)
  have hv : (v : ℝ) ≤ W^3 := hmult v (by exact_mod_cast hv2)
  have hk : j.val % 4 ≤ 3 := by omega
  have hentry : 0 ≤ (sourceIntegerRow inverse b d u v j : ℝ) := by
    cases inverse <;> simp only [sourceIntegerRow,Bool.false_eq_true,ite_false,ite_true,
      Int.cast_mul,Int.cast_pow,Int.cast_natCast] <;> split_ifs <;> positivity
  rw [abs_of_nonneg hentry]
  have hroot : (sourceIntegerRow inverse b d u v j : ℝ) ≤ W^11 := by
    cases inverse
    · have hm := mixed_power_bound (b:ℝ) (d:ℝ) (W^2) (by positivity) (by positivity) (by positivity) hb hd _ hk
      have hm' : (b:ℝ)^(j.val%4)*(d:ℝ)^(3-j.val%4) ≤ W^6 := by simpa only [← pow_mul] using hm
      have hp : (if j.val < 4 then (u:ℝ) else v) ≤ W^3 := by split_ifs <;> assumption
      calc
        _ ≤ W^6*W^3 := by
          simp only [sourceIntegerRow,Bool.false_eq_true,ite_false,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ite,Nat.cast_ite]
          exact mul_le_mul hm' hp (by split_ifs <;> positivity) (by positivity)
        _ = W^9 := by ring
        _ ≤ W^11 := pow_le_pow_right₀ hW (by norm_num)
    · have hm := mixed_power_bound (v:ℝ) (u:ℝ) (W^3) (by positivity) (by positivity) (by positivity) hv hu _ hk
      have hm' : (u:ℝ)^(3-j.val%4)*(v:ℝ)^(j.val%4) ≤ W^9 := by simpa only [mul_comm,← pow_mul] using hm
      have hp : (if j.val < 4 then (d:ℝ) else b) ≤ W^2 := by split_ifs <;> assumption
      calc
        _ ≤ W^9*W^2 := by
          simp only [sourceIntegerRow,ite_true,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ite,Nat.cast_ite]
          exact mul_le_mul hm' hp (by split_ifs <;> positivity) (by positivity)
        _ = W^11 := by ring
  calc
    _ ≤ W^11 := hroot
    _ = (3:ℝ)^(11/6:ℝ)*X^(11/6:ℝ) := by
      dsimp [W]
      rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0≤3*X)]
      norm_num
      exact Real.mul_rpow (by norm_num : (0:ℝ)≤3) hXp.le
    _ ≤ 9*X^(11/6:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXp.le _)
      calc
        _ ≤ (3:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 9 := by norm_num

private theorem exponent_injective (inverse : Bool) : Function.Injective (relationExponent inverse) := by
  intro j k h
  have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  apply Fin.ext
  cases inverse <;> by_cases hj : j.val < 4 <;> by_cases hk : k.val < 4 <;>
    simp [relationExponent,hj,hk] at h0 h1 <;> omega

/-- The eight actual monomials have no exponent collision in either chart. -/
theorem relation_polynomial : CF12RelationPolynomial := by
  classical
  intro inverse c
  have hcoeff (j : Fin 8) : (relationPolynomial inverse c).coeff (relationExponent inverse j) = c j := by
    unfold relationPolynomial
    simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      rw [ite_eq_right (fun h => hkj (exponent_injective inverse h))]
    · simp
  have hother (e : Fin 2 →₀ ℕ) : (relationPolynomial inverse c).coeff e = 0 ∨
      ∃ j, e = relationExponent inverse j ∧ (relationPolynomial inverse c).coeff e = c j := by
    by_cases he : ∃ j, e = relationExponent inverse j
    · obtain ⟨j,rfl⟩ := he
      exact Or.inr ⟨j,rfl,hcoeff j⟩
    · left
      unfold relationPolynomial
      simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro j hj
      exact ite_eq_right (fun h => he ⟨j,h.symm⟩)
  refine ⟨hcoeff,?_,hother,?_,?_⟩
  · constructor
    · intro h
      ext j
      have hj := hcoeff j
      rw [h] at hj
      simpa using hj.symm
    · intro h
      simp [h,relationPolynomial]
  · intro e he
    obtain hz | ⟨j,rfl,hj⟩ := hother e
    · exact False.elim ((MvPolynomial.mem_support_iff.mp he) hz)
    · cases inverse <;> by_cases hj : j.val < 4 <;> simp [relationExponent,hj] <;> omega
  · intro z
    unfold relationPolynomial polynomialValue
    rw [MvPolynomial.eval₂_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [MvPolynomial.eval₂_monomial,Finsupp.prod_pow]
    cases inverse <;> fin_cases j <;>
      simp [relationExponent,chartMonomial,Fin.prod_univ_succ,mul_comm,mul_left_comm,mul_assoc]

private theorem rational_row (inverse : Bool) (b d u v : ℕ) (hd : 0 < d) (hu : 0 < u) (j : Fin 8) :
    (sourceIntegerRow inverse b d u v j : ℚ) =
      (sourceRowDenominator inverse d u : ℚ)*chartMonomial inverse (sourcePoint b d u v) j := by
  have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hu' : (u:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  cases inverse <;> fin_cases j <;>
    norm_num [sourceIntegerRow,sourceRowDenominator,chartMonomial,sourcePoint] <;>
    field_simp [hd',hu'] <;> ring
  all_goals
    simp only [mul_assoc]
    first
    | erw [← mul_pow,mul_inv_cancel₀ hd',one_pow,mul_one]
    | erw [← mul_pow,mul_inv_cancel₀ hu',one_pow,mul_one]

/-- Positive actual denominators identify the integer and rational relations. -/
theorem source_relation_evaluation : CF12SourceRelationEvaluation := by
  intro n b d u v hs inverse c
  have hd := hs.2.1
  have hu := hs.2.2.1
  have hden : (sourceRowDenominator inverse d u : ℚ) ≠ 0 := by
    have hd' : (d:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hu' : (u:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
    cases inverse <;> simp [sourceRowDenominator,hd',hu']
  have heq : ((∑ j : Fin 8, sourceIntegerRow inverse b d u v j*c j : ℤ) : ℚ) =
      (sourceRowDenominator inverse d u : ℚ) * polynomialValue (relationPolynomial inverse c) (sourcePoint b d u v) := by
    rw [(relation_polynomial inverse c).2.2.2.2]
    simp only [Int.cast_sum,Int.cast_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rational_row inverse b d u v hd hu j]
    ring
  constructor
  · intro h
    have hh : (sourceRowDenominator inverse d u : ℚ)*
        polynomialValue (relationPolynomial inverse c) (sourcePoint b d u v) = 0 := by rw [← heq,h]; norm_num
    exact (mul_eq_zero.mp hh).resolve_left hden
  · intro h
    apply Int.cast_injective (α := ℚ)
    rw [heq,h,mul_zero,Int.cast_zero]

/-- A fixed threshold absorbs all seven-minor constants, at every class rank. -/
theorem actual_class_relation : CF12ActualClassRelation := by
  let C : ℝ := 5040*9^7
  refine ⟨C,by norm_num [C],?_⟩
  intro X hX ι n b d u v hs hn inverse hzero
  have hX1 : 1 ≤ X := by
    have hC : 1≤C := by norm_num [C]
    linarith
  have hXp : 0 < X := by linarith
  have hH : 1 ≤ 9*X^(11/6:ℝ) := by
    have hh := Real.one_le_rpow hX1 (by norm_num : (0:ℝ)≤11/6)
    linarith
  obtain ⟨c,hc,hbound,hrel⟩ := bounded_integer_relation ι
    (fun i j => sourceIntegerRow inverse (b i) (d i) (u i) (v i) j)
    (9*X^(11/6:ℝ)) hH (fun i j => source_row_height X hX1 _ _ _ _ _ (hs i) (hn i) inverse j) hzero
  have hcX (j : Fin 8) : |(c j : ℝ)| ≤ X^(14:ℕ) := by
    calc
      _ ≤ 5040*(9*X^(11/6:ℝ))^7 := hbound j
      _ = C*X^(77/6:ℝ) := by
        rw [mul_pow,← Real.rpow_natCast (X^(11/6:ℝ)) 7,← Real.rpow_mul hXp.le]
        dsimp [C]
        norm_num
        ring
      _ ≤ C*X^(13:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)) (by dsimp [C]; positivity)
      _ ≤ X*X^(13:ℝ) := mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hXp.le _)
      _ = X^(14:ℕ) := by norm_num [Real.rpow_natCast] <;> ring
  refine ⟨relationPolynomial inverse c,⟨?_,?_,(relation_polynomial inverse c).2.2.2.1⟩,?_⟩
  · exact fun h => hc ((relation_polynomial inverse c).2.1.mp h)
  · intro e
    obtain hz | ⟨j,he,hj⟩ := (relation_polynomial inverse c).2.2.1 e
    · simpa only [hz,Int.cast_zero,abs_zero] using (pow_nonneg hXp.le 14)
    · rw [hj]; exact hcX j
  · intro i
    exact (source_relation_evaluation _ _ _ _ _ (hs i) inverse c).mp (hrel i)

/-- One actual polynomial covers the entire selected smooth class. -/
theorem rounded_entire_class_relation : CF12RoundedEntireClassRelation := by
  intro δ hδ hδ1
  obtain ⟨X₁,hX₁,hminors⟩ := rounded_actual_minor_vanishing δ hδ hδ1
  obtain ⟨X₂,hX₂,hclass⟩ := actual_class_relation
  refine ⟨max X₁ X₂,hX₁.trans (le_max_left _ _),?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  apply hclass X ((le_max_right _ _).trans hX) ι n b d u v hs (fun i => (hb i).2.1) (selectedRealChart ψ)
  intro f
  apply hminors X ψ B E a ((le_max_left _ _).trans hX) hψ0 hψ2 hB hE ha hBE F p
    (n ∘ f) (b ∘ f) (d ∘ f) (u ∘ f) (v ∘ f) hp hscale
    (fun i => hs (f i)) (fun i => hb (f i)) (fun i => hi (f i))
    (fun i => hf (f i)) (fun i => hg (f i))
  intro i
  exact (hz (f i)).trans (hz (f 0)).symm

end
end P0365Subquarter
