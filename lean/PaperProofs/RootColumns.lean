import PaperTargets.RootColumns
import PaperProofs.DividedMinors
import Mathlib.Algebra.MvPolynomial.Degrees

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open MvPolynomial

private theorem root_degrees (i j : ℕ) :
    (rootColumnPolynomial i j).degreeOf 0≤2*i+3*j ∧
    (rootColumnPolynomial i j).degreeOf 1≤j := by
  let U : SourcePolynomial := 1+X (0:Fin 2)
  let V : SourcePolynomial := U^3+X (1:Fin 2)
  have hU₀ : U.degreeOf 0≤1 := by
    exact (degreeOf_add_le 0 1 (X 0)).trans (by norm_num)
  have hU₁ : U.degreeOf 1≤0 := by
    exact (degreeOf_add_le 1 1 (X 0)).trans (by norm_num [degreeOf_X])
  have hV₀ : V.degreeOf 0≤3 := by
    apply (degreeOf_add_le 0 (U^3) (X 1)).trans
    apply max_le
    · exact (degreeOf_pow_le 0 U 3).trans (by omega)
    · norm_num [degreeOf_X]
  have hV₁ : V.degreeOf 1≤1 := by
    apply (degreeOf_add_le 1 (U^3) (X 1)).trans
    apply max_le
    · exact (degreeOf_pow_le 1 U 3).trans (by omega)
    · norm_num
  constructor
  · apply (degreeOf_mul_le 0 (U^(2*i)) (V^j)).trans
    have h₀ := (degreeOf_pow_le 0 U (2*i)).trans (Nat.mul_le_mul_left (2*i) hU₀)
    have h₁ := (degreeOf_pow_le 0 V j).trans (Nat.mul_le_mul_left j hV₀)
    nlinarith
  · apply (degreeOf_mul_le 1 (U^(2*i)) (V^j)).trans
    have h₀ := (degreeOf_pow_le 1 U (2*i)).trans (Nat.mul_le_mul_left (2*i) hU₁)
    have h₁ := (degreeOf_pow_le 1 V j).trans (Nat.mul_le_mul_left j hV₁)
    omega

/-- Fixed polynomial degrees bound every actual support monomial. -/
theorem root_column_support : CF04RootColumnSupport := by
  intro i j e he
  exact ⟨(monomial_le_degreeOf 0 he).trans (root_degrees i j).1,
    (monomial_le_degreeOf 1 he).trans (root_degrees i j).2⟩

/-- A finite prefix sum gives one coefficient bound before all source scales. -/
theorem root_column_coefficient_bound : CF04RootColumnCoefficientBound := by
  classical
  intro A C
  let L (i j : ℕ) : ℝ := ∑ e ∈ (rootColumnPolynomial i j).support,
    |((rootColumnPolynomial i j).coeff e:ℝ)|
  have hL (i j : ℕ) : 0≤L i j := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let K : ℝ := 1+∑ i ∈ Finset.range (A+1), ∑ j ∈ Finset.range (C+1), L i j
  have hsum : 0≤∑ i ∈ Finset.range (A+1), ∑ j ∈ Finset.range (C+1), L i j :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hL _ _))
  refine ⟨K,by dsimp [K]; linarith,?_⟩
  intro i j hi hj
  have h₁ : L i j≤∑ k ∈ Finset.range (C+1), L i k :=
    Finset.single_le_sum (fun k _ => hL i k) (Finset.mem_range.mpr (by omega))
  have h₂ : (∑ k ∈ Finset.range (C+1), L i k)≤
      ∑ l ∈ Finset.range (A+1), ∑ k ∈ Finset.range (C+1), L l k :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => hL l k))
      (Finset.mem_range.mpr (by omega))
  exact (h₁.trans h₂).trans (by dsimp [K]; linarith)

private theorem root_column_value (i j : ℕ) (α β : ℝ) :
    rootColumnValue i j α β=(1+α)^(2*i)*((1+α)^3+β)^j := by
  simp [rootColumnValue,rootColumnPolynomial]

/-- The existing actual CF11 linear and partner columns supply the same chart
coordinates for every rectangular degree. Only positive denominators are cleared. -/
theorem actual_rectangular_root_columns : CF04ActualRectangularRootColumns := by
  intro n b d u v hs X M a hX hn hM hMX ha hint
  have hdata := actual_interval_nodes n b d u v hs X M a hX hn hM hMX ha hint false
  simp only [realIntervalScale,Bool.false_eq_true,ite_false] at hdata
  let w : ℝ := realIntervalNode false a b d u v
  let β : ℝ := realNormalizedError false a b d u v
  have hd : (d:ℝ)≠0 := by
    exact_mod_cast (ne_of_gt hs.2.1)
  have hu : (u:ℝ)≠0 := by
    exact_mod_cast (ne_of_gt hs.2.2.1)
  have hb : (b:ℝ)=(d:ℝ)*a*w^2 := by
    have hh := actual_row_normalization n b d u v hs false a ha (1:Fin 8)
    rw [hdata.2.2.2.2 (1:Fin 8)] at hh
    norm_num [sourceIntegerRow,sourceRowDenominator,realColumnScale,
      rootNormalizedRow,rootSmoothRow,rootErrorRow,realRootOrder,realRootPartnerOrder] at hh
    apply (mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hd) hu))
    convert hh using 1 <;> ring
  have hv : (v:ℝ)=(u:ℝ)*(a^(3/2:ℝ))*(w^3+β) := by
    have hh := actual_row_normalization n b d u v hs false a ha (4:Fin 8)
    rw [hdata.2.2.2.2 (4:Fin 8)] at hh
    norm_num [sourceIntegerRow,sourceRowDenominator,realColumnScale,
      rootNormalizedRow,rootSmoothRow,rootErrorRow,realRootOrder,realRootPartnerOrder,
      realChartExponent] at hh
    apply (mul_left_cancel₀ (pow_ne_zero 3 hd))
    convert hh using 1; ring
  refine ⟨w-1,β,by dsimp [w]; linarith [hdata.1],?_,hdata.2.2.2.1,?_⟩
  · dsimp [w]; linarith [hdata.2.2.1]
  · intro A C i j hi hj
    have hdA : (d:ℝ)^i*(d:ℝ)^(A-i)=(d:ℝ)^A := by
      rw [←pow_add,Nat.add_sub_of_le hi]
    have huC : (u:ℝ)^j*(u:ℝ)^(C-j)=(u:ℝ)^C := by
      rw [←pow_add,Nat.add_sub_of_le hj]
    simp only [rectangularIntegerEntry,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    rw [hb,hv,root_column_value]
    have hw : 1+(w-1)=w := by ring
    rw [hw]
    calc
      _ = ((d:ℝ)^i*(d:ℝ)^(A-i))*((u:ℝ)^j*(u:ℝ)^(C-j))*
          a^i*(a^(3/2:ℝ))^j*(w^2)^i*(w^3+β)^j := by
        simp only [mul_pow]; ring
      _ = _ := by rw [hdA,huC,pow_mul]; ring

end
end P0365Subquarter
