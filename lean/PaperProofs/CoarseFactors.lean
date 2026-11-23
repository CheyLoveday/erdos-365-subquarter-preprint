import PaperTargets.CoarseFactors
import PaperProofs.GraphRulings

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem support_ball (D : ℕ) (F : SourcePolynomial) (hD : F.totalDegree≤D)
    (e : Fin 2 →₀ ℕ) (he : e∈F.support) : e 0+e 1≤D := by
  have h := (MvPolynomial.le_totalDegree he).trans hD
  rwa [Finsupp.sum_fintype e (fun _ a => a) (fun _ => rfl),Fin.sum_univ_two] at h

private theorem label_injective (D : ℕ) (e f : Fin 2 →₀ ℕ)
    (he : e 0+e 1≤D) (hf : f 0+f 1≤D)
    (h : e 0+(D+1)*e 1=f 0+(D+1)*f 1) : e=f := by
  have he0 : e 0<D+1 := by omega
  have hf0 : f 0<D+1 := by omega
  have h0 : e 0=f 0 := by
    have hm := congrArg (fun n : ℕ => n%(D+1)) h
    simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt he0,Nat.mod_eq_of_lt hf0] using hm
  have hmul : (D+1)*e 1=(D+1)*f 1 := by omega
  have h1 : e 1=f 1 := mul_left_cancel₀ (Nat.succ_ne_zero D) hmul
  ext i
  fin_cases i <;> assumption

private theorem label_bound (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e 0+e 1≤D) :
    e 0+(D+1)*e 1≤D*(D+1) := by
  calc
    _ ≤ (D+1)*e 0+(D+1)*e 1 := by nlinarith
    _ = (D+1)*(e 0+e 1) := by ring
    _ ≤ (D+1)*D := Nat.mul_le_mul_left _ he
    _ = _ := by ring

private theorem coarse_expansion (D : ℕ) (F : SourcePolynomial) :
    coarseKronecker D F=∑ e ∈ F.support,
      Polynomial.monomial (e 0+(D+1)*e 1) (F.coeff e) := by
  classical
  simp only [coarseKronecker,MvPolynomial.eval₂_eq',Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro e _
  rw [←pow_mul,←pow_add,Polynomial.C_mul_X_pow_eq_monomial]

private theorem coarse_coefficient (D : ℕ) (F : SourcePolynomial) (hD : F.totalDegree≤D)
    (e : Fin 2 →₀ ℕ) (he : e 0+e 1≤D) :
    (coarseKronecker D F).coeff (e 0+(D+1)*e 1)=F.coeff e := by
  classical
  rw [coarse_expansion,Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hne
    have hn : f 0+(D+1)*f 1≠e 0+(D+1)*e 1 := by
      intro hh
      exact hne (label_injective D f e (support_ball D F hD f hf) he hh)
    simp [Polynomial.coeff_monomial,hn]
  · intro hnot
    simp [MvPolynomial.notMem_support_iff.mp hnot]

/-- Unique bounded-degree labels preserve actual coefficients and nonvanishing. -/
theorem kronecker_control : CF05KroneckerControl := by
  classical
  intro D F hD
  refine ⟨coarse_coefficient D F hD,?_,?_⟩
  · rw [coarse_expansion]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    exact (Polynomial.natDegree_monomial_le _).trans (label_bound D e (support_ball D F hD e he))
  · intro hF hzero
    apply hF
    ext e
    by_cases he : e∈F.support
    · have hc := coarse_coefficient D F hD e (support_ball D F hD e he)
      rw [hzero,Polynomial.coeff_zero] at hc
      exact hc.symm
    · exact MvPolynomial.notMem_support_iff.mp he

private theorem coarse_height (D : ℕ) (F : SourcePolynomial) (hD : F.totalDegree≤D)
    (H : ℝ) (hH : 0≤H) (hcoeff : ∀ e, |(F.coeff e:ℝ)|≤H) :
    ∀ k, |((coarseKronecker D F).coeff k:ℝ)|≤H := by
  classical
  intro k
  by_cases hex : ∃ e ∈ F.support, e 0+(D+1)*e 1=k
  · obtain ⟨e,he,hk⟩ := hex
    rw [←hk,coarse_coefficient D F hD e (support_ball D F hD e he)]
    exact hcoeff e
  · have hz : (coarseKronecker D F).coeff k=0 := by
      rw [coarse_expansion,Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro e he
      have hn : e 0+(D+1)*e 1≠k := fun hk => hex ⟨e,he,hk⟩
      simp [Polynomial.coeff_monomial,hn]
    simpa [hz] using hH

/-- Apply actual univariate divisibility, then recover every factor coefficient. -/
theorem integer_coarse_factor_height : CF05IntegerCoarseFactorHeight := by
  classical
  intro D H hH F hF hD hcoeff A hdiv
  have hAD : A.totalDegree≤D := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hF).trans hD
  have hFcontrol := kronecker_control D F hD
  have himage : coarseKronecker D A∣coarseKronecker D F := by
    obtain ⟨Q,hQ⟩ := hdiv
    refine ⟨coarseKronecker D Q,?_⟩
    simpa [coarseKronecker,MvPolynomial.eval₂_mul] using congrArg (coarseKronecker D) hQ
  have hh := integer_factor_height (D*(D+1)) H hH (coarseKronecker D F)
    (hFcontrol.2.2 hF) hFcontrol.2.1 (coarse_height D F hD H (by linarith) hcoeff)
    (coarseKronecker D A) himage
  refine ⟨hAD,?_⟩
  intro e
  by_cases he : e∈A.support
  · rw [←coarse_coefficient D A hAD e (support_ball D A hAD e he)]
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hh (e 0+(D+1)*e 1)
  · rw [MvPolynomial.notMem_support_iff.mp he]
    simp only [Int.cast_zero,abs_zero]
    positivity

/-- One height constant retains the same exponent for all actual factors. -/
theorem uniform_coarse_factor_height : CF05UniformCoarseFactorHeight := by
  intro D H C hH hC
  let B : ℝ := (2:ℝ)^(D*(D+1))*(D*(D+1)+1)
  refine ⟨B*(C+1),by dsimp [B]; positivity,?_⟩
  intro X hX F hF hD hcoeff A hdiv
  have hpow : 1≤X^H := Real.one_le_rpow hX hH
  have hheight : 1≤(C+1)*X^H := by nlinarith
  have hcoeff' : ∀ e, |(F.coeff e:ℝ)|≤(C+1)*X^H := by
    intro e
    exact (hcoeff e).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  obtain ⟨hAD,hh⟩ := integer_coarse_factor_height D ((C+1)*X^H) hheight F hF hD hcoeff' A hdiv
  refine ⟨hAD,?_⟩
  intro e
  calc
    _ ≤ (2:ℝ)^(D*(D+1))*(D*(D+1)+1)*((C+1)*X^H) := hh e
    _ = (B*(C+1))*X^H := by dsimp [B]; ring

end
end P0365Subquarter
