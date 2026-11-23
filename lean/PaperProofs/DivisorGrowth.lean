import PaperTargets.DivisorGrowth
import PaperProofs.FactorDispatch

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

/-- A convergent polynomial/exponential ratio gives a uniform bound after
paying its finite initial segment explicitly. -/
theorem polynomial_exponential_bound : CF15PolynomialExponentialBound := by
  intro k
  have ht := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1:ℝ)<2)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_le_const (by norm_num : (0:ℝ)<1))
  let C : ℕ := 2+∑ i ∈ Finset.range N, (i+1)^k
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C,by omega,?_⟩
  intro e
  by_cases he : e<N
  · have hs : (e+1)^k ≤ ∑ i ∈ Finset.range N, (i+1)^k :=
      Finset.single_le_sum (f := fun i : ℕ => (i+1)^k) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr he)
    have hpow : 1 ≤ (2:ℕ)^e := one_le_pow₀ (by decide)
    calc
      _ ≤ C := by dsimp [C]; omega
      _ = C*1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left C hpow
  · have hn := hN (e+1) (by omega)
    have hr : (((e+1:ℕ):ℝ)^k) ≤ (2:ℝ)^(e+1) := (div_le_one (by positivity)).mp hn
    have hnat : (e+1)^k ≤ (2:ℕ)^(e+1) := by exact_mod_cast hr
    calc
      _ ≤ 2^(e+1) := hnat
      _ = 2*2^e := by rw [pow_succ]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hC

/-- Large primes absorb the valuation polynomial; only finitely many primes
below2^k cost a constant. No divisor asymptotic is an external premise. -/
theorem divisor_power_growth : CF15DivisorPowerGrowth := by
  classical
  intro k
  obtain ⟨C,hC,hpoly⟩ := polynomial_exponential_bound k
  refine ⟨C^(2^k),one_le_pow₀ hC,?_⟩
  intro n hn
  let S := n.primeFactors.filter (fun p => p<2^k)
  have hcard : S.card ≤ 2^k := by
    have hsub : S ⊆ Finset.range (2^k) := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hcost : (∏ p ∈ n.primeFactors, if p<2^k then C else 1)=C^S.card := by
    rw [← Finset.prod_filter]
    simp [S]
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p+1)^k ≤ (if p<2^k then C else 1)*p^(n.factorization p) := by
    by_cases hsmall : p<2^k
    · rw [ite_eq_left hsmall]
      exact (hpoly _).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _))
    · rw [ite_eq_right hsmall,one_mul]
      calc
        _ ≤ (2^(n.factorization p))^k := Nat.pow_le_pow_left (Nat.succ_le_iff.mpr (show n.factorization p < 2^(n.factorization p) from Nat.lt_two_pow_self)) _
        _ = (2^k)^(n.factorization p) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
        _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  have hformula : divisorCount n=n.primeFactors.prod (fun p : ℕ => n.factorization p+1) := Nat.card_divisors hn
  calc
    (divisorCount n)^k=(n.primeFactors.prod (fun p : ℕ => n.factorization p+1))^k := congrArg (fun a : ℕ => a^k) hformula
    _ = ∏ p ∈ n.primeFactors, (n.factorization p+1)^k := (Finset.prod_pow n.primeFactors k (fun p : ℕ => n.factorization p+1)).symm
    _ ≤ ∏ p ∈ n.primeFactors, (if p<2^k then C else 1)*p^(n.factorization p) := Finset.prod_le_prod hlocal
    _ = (∏ p ∈ n.primeFactors, if p<2^k then C else 1)*(∏ p ∈ n.primeFactors, p^(n.factorization p)) := Finset.prod_mul_distrib
    _ = C^S.card*n := by rw [hcost,← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ _ := Nat.mul_le_mul_right n (pow_le_pow_right₀ hC hcard)

/-- Taking a positive integer root and choosing its reciprocal below epsilon
converts the integer-power estimate to the uniform real subpower bound. -/
theorem divisor_subpower : CF15DivisorSubpower := by
  intro ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  let k := m+1
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hkpos : 0<(k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hsmall : (k:ℝ)⁻¹ ≤ ε := by simpa only [k,Nat.cast_add,Nat.cast_one,one_div] using hm.le
  obtain ⟨C,hC,hbound⟩ := divisor_power_growth k
  have hCpos : 0<(C:ℝ) := by exact_mod_cast (show 0<C by omega)
  refine ⟨(C:ℝ)^((k:ℝ)⁻¹),Real.rpow_pos_of_pos hCpos _,?_⟩
  intro n hn
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : 0≤(n:ℝ) := by positivity
  have hreal : (divisorCount n:ℝ)^k ≤ (C:ℝ)*(n:ℝ) := by exact_mod_cast hbound n hn
  have hroot := Real.rpow_le_rpow (by positivity : 0≤(divisorCount n:ℝ)^k) hreal (inv_nonneg.mpr hkpos.le)
  rw [Real.pow_rpow_inv_natCast (by positivity) hk,Real.mul_rpow hCpos.le hn0] at hroot
  exact hroot.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn1 hsmall) (by positivity))

/-- Allocate epsilon/720 before taking the eighth power and then applying
height exponent90. This preserves the requested final epsilon exactly. -/
theorem polynomial_height_divisor_growth : CF15PolynomialHeightDivisorGrowth := by
  intro ε hε
  have hε720 : 0<ε/720 := by positivity
  obtain ⟨C,hC,hτ⟩ := divisor_subpower (ε/720) hε720
  refine ⟨C^8*(720:ℝ)^(ε/90),mul_pos (pow_pos hC _) (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  intro X hX R hR hheight
  have hX0 : 0≤X := by linarith
  have hR0 : 0≤(R:ℝ) := by positivity
  have hτR := hτ R hR
  have he1 : (ε/720)*(8:ℝ)=ε/90 := by ring
  have he2 : (90:ℝ)*(ε/90)=ε := by ring
  calc
    (divisorCount R:ℝ)^8 ≤ (C*(R:ℝ)^(ε/720))^8 := by gcongr
    _ = C^8*(R:ℝ)^(ε/90) := by
      rw [mul_pow,← Real.rpow_mul_natCast hR0 (ε/720) 8]
      norm_num only [Nat.cast_ofNat]
      rw [he1]
    _ ≤ C^8*(720*X^(90:ℕ))^(ε/90) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR0 hheight (by positivity))
      positivity
    _ = C^8*((720:ℝ)^(ε/90)*X^ε) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤720) (pow_nonneg hX0 _),
        ← Real.rpow_natCast_mul hX0 90 (ε/90)]
      norm_num only [Nat.cast_ofNat]
      rw [he2]
    _ = _ := by ring

/-- Derive the arithmetic growth for the one actual full graph resultant. -/
theorem actual_graph_divisor_growth : CF15ActualGraphDivisorGrowth := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := polynomial_height_divisor_growth ε hε
  refine ⟨C,hC,?_⟩
  intro X D A B hX hg hr
  obtain ⟨hR,hheight,_⟩ := actual_graph_divisor_inventory X D A B hX hg hr
  exact ⟨hR,hbound X hX _ hR hheight⟩

end
end P0365Subquarter
