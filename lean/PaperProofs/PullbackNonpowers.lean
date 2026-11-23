import PaperTargets.PullbackNonpowers
import PaperProofs.PullbackGeometry
import Mathlib.RingTheory.Coprime.Lemmas

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open UniqueFactorizationMonoid

/-- Every affine monomial comes from an exponent pair whose sum is d. -/
theorem binary_dehomogenization : CF14BinaryDehomogenization := by
  classical
  intro G d hG
  have hp : binaryDehomogenize G = ∑ e ∈ G.support,
      Polynomial.C (G.coeff e)*Polynomial.X^(e 0) := by
    unfold binaryDehomogenize
    conv_lhs => rw [G.as_sum,map_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [MvPolynomial.aeval_monomial]
    simp [Finsupp.prod_fintype,Fin.prod_univ_two]
  have hd : (binaryDehomogenize G).natDegree ≤ d := by
    rw [hp]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    have hm : e 0+e 1=d := by
      simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_two] using
        hG (MvPolynomial.mem_support_iff.mp he)
    have h := Polynomial.natDegree_mul_le (p := Polynomial.C (G.coeff e))
      (q := Polynomial.X^(e 0))
    simp only [Polynomial.natDegree_C,Polynomial.natDegree_X_pow,zero_add] at h
    exact h.trans (by omega)
  have he := Polynomial.homogenize_eq_of_isHomogeneous hG (show
    MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1] G=binaryDehomogenize G from rfl)
  refine ⟨hd,he,?_⟩
  intro hn hz
  apply hn
  rw [← he,hz,Polynomial.homogenize_zero]

private theorem trail_power (P : Polynomial ℤ) (hP : P ≠ 0) (k : ℕ) :
    (P^k).natTrailingDegree=k*P.natTrailingDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Polynomial.natTrailingDegree_mul (pow_ne_zero _ hP) hP,ih]
    ring

private theorem affine_of_homogeneous_power (inverse : Bool) (A B : Polynomial ℤ)
    (G : SourcePolynomial) (k : ℕ) (c : ℤ)
    (he : graphPullback inverse A B=MvPolynomial.C c*G^k) :
    affineGraphPullback inverse A B=Polynomial.C c*(binaryDehomogenize G)^k := by
  have h := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℤ),1]) he
  have hd := (homogeneous_pullback inverse A B).1
  have hh := (homogeneous_pullback inverse A B).2.1
  rw [← hh,Polynomial.aeval_homogenize_X_one _ hd] at h
  simpa [binaryDehomogenize] using h

/-- High repeated multiplicity is incompatible with either actual axis bound.
Only after this argument is the polynomial-abc coprimality screen available. -/
theorem small_power_axis_screen : CF14SmallPowerAxisScreen := by
  intro A B hr hc inverse G d k c hG hsmall he
  obtain ⟨hA,hB⟩ := mixed_sections_nonzero A B hr hc
  obtain ⟨hH,hN⟩ := (homogeneous_pullback inverse A B).2.2.2 hA hB
  have hpH : MvPolynomial.C c*G^k ≠ 0 := by rw [← he]; exact hH
  have hdk : graphPullbackDegree inverse (graphDegree A B)=d*k :=
    hN.symm.trans ((congrArg MvPolynomial.totalDegree he).trans (((hG.pow k).C_mul c).totalDegree hpH))
  have hk : (if inverse then 2 else 3)<k := by
    cases inverse <;> dsimp [graphPullbackDegree] at hdk ⊢ <;>
      rcases hsmall with rfl | rfl <;> omega
  have hk0 : k ≠ 0 := by cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hk <;> omega
  have hc0 : c ≠ 0 := by intro hz; apply hpH; simp [hz]
  have hG0 : G ≠ 0 := by intro hz; apply hpH; simp [hz,zero_pow hk0]
  obtain ⟨hpd,_,hp0⟩ := binary_dehomogenization G d hG
  have hp := hp0 hG0
  have hF := affine_of_homogeneous_power inverse A B G k c he
  have hdeg : (affineGraphPullback inverse A B).natDegree=k*(binaryDehomogenize G).natDegree := by
    rw [hF,Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero _ hp),
      Polynomial.natDegree_C,Polynomial.natDegree_pow,zero_add]
  have htrail : (affineGraphPullback inverse A B).natTrailingDegree=k*(binaryDehomogenize G).natTrailingDegree := by
    rw [hF,Polynomial.natTrailingDegree_mul (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero _ hp),
      Polynomial.natTrailingDegree_C,trail_power _ hp,zero_add]
  obtain ⟨_,hx,hy,_⟩ := axis_orders A B hr hc inverse
  have hpx : (binaryDehomogenize G).natTrailingDegree=0 := by
    by_contra hn
    have hm : k ≤ k*(binaryDehomogenize G).natTrailingDegree :=
      Nat.le_mul_of_pos_right k (by omega)
    rw [htrail] at hx
    omega
  have hpconst : (binaryDehomogenize G).coeff 0 ≠ 0 := by
    rcases Polynomial.natTrailingDegree_eq_zero.mp hpx with hz | hn
    · exact (hp hz).elim
    · exact hn
  have hpdeg : (binaryDehomogenize G).natDegree=d := by
    rw [hdeg,hdk] at hy
    rcases hsmall with rfl | rfl
    · have hp' : (binaryDehomogenize G).natDegree=0 ∨ (binaryDehomogenize G).natDegree=1 := by omega
      rcases hp' with hz | ho
      · rw [hz,mul_zero,one_mul,Nat.sub_zero] at hy
        omega
      · exact ho
    · have hp' : (binaryDehomogenize G).natDegree=0 ∨ (binaryDehomogenize G).natDegree=1 ∨
          (binaryDehomogenize G).natDegree=2 := by omega
      rcases hp' with hz | ho | ht
      · rw [hz,mul_zero,Nat.sub_zero] at hy
        omega
      · rw [ho,mul_one,show 2*k-k=k by omega] at hy
        omega
      · exact ht
  exact ⟨hdk,hc0,hG0,hk,hpdeg,hpconst,hF⟩

/-- Strip exponents and the nonzero scalar before counting radical degrees. -/
theorem radical_support_bound : CF14RadicalSupportBound := by
  classical
  intro A B P hA hB hP c hc e s t k
  have pow_dvd (Q : Polynomial ℚ) (j : ℕ) : radical (Q^j) ∣ Q :=
    radical_pow_dvd.trans radical_dvd_self
  have hunit : IsUnit (Polynomial.C c) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hp : radical (Polynomial.C c*P^k) ∣ P := by
    rw [radical_mul_of_isUnit_left hunit]
    exact pow_dvd P k
  have hx : radical (Polynomial.X^e*B^t) ∣ Polynomial.X*B :=
    radical_mul_dvd.trans (mul_dvd_mul (pow_dvd Polynomial.X e) (pow_dvd B t))
  have hd : radical ((A^s)*(Polynomial.X^e*B^t)*(Polynomial.C c*P^k)) ∣ (A*(Polynomial.X*B))*P :=
    radical_mul_dvd.trans (mul_dvd_mul
      (radical_mul_dvd.trans (mul_dvd_mul (pow_dvd A s) hx)) hp)
  have hn : (A*(Polynomial.X*B))*P ≠ 0 := mul_ne_zero
    (mul_ne_zero hA (mul_ne_zero Polynomial.X_ne_zero hB)) hP
  apply (Polynomial.natDegree_le_of_dvd hd hn).trans
  rw [Polynomial.natDegree_mul (mul_ne_zero hA (mul_ne_zero Polynomial.X_ne_zero hB)) hP,
    Polynomial.natDegree_mul hA (mul_ne_zero Polynomial.X_ne_zero hB),
    Polynomial.natDegree_mul Polynomial.X_ne_zero hB,Polynomial.natDegree_X]
  omega

private theorem abc_difference (U V F : Polynomial ℚ) (hU : U ≠ 0) (hV : V ≠ 0)
    (hF : F ≠ 0) (hc : IsCoprime U V) (he : U-V=F) (hd : 0<F.natDegree) :
    F.natDegree+1 ≤ (radical (U*(-V)*(-F))).natDegree := by
  rcases Polynomial.abc hU (neg_ne_zero.mpr hV) (neg_ne_zero.mpr hF) hc.neg_right
      (show U+(-V)+(-F)=0 by rw [← he]; ring) with h | hz
  · simpa only [Polynomial.natDegree_neg] using h.2.2
  · have hf := Polynomial.derivative_eq_zero.mp hz.2.2
    rw [Polynomial.natDegree_neg] at hf
    omega

/-- Polynomial abc applies to the original two summands only after their
coprimality has been derived from the proved nonzero affine constant term. -/
theorem nonaxis_abc : CF14NonaxisABC := by
  classical
  intro A B hA hB hc inverse P c k hc0 hk hP0 hF hdeg
  let a := rationalPolynomial A
  let b := rationalPolynomial B
  let p := rationalPolynomial P
  let f := rationalPolynomial (affineGraphPullback inverse A B)
  have ha : a ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hA
  have hb : b ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hB
  have hP : P ≠ 0 := by intro h; apply hP0; simp [h]
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hP
  have hf : f ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr
    (affine_pullback_degrees A B hA hB inverse).1
  have hdf : 0<f.natDegree := by
    simpa only [f,rationalPolynomial,Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℚ) Int.cast_injective] using hdeg
  have hfp : f=Polynomial.C (c:ℚ)*p^k := by
    dsimp [f,p,rationalPolynomial]
    rw [hF,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow]
    rfl
  have hFeval : (affineGraphPullback inverse A B).eval 0 ≠ 0 := by
    rw [hF,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow]
    apply mul_ne_zero hc0
    apply pow_ne_zero
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hP0
  have hAeval : A.eval 0 ≠ 0 := by
    intro hz; apply hFeval
    cases inverse <;> simp [affineGraphPullback,hz]
  have hac : a.coeff 0 ≠ 0 := by
    have hAz : A.coeff 0 ≠ 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hAeval
    simpa [a,rationalPolynomial] using hAz
  have hax : IsCoprime a Polynomial.X := by
    rcases (Polynomial.irreducible_X (R := ℚ)).isCoprime_or_dvd a with h | h
    · exact h.symm
    · exact (hac (Polynomial.X_dvd_iff.mp h)).elim
  have hcQ : (c:ℚ) ≠ 0 := by exact_mod_cast hc0
  have hbound : f.natDegree+1 ≤ a.natDegree+b.natDegree+1+p.natDegree := by
    cases inverse
    · have he : a^2-Polynomial.X^3*b^2=f := by
        simp [a,b,f,rationalPolynomial,affineGraphPullback]
      have hcop : IsCoprime (a^2) (Polynomial.X^3*b^2) := hax.pow.mul_right hc.pow
      have hprod : a^2*(-(Polynomial.X^3*b^2))*(-f)=
          (a^2)*(Polynomial.X^3*b^2)*(Polynomial.C (c:ℚ)*p^k) := by rw [hfp]; ring
      have h := abc_difference (a^2) (Polynomial.X^3*b^2) f (pow_ne_zero _ ha)
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb)) hf hcop he hdf
      rw [hprod] at h
      exact h.trans (radical_support_bound a b p ha hb hp (c:ℚ) hcQ 3 2 2 k)
    · have he : Polynomial.X^2*b^3-a^3=f := by
        simp [a,b,f,rationalPolynomial,affineGraphPullback]
      have hcop : IsCoprime (Polynomial.X^2*b^3) (a^3) := hax.pow.symm.mul_left hc.pow.symm
      have hprod : (Polynomial.X^2*b^3)*(-(a^3))*(-f)=
          (a^3)*(Polynomial.X^2*b^3)*(Polynomial.C (c:ℚ)*p^k) := by rw [hfp]; ring
      have h := abc_difference (Polynomial.X^2*b^3) (a^3) f
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb))
        (pow_ne_zero _ ha) hf hcop he hdf
      rw [hprod] at h
      exact h.trans (radical_support_bound a b p ha hb hp (c:ℚ) hcQ 2 3 3 k)
  simpa only [f,a,b,p,rationalPolynomial,Polynomial.natDegree_map_eq_of_injective
    (f := Int.castRingHom ℚ) Int.cast_injective] using hbound

/-- The axis screen makes the affine power have full degree N. Abc's support
bound is strictly smaller for every positive actual graph degree. -/
theorem homogeneous_small_power_exclusion : CF14HomogeneousSmallPowerExclusion := by
  intro A B hr hc inverse G d k c hG hsmall he
  obtain ⟨hA,hB⟩ := mixed_sections_nonzero A B hr hc
  obtain ⟨hdk,hc0,_,hk,hpd,hp0,hF⟩ := small_power_axis_screen A B hr hc inverse G d k c hG hsmall he
  have hp : binaryDehomogenize G ≠ 0 := by intro hz; apply hp0; simp [hz]
  have hk0 : 0<k := by cases inverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hk <;> omega
  have hfull : (affineGraphPullback inverse A B).natDegree=graphPullbackDegree inverse (graphDegree A B) := by
    rw [hF,Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero _ hp),
      Polynomial.natDegree_C,zero_add,Polynomial.natDegree_pow,hpd,hdk,Nat.mul_comm]
  have hN : 5 ≤ graphPullbackDegree inverse (graphDegree A B) := by
    cases inverse <;> dsimp [graphPullbackDegree] <;> omega
  have habc := nonaxis_abc A B hA hB hc inverse (binaryDehomogenize G) c k hc0 hk0 hp0 hF (by omega)
  rw [hfull,hpd] at habc
  cases inverse <;> dsimp [graphPullbackDegree,graphDegree] at hdk habc hr <;>
    rcases hsmall with rfl | rfl <;> omega

/-- Complete CF14 for every actual bounded mixed graph, before sources. -/
theorem actual_mixed_nonpowers : CF14ActualMixedNonpowers := by
  intro X D A B hX hb hr inverse
  obtain ⟨hN,hN1,hgeom⟩ := actual_mixed_pullback X D A B hX hb hr inverse
  exact ⟨hN,hN1,hgeom,homogeneous_small_power_exclusion A B hr hb.2.2.1 inverse⟩

/-- Compose with the same entire actual class and its corrected signed/content
levels. There is no supplied relation, resultant or pure-power exclusion. -/
theorem rounded_class_nonpowers : CF14RoundedClassNonpowers := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_class_resultant_levels δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  obtain ⟨D,A,C,hgraph,hroots,hclass,ht⟩ := h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v
    hp hscale hs hb hi hf hg hz
  refine ⟨D,A,C,hgraph,hroots,hclass,?_⟩
  rcases ht with hr0 | ⟨hR,hRb,hlevels⟩
  · exact Or.inl hr0
  · by_cases hr0 : graphDegree A C=0
    · exact Or.inl hr0
    · have hr : 1 ≤ graphDegree A C := by omega
      have hn := (actual_mixed_nonpowers X D A C (hX₀.trans hX) hgraph hr (selectedRealChart ψ)).2.2
      exact Or.inr ⟨hR,hRb,hn,hlevels⟩

end
end P0365Subquarter
