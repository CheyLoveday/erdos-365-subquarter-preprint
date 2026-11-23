import PaperTargets.PrimitiveFactors
import PaperProofs.ResultantDivisors

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Nonzero scalar multiplication preserves the exact monomial support. -/
theorem homogeneous_scalar_cancellation : CF15HomogeneousScalarCancellation := by
  intro H Q c N hc he hH e heQ
  apply hH
  rw [he,MvPolynomial.coeff_C_mul]
  exact mul_ne_zero hc heQ

/-- Any scalar divisor of the affine section divides every coefficient of
its homogeneous reconstruction, so content one makes the scalar a unit. -/
theorem primitive_dehomogenization : CF15PrimitiveDehomogenization := by
  classical
  intro Q N hhom hcontent
  have hQ : Q ≠ 0 := by
    intro hz
    simp [hz,binaryContent] at hcontent
  obtain ⟨hdeg,hform,hPn⟩ := binary_dehomogenization Q N hhom
  have hprim : (binaryDehomogenize Q).IsPrimitive := by
    intro a ha
    obtain ⟨F,hF⟩ := ha
    have he : Q=MvPolynomial.C a*F.homogenize N := by
      rw [← hform,hF,Polynomial.homogenize_C_mul]
    have hd : a.natAbs ∣ binaryContent Q := by
      apply Finset.dvd_gcd_iff.mpr
      intro e heQ
      apply Int.natAbs_dvd_natAbs.mpr
      rw [he,MvPolynomial.coeff_C_mul]
      exact dvd_mul_right _ _
    have hd1 : a.natAbs ∣ (1:ℕ) := by simpa only [hcontent] using hd
    apply isUnit_iff_dvd_one.mpr
    exact Int.natAbs_dvd_natAbs.mp (by simpa using hd1)
  exact ⟨hQ,hprim,hPn hQ,hdeg,hform⟩

/-- Homogeneous uniqueness identifies the exact axis padding, also at zero. -/
theorem homogenization_padding : CF15HomogenizationPadding := by
  intro P N hN
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · have h := (Polynomial.isHomogeneous_homogenize (n := P.natDegree) P).mul
      (MvPolynomial.isHomogeneous_X_pow (R := ℤ) 1 (N-P.natDegree))
    convert h using 1; omega
  · simp [Polynomial.aeval_homogenize_X_one P le_rfl]

/-- Factor divisibility lifts first at the true affine degree, then through
all missing infinity factors. Primitivity passes to every integral divisor. -/
theorem homogeneous_factor_lift : CF15HomogeneousFactorLift := by
  intro P f N hP hf hN
  have hfp : f.IsPrimitive := Polynomial.isPrimitive_of_dvd hP hf
  have hdeg := (Polynomial.natDegree_le_of_dvd hf hP.ne_zero).trans hN
  refine ⟨hfp,hfp.ne_zero,hdeg,Polynomial.isHomogeneous_homogenize f,?_⟩
  rw [homogenization_padding P N hN]
  exact (Polynomial.homogenize_dvd hf).trans (dvd_mul_right _ _)

/-- Integer scalar composition absorbs the content into the tested power's
coefficient; no factor of the polynomial content is charged to R. -/
theorem primitive_small_power_transfer : CF15PrimitiveSmallPowerTransfer := by
  intro H Q c he hnon G d k a hG hd hQ
  apply hnon G d k (c*a) hG hd
  rw [he,hQ,← mul_assoc,← MvPolynomial.C_mul]

/-- Prepare one primitive section and every fixed factor before any source
or admitted level labels are chosen. -/
theorem actual_primitive_graph_factors : CF15ActualPrimitiveGraphFactors := by
  intro X D A B hX hgraph hr inverse
  obtain ⟨hN,hNupper,hgeo,hnon⟩ := actual_mixed_nonpowers X D A B hX hgraph hr inverse
  obtain ⟨hc,hprim,hfactor,_⟩ := binary_content_removal (graphPullback inverse A B) hgeo.1
  have hcZ : (binaryContent (graphPullback inverse A B):ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  have hhom := homogeneous_scalar_cancellation _ _ _ _ hcZ hfactor hgeo.2.1
  obtain ⟨hQ,hPprim,hPn,hPdeg,hPhom⟩ := primitive_dehomogenization _ _ hhom hprim
  refine ⟨hQ,hprim,hhom,hN,hNupper.trans (by split_ifs <;> norm_num),hPprim,hPn,hPdeg,hPhom,?_,?_⟩
  · exact primitive_small_power_transfer _ _ _ hfactor hnon
  · intro f hf
    have h := homogeneous_factor_lift _ f _ hPprim hf hPdeg
    rw [hPhom] at h
    exact h

end
end P0365Subquarter
