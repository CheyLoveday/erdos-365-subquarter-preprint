import PaperTargets.FactorInventory
import PaperProofs.CoarseFactors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Nilpotent

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem primitive_of_positive_irreducible (A : SourcePolynomial)
    (hA : Irreducible A) (hpos : 0<A.totalDegree) : coarseIntegralPrimitive A := by
  intro a ha
  obtain ⟨B,hB⟩ := (MvPolynomial.C_dvd_iff_dvd_coeff a A).2 ha
  rcases hA.isUnit_or_isUnit hB with hu | hu
  · simpa only [MvPolynomial.constantCoeff_C] using
      hu.map (MvPolynomial.constantCoeff (σ := Fin 2) (R := ℤ))
  · have hc : (MvPolynomial.C a : SourcePolynomial)≠0 := by
      intro hz
      exact hA.ne_zero (by rw [hB,hz,zero_mul])
    have hb : B≠0 := by
      intro hz
      exact hA.ne_zero (by rw [hB,hz,mul_zero])
    have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hB,MvPolynomial.totalDegree_mul_of_isDomain hc hb,MvPolynomial.totalDegree_C,hd] at hpos
    omega

private theorem rational_irreducible_of_positive_prime (A : SourcePolynomial)
    (hA : Prime A) (hpos : 0<A.totalDegree) :
    Irreducible (coarseRationalPolynomial A) := by
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin 2) (Int.castRingHom ℚ)) :=
    MvPolynomial.map_injective _ Int.cast_injective
  have hnz : coarseRationalPolynomial A≠0 := by
    intro hz
    apply hA.ne_zero
    apply hinj
    simpa [coarseRationalPolynomial] using hz
  have hnu : ¬IsUnit (coarseRationalPolynomial A) := by
    intro hu
    have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
    have hconst : A=MvPolynomial.C (A.coeff 0) := by
      apply hinj
      simpa [coarseRationalPolynomial,MvPolynomial.coeff_map] using hc
    rw [hconst,MvPolynomial.totalDegree_C] at hpos
    omega
  let f := IsLocalization.toLocalizationMap
    ((nonZeroDivisors ℤ).map (MvPolynomial.C (σ := Fin 2))) (MvPolynomial (Fin 2) ℚ)
  have hf : f A=coarseRationalPolynomial A := rfl
  have hp := f.map_prime hA (by simpa [hf] using hnz) (by simpa [hf] using hnu)
  exact (hf ▸ hp).irreducible

private theorem positive_factor_card (l : Multiset SourcePolynomial)
    (hne : ∀ A ∈ l, A≠0) :
    (l.filter (fun A => 0<A.totalDegree)).card≤l.prod.totalDegree := by
  classical
  induction l using Multiset.induction_on with
  | empty => simp
  | @cons A l ih =>
    have ha := hne A (Multiset.mem_cons_self _ _)
    have hl : ∀ B ∈ l, B≠0 := fun B hB => hne B (Multiset.mem_cons_of_mem hB)
    have hp : l.prod≠0 := Multiset.prod_ne_zero (by intro h; exact hl 0 h rfl)
    have hi := ih hl
    rw [Multiset.prod_cons,MvPolynomial.totalDegree_mul_of_isDomain ha hp]
    by_cases hd : 0<A.totalDegree
    · rw [Multiset.filter_cons_of_pos (p := fun B : SourcePolynomial => 0<B.totalDegree) l hd,Multiset.card_cons]
      omega
    · rw [Multiset.filter_cons_of_neg (p := fun B : SourcePolynomial => 0<B.totalDegree) l hd]
      omega

private theorem zero_of_factor_product (l : Multiset SourcePolynomial) (z : Fin 2 → ℚ)
    (hz : polynomialValue l.prod z=0) : ∃ A ∈ l, polynomialValue A z=0 := by
  induction l using Multiset.induction_on with
  | empty => simp [polynomialValue] at hz
  | @cons A l ih =>
    have hm : polynomialValue A z*polynomialValue l.prod z=0 := by
      simpa [polynomialValue] using hz
    rcases mul_eq_zero.mp hm with ha | hl
    · exact ⟨A,Multiset.mem_cons_self _ _,ha⟩
    · obtain ⟨B,hB,hzB⟩ := ih hl
      exact ⟨B,Multiset.mem_cons_of_mem hB,hzB⟩

/-- Remove constant content before counting actual curve factors. -/
theorem primitive_factor_inventory : CF05PrimitiveFactorInventory := by
  classical
  intro D F hF hD
  let : StrongNormalizationMonoid SourcePolynomial :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let l := UniqueFactorizationMonoid.normalizedFactors F
  let s := (l.filter (fun A => 0<A.totalDegree)).toFinset
  have hprime : ∀ A ∈ l, Prime A := fun A hA =>
    UniqueFactorizationMonoid.prime_of_normalized_factor A hA
  have hassoc : Associated l.prod F := UniqueFactorizationMonoid.prod_normalizedFactors hF
  have hdeg : l.prod.totalDegree≤D :=
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hassoc.dvd hF).trans hD
  refine ⟨s,?_,?_,?_⟩
  · exact (Multiset.toFinset_card_le _).trans
      ((positive_factor_card l (fun A hA => (hprime A hA).ne_zero)).trans hdeg)
  · intro A hA
    obtain ⟨hl,hpos⟩ := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hA)
    have hdiv := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hl
    have hir := (hprime A hl).irreducible
    exact ⟨hdiv,hpos,(MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hF).trans hD,
      hir,primitive_of_positive_irreducible A hir hpos,
      rational_irreducible_of_positive_prime A (hprime A hl) hpos⟩
  · intro z hz
    have hpz : polynomialValue l.prod z=0 := by
      have hh := (hassoc.map (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) z)).eq_zero_iff
      exact hh.mpr hz
    obtain ⟨A,hA,hzA⟩ := zero_of_factor_product l z hpz
    have hpos : 0<A.totalDegree := by
      by_contra hn
      have hd : A.totalDegree=0 := Nat.eq_zero_of_not_pos hn
      have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
      have ha : A.coeff 0≠0 := by
        intro hh
        exact (hprime A hA).ne_zero (by rw [hc,hh,MvPolynomial.C_0])
      have hh : (A.coeff 0:ℚ)=0 := by
        change MvPolynomial.eval₂ (Int.castRingHom ℚ) z A=0 at hzA
        rw [hc,MvPolynomial.eval₂_C] at hzA
        exact hzA
      exact ha (by exact_mod_cast hh)
    exact ⟨A,Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hA,hpos⟩),hzA⟩

/-- Apply the uniform height theorem to the produced integral divisors. -/
theorem uniform_primitive_factor_cover : CF05UniformPrimitiveFactorCover := by
  intro D H C hH hC
  obtain ⟨K,hK,hh⟩ := uniform_coarse_factor_height D H C hH hC
  refine ⟨K,hK,?_⟩
  intro X hX F hF hD hcoeff
  obtain ⟨s,hcard,hprops,hcover⟩ := primitive_factor_inventory D F hF hD
  refine ⟨s,hcard,?_,hcover⟩
  intro A hA
  obtain ⟨hdiv,hpos,hAD,_,hprim,hir⟩ := hprops A hA
  exact ⟨hdiv,hpos,hAD,hprim,hir,(hh X hX F hF hD hcoeff A hdiv).2⟩

end
end P0365Subquarter
