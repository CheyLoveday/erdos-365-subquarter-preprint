import PaperTargets.FactorDispatch
import PaperProofs.PrimitiveFactors

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open UniqueFactorizationMonoid

private theorem full_lift_nonzero (f : Polynomial ℤ) (hf : f ≠ 0) :
    f.homogenize f.natDegree ≠ 0 := by
  intro hz
  exact hf (Polynomial.eq_zero_of_homogenize_eq_zero le_rfl hz)

private theorem rational_lift_section (f : Polynomial ℤ) :
    MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]
      (rationalBinary (f.homogenize f.natDegree))=rationalPolynomial f := by
  change MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]
    (MvPolynomial.map (Int.castRingHom ℚ) (f.homogenize f.natDegree))=rationalPolynomial f
  rw [← Polynomial.homogenize_map]
  apply Polynomial.aeval_homogenize_X_one
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]

private theorem rational_degree (f : Polynomial ℤ) : (rationalPolynomial f).natDegree=f.natDegree :=
  Polynomial.natDegree_map_eq_of_injective Int.cast_injective f

private theorem rational_multiple_associated (f g : Polynomial ℤ)
    (hf : f.IsPrimitive) (hg : g.IsPrimitive) (q : ℚ)
    (he : rationalPolynomial f=Polynomial.C q*rationalPolynomial g) : Associated f g := by
  have hfn : rationalPolynomial f ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hf.ne_zero
  have hq : q ≠ 0 := by intro hz; apply hfn; simp [hz] at he; exact he
  have hqu : IsUnit (Polynomial.C q : Polynomial ℚ) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hq)
  have has : Associated (rationalPolynomial f) (rationalPolynomial g) :=
    (Associated.of_eq he).trans (associated_unit_mul_left _ _ hqu)
  exact associated_of_dvd_dvd
    ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast f g hf).mpr has.dvd)
    ((Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast g f hg).mpr has.dvd')

private theorem lifted_nonproportional (f g : Polynomial ℤ)
    (hf : f.IsPrimitive) (hg : g.IsPrimitive) (hna : ¬ Associated f g) :
    binaryNonproportional (f.homogenize f.natDegree) (g.homogenize g.natDegree) := by
  rintro ⟨q,he⟩
  have hs := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]) he
  simp only [map_mul,MvPolynomial.aeval_C,Polynomial.algebraMap_eq,rational_lift_section] at hs
  exact hna (rational_multiple_associated f g hf hg q hs)

private theorem quadratic_not_linear_square (f L : Polynomial ℤ)
    (hf : Irreducible (rationalPolynomial f)) (hL : L.natDegree=1) :
    binaryNonproportional (f.homogenize f.natDegree) ((L.homogenize L.natDegree)^2) := by
  rintro ⟨q,he⟩
  have hs := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]) he
  simp only [map_mul,map_pow,MvPolynomial.aeval_C,Polynomial.algebraMap_eq,rational_lift_section] at hs
  have hn : ¬ IsUnit (rationalPolynomial L) := by
    apply Polynomial.not_isUnit_of_natDegree_pos
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,hL]
    decide
  have heq : rationalPolynomial f=(Polynomial.C q*rationalPolynomial L)*rationalPolynomial L := by
    rw [hs,pow_two,mul_assoc]
  rcases hf.isUnit_or_isUnit heq with hu | hu
  · exact hn (isUnit_of_mul_isUnit_right hu)
  · exact hn hu

/-- Primitive sections have no nonunit constant prime factors; Gauss then
supplies precisely rational irreducibility for every selected affine factor. -/
theorem primitive_irreducible_factor : CF15PrimitiveIrreducibleFactor := by
  intro P f hP hi hf
  have hp := Polynomial.isPrimitive_of_dvd hP hf
  have hd : 1 ≤ f.natDegree := by
    by_contra hn
    have hz : f.natDegree=0 := by omega
    have he := Polynomial.eq_C_of_natDegree_eq_zero hz
    have hu := hp (f.coeff 0) ⟨1,by simpa using he⟩
    exact hi.not_isUnit (he.symm ▸ Polynomial.isUnit_C.mpr hu)
  exact ⟨hp,hd,(Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).mp hi⟩

/-- Distinct primitive factors remain distinct over Q, and an irreducible
quadratic cannot become a scalar square of a linear factor. -/
theorem distinct_low_factor_pair : CF15DistinctLowFactorPair := by
  intro f g hf hg hif hig hna hdfe hdge
  have hgf := lifted_nonproportional f g hf hg hna
  have hfirr := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf).mp hif
  have hgirr := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hg).mp hig
  refine ⟨full_lift_nonzero f hf.ne_zero,full_lift_nonzero g hg.ne_zero,?_⟩
  rcases hdfe with hdf | hdf <;> rcases hdge with hdg | hdg
  · exact Or.inl ⟨by simpa only [hdf] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,
      by simpa only [hdg] using Polynomial.isHomogeneous_homogenize (n := g.natDegree) g,hgf⟩
  · exact Or.inr (Or.inl ⟨by simpa only [hdf] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,
      by simpa only [hdg] using Polynomial.isHomogeneous_homogenize (n := g.natDegree) g,quadratic_not_linear_square g f hgirr hdf⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simpa only [hdf] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,
      by simpa only [hdg] using Polynomial.isHomogeneous_homogenize (n := g.natDegree) g,quadratic_not_linear_square f g hfirr hdg⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by simpa only [hdf] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,
      by simpa only [hdg] using Polynomial.isHomogeneous_homogenize (n := g.natDegree) g,hgf⟩))

/-- The positive full affine degree prevents an infinity-axis proportionality. -/
theorem infinity_low_factor_pair : CF15InfinityLowFactorPair := by
  intro f hd
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  refine ⟨by simp,full_lift_nonzero f hf,?_⟩
  rcases hd with hd | hd
  · apply Or.inl
    refine ⟨MvPolynomial.isHomogeneous_X ℤ 1,by simpa only [hd] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,?_⟩
    rintro ⟨q,he⟩
    have hs := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]) he
    simp only [rationalBinary,MvPolynomial.map_X,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Polynomial.algebraMap_eq] at hs
    rw [rational_lift_section] at hs
    change (1:Polynomial ℚ)=Polynomial.C q*rationalPolynomial f at hs
    have hq : q ≠ 0 := by intro hz; simp [hz] at hs
    have hh := congrArg Polynomial.natDegree hs
    simp only [Polynomial.natDegree_one,Polynomial.natDegree_C_mul hq,
      rational_degree f,hd] at hh
    omega
  · apply Or.inr; apply Or.inl
    refine ⟨MvPolynomial.isHomogeneous_X ℤ 1,by simpa only [hd] using Polynomial.isHomogeneous_homogenize (n := f.natDegree) f,?_⟩
    rintro ⟨q,he⟩
    have hs := congrArg (MvPolynomial.aeval ![(Polynomial.X:Polynomial ℚ),1]) he
    simp only [rationalBinary,map_pow,MvPolynomial.map_X,map_mul,MvPolynomial.aeval_X,
      MvPolynomial.aeval_C,Polynomial.algebraMap_eq] at hs
    rw [rational_lift_section] at hs
    change rationalPolynomial f=Polynomial.C q*(1:Polynomial ℚ)^2 at hs
    simp only [one_pow,mul_one] at hs
    have hh := congrArg Polynomial.natDegree hs
    simp only [Polynomial.natDegree_C,rational_degree f,hd] at hh
    omega

private theorem full_homogenize_power (f : Polynomial ℤ) (k : ℕ) :
    (f^k).homogenize (f.natDegree*k)=(f.homogenize f.natDegree)^k := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · simpa only [Nat.mul_comm] using (Polynomial.isHomogeneous_homogenize (n := f.natDegree) f).pow k
  · simp [Polynomial.aeval_homogenize_X_one f le_rfl]

/-- Unique factorization is used only to choose fixed divisors of one Q.
An infinity gap or two distinct small factors gives the low branch; the only
remaining all-small case would be a forbidden scalar pure power. -/
theorem primitive_factor_dispatch : CF15PrimitiveFactorDispatch := by
  classical
  intro Q N hhom hc hN hnon
  let P := binaryDehomogenize Q
  obtain ⟨hQ,hP,hPn,hdeg,hform⟩ := primitive_dehomogenization Q N hhom hc
  change P.IsPrimitive at hP
  change P ≠ 0 at hPn
  change P.natDegree ≤ N at hdeg
  change P.homogenize N=Q at hform
  have hPpos : 0<P.natDegree := by
    by_contra hn
    have hz : P.natDegree=0 := by omega
    have he := Polynomial.eq_C_of_natDegree_eq_zero hz
    apply hnon (MvPolynomial.X 1) 1 N (P.coeff 0) (MvPolynomial.isHomogeneous_X ℤ 1) (Or.inl rfl)
    rw [← hform,he,Polynomial.homogenize_C]; simp
  have hnotunit := Polynomial.not_isUnit_of_natDegree_pos P hPpos
  obtain ⟨f,hfmem⟩ := exists_mem_normalizedFactors hPn hnotunit
  have hif := irreducible_of_normalized_factor f hfmem
  have hfdvd := dvd_of_mem_normalizedFactors hfmem
  have hfdata := primitive_irreducible_factor P f hP hif hfdvd
  have hflift := homogeneous_factor_lift P f N hP hfdvd hdeg
  rw [hform] at hflift
  by_cases hhigh : ∃ g ∈ normalizedFactors P, 3 ≤ g.natDegree
  · obtain ⟨g,hg,hgd⟩ := hhigh
    have hgdvd := dvd_of_mem_normalizedFactors hg
    have hgi := irreducible_of_normalized_factor g hg
    have hgp := primitive_irreducible_factor P g hP hgi hgdvd
    have hglift := homogeneous_factor_lift P g N hP hgdvd hdeg
    rw [hform] at hglift
    exact Or.inr ⟨g,hgp.1,hgp.2.2,hgd,hglift.2.2.1.trans hN,hglift.2.2.2.2⟩
  have hsmall (g : Polynomial ℤ) (hg : g ∈ normalizedFactors P) : g.natDegree=1 ∨ g.natDegree=2 := by
    have hp := (primitive_irreducible_factor P g hP (irreducible_of_normalized_factor g hg)
      (dvd_of_mem_normalizedFactors hg)).2.1
    have hh : ¬3≤g.natDegree := by intro h; exact hhigh ⟨g,hg,h⟩
    omega
  by_cases hgap : P.natDegree<N
  · left
    refine ⟨MvPolynomial.X 1,f.homogenize f.natDegree,infinity_low_factor_pair f (hsmall f hfmem),?_,hflift.2.2.2.2⟩
    rw [← hform,homogenization_padding P N hdeg]
    exact (dvd_pow_self (MvPolynomial.X 1 : SourcePolynomial) (by omega : N-P.natDegree ≠ 0)).trans (dvd_mul_left _ _)
  by_cases hother : ∃ g ∈ normalizedFactors P, g ≠ f
  · obtain ⟨g,hg,hgf⟩ := hother
    have hgdvd := dvd_of_mem_normalizedFactors hg
    have hgi := irreducible_of_normalized_factor g hg
    have hgp := primitive_irreducible_factor P g hP hgi hgdvd
    have hglift := homogeneous_factor_lift P g N hP hgdvd hdeg
    rw [hform] at hglift
    have hna : ¬ Associated f g := by
      intro ha
      exact hgf (mem_normalizedFactors_eq_of_associated hfmem hg ha).symm
    exact Or.inl ⟨f.homogenize f.natDegree,g.homogenize g.natDegree,
      distinct_low_factor_pair f g hfdata.1 hgp.1 hif hgi hna (hsmall f hfmem) (hsmall g hg),
      hflift.2.2.2.2,hglift.2.2.2.2⟩
  have huniq : ∀ {m : Polynomial ℤ}, m ∈ normalizedFactors P → m=f := by
    intro m hm
    by_contra hn
    exact hother ⟨m,hm,hn⟩
  obtain ⟨k,ha⟩ := exists_associated_prime_pow_of_unique_normalized_factor huniq hPn
  obtain ⟨u,hu⟩ := ha
  obtain ⟨a,hau,haeq⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have he : P=Polynomial.C a*f^k := by rw [← hu,← haeq,mul_comm]
  have ha0 : a ≠ 0 := hau.ne_zero
  have hNd : N=f.natDegree*k := by
    calc
      _ = P.natDegree := by omega
      _ = (f^k).natDegree := by rw [he,Polynomial.natDegree_C_mul ha0]
      _ = _ := by simpa only [Nat.mul_comm] using Polynomial.natDegree_pow f k
  exfalso
  apply hnon (f.homogenize f.natDegree) f.natDegree k a
    (Polynomial.isHomogeneous_homogenize (n := f.natDegree) f) (hsmall f hfmem)
  rw [← hform,he,Polynomial.homogenize_C_mul,hNd,full_homogenize_power]

/-- Select the fixed factors of the actual class polynomial in either chart. -/
theorem actual_graph_factor_dispatch : CF15ActualGraphFactorDispatch := by
  intro X D A B hX hg hr inverse
  obtain ⟨_,hc,hhom,_,hN,_,_,_,_,hnon,_⟩ := actual_primitive_graph_factors X D A B hX hg hr inverse
  exact primitive_factor_dispatch _ _ hhom hc hN hnon

end
end P0365Subquarter
