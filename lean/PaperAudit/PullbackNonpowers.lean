import PaperProofs.PullbackNonpowers

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print binaryDehomogenize
#print mixedPullbackNonpowers
#print CF14BinaryDehomogenization
#print CF14SmallPowerAxisScreen
#print CF14RadicalSupportBound
#print CF14NonaxisABC
#print CF14HomogeneousSmallPowerExclusion
#print CF14ActualMixedNonpowers
#print CF14RoundedClassNonpowers
#check (binary_dehomogenization : CF14BinaryDehomogenization)
#check (small_power_axis_screen : CF14SmallPowerAxisScreen)
#check (radical_support_bound : CF14RadicalSupportBound)
#check (nonaxis_abc : CF14NonaxisABC)
#check (homogeneous_small_power_exclusion : CF14HomogeneousSmallPowerExclusion)
#check (actual_mixed_nonpowers : CF14ActualMixedNonpowers)
#check (rounded_class_nonpowers : CF14RoundedClassNonpowers)
#print axioms binary_dehomogenization
#print axioms small_power_axis_screen
#print axioms radical_support_bound
#print axioms nonaxis_abc
#print axioms homogeneous_small_power_exclusion
#print axioms actual_mixed_nonpowers
#print axioms rounded_class_nonpowers
set_option pp.all false

-- All seven complete independently frozen target applications.
example : CF14BinaryDehomogenization := by
  intro G d hG
  obtain ⟨hd,he,hn⟩ := binary_dehomogenization G d hG
  exact ⟨hd,he,fun h => hn h⟩
example : CF14SmallPowerAxisScreen := by
  intro A B hr hc inverse G d k c hG hd he
  exact small_power_axis_screen A B hr hc inverse G d k c hG hd he
example : CF14RadicalSupportBound := by
  intro A B P hA hB hP c hc e s t k
  exact radical_support_bound A B P hA hB hP c hc e s t k
example : CF14NonaxisABC := by
  intro A B hA hB hc inverse P c k hc0 hk hP0 hF hd
  exact nonaxis_abc A B hA hB hc inverse P c k hc0 hk hP0 hF hd
example : CF14HomogeneousSmallPowerExclusion := by
  intro A B hr hc inverse G d k c hG hd
  exact homogeneous_small_power_exclusion A B hr hc inverse G d k c hG hd
example : CF14ActualMixedNonpowers := by
  intro X D A B hX hb hr inverse
  exact actual_mixed_nonpowers X D A B hX hb hr inverse
example : CF14RoundedClassNonpowers := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_class_nonpowers δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  exact h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz

-- Generic homogeneous zero forms and roots at infinity are retained.
example (d : ℕ) : binaryDehomogenize (0:SourcePolynomial)=0 ∧
    (binaryDehomogenize (0:SourcePolynomial)).homogenize d=0 := by
  simp [binaryDehomogenize]
example : binaryDehomogenize (MvPolynomial.X 1^2)=1 := by simp [binaryDehomogenize]
example : (binaryDehomogenize (MvPolynomial.X 1^2)).natDegree=0 := by simp [binaryDehomogenize]

private theorem nonpower_coprime : IsCoprime
    (rationalPolynomial (Polynomial.X:Polynomial ℤ)) (rationalPolynomial 1) :=
  ⟨0,1,by simp [rationalPolynomial]⟩
private theorem nonpower_degree : 1 ≤ graphDegree Polynomial.X 1 := by simp [graphDegree]

-- Proper repeated factors on BOTH axes remain possible; no premature coprime
-- assumption on the original summands is introduced into the actual theorem.
example : graphPullback true Polynomial.X 1 =
    MvPolynomial.X 0^2*MvPolynomial.X 1^2*(MvPolynomial.X 1-MvPolynomial.X 0) := by
  unfold graphPullback
  have hr : graphDegree Polynomial.X 1=1 := by simp [graphDegree]
  rw [hr]
  simp only [ite_true,Polynomial.homogenize_one]
  rw [Polynomial.homogenize_X (by decide)]
  simp
  ring
-- Reducible quadratic powers are also excluded, including scalar and exponent0.
example (c : ℤ) (k : ℕ) : graphPullback true Polynomial.X 1 ≠
    MvPolynomial.C c*(MvPolynomial.X 0*MvPolynomial.X 1)^k := by
  apply homogeneous_small_power_exclusion Polynomial.X 1 nonpower_degree nonpower_coprime true
    (MvPolynomial.X 0*MvPolynomial.X 1) 2 k c
  · exact (MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1)
  · exact Or.inr rfl
example (c : ℤ) (k : ℕ) : graphPullback false Polynomial.X 1 ≠
    MvPolynomial.C c*(MvPolynomial.X 0+MvPolynomial.X 1)^k := by
  apply homogeneous_small_power_exclusion Polynomial.X 1 nonpower_degree nonpower_coprime false
    (MvPolynomial.X 0+MvPolynomial.X 1) 1 k c
  · exact (MvPolynomial.isHomogeneous_X ℤ 0).add (MvPolynomial.isHomogeneous_X ℤ 1)
  · exact Or.inl rfl
example : graphPullback true Polynomial.X 1 ≠ 1 := by
  simpa using homogeneous_small_power_exclusion Polynomial.X 1 nonpower_degree nonpower_coprime true
    (MvPolynomial.X 0) 1 0 1 (MvPolynomial.isHomogeneous_X ℤ 0) (Or.inl rfl)

-- r=0 cannot be admitted to this exclusion: its pullback IS a quadratic power.
example : ∃ G : SourcePolynomial, G.IsHomogeneous 2 ∧
    graphPullback true (Polynomial.C 2) 1=MvPolynomial.C 1*G^1 := by
  refine ⟨graphPullback true (Polynomial.C 2) 1,?_,by simp⟩
  have h := (homogeneous_pullback true (Polynomial.C 2) 1).2.2.1
  simpa [graphPullbackDegree,graphDegree] using h

-- All-zero exponents in the radical-support target are valid, not an omitted case.
example : (UniqueFactorizationMonoid.radical ((1:Polynomial ℚ)^0*
    (Polynomial.X^0*1^0)*(Polynomial.C 2*1^0))).natDegree ≤ 1 := by
  simpa using radical_support_bound 1 1 1 one_ne_zero one_ne_zero one_ne_zero 2 (by norm_num) 0 0 0 0

end
end P0365Subquarter
