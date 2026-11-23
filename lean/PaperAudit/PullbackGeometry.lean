import PaperProofs.PullbackGeometry

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print graphPullbackDegree
#print affineGraphPullback
#print pullbackAxisGeometry
#print CF14MixedSectionsNonzero
#print CF14AffinePullbackDegrees
#print CF14HomogeneousPullback
#print CF14AxisOrders
#print CF14AxisPowerExclusion
#print CF14ActualMixedPullback
#check (mixed_sections_nonzero : CF14MixedSectionsNonzero)
#check (affine_pullback_degrees : CF14AffinePullbackDegrees)
#check (homogeneous_pullback : CF14HomogeneousPullback)
#check (axis_orders : CF14AxisOrders)
#check (axis_power_exclusion : CF14AxisPowerExclusion)
#check (actual_mixed_pullback : CF14ActualMixedPullback)
#print axioms mixed_sections_nonzero
#print axioms affine_pullback_degrees
#print axioms homogeneous_pullback
#print axioms axis_orders
#print axioms axis_power_exclusion
#print axioms actual_mixed_pullback
set_option pp.all false

-- Full typed applications of all six reviewed targets.
example : CF14MixedSectionsNonzero := by
  intro A B hr hc
  exact mixed_sections_nonzero A B hr hc
example : CF14AffinePullbackDegrees := by
  intro A B hA hB inverse
  exact affine_pullback_degrees A B hA hB inverse
example : CF14HomogeneousPullback := by
  intro inverse A B
  obtain ⟨hd,he,hh,h⟩ := homogeneous_pullback inverse A B
  exact ⟨hd,he,hh,fun hA hB => h hA hB⟩
example : CF14AxisOrders := by
  intro A B hr hc inverse
  obtain ⟨he,hx,hy,hi⟩ := axis_orders A B hr hc inverse
  exact ⟨he,hx,hy,fun h => hi h⟩
example : CF14AxisPowerExclusion := by
  intro A B hr hc inverse c i
  exact axis_power_exclusion A B hr hc inverse c i
example : CF14ActualMixedPullback := by
  intro X D A B hX hb hr inverse
  exact actual_mixed_pullback X D A B hX hb hr inverse

-- Homogenization retains both zero sections. Nonzero conclusions are guarded.
example (inverse : Bool) : graphPullback inverse 0 0=0 := by
  cases inverse <;> simp [graphPullback]
example : ¬ (∀ p q : Polynomial ℤ, p.natTrailingDegree ≠ q.natTrailingDegree →
    (p-q).natTrailingDegree=min p.natTrailingDegree q.natTrailingDegree) := by
  intro h
  have he := h 0 Polynomial.X (by simp)
  simp at he

-- Actual degree zero remains a ruling: inverse H=x²-8y² has the 8/9 source.
example : graphDegree (Polynomial.C 2) 1=0 := by simp [graphDegree]
example : graphPullback true (Polynomial.C 2) 1 =
    MvPolynomial.X 0^2-MvPolynomial.C 8*MvPolynomial.X 1^2 := by
  unfold graphPullback
  have hd : graphDegree (Polynomial.C 2) 1=0 := by simp [graphDegree]
  rw [hd]
  simp only [ite_true,Polynomial.homogenize_one,Polynomial.homogenize_C]
  norm_num
  ring
private theorem axis_source_eight : PairSource 8 2 1 1 3 := by
  norm_num [PairSource]
  exact Nat.prime_two.squarefree
example : signedGraphRecovery true (Polynomial.C 2) 1 2 1 1 3 :=
  inverse_source_recovery _ _ _ _ _ _ _ axis_source_eight (by
    norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial])

private def axisA : Polynomial ℤ := Polynomial.X+1
private theorem axis_degree : graphDegree axisA 1=1 := by
  have h : axisA.natDegree=1 := by
    simpa only [axisA,Polynomial.C_1] using (Polynomial.natDegree_X_add_C (1:ℤ))
  simp [graphDegree,h]
private theorem axis_coprime : IsCoprime (rationalPolynomial axisA) (rationalPolynomial 1) :=
  ⟨0,1,by simp [rationalPolynomial]⟩

-- A genuine source can lie on a pullback with a repeated axis factor.
-- The factor is retained; abc must wait for the separate support screen.
example : graphPullback false axisA 1 = MvPolynomial.X 1^2*
    (MvPolynomial.X 1*(MvPolynomial.X 0+MvPolynomial.X 1)^2-MvPolynomial.X 0^3) := by
  unfold graphPullback
  rw [axis_degree]
  simp only [Bool.false_eq_true,ite_false,axisA,Polynomial.homogenize_add,Polynomial.homogenize_one]
  rw [Polynomial.homogenize_X (by decide)]
  simp
  ring
example : (affineGraphPullback false axisA 1).natTrailingDegree=0 ∧
    graphPullbackDegree false (graphDegree axisA 1)-(affineGraphPullback false axisA 1).natDegree=2 := by
  have he := axis_orders axisA 1 (by rw [axis_degree]) axis_coprime false
  have hd := (affine_pullback_degrees axisA 1 (by
    intro h; have := congrArg Polynomial.natDegree h
    simp [axisA] at this) one_ne_zero false).2
  have ha0 : axisA.natTrailingDegree=0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right; norm_num [axisA]
  have ha1 : axisA.natDegree=1 := by simpa [graphDegree] using axis_degree
  constructor
  · simpa [ha0] using he.1
  · rw [hd]; norm_num [ha1,axis_degree,graphPullbackDegree]
example : signedGraphRecovery false axisA 1 2 1 1 3 :=
  direct_source_recovery _ _ _ _ _ _ _ axis_source_eight (by
    norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial,axisA])

-- Inverse order two occurs at BOTH axes; coprimality alone does not remove it.
example : (affineGraphPullback true Polynomial.X 1).natTrailingDegree=2 ∧
    graphPullbackDegree true (graphDegree Polynomial.X 1)-
      (affineGraphPullback true Polynomial.X 1).natDegree=2 := by
  have hc : IsCoprime (rationalPolynomial (Polynomial.X:Polynomial ℤ)) (rationalPolynomial 1) :=
    ⟨0,1,by simp [rationalPolynomial]⟩
  have he := axis_orders Polynomial.X 1 (by simp [graphDegree]) hc true
  have hd := (affine_pullback_degrees Polynomial.X 1 Polynomial.X_ne_zero one_ne_zero true).2
  constructor
  · simpa using he.1
  · rw [hd]; norm_num [graphDegree,graphPullbackDegree]

-- Nonunit integral scalar contents survive: A=2X,B=2 are coprime over Q[X].
example : IsCoprime (rationalPolynomial (Polynomial.C 2*Polynomial.X))
    (rationalPolynomial (Polynomial.C 2)) := by
  refine ⟨0,Polynomial.C (1/2:ℚ),?_⟩
  simp only [zero_mul,zero_add,rationalPolynomial,Polynomial.map_C]
  change Polynomial.C (1/2:ℚ)*Polynomial.C 2=1
  rw [← Polynomial.C_mul]
  norm_num
-- The r=1,2,3 degrees are exactly 5,7,9 / 5,8,11.
example : (List.map (graphPullbackDegree false) [1,2,3])=[5,7,9] ∧
    (List.map (graphPullbackDegree true) [1,2,3])=[5,8,11] := by decide

end
end P0365Subquarter
