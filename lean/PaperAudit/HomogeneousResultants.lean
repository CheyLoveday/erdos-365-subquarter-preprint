import PaperProofs.HomogeneousResultants

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print graphDegree
#print homogeneousGraphValue
#print fullGraphResultant
#print CF13HomogeneousForm
#print CF13FullResultantNonzero
#print CF13HomogeneousBezout
#print CF13EvaluatedGCD
#print CF13ResultantHeight
#print CF13ActualMixedResultant
#check (homogeneous_form : CF13HomogeneousForm)
#check (full_resultant_nonzero : CF13FullResultantNonzero)
#check (homogeneous_bezout : CF13HomogeneousBezout)
#check (evaluated_gcd : CF13EvaluatedGCD)
#check (resultant_height : CF13ResultantHeight)
#check (actual_mixed_resultant : CF13ActualMixedResultant)
#print axioms homogeneous_form
#print axioms full_resultant_nonzero
#print axioms homogeneous_bezout
#print axioms evaluated_gcd
#print axioms resultant_height
#print axioms actual_mixed_resultant
set_option pp.all false

-- Complete applications of all six frozen targets.
example : CF13HomogeneousForm := by
  intro P r hd
  obtain ⟨hh,he,hi⟩ := homogeneous_form P r hd
  exact ⟨hh,fun x y hy => he x y hy,fun x => hi x⟩
example : CF13FullResultantNonzero := by
  intro A B hr hcop
  exact full_resultant_nonzero A B hr hcop
example : CF13HomogeneousBezout := by
  intro A B r hr hA hB
  obtain ⟨L₁,L₂,L₃,L₄,h₁,h₂,h₃,h₄,hx,hy⟩ := homogeneous_bezout A B r hr hA hB
  exact ⟨L₁,L₂,L₃,L₄,h₁,h₂,h₃,h₄,hx,hy⟩
example : CF13EvaluatedGCD := by
  intro A B r hr hA hB x y hxy
  exact evaluated_gcd A B r hr hA hB x y hxy
example : CF13ResultantHeight := by
  intro A B r H hH hA hB
  exact resultant_height A B r H hH hA hB
example : CF13ActualMixedResultant := by
  intro X D A B hX hd hr
  obtain ⟨hne,hbound,hg⟩ := actual_mixed_resultant X D A B hX hd hr
  exact ⟨hne,hbound,fun x y hxy => hg x y hxy⟩

-- Padding two constants creates a common root at infinity, despite Q[X]
-- coprimality. The actual degree binder in nonvanishing cannot be omitted.
example : IsCoprime (1 : Polynomial ℚ) 1 := ⟨1,0,by simp⟩
example : Polynomial.resultant (1 : Polynomial ℤ) 1 1 1 = 0 :=
  Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ (by simp) (by simp)
example : fullGraphResultant 1 1 = 1 := by
  norm_num [fullGraphResultant,graphDegree]

-- Degree-zero scalar graphs cannot use the mixed evaluated-gcd conclusion.
example : fullGraphResultant (Polynomial.C 2) (Polynomial.C 2) = 1 := by
  norm_num [fullGraphResultant,graphDegree]
example : ¬ ((Int.gcd (2:ℤ) 2 : ℤ) ∣ fullGraphResultant (Polynomial.C 2) (Polynomial.C 2)) := by
  norm_num [fullGraphResultant,graphDegree]

-- Both primitive signed axes are retained, with one evaluated form zero.
example : homogeneousGraphValue Polynomial.X 1 1 0 = 1 ∧
    homogeneousGraphValue 1 1 1 0 = 0 := by
  norm_num [homogeneousGraphValue]
example : homogeneousGraphValue Polynomial.X 1 0 (-1) = 0 ∧
    homogeneousGraphValue 1 1 0 (-1) = -1 := by
  norm_num [homogeneousGraphValue]
example : (Int.gcd (homogeneousGraphValue Polynomial.X 1 1 0)
    (homogeneousGraphValue 1 1 1 0) : ℤ) ∣ Polynomial.resultant Polynomial.X 1 1 1 := by
  exact evaluated_gcd Polynomial.X 1 1 (by decide) (by simp) (by simp) 1 0 ⟨1,0,by norm_num⟩
example : (Int.gcd (homogeneousGraphValue Polynomial.X 1 0 (-1))
    (homogeneousGraphValue 1 1 0 (-1)) : ℤ) ∣ Polynomial.resultant Polynomial.X 1 1 1 := by
  exact evaluated_gcd Polynomial.X 1 1 (by decide) (by simp) (by simp) 0 (-1) ⟨0,-1,by norm_num⟩

private abbrev infinityA : Polynomial ℤ := Polynomial.X^2+1
private abbrev infinityB : Polynomial ℤ := Polynomial.X+Polynomial.C 2
private theorem infinityA_degree : infinityA.natDegree = 2 := by
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt (by norm_num)]
  norm_num
private theorem infinityB_degree : infinityB.natDegree = 1 := by simp

-- Source-retained affine5/gcd10 control: the supplied degree-three forms
-- share infinity. Their full homogeneous resultant is zero, as required.
example : Polynomial.resultant infinityA infinityB 3 3 = 0 := by
  apply Polynomial.resultant_eq_zero_of_lt_lt
  · rw [infinityA_degree]; decide
  · rw [infinityB_degree]; decide
example : homogeneousGraphValue infinityA 3 1 2 = 10 ∧
    homogeneousGraphValue infinityB 3 1 2 = 20 := by
  constructor
  · norm_num [homogeneousGraphValue,infinityA,
      Polynomial.homogenize_X_pow (by decide : (2:ℕ) ≤ 3)]
  · change (MvPolynomial.eval (![1,2] : Fin 2 → ℤ))
      ((Polynomial.X+Polynomial.C 2 : Polynomial ℤ).homogenize 3)=20
    rw [Polynomial.homogenize_add,Polynomial.homogenize_X (by decide),Polynomial.homogenize_C]
    norm_num
example : Polynomial.resultant infinityA infinityB = 5 := by
  rw [show infinityA.natDegree = 2 from infinityA_degree,
    show infinityB.natDegree = 1 from infinityB_degree]
  unfold Polynomial.resultant
  rw [Matrix.det_fin_three]
  norm_num [Polynomial.sylvester,Fin.addCases,infinityA,infinityB,Polynomial.coeff_one]
example : ¬ ((Int.gcd (10:ℤ) 20 : ℤ) ∣ (5:ℤ)) := by norm_num

-- Nonunit integer scalar contents survive: the full resultant differs
-- from the affine one, while rational coprimality still holds.
private abbrev scalarA : Polynomial ℤ := Polynomial.C 2*Polynomial.X
private theorem scalarA_degree : scalarA.natDegree = 1 := by
  rw [Polynomial.natDegree_mul (by norm_num) Polynomial.X_ne_zero]
  norm_num
example : IsCoprime (rationalPolynomial scalarA) (rationalPolynomial (Polynomial.C 2)) := by
  refine ⟨0,Polynomial.C (1/2 : ℚ),?_⟩
  simp only [zero_mul,zero_add,rationalPolynomial,Polynomial.map_C,Int.coe_castRingHom,
    ← Polynomial.C_mul]
  norm_num
example : fullGraphResultant scalarA (Polynomial.C 2) = 4 := by
  unfold fullGraphResultant graphDegree
  rw [scalarA_degree,Polynomial.natDegree_C]
  change Polynomial.resultant scalarA (Polynomial.C 2) 1 1=4
  rw [Polynomial.resultant_C_right]
  norm_num [scalarA]
example : Polynomial.resultant scalarA (Polynomial.C 2) = 2 := by
  rw [Polynomial.resultant_C_right]
  norm_num [scalarA_degree]
example : homogeneousGraphValue scalarA 1 3 1 = 6 ∧
    homogeneousGraphValue (Polynomial.C 2) 1 3 1 = 2 := by
  constructor
  · unfold homogeneousGraphValue scalarA
    rw [Polynomial.homogenize_C_mul,Polynomial.homogenize_X (by decide)]
    norm_num
  · unfold homogeneousGraphValue
    rw [Polynomial.homogenize_C]
    norm_num
example : (Int.gcd (homogeneousGraphValue scalarA 1 3 1)
    (homogeneousGraphValue (Polynomial.C 2) 1 3 1) : ℤ) ∣ fullGraphResultant scalarA (Polynomial.C 2) := by
  simpa [fullGraphResultant,graphDegree,scalarA_degree] using
    evaluated_gcd scalarA (Polynomial.C 2) 1 (by decide) (by rw [scalarA_degree])
      (by simp) 3 1 ⟨0,1,by norm_num⟩

-- Generic zero-resultant and degree-zero height cases remain valid.
example : (Int.gcd (homogeneousGraphValue 0 1 1 0)
    (homogeneousGraphValue 0 1 1 0) : ℤ) ∣ Polynomial.resultant (0 : Polynomial ℤ) 0 1 1 :=
  evaluated_gcd 0 0 1 (by decide) (by simp) (by simp) 1 0 ⟨1,0,by norm_num⟩
example : |((Polynomial.resultant (0 : Polynomial ℤ) 0 0 0 : ℤ) : ℝ)| ≤ 1 := by
  norm_num [Polynomial.resultant]

end
end P0365Subquarter
