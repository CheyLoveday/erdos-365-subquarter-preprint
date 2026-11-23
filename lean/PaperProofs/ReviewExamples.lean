import PaperProofs.SourceRecovery

/-! Source-bound local checks for the manuscript §9. The polynomials, full
common homogenization degree, original canonical sources and admitted signs
are checked together. These examples are supplemental to the general proofs. -/
namespace P0365Subquarter.ReviewExamples
noncomputable section
set_option autoImplicit false
open Polynomial

def A8 : Polynomial ℤ := C 2 * (X - 1)
def B8 : Polynomial ℤ := C 2 * (X - C 2)
def A288 : Polynomial ℤ := C 6 * X - C 5
def B288 : Polynomial ℤ := C 6

theorem source8 : PairSource 8 2 1 1 3 := by
  norm_num [PairSource, Nat.prime_two.squarefree]
theorem source288 : PairSource 288 2 1 6 17 := by
  norm_num [PairSource, Nat.prime_two.squarefree]

/-- The second source intentionally has gcd(b,u)=2, which is admissible. -/
theorem source288_same_endpoint_overlap : ¬ Nat.Coprime 2 6 := by decide

theorem degree8 : graphDegree A8 B8 = 1 := by
  unfold graphDegree A8 B8
  rw [Polynomial.natDegree_C_mul (by decide : (2:ℤ)≠0),
    Polynomial.natDegree_C_mul (by decide : (2:ℤ)≠0)]
  change max (X-C (1:ℤ)).natDegree (X-C (2:ℤ)).natDegree=1
  rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  rfl

theorem degree288 : graphDegree A288 B288 = 1 := by
  unfold graphDegree A288 B288
  rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_C_mul_X 6 (by decide)]
  simp


/-- Scalar integer contents are allowed: graph coprimality is over Q[X]. -/
theorem coprime8 : IsCoprime (rationalPolynomial A8) (rationalPolynomial B8) := by
  refine ⟨C (1/2:ℚ),C (-1/2:ℚ),?_⟩
  norm_num [A8,B8]
  ring_nf
  change C (1/2:ℚ)*C 2=C 1
  rw [← map_mul]
  norm_num

theorem coprime288 : IsCoprime (rationalPolynomial A288) (rationalPolynomial B288) := by
  refine ⟨0,C (1/6:ℚ),?_⟩
  norm_num [B288]
  change C (1/6:ℚ)*C 6=C 1
  rw [← map_mul]
  norm_num

theorem negative_coprime_graphs :
    IsCoprime (rationalPolynomial (-A8)) (rationalPolynomial (-B8)) ∧
    IsCoprime (rationalPolynomial (-A288)) (rationalPolynomial (-B288)) := by
  constructor
  · simpa [rationalPolynomial] using coprime8.neg_neg
  · simpa [rationalPolynomial] using coprime288.neg_neg

theorem branch8 : sourceGraphBranch true A8 B8 2 1 1 3 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,A8,B8]
theorem branch8_negative : sourceGraphBranch true (-A8) (-B8) 2 1 1 3 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,A8,B8]
theorem branch288 : sourceGraphBranch true A288 B288 2 1 6 17 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,A288,B288]
theorem branch288_negative : sourceGraphBranch true (-A288) (-B288) 2 1 6 17 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,A288,B288]

theorem full_resultant8 : fullGraphResultant A8 B8 = -4 := by
  unfold fullGraphResultant
  rw [degree8]
  change Polynomial.resultant (C 2*(X-C (1:ℤ))) (C 2*(X-C 2)) 1 1 = -4
  rw [Polynomial.resultant_C_mul_left,Polynomial.resultant_C_mul_right,
    Polynomial.resultant_X_sub_C_left _ _ _ (Polynomial.natDegree_X_sub_C_le 2)]
  norm_num

theorem full_resultant288 : fullGraphResultant A288 B288 = 36 := by
  unfold fullGraphResultant
  rw [degree288]
  change Polynomial.resultant (C 6*X-C (5:ℤ)) (C 6) 1 1=36
  rw [Polynomial.resultant_C_right]
  norm_num

/-- Actual affine degrees (1,0) lose the factor needed at infinity. -/
theorem affine_resultant288 : Polynomial.resultant A288 B288 = 6 := by
  unfold A288 B288
  rw [Polynomial.natDegree_sub_C,Polynomial.natDegree_C_mul_X 6 (by decide)]
  norm_num

private theorem homogenize8 :
    A8.homogenize 1=2*(MvPolynomial.X 0-MvPolynomial.X 1) ∧
    B8.homogenize 1=2*(MvPolynomial.X 0-2*MvPolynomial.X 1) := by
  constructor
  · rw [A8,Polynomial.homogenize_C_mul,Polynomial.homogenize_sub,
      Polynomial.homogenize_X (by decide)]
    norm_num
  · rw [B8,Polynomial.homogenize_C_mul,Polynomial.homogenize_sub,
      Polynomial.homogenize_X (by decide),Polynomial.homogenize_C]
    norm_num

private theorem homogenize288 :
    A288.homogenize 1=6*MvPolynomial.X 0-5*MvPolynomial.X 1 ∧
    B288.homogenize 1=6*MvPolynomial.X 1 := by
  constructor
  · rw [A288,Polynomial.homogenize_sub,Polynomial.homogenize_C_mul,
      Polynomial.homogenize_X (by decide),Polynomial.homogenize_C]
    norm_num
  · rw [B288,Polynomial.homogenize_C]
    norm_num

theorem values8 : homogeneousGraphValue A8 1 3 1=4 ∧
    homogeneousGraphValue B8 1 3 1=2 := by
  simp only [homogeneousGraphValue,homogenize8.1,homogenize8.2]
  norm_num

theorem values288 : homogeneousGraphValue A288 1 17 6=72 ∧
    homogeneousGraphValue B288 1 17 6=36 := by
  simp only [homogeneousGraphValue,homogenize288.1,homogenize288.2]
  norm_num

theorem gcd8 : sourceGraphGCD true A8 B8 2 1 1 3=2 := by
  simp only [sourceGraphGCD,graphParameter,ite_true,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,degree8]
  norm_num [values8.1,values8.2]

theorem gcd288 : sourceGraphGCD true A288 B288 2 1 6 17=36 := by
  simp only [sourceGraphGCD,graphParameter,ite_true,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,degree288]
  norm_num [values288.1,values288.2]

theorem full_versus_affine288 :
    sourceGraphGCD true A288 B288 2 1 6 17 ∣ (fullGraphResultant A288 B288).natAbs ∧
    ¬ sourceGraphGCD true A288 B288 2 1 6 17 ∣ (Polynomial.resultant A288 B288).natAbs := by
  rw [gcd288,full_resultant288,affine_resultant288]
  norm_num


private theorem negated_gcd (A B : Polynomial ℤ) (b d u v : ℕ) :
    sourceGraphGCD true (-A) (-B) b d u v=sourceGraphGCD true A B b d u v := by
  simp [sourceGraphGCD,graphDegree,homogeneousGraphValue]

/-- Globally negating both sections preserves the positive evaluated gcd. -/
theorem negative_gcds : sourceGraphGCD true (-A8) (-B8) 2 1 1 3=2 ∧
    sourceGraphGCD true (-A288) (-B288) 2 1 6 17=36 := by
  rw [negated_gcd,negated_gcd]
  exact ⟨gcd8,gcd288⟩

private theorem negated_resultant (A B : Polynomial ℤ) (hd : graphDegree A B=1) :
    fullGraphResultant (-A) (-B)=fullGraphResultant A B := by
  have hdeg : graphDegree (-A) (-B)=graphDegree A B := by simp [graphDegree]
  simp only [fullGraphResultant,hdeg,hd]
  have ha : -A=C (-1:ℤ)*A := by simp
  have hb : -B=C (-1:ℤ)*B := by simp
  rw [ha,hb,Polynomial.resultant_C_mul_left,Polynomial.resultant_C_mul_right]
  norm_num

/-- The full homogeneous resultants are fixed for either graph sign. -/
theorem negative_resultants : fullGraphResultant (-A8) (-B8)= -4 ∧
    fullGraphResultant (-A288) (-B288)=36 := by
  rw [negated_resultant _ _ degree8,negated_resultant _ _ degree288]
  exact ⟨full_resultant8,full_resultant288⟩

/-- The precise graph pullback is expanded, rather than a supplied value. -/
theorem pullback8 : graphPullback true A8 B8 =
    MvPolynomial.X 0^2*(2*(MvPolynomial.X 0-2*MvPolynomial.X 1))^3-
    MvPolynomial.X 1^2*(2*(MvPolynomial.X 0-MvPolynomial.X 1))^3 := by
  simp only [graphPullback,degree8,ite_true,homogenize8.1,homogenize8.2]

theorem pullback288 : graphPullback true A288 B288 =
    MvPolynomial.X 0^2*(6*MvPolynomial.X 1)^3-
    MvPolynomial.X 1^2*(6*MvPolynomial.X 0-5*MvPolynomial.X 1)^3 := by
  simp only [graphPullback,degree288,ite_true,homogenize288.1,homogenize288.2]

theorem pullback_value8 : MvPolynomial.eval ![3,1] (graphPullback true A8 B8)=8 := by
  rw [pullback8]
  norm_num

theorem pullback_value288 : MvPolynomial.eval ![17,6] (graphPullback true A288 B288)=46656 := by
  rw [pullback288]
  norm_num

private theorem content_dvd_value (H : SourcePolynomial) (hH : H≠0)
    (z : Fin 2 → ℤ) : binaryContent H ∣ (MvPolynomial.eval z H).natAbs := by
  obtain ⟨_,_,_,he⟩ := binary_content_removal H hH
  rw [he z,Int.natAbs_mul,Int.natAbs_natCast]
  exact dvd_mul_right _ _

private theorem nonzero8 : graphPullback true A8 B8 ≠ 0 := by
  intro hz
  have h:=pullback_value8
  rw [hz,map_zero] at h
  norm_num at h
private theorem nonzero288 : graphPullback true A288 B288 ≠ 0 := by
  intro hz
  have h:=pullback_value288
  rw [hz,map_zero] at h
  norm_num at h

theorem content8 : binaryContent (graphPullback true A8 B8)=8 := by
  apply Nat.dvd_antisymm
  · have h:=content_dvd_value (graphPullback true A8 B8) nonzero8 ![3,1]
    simpa [pullback_value8] using h
  · classical
    have hfactor : graphPullback true A8 B8=MvPolynomial.C (8:ℤ)*
        (MvPolynomial.X 0^2*(MvPolynomial.X 0-2*MvPolynomial.X 1)^3-
          MvPolynomial.X 1^2*(MvPolynomial.X 0-MvPolynomial.X 1)^3) := by
      rw [pullback8]
      norm_num
      ring
    unfold binaryContent
    apply Finset.dvd_gcd_iff.mpr
    intro e _
    rw [hfactor,MvPolynomial.coeff_C_mul,Int.natAbs_mul]
    exact dvd_mul_right _ _

theorem content288 : binaryContent (graphPullback true A288 B288)=1 := by
  have h1:=content_dvd_value (graphPullback true A288 B288) nonzero288 ![0,1]
  have h2:=content_dvd_value (graphPullback true A288 B288) nonzero288 ![2,1]
  norm_num [pullback288] at h1 h2
  have h3:=Nat.dvd_gcd h1 h2
  norm_num at h3
  simpa only [pullback288] using h3

theorem content8_corrected_divisibility :
    ¬ binaryContent (graphPullback true A8 B8) ∣ (fullGraphResultant A8 B8).natAbs ∧
    binaryContent (graphPullback true A8 B8) ∣ (sourceGraphGCD true A8 B8 2 1 1 3)^3 := by
  rw [content8,full_resultant8,gcd8]
  norm_num

private theorem inverse_pullback_neg (A B : Polynomial ℤ) :
    graphPullback true (-A) (-B)= -graphPullback true A B := by
  simp only [graphPullback,graphDegree,Polynomial.natDegree_neg,ite_true,
    Polynomial.homogenize_neg]
  ring

private theorem content_neg (H : SourcePolynomial) : binaryContent (-H)=binaryContent H := by
  classical
  simp [binaryContent]

theorem content8_negative : binaryContent (graphPullback true (-A8) (-B8))=8 := by
  rw [inverse_pullback_neg,content_neg,content8]
theorem content288_negative : binaryContent (graphPullback true (-A288) (-B288))=1 := by
  rw [inverse_pullback_neg,content_neg,content288]

private theorem primitive_value_of_content (H : SourcePolynomial) (hH : H≠0)
    (z : Fin 2 → ℤ) (c v : ℤ) (hc : (binaryContent H:ℤ)=c)
    (hv : MvPolynomial.eval z H=c*v) (hc0 : c≠0) :
    MvPolynomial.eval z (binaryPrimitivePart H)=v := by
  obtain ⟨_,_,_,he⟩ := binary_content_removal H hH
  have h := (he z).symm.trans hv
  rw [hc] at h
  exact mul_left_cancel₀ hc0 h

theorem reduced_level8 : MvPolynomial.eval ![3,1] (binaryPrimitivePart (graphPullback true A8 B8))=1 := by
  apply primitive_value_of_content _ nonzero8 _ 8 1
  · norm_num [content8]
  · simpa using pullback_value8
  · norm_num

theorem reduced_level8_negative :
    MvPolynomial.eval ![3,1] (binaryPrimitivePart (graphPullback true (-A8) (-B8)))= -1 := by
  rw [inverse_pullback_neg]
  apply primitive_value_of_content _ (neg_ne_zero.mpr nonzero8) _ 8 (-1)
  · norm_num [content_neg,content8]
  · simp [pullback_value8]
  · norm_num

theorem reduced_level288 :
    MvPolynomial.eval ![17,6] (binaryPrimitivePart (graphPullback true A288 B288))=46656 := by
  apply primitive_value_of_content _ nonzero288 _ 1 46656
  · norm_num [content288]
  · simpa using pullback_value288
  · norm_num

theorem reduced_level288_negative :
    MvPolynomial.eval ![17,6] (binaryPrimitivePart (graphPullback true (-A288) (-B288)))= -46656 := by
  rw [inverse_pullback_neg]
  apply primitive_value_of_content _ (neg_ne_zero.mpr nonzero288) _ 1 (-46656)
  · norm_num [content_neg,content288]
  · simp [pullback_value288]
  · norm_num

/-- All four signed graph points invoke the source-recovery theorem with a
proved original source and branch, not a supplied signed-level equation. -/
theorem actual_signed_recoveries :
    signedGraphRecovery true A8 B8 2 1 1 3 ∧
    signedGraphRecovery true (-A8) (-B8) 2 1 1 3 ∧
    signedGraphRecovery true A288 B288 2 1 6 17 ∧
    signedGraphRecovery true (-A288) (-B288) 2 1 6 17 := by
  exact ⟨inverse_source_recovery _ _ _ _ _ _ _ source8 branch8,
    inverse_source_recovery _ _ _ _ _ _ _ source8 branch8_negative,
    inverse_source_recovery _ _ _ _ _ _ _ source288 branch288,
    inverse_source_recovery _ _ _ _ _ _ _ source288 branch288_negative⟩

/-- The non-admitted direct point from §9: parameter membership alone does
not imply the actual-source equation. -/
theorem nonadmitted_parameter :
    Int.gcd (homogeneousGraphValue (X:Polynomial ℤ) 1 2 1)
      (homogeneousGraphValue (1:Polynomial ℤ) 1 2 1)=1 ∧
    MvPolynomial.eval ![2,1] (graphPullback false X 1)= -4 ∧ (-4:ℤ)≠1^2 := by
  have hd : graphDegree (X:Polynomial ℤ) 1=1 := by simp [graphDegree]
  simp only [graphPullback,hd,Bool.false_eq_true,ite_false,homogeneousGraphValue,
    Polynomial.homogenize_X (by decide : (1:ℕ)≠0),Polynomial.homogenize_one]
  norm_num

end
end P0365Subquarter.ReviewExamples
