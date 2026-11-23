import PaperProofs.SourceRecovery

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print binaryContent
#print binaryPrimitivePart
#print graphParameter
#print graphPartner
#print graphLevelPower
#print graphPullback
#print sourceGraphGCD
#print sourceGraphBranch
#print signedGraphRecovery
#print reducedGraphLevel
#print CF13PrimitiveSignedRecovery
#print CF13DirectSourceRecovery
#print CF13InverseSourceRecovery
#print CF13BinaryContentRemoval
#print CF13AdmittedContentLevel
#print CF13ActualSourceResultantLevel
#print CF13RoundedClassResultantLevels
#check (primitive_signed_recovery : CF13PrimitiveSignedRecovery)
#check (direct_source_recovery : CF13DirectSourceRecovery)
#check (inverse_source_recovery : CF13InverseSourceRecovery)
#check (binary_content_removal : CF13BinaryContentRemoval)
#check (admitted_content_level : CF13AdmittedContentLevel)
#check (actual_source_resultant_level : CF13ActualSourceResultantLevel)
#check (rounded_class_resultant_levels : CF13RoundedClassResultantLevels)
#print axioms primitive_signed_recovery
#print axioms direct_source_recovery
#print axioms inverse_source_recovery
#print axioms binary_content_removal
#print axioms admitted_content_level
#print axioms actual_source_resultant_level
#print axioms rounded_class_resultant_levels
set_option pp.all false

-- Complete applications of all seven frozen targets.
example : CF13PrimitiveSignedRecovery := by
  intro v u hv hu hcop a b ha hb he
  obtain ⟨σ,hσ,hg,ha',hb',hv',hu'⟩ := primitive_signed_recovery v u hv hu hcop a b ha hb he
  exact ⟨σ,hσ,hg,ha',hb',hv',hu'⟩
example : CF13DirectSourceRecovery := by
  intro A B n b d u v hs hb
  exact direct_source_recovery A B n b d u v hs hb
example : CF13InverseSourceRecovery := by
  intro A B n b d u v hs hb
  exact inverse_source_recovery A B n b d u v hs hb
example : CF13BinaryContentRemoval := by
  intro H hH
  obtain ⟨hc,hprim,hfactor,he⟩ := binary_content_removal H hH
  exact ⟨hc,hprim,hfactor,fun z => he z⟩
example : CF13AdmittedContentLevel := by
  intro H z g ℓ σ hg hσ he
  obtain ⟨hc,hprim,hfactor,hcdiv,h,hh,hval,heq,hhdiv⟩ := admitted_content_level H z g ℓ σ hg hσ he
  exact ⟨hc,hprim,hfactor,hcdiv,h,hh,hval,heq,hhdiv⟩
example : CF13ActualSourceResultantLevel := by
  intro X D A B hX hd hr
  obtain ⟨hR,hbound,h⟩ := actual_source_resultant_level X D A B hX hd hr
  exact ⟨hR,hbound,fun inverse n b d u v hs hb => h inverse n b d u v hs hb⟩
example : CF13RoundedClassResultantLevels := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_class_resultant_levels δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  exact h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz

-- Generic zero-polynomial content is zero; it cannot be an admitted nonzero level.
example : binaryContent 0=0 := by simp [binaryContent]
example : binaryPrimitivePart 0=0 := by simp [binaryPrimitivePart]
example (z : Fin 2 → ℤ) : MvPolynomial.eval z (0 : SourcePolynomial) ≠ 1 := by simp
-- The exponent-zero admitted level is valid and forces content/reduced level one.
example : binaryContent (1 : SourcePolynomial)=1 := by simp [binaryContent]
example (z : Fin 2 → ℤ) : ∃ h : ℤ, h ≠ 0 ∧
    MvPolynomial.eval z (binaryPrimitivePart 1)=h ∧ h.natAbs ∣ 1 := by
  obtain ⟨_,_,_,_,h,hh,hv,_,hd⟩ := admitted_content_level 1 z 2 0 1 (by decide) (Or.inl rfl) (by simp)
  exact ⟨h,hh,hv,by simpa using hd⟩

private theorem source_eight : PairSource 8 2 1 1 3 := by
  norm_num [PairSource]
  exact Nat.prime_two.squarefree

-- Constant inverse graph r=0 has a real source; it remains a ruling.
example : graphDegree (Polynomial.C 2) 1=0 := by simp [graphDegree]
example : signedGraphRecovery true (Polynomial.C 2) 1 2 1 1 3 := by
  apply inverse_source_recovery _ _ 8 _ _ _ _ source_eight
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial]

private abbrev recoveryA : Polynomial ℤ := Polynomial.C 2*(Polynomial.X-Polynomial.C 1)
private abbrev recoveryB : Polynomial ℤ := Polynomial.C 2*(Polynomial.X-Polynomial.C 2)
private theorem recoveryA_degree : recoveryA.natDegree=1 := by
  rw [Polynomial.natDegree_mul (by norm_num) (Polynomial.X_sub_C_ne_zero (1:ℤ))]
  rw [Polynomial.natDegree_C,Polynomial.natDegree_X_sub_C]
private theorem recoveryB_degree : recoveryB.natDegree=1 := by
  rw [Polynomial.natDegree_mul (by norm_num) (Polynomial.X_sub_C_ne_zero (2:ℤ))]
  rw [Polynomial.natDegree_C,Polynomial.natDegree_X_sub_C]
private theorem recovery_degree : graphDegree recoveryA recoveryB=1 := by
  simp [graphDegree,recoveryA_degree,recoveryB_degree]

private theorem recovery_A_form : recoveryA.homogenize (graphDegree recoveryA recoveryB)=
    MvPolynomial.C (2:ℤ)*(MvPolynomial.X 0-MvPolynomial.X 1) := by
  rw [recovery_degree]
  unfold recoveryA
  rw [Polynomial.homogenize_C_mul,Polynomial.homogenize_sub,
    Polynomial.homogenize_X (by decide),Polynomial.homogenize_C]
  simp
private theorem recovery_B_form : recoveryB.homogenize (graphDegree recoveryA recoveryB)=
    MvPolynomial.C (2:ℤ)*(MvPolynomial.X 0-MvPolynomial.C 2*MvPolynomial.X 1) := by
  rw [recovery_degree]
  unfold recoveryB
  rw [Polynomial.homogenize_C_mul,Polynomial.homogenize_sub,
    Polynomial.homogenize_X (by decide),Polynomial.homogenize_C]
  simp

private theorem recovery_branch : sourceGraphBranch true recoveryA recoveryB 2 1 1 3 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial,recoveryA,recoveryB]
example : signedGraphRecovery true recoveryA recoveryB 2 1 1 3 :=
  inverse_source_recovery recoveryA recoveryB 8 2 1 1 3 source_eight recovery_branch

private theorem recovery_resultant : fullGraphResultant recoveryA recoveryB = -4 := by
  unfold fullGraphResultant
  rw [recovery_degree]
  unfold Polynomial.resultant
  rw [Matrix.det_fin_two]
  norm_num [Polynomial.sylvester,Fin.addCases,recoveryA,recoveryB,Polynomial.coeff_one]

private theorem recovery_value : MvPolynomial.eval (![3,1] : Fin 2 → ℤ)
    (graphPullback true recoveryA recoveryB)=8 := by
  simp only [graphPullback,ite_true,recovery_A_form,recovery_B_form]
  norm_num
private theorem recovery_gcd : sourceGraphGCD true recoveryA recoveryB 2 1 1 3=2 := by
  unfold sourceGraphGCD homogeneousGraphValue
  simp only [graphParameter,ite_true,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,recovery_A_form,recovery_B_form]
  norm_num

private theorem recovery_scalar : ∃ Q : SourcePolynomial,
    graphPullback true recoveryA recoveryB=MvPolynomial.C (8:ℤ)*Q := by
  refine ⟨MvPolynomial.X 0^2*(MvPolynomial.X 0-MvPolynomial.C 2*MvPolynomial.X 1)^3-
    MvPolynomial.X 1^2*(MvPolynomial.X 0-MvPolynomial.X 1)^3,?_⟩
  simp only [graphPullback,ite_true,recovery_A_form,recovery_B_form]
  norm_num
  ring

-- Derive exact content 8 from its common coefficient factor and its admitted
-- value 8. This avoids assuming the rejected content-divides-resultant claim.
private theorem recovery_content : binaryContent (graphPullback true recoveryA recoveryB)=8 := by
  classical
  obtain ⟨_,_,_,hcdiv,h,hh,hval,heq,hdiv⟩ := admitted_content_level
    (graphPullback true recoveryA recoveryB) ![3,1] 2 3 1 (by decide) (Or.inl rfl) (by simpa using recovery_value)
  have hc8 : binaryContent (graphPullback true recoveryA recoveryB) ∣ 8 := by simpa using hcdiv
  have h8c : 8 ∣ binaryContent (graphPullback true recoveryA recoveryB) := by
    obtain ⟨Q,hQ⟩ := recovery_scalar
    apply Finset.dvd_gcd
    intro e he
    apply Int.natCast_dvd.mp
    refine ⟨Q.coeff e,?_⟩
    simpa only [MvPolynomial.coeff_C_mul,Nat.cast_ofNat] using congrArg (fun P : SourcePolynomial => P.coeff e) hQ
  exact Nat.dvd_antisymm hc8 h8c

example : (fullGraphResultant recoveryA recoveryB).natAbs=4 ∧
    sourceGraphGCD true recoveryA recoveryB 2 1 1 3=2 ∧
    binaryContent (graphPullback true recoveryA recoveryB)=8 := by
  exact ⟨by rw [recovery_resultant]; decide,recovery_gcd,recovery_content⟩
example : ¬ binaryContent (graphPullback true recoveryA recoveryB) ∣
    (fullGraphResultant recoveryA recoveryB).natAbs := by
  rw [recovery_content,recovery_resultant]
  norm_num
example : MvPolynomial.eval (![3,1] : Fin 2 → ℤ)
    (binaryPrimitivePart (graphPullback true recoveryA recoveryB))=1 := by
  obtain ⟨_,_,_,_,h,hh,hval,heq,_⟩ := admitted_content_level
    (graphPullback true recoveryA recoveryB) ![3,1] 2 3 1 (by decide) (Or.inl rfl) (by simpa using recovery_value)
  rw [recovery_content] at heq
  norm_num at heq
  rw [hval]
  linarith

private theorem negated_pullback : graphPullback true (-recoveryA) (-recoveryB)=
    -graphPullback true recoveryA recoveryB := by
  simp only [graphPullback,graphDegree,Polynomial.natDegree_neg,ite_true,Polynomial.homogenize_neg]
  ring
private theorem content_neg (H : SourcePolynomial) : binaryContent (-H)=binaryContent H := by
  simp [binaryContent]
example : MvPolynomial.eval (![3,1] : Fin 2 → ℤ)
    (binaryPrimitivePart (graphPullback true (-recoveryA) (-recoveryB))) = -1 := by
  have hv : MvPolynomial.eval (![3,1] : Fin 2 → ℤ)
      (graphPullback true (-recoveryA) (-recoveryB))=(-1:ℤ)*(2:ℤ)^3 := by
    rw [negated_pullback,map_neg,recovery_value]
    norm_num
  obtain ⟨_,_,_,_,h,hh,hval,heq,_⟩ := admitted_content_level
    (graphPullback true (-recoveryA) (-recoveryB)) ![3,1] 2 3 (-1) (by decide) (Or.inr rfl) hv
  rw [negated_pullback,content_neg,recovery_content] at heq
  norm_num at heq
  rw [hval]
  linarith

end
end P0365Subquarter
