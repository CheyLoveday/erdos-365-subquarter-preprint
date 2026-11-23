import PaperProofs.GraphRulings

namespace P0365Subquarter
set_option pp.all true
#print rationalPolynomial
#print integerPolynomialValue
#print graphSection
#print rulingRoots
#print boundedGraphData
#print graphRulingCase
#print CF13RelationSections
#print CF13PrimitiveGCDRemoval
#print CF13IntegerFactorHeight
#print CF13GraphRulingDispatch
#print CF13ActualGraphRulingDecomposition
#print CF13RoundedClassGraphRulings
#check (relation_sections : CF13RelationSections)
#check (primitive_gcd_removal : CF13PrimitiveGCDRemoval)
#check (integer_factor_height : CF13IntegerFactorHeight)
#check (graph_ruling_dispatch : CF13GraphRulingDispatch)
#check (actual_graph_ruling_decomposition : CF13ActualGraphRulingDecomposition)
#check (rounded_class_graph_rulings : CF13RoundedClassGraphRulings)
#print axioms relation_sections
#print axioms primitive_gcd_removal
#print axioms integer_factor_height
#print axioms graph_ruling_dispatch
#print axioms actual_graph_ruling_decomposition
#print axioms rounded_class_graph_rulings
set_option pp.all false

-- Complete applications of all six pre-proof reviewed targets.
example : CF13RelationSections := by
  intro inverse X G hG
  obtain ⟨hne,hp,hq,hc,he⟩ := relation_sections inverse X G hG
  exact ⟨hne,hp,hq,hc,fun z => he z⟩
example : CF13PrimitiveGCDRemoval := by
  intro P Q hne
  obtain ⟨D,A,B,hD,hprim,hP,hQ,hcop,hdegD,hdegA,hdegB⟩ := primitive_gcd_removal P Q hne
  exact ⟨D,A,B,hD,hprim,hP,hQ,hcop,hdegD,hdegA,hdegB⟩
example : CF13IntegerFactorHeight := by
  intro d H hH P hP hdeg hc A hdiv k
  exact integer_factor_height d H hH P hP hdeg hc A hdiv k
example : CF13GraphRulingDispatch := by
  intro P Q D A B hD hP hQ hcop hdeg
  obtain ⟨hc,he,hzero,hconstant⟩ := graph_ruling_dispatch P Q D A B hD hP hQ hcop hdeg
  exact ⟨hc,fun s t ht => he s t ht,hzero,hconstant⟩
example : CF13ActualGraphRulingDecomposition := by
  intro inverse X G hX hG
  obtain ⟨D,A,B,hd,hc,h⟩ := actual_graph_ruling_decomposition inverse X G hX hG
  exact ⟨D,A,B,hd,hc,fun n b d u v hs hz => h n b d u v hs hz⟩
example : CF13RoundedClassGraphRulings := by
  intro δ hδ hδ1
  obtain ⟨X₀,hX₀,h⟩ := rounded_class_graph_rulings δ hδ hδ1
  refine ⟨X₀,hX₀,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  exact h X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz

-- Scalar contents do not require Bezout coprimality over Z[X].
example : IsCoprime (rationalPolynomial (Polynomial.C 2)) (rationalPolynomial (Polynomial.C 2)) := by
  refine ⟨Polynomial.C (1/2 : ℚ),0,?_⟩
  simp only [rationalPolynomial,Polynomial.map_C,Int.coe_castRingHom]
  change Polynomial.C (1/2 : ℚ)*Polynomial.C 2+0*Polynomial.C 2=1
  rw [zero_mul,add_zero,← Polynomial.C_mul]
  norm_num
example : ¬ IsCoprime (Polynomial.C 2 : Polynomial ℤ) (Polynomial.C 2) := by
  rintro ⟨u,v,h⟩
  have hh := congrArg (fun Z : Polynomial ℤ => Z.coeff 0) h
  simp only [Polynomial.coeff_add,Polynomial.coeff_mul_C,Polynomial.coeff_one_zero] at hh
  omega

-- A zero section is allowed; the graph numerator must then be zero.
example : ∃ D A B : Polynomial ℤ, D ≠ 0 ∧ D.IsPrimitive ∧ A = 0 ∧
    (Polynomial.X : Polynomial ℤ) = D*B ∧ IsCoprime (rationalPolynomial A) (rationalPolynomial B) := by
  obtain ⟨D,A,B,hD,hprim,hP,hQ,hcop,hdegD,hdegA,hdegB⟩ :=
    primitive_gcd_removal 0 Polynomial.X (Or.inr Polynomial.X_ne_zero)
  have ha : A = 0 := neg_eq_zero.mp ((mul_eq_zero.mp hP.symm).resolve_left hD)
  exact ⟨D,A,B,hD,hprim,ha,hQ,hcop⟩

-- Zero numerator/denominator graphs cannot discard their common-factor rulings.
example (P Q D A B : Polynomial ℤ) (hD : D ≠ 0) (hP : P = D*(-A))
    (hQ : Q = D*B) (hcop : IsCoprime (rationalPolynomial A) (rationalPolynomial B))
    (hdeg : D.natDegree ≤ 3) (hz : A = 0 ∨ B = 0) (s t : ℚ) (ht : t ≠ 0)
    (he : integerPolynomialValue P s+t*integerPolynomialValue Q s = 0) :
    s ∈ rulingRoots D :=
  (graph_ruling_dispatch P Q D A B hD hP hQ hcop hdeg).2.2.1 hz s t ht he

-- Repeated cubic roots count once, and the full cubic ruling is retained.
example : (2:ℚ) ∈ rulingRoots ((Polynomial.X-Polynomial.C 2)^3 : Polynomial ℤ) := by
  have h0 : (Polynomial.X-2 : Polynomial ℚ) ≠ 0 := Polynomial.X_sub_C_ne_zero 2
  simp [rulingRoots,rationalPolynomial,Polynomial.IsRoot,h0]

-- The actual 8/9 source belongs to the constant graph t=3 and the ruling s=2.
example : graphRulingCase false 1 (Polynomial.C 3) 1 (sourcePoint 2 1 1 3) := by
  right
  norm_num [graphRulingCase,sourcePoint,integerPolynomialValue,rationalPolynomial]
example : graphRulingCase false (Polynomial.X-Polynomial.C 2) 0 1 (sourcePoint 2 1 1 3) := by
  left
  have h0 : (Polynomial.X-2 : Polynomial ℚ) ≠ 0 := Polynomial.X_sub_C_ne_zero 2
  simp [sourcePoint,rulingRoots,rationalPolynomial,Polynomial.IsRoot,h0]

-- Actual cubic factor coefficient bound with the explicit constant 32.
example (P A : Polynomial ℤ) (hP : P ≠ 0) (hd : P.natDegree ≤ 3)
    (hc : ∀ k, |(P.coeff k : ℝ)| ≤ 1) (ha : A ∣ P) (k : ℕ) :
    |(A.coeff k : ℝ)| ≤ 32 := by
  convert integer_factor_height 3 1 (by norm_num) P hP hd hc A ha k using 1 <;> norm_num

end P0365Subquarter
