import PaperProofs.ClassCounts

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print CF15ConstantGraphRuling
#print CF15BoundedGraphRulingClassSubpower
#print CF15RoundedClassSourceSubpower
#check (constant_graph_ruling : CF15ConstantGraphRuling)
#check (bounded_graph_ruling_class_subpower : CF15BoundedGraphRulingClassSubpower)
#check (rounded_class_source_subpower : CF15RoundedClassSourceSubpower)
#print axioms constant_graph_ruling
#print axioms bounded_graph_ruling_class_subpower
#print axioms rounded_class_source_subpower
set_option pp.all false

example : CF15ConstantGraphRuling := by
  intro inverse A B hr b d u v hbranch
  exact constant_graph_ruling inverse A B hr b d u v hbranch
example : CF15BoundedGraphRulingClassSubpower := by
  intro hThue ε hε
  exact bounded_graph_ruling_class_subpower hThue ε hε
example : CF15RoundedClassSourceSubpower := by
  intro hThue δ hδ hδ1 ε hε
  exact rounded_class_source_subpower hThue δ hδ hδ1 ε hε

-- Genuine 8/9 coordinates appear in either constant-graph chart.
example : sourceGraphBranch false (Polynomial.C 3) (Polynomial.C 1) 2 1 1 3 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial]
example : sourceGraphBranch true (Polynomial.C 2) (Polynomial.C 1) 2 1 1 3 := by
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial]
example : sourcePoint 2 1 1 3 (if false then 0 else 1)=
    integerPolynomialValue (Polynomial.C 3) 0/integerPolynomialValue (Polynomial.C 1) 0 := by
  apply constant_graph_ruling false (Polynomial.C 3) (Polynomial.C 1) (by simp [graphDegree])
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial]
example : sourcePoint 2 1 1 3 (if true then 0 else 1)=
    integerPolynomialValue (Polynomial.C 2) 0/integerPolynomialValue (Polynomial.C 1) 0 := by
  apply constant_graph_ruling true (Polynomial.C 2) (Polynomial.C 1) (by simp [graphDegree])
  norm_num [sourceGraphBranch,sourcePoint,integerPolynomialValue,rationalPolynomial]
-- Zero numerator or denominator admits no graph branch; D=0 is excluded.
example (inverse : Bool) (B : Polynomial ℤ) (b d u v : ℕ) :
    ¬sourceGraphBranch inverse 0 B b d u v := by
  simp [sourceGraphBranch,integerPolynomialValue,rationalPolynomial]
example (inverse : Bool) (A : Polynomial ℤ) (b d u v : ℕ) :
    ¬sourceGraphBranch inverse A 0 b d u v := by
  simp [sourceGraphBranch,integerPolynomialValue,rationalPolynomial]
example (X : ℝ) (A B : Polynomial ℤ) : ¬boundedGraphData X 0 A B := by
  intro h
  exact h.1 rfl
-- At most three ruling fibers and the constant-or-mixed graph share one budget.
example (Cr Cm x : ℝ) : 3*Cr*x+(Cr+Cm)*x=(4*Cr+Cm)*x := by ring
example (C X ε : ℝ) (hC : 0≤C) (hX : 0≤X) :
    ((∅:Finset ℕ).card:ℝ)≤C*X^ε := by simp; positivity

end
end P0365Subquarter
