import PaperProofs.EndpointRelations

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04ActualEndpointRelation
#print CF04ClosedIntervalRelation
#check (actual_endpoint_relation : CF04ActualEndpointRelation)
#check (closed_interval_relation : CF04ClosedIntervalRelation)
#print axioms actual_endpoint_relation
#print axioms closed_interval_relation
set_option pp.all false

example : CF04ActualEndpointRelation := by
  intro X hX a
  exact actual_endpoint_relation X hX a
example : CF04ClosedIntervalRelation := by
  intro D H C hH hC
  obtain ⟨K,hK,hbound⟩ := closed_interval_relation D H C hH hC
  refine ⟨K,hK,?_⟩
  intro X hX a M ha hM F hFnz hD hcoeff hzero
  exact hbound X hX a M ha hM F hFnz hD hcoeff hzero

-- A nonempty actual endpoint with denominator kernel one: 8 and 9.
example : ∃ L : SourcePolynomial, L≠0 ∧ L.totalDegree≤1 ∧
    polynomialValue L (sourcePoint 2 1 1 3)=0 := by
  obtain ⟨L,hL,hD,_,hzero⟩ := actual_endpoint_relation 32 (by norm_num) 2
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  exact ⟨L,hL,hD,hzero 8 2 1 1 3 hs (by norm_num) (by norm_num)⟩

-- Nonpositive endpoints cannot be attained by positive canonical kernels.
example (a : ℝ) (ha : a≤0) (n b d u v : ℕ) (hs : PairSource n b d u v) :
    (b:ℝ)/d≠a := by
  have hb : (0:ℝ)<b := by exact_mod_cast hs.1
  have hd : (0:ℝ)<d := by exact_mod_cast hs.2.1
  exact ne_of_gt (lt_of_le_of_lt ha (div_pos hb hd))

end
end P0365Subquarter
