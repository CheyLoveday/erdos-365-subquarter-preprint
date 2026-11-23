import PaperProofs.WeightedMonomials

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04PositivePartRectangle
#print CF04FiniteWeightMoment
#print CF04OptimizedWeightMoment
#check (positive_part_rectangle : CF04PositivePartRectangle)
#check (finite_weight_moment : CF04FiniteWeightMoment)
#check (optimized_weight_moment : CF04OptimizedWeightMoment)
#print axioms positive_part_rectangle
#print axioms finite_weight_moment
#print axioms optimized_weight_moment
set_option pp.all false

example : CF04PositivePartRectangle := by
  intro a b T ha hb hT N M
  exact positive_part_rectangle a b T ha hb hT N M
example : CF04FiniteWeightMoment := by
  intro a b ha hb S T hT
  exact finite_weight_moment a b ha hb S T hT
example : CF04OptimizedWeightMoment := by
  intro a b ha hb S
  exact optimized_weight_moment a b ha hb S

-- Empty rectangles and T=0 retain their original quantifiers.
example (a b : ℝ) (ha : 0<a) (hb : 0<b) (M : ℕ) :
    (∑ i ∈ Finset.range 0, ∑ j ∈ Finset.range M,
      max 0 (0-a*(i:ℝ)-b*(j:ℝ)))≤(0+a+b)^3/(6*a*b) :=
  positive_part_rectangle a b 0 ha hb (by norm_num) 0 M

-- H=0 is included, rather than inferred from a positive-cardinality theorem.
example (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    let S : Finset (ℕ×ℕ) := ∅
    (2/3)*(S.card:ℝ)*Real.sqrt (2*a*b*(S.card:ℝ))-(S.card:ℝ)*(a+b)≤
      (∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ))) :=
  (optimized_weight_moment a b ha hb ∅).1

-- Two distinct exponent pairs may have equal numerical weight.
example (a : ℝ) (ha : 0<a) :
    let S : Finset (ℕ×ℕ) := {(1,0),(0,1)}
    S.card=2 ∧ a*1+a*0=a*0+a*1 ∧
      (2/3)*(S.card:ℝ)*Real.sqrt (2*a*a*(S.card:ℝ))-(S.card:ℝ)*(a+a)≤
        (∑ e ∈ S, (a*(e.1:ℝ)+a*(e.2:ℝ))) := by
  dsimp
  exact ⟨by decide,by ring,(optimized_weight_moment a a ha ha {(1,0),(0,1)}).1⟩

end
end P0365Subquarter
