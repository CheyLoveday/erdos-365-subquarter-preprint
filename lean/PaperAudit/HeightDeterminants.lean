import PaperProofs.HeightDeterminants

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04RectangularScaleProducts
#print CF04ActualHeightDeterminant
#check (rectangular_scale_products : CF04RectangularScaleProducts)
#check (actual_height_determinant : CF04ActualHeightDeterminant)
#print axioms rectangular_scale_products
#print axioms actual_height_determinant
set_option pp.all false

example : CF04RectangularScaleProducts := by
  intro A C
  exact rectangular_scale_products A C
example : CF04ActualHeightDeterminant := by
  intro A C
  exact actual_height_determinant A C

-- Degree zero retains the full constant-before-scales quantifier order.
example : ∃ K : ℝ, 1≤K ∧ ∀ B E U V t : ℝ,
    0<B → 0<E → 0<U → 0<V → 0<t → t≤2*(B/E) →
    V/U=(B/E)^(3/2:ℝ) → ∀ d u : RectangularIndex 0 0 → ℕ,
      (∀ i, 0<d i ∧ 0<u i ∧ (d i:ℝ)≤E ∧ (u i:ℝ)≤U) →
        (∏ i, rectangularRowScale 0 0 (d i) (u i))*
          (∏ j : RectangularIndex 0 0, rectangularColumnScale t j)≤
            K*Real.exp (rectangularHeightExponent 0 0 B E U V) :=
  rectangular_scale_products 0 0

-- Actual8/9, unit d=u=1, every degree including zero, upper closed endpoint.
example (A C : ℕ) : ∃ K : ℝ, 1≤K ∧
    |((rectangularSourceMatrix A C (fun _ => 2) (fun _ => 1)
      (fun _ => 1) (fun _ => 3)).det:ℝ)|≤K*Real.exp
        (rectangularHeightExponent A C 8 4
          (4*reussMultiplierScale 8 2) (4*reussMultiplierScale 8 1)-
          latticeDeterminantLower (Fintype.card (RectangularIndex A C))
            (Real.log 2) (Real.log 8)) := by
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  obtain ⟨K,hK,hbound⟩ := actual_height_determinant A C
  refine ⟨K,hK,?_⟩
  simpa only [show (4:ℝ)*2=8 by norm_num,mul_one] using
    hbound 8 2 2 1 (4/3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => 1) (fun _ => 3)
    (fun _ => hs) (fun _ => by norm_num [actualRealBox])
    (fun _ => by norm_num [actualDirectInterval])

end
end P0365Subquarter
