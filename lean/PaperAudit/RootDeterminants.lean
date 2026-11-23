import PaperProofs.RootDeterminants

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04RectangularRootDeterminant
#print CF04ActualRectangularDeterminant
#check (rectangular_root_determinant : CF04RectangularRootDeterminant)
#check (actual_rectangular_determinant : CF04ActualRectangularDeterminant)
#print axioms rectangular_root_determinant
#print axioms actual_rectangular_determinant
set_option pp.all false

example : CF04RectangularRootDeterminant := by
  intro A C
  exact rectangular_root_determinant A C
example : CF04ActualRectangularDeterminant := by
  intro A C
  exact actual_rectangular_determinant A C

-- Degree zero retains a genuine uniform constant before weights and nodes.
example : ∃ K : ℝ, 1≤K ∧ ∀ a b : ℝ, 0<a → a≤b →
    ∀ α β : RectangularIndex 0 0 → ℝ,
      (∀ i, |α i|≤3*Real.exp (-a)) → (∀ i, |β i|≤8*Real.exp (-b)) →
        |(rectangularRootMatrix 0 0 α β).det|≤K*Real.exp
          (-latticeDeterminantLower (Fintype.card (RectangularIndex 0 0)) a b) :=
  rectangular_root_determinant 0 0

-- Actual8/9, unit d=u=1, high degrees, and the upper closed endpoint.
-- t=4/3,M=2 gives t*(1+1/M)=b/d=2, with strictly positive log weights.
example : ∃ K : ℝ, 1≤K ∧
    |((rectangularSourceMatrix 8 9 (fun _ => 2) (fun _ => 1)
      (fun _ => 1) (fun _ => 3)).det:ℝ)|≤
      (∏ _i : RectangularIndex 8 9, rectangularRowScale 8 9 1 1)*
      (∏ j : RectangularIndex 8 9, rectangularColumnScale (4/3) j)*K*
      Real.exp (-latticeDeterminantLower (Fintype.card (RectangularIndex 8 9))
        (Real.log 2) (Real.log 8)) := by
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  obtain ⟨K,hK,hbound⟩ := actual_rectangular_determinant 8 9
  refine ⟨K,hK,?_⟩
  exact hbound 8 2 (4/3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => 1) (fun _ => 3)
    (fun _ => hs) (fun _ => by norm_num) (fun _ => by norm_num [actualDirectInterval])

end
end P0365Subquarter
