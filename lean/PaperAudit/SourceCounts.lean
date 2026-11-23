import PaperProofs.SourceCounts

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print CF15FixedContentLevelBound
#print CF15FixedContentDivisorCount
#print CF15ActualGraphParameterCount
#print CF15GraphParameterInjection
#print CF15ActualGraphSourceCount
#print CF15ActualGraphSourceSubpower
#check (fixed_content_level_bound : CF15FixedContentLevelBound)
#check (fixed_content_divisor_count : CF15FixedContentDivisorCount)
#check (actual_graph_parameter_count : CF15ActualGraphParameterCount)
#check (graph_parameter_injection : CF15GraphParameterInjection)
#check (actual_graph_source_count : CF15ActualGraphSourceCount)
#check (actual_graph_source_subpower : CF15ActualGraphSourceSubpower)
#print axioms fixed_content_level_bound
#print axioms fixed_content_divisor_count
#print axioms actual_graph_parameter_count
#print axioms graph_parameter_injection
#print axioms actual_graph_source_count
#print axioms actual_graph_source_subpower
set_option pp.all false

example : CF15FixedContentLevelBound := by
  intro hThue Q c R g ell σ hd hc hR hg hell hσ S hS
  exact fixed_content_level_bound hThue Q c R g ell σ hd hc hR hg hell hσ S hS
example : CF15FixedContentDivisorCount := by
  intro hThue Q c R ell hd hc hR hell S hS
  exact fixed_content_divisor_count hThue Q c R ell hd hc hR hell S hS
example : CF15ActualGraphParameterCount := by
  intro hThue X D A B hX hg hr inverse S hS
  exact actual_graph_parameter_count hThue X D A B hX hg hr inverse S hS
example : CF15GraphParameterInjection := by
  intro inverse A B n m b d u v b' d' u' v' hs hs' hbr hbr' hp
  exact graph_parameter_injection inverse A B n m b d u v b' d' u' v' hs hs' hbr hbr' hp
example : CF15ActualGraphSourceCount := by
  intro hThue X D A B hX hg hr inverse S hS
  exact actual_graph_source_count hThue X D A B hX hg hr inverse S hS
example : CF15ActualGraphSourceSubpower := by
  intro hThue ε hε
  exact actual_graph_source_subpower hThue ε hε

-- Content need not divide R: the genuine8/9 arithmetic has c8,R4,g2,ell3.
example : ¬ (8:ℕ)∣4 := by decide
example : (8:ℤ)*1=1*(2:ℤ)^3 ∧ (8:ℤ)*(-1)=(-1)*(2:ℤ)^3 := by norm_num
-- Fixed nonzero content cannot hide extra reduced levels.
example (h k : ℤ) (he : (8:ℤ)*h=8*k) : h=k := by omega
example (h : ℤ) : ¬ (2:ℤ)*h=1 := by omega
-- At R1 and ell0, both signs remain and there is no prime/divisor loss.
example (hThue : StewartPrimitiveThue) (Q : SourcePolynomial) (c : ℕ)
    (hd : binaryFactorDispatch Q) (hc : 0<c) (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ ∃ (g : ℕ) (σ : ℤ),
      g∣1 ∧ (σ=1 ∨ σ= -1) ∧ (c:ℤ)*MvPolynomial.eval z Q=σ*(g:ℤ)^0) :
    S.card≤123232 := by
  simpa [divisorCount] using fixed_content_divisor_count hThue Q c 1 0 hd hc
    (by decide) (by decide) S hS
-- The nonzero resultant guard is essential to this divisor budget.
example : (1:ℕ)∣0 ∧ ¬ 1≤123232*(divisorCount 0)^8 := by simp [divisorCount]

end
end P0365Subquarter
