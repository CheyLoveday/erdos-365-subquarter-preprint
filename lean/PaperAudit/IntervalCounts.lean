import PaperProofs.IntervalCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF17IrreducibleIntervalSourceCount
#print CF17CoarseIntervalSourceCount
#check (irreducible_interval_source_count : CF17IrreducibleIntervalSourceCount)
#check (coarse_interval_source_count : CF17CoarseIntervalSourceCount)
#print axioms irreducible_interval_source_count
#print axioms coarse_interval_source_count
set_option pp.all false

example : CF17IrreducibleIntervalSourceCount := by
  intro hThue D H C δ hH hC hδ hδ1 ε hε
  exact irreducible_interval_source_count hThue D H C δ hH hC hδ hδ1 ε hε
example : CF17CoarseIntervalSourceCount := by
  intro hThue D H C δ hH hC hδ hδ1 ε hε
  exact coarse_interval_source_count hThue D H C δ hH hC hδ hδ1 ε hε

-- A zero polynomial would make every source singular; both target routes
-- exclude it through explicit nonzero or rational irreducibility hypotheses.
example (z : Fin 2 → ℚ) : singularRationalPoint 0 z := by
  simp [singularRationalPoint,polynomialValue]
example : ¬Irreducible (rationalSourcePolynomial 0) := by
  simp [rationalSourcePolynomial]

-- A vanishing value alone does not make a point singular.
example (F : SourcePolynomial) (z : Fin 2 → ℚ) (i : Fin 2)
    (h : polynomialValue (MvPolynomial.pderiv i F) z≠0) :
    ¬singularRationalPoint F z := by
  intro hs
  exact h (hs.2 i)

-- Nonunit constant content creates no original-source population.
example (S : Finset ℕ) (b d u v : ℕ → ℕ)
    (hzero : ∀ n ∈ S, polynomialValue (MvPolynomial.C (6:ℤ))
      (sourcePoint (b n) (d n) (u n) (v n))=0) : S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hh := hzero n hn
  norm_num [polynomialValue] at hh

end
end P0365Subquarter
