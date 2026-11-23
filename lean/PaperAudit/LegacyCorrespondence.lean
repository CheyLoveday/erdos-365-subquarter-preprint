import PaperProofs.LegacyCorrespondence

namespace P0365Subquarter

set_option pp.all true

#print P365Bound.IsPrime
#print P365Bound.Powerful
#print P365Bound.PairSource
#print P365Bound.pairCount
#print CF01LegacyPrimeCorrespondence
#print CF01LegacyPowerfulCorrespondence
#print CF01LegacySourceCorrespondence
#print CF01LegacyCountCorrespondence

#check (legacy_prime_correspondence : CF01LegacyPrimeCorrespondence)
#check (legacy_powerful_correspondence : CF01LegacyPowerfulCorrespondence)
#check (legacy_source_correspondence : CF01LegacySourceCorrespondence)
#check (legacy_count_correspondence : CF01LegacyCountCorrespondence)
#check (legacy_count_correspondence : ∀ N : ℕ, P365Bound.pairCount N = PairCount N)

#print axioms legacy_prime_correspondence
#print axioms legacy_powerful_correspondence
#print axioms legacy_source_correspondence
#print axioms legacy_count_correspondence

-- Ordinary kernel-checked controls for the source-complete legacy population.
example : ¬ P365Bound.Powerful 0 := by
  intro h
  exact zero_not_powerful ((legacy_powerful_correspondence 0).mp h)

example : P365Bound.Powerful 1 :=
  (legacy_powerful_correspondence 1).mpr one_powerful

example : P365Bound.pairCount 0 = 0 := by
  rw [legacy_count_correspondence 0]
  exact count_empty_boundary.1

example : P365Bound.pairCount 1 = 0 := by
  rw [legacy_count_correspondence 1]
  exact count_empty_boundary.2

example : P365Bound.PairSource 12167 23 2 1 39 := by
  apply (legacy_source_correspondence 12167 23 2 1 39).mpr
  rcases endpoint_overlap_controls with ⟨_, _, _, _, _, _, _, _, _, _, h⟩
  exact h

end P0365Subquarter
