import PaperProofs.RealSources

namespace P0365Subquarter
set_option pp.all true
#print realSourceCoordinate
#print realSourcePartner
#print realChartExponent
#print realSourceError
#print realNormalizedError
#print realNormalizedRow
#print realColumnScale
#print CF11ActualRelativeErrors
#print CF11ActualNormalizedError
#print CF11ActualRowNormalization
#print CF11ActualMinorNormalization
#print CF11RealScaleCancellation
#print CF11RoundedMinorVanishing
#check (actual_relative_errors : CF11ActualRelativeErrors)
#check (actual_normalized_error : CF11ActualNormalizedError)
#check (actual_row_normalization : CF11ActualRowNormalization)
#check (actual_minor_normalization : CF11ActualMinorNormalization)
#check (real_scale_cancellation : CF11RealScaleCancellation)
#check (rounded_minor_vanishing : CF11RoundedMinorVanishing)
#print axioms actual_relative_errors
#print axioms actual_normalized_error
#print axioms actual_row_normalization
#print axioms actual_minor_normalization
#print axioms real_scale_cancellation
#print axioms rounded_minor_vanishing
set_option pp.all false

-- Typechecked applications at every frozen expected target, including the
-- explicit still-open analytic bound in the last target's antecedent.
example : CF11ActualRelativeErrors := by
  intro n b d u v h
  exact actual_relative_errors n b d u v h
example : CF11ActualNormalizedError := by
  intro n b d u v h inverse a X ha hX hXn hz1 hz2
  exact actual_normalized_error n b d u v h inverse a X ha hX hXn hz1 hz2
example : CF11ActualRowNormalization := by
  intro n b d u v h inverse a ha j
  exact actual_row_normalization n b d u v h inverse a ha j
example : CF11ActualMinorNormalization := by
  intro n b d u v h inverse a ha
  exact actual_minor_normalization n b d u v h inverse a ha
example : CF11RealScaleCancellation := by
  intro B E U X hB hE hX
  exact real_scale_cancellation B E U X hB hE hX
example : CF11RoundedMinorVanishing := by
  intro δ C hδ hC
  obtain ⟨X₀, hX₀, hg⟩ := rounded_minor_vanishing δ C hδ hC
  refine ⟨X₀, hX₀, ?_⟩
  intro X ψ hX hψ0 hψ2 F p n b d u v hp hscale hs hc hgood hres inverse hbound
  exact hg X ψ hX hψ0 hψ2 F p n b d u v hp hscale hs hc hgood hres inverse hbound

-- Both actual chart shapes preserve the order of the four base and four
-- perturbed monomials. No derivative of the source error is required.
example (inverse : Bool) (z β : ℝ) : realNormalizedRow inverse z β =
    ![1, z, z^2, z^3, z^realChartExponent inverse + β,
      z*(z^realChartExponent inverse + β), z^2*(z^realChartExponent inverse + β),
      z^3*(z^realChartExponent inverse + β)] := by
  ext j; fin_cases j <;> norm_num [realNormalizedRow]

private theorem source_eight : PairSource 8 2 1 1 3 := by
  norm_num [PairSource]
  exact Nat.prime_two.squarefree

-- Genuine 8/9 source, kernel one and multiplier one, in either chart.
example (inverse : Bool) :
    |realNormalizedError inverse (realSourceCoordinate inverse 2 1 1 3) 2 1 1 3| ≤ 4 / 8 := by
  apply actual_normalized_error 8 2 1 1 3 source_eight inverse
  · cases inverse <;> norm_num [realSourceCoordinate]
  · norm_num
  · norm_num
  · cases inverse <;> norm_num [realSourceCoordinate]
  · cases inverse <;> norm_num [realSourceCoordinate]

example : 0 ≤ realSourceError false 2 1 1 3 ∧ realSourceError true 2 1 1 3 ≤ 0 :=
  ⟨(actual_relative_errors 8 2 1 1 3 source_eight).1.1,
    (actual_relative_errors 8 2 1 1 3 source_eight).2.2⟩

-- Exact integer-row identities at that source; fractional powers are over ℝ.
example (inverse : Bool) (j : Fin 8) :
    (sourceIntegerRow inverse 2 1 1 3 j : ℝ) =
      (sourceRowDenominator inverse 1 1 : ℝ) * realColumnScale inverse 1 j *
        realNormalizedRow inverse (realSourceCoordinate inverse 2 1 1 3 / 1)
          (realNormalizedError inverse 1 2 1 1 3) j :=
  actual_row_normalization 8 2 1 1 3 source_eight inverse 1 (by norm_num) j

-- Extreme nominal skew is not excluded by either exact cancellation.
example : (1024^3 * (1:ℝ))^8 * (1/1024)^18 = (1*1024)^6 ∧
    (1024 * (1:ℝ)^3)^8 * (1/1024)^22 = 1/(1*1024)^14 := by
  simpa using real_scale_cancellation 1 1024 1 1 (by norm_num) (by norm_num) (by norm_num)

end P0365Subquarter
