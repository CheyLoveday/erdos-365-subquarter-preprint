import PaperTargets.PrimeAssignment

/-! CF08 application adapter to the actual CF11/CF15 shell. The selected prime
scale stays at X while canonical sources may have n<=2X. Rounded scale
monotonicity across a ceiling jump is not a hypothesis. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- One profile-uniform list for every actual source up to the shell upper
cutoff2X, at the original roundedScale X. Coefficient/degree hypotheses remain
actual polynomial hypotheses to be produced by the coarse-factor route. -/
def CF08RoundedShellSourceAssignment : Prop :=
  ∀ (D : ℕ) (H C δ : ℝ), 0≤H → 0≤C → 0<δ →
    ∃ (L : ℕ) (X₀ : ℝ), 0<L ∧ 1<X₀ ∧ ∀ X : ℝ, X₀≤X →
      ∀ ψ : ℝ, 0≤ψ → ψ≤2/3 →
      ∃ s : Finset ℕ, s.card=L ∧
        (∀ p ∈ s, Nat.Prime p ∧ roundedScale X ψ δ≤(p:ℝ) ∧
          (p:ℝ)≤2^(L+1)*roundedScale X ψ δ) ∧
        (∀ F : SourcePolynomial, F.totalDegree≤D →
          (∀ e, |(F.coeff e:ℝ)|≤C*X^H) →
          ∀ n b d u v : ℕ, PairSource n b d u v → (n:ℝ)≤2*X →
            nonsingularSource F b d u v →
            firstGoodPrime F b d u v s∈s ∧
            goodSourcePrime F b d u v (firstGoodPrime F b d u v s) ∧
            sourceReduction b d u v (firstGoodPrime F b d u v s)∈
              smoothResidues F (firstGoodPrime F b d u v s)) ∧
        (∀ F : SourcePolynomial, F.totalDegree≤D →
          (∑ p ∈ s, ((smoothResidues F p).card:ℝ))≤
            (L:ℝ)*D*2^(L+1)*roundedScale X ψ δ)

end
end P0365Subquarter
