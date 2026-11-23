import PaperTargets.DividedMinors

/-! CF04 endpoint adapter proposal. This supplies no coarse polynomial on an
open interval; it extends a supplied actual-source half-open relation. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- One bounded linear relation covers all original sources on a fixed real
kernel-ratio endpoint. If no source meets it, the constant one is permitted. -/
def CF04ActualEndpointRelation : Prop :=
  ∀ X : ℝ, 32≤X → ∀ a : ℝ, ∃ L : SourcePolynomial,
    L≠0 ∧ L.totalDegree≤1 ∧ (∀ e, |(L.coeff e:ℝ)|≤3*X) ∧
    ∀ n b d u v : ℕ, PairSource n b d u v → (n:ℝ)≤2*X →
      (b:ℝ)/d=a → polynomialValue L (sourcePoint b d u v)=0

/-- A nonzero polynomial vanishing on all actual half-open interval sources
extends to the closed original interval at degree cost one and one height
power. The uniform height constant precedes scales, intervals and polynomials. -/
def CF04ClosedIntervalRelation : Prop :=
  ∀ D : ℕ, ∀ H C : ℝ, 0≤H → 0≤C → ∃ C' : ℝ, 0<C' ∧
    ∀ X : ℝ, 32≤X → ∀ a M : ℝ, 0<a → 1≤M →
    ∀ F : SourcePolynomial, F≠0 → F.totalDegree≤D →
      (∀ e, |(F.coeff e:ℝ)|≤C*X^H) →
      (∀ n b d u v : ℕ, PairSource n b d u v → (n:ℝ)≤2*X →
        a<(b:ℝ)/d → (b:ℝ)/d≤a*(1+1/M) →
          polynomialValue F (sourcePoint b d u v)=0) →
      ∃ G : SourcePolynomial, G≠0 ∧ G.totalDegree≤D+1 ∧
        (∀ e, |(G.coeff e:ℝ)|≤C'*X^(H+1)) ∧
        ∀ n b d u v : ℕ, PairSource n b d u v → (n:ℝ)≤2*X →
          actualDirectInterval a M b d →
            polynomialValue G (sourcePoint b d u v)=0

end
end P0365Subquarter
