import PaperTargets.SourceCounts

/-! CF15 all coordinate rulings, including constant graphs. The primitive
cubic uses the authorized separable-form Thue input even when reducible. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def multiplierCubic (u v : ℕ) : Polynomial ℤ :=
  Polynomial.C ((v:ℤ)^2)-Polynomial.C ((u:ℤ)^2)*Polynomial.X^3

/-- No irreducibility is required: positive coprime multipliers give a primitive
separable full-degree cubic. Its homogeneous value is the actual source level. -/
def CF15MultiplierCubicAdmissibility : Prop :=
  ∀ u v : ℕ, 0<u → 0<v → Nat.Coprime v u →
    let f := multiplierCubic u v
    f.natDegree=3 ∧ f.IsPrimitive ∧ binaryContent (f.homogenize f.natDegree)=1 ∧
      (rationalPolynomial f).Separable ∧
      ∀ b d : ℕ, MvPolynomial.eval ![(b:ℤ),d] (f.homogenize f.natDegree)=
        (d:ℤ)^3*(v:ℤ)^2-(b:ℤ)^3*(u:ℤ)^2

/-- A positive primitive multiplier ratio fixes u,v. The precise Thue bound
at level1 counts the remaining primitive kernels; original starts inject. -/
def CF15FixedMultiplierRatioCount : Prop :=
  StewartPrimitiveThue → ∀ q : ℚ, ∀ S : Finset ℕ,
    (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ (v:ℚ)/u=q) →
    S.card≤8400

/-- A positive primitive kernel ratio fixes b,d and hence their product.
The proved CF02 recurrence estimate counts original starts up to N. -/
def CF15FixedKernelRatioCount : Prop :=
  ∀ (q : ℚ) (N : ℕ), ∀ S : Finset ℕ,
    (∀ n ∈ S, n≤N ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧ (b:ℚ)/d=q) →
    S.card≤Nat.log 2 (2*N+1)+1

/-- One common envelope for either coordinate ruling, independent of q. -/
def CF15CoordinateRulingCount : Prop :=
  StewartPrimitiveThue → ∀ (i : Fin 2) (q : ℚ) (N : ℕ), ∀ S : Finset ℕ,
    (∀ n ∈ S, n≤N ∧ ∃ b d u v : ℕ,
      PairSource n b d u v ∧ sourcePoint b d u v i=q) →
    S.card≤8401+Nat.log 2 (2*N+1)

/-- Pay the logarithmic ruling budget with one uniform epsilon loss at the
actual shell scale. This is proved from elementary logarithm/power estimates. -/
def CF15RulingLogSubpower : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ X : ℝ, 32≤X →
    ∀ N : ℕ, (N:ℝ)≤2*X → (8401+Nat.log 2 (2*N+1):ℝ)≤C*X^ε

/-- Actual finite source classes on any coordinate ruling, including those
arising from degree-zero graphs, have a uniform shell-scale subpower count. -/
def CF15CoordinateRulingSubpower : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ X : ℝ, 32≤X → ∀ (i : Fin 2) (q : ℚ), ∀ S : Finset ℕ,
      (∀ n ∈ S, (n:ℝ)≤2*X ∧ ∃ b d u v : ℕ,
        PairSource n b d u v ∧ sourcePoint b d u v i=q) →
      (S.card:ℝ)≤C*X^ε

end
end P0365Subquarter
