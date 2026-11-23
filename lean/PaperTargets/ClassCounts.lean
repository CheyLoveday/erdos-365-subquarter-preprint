import PaperTargets.RulingCounts

/-! CF15 connected entire-class count from CF13 decomposition, mixed graphs
and all coordinate rulings. Coarse-cover and final inventory remain separate. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- An actual degree-zero graph is exactly one coordinate ruling, in either
chart. Degenerate zero sections are handled by the branch's nonvanishing. -/
def CF15ConstantGraphRuling : Prop :=
  ∀ (inverse : Bool) (A B : Polynomial ℤ), graphDegree A B=0 →
    ∀ b d u v : ℕ, sourceGraphBranch inverse A B b d u v →
      sourcePoint b d u v (if inverse then 0 else 1)=
        integerPolynomialValue A 0/integerPolynomialValue B 0

/-- Derive the bounded common-factor ruling inventory from D's actual degree;
count those rulings and the constant-or-mixed graph branch on original starts. -/
def CF15BoundedGraphRulingClassSubpower : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (X : ℝ) (D A B : Polynomial ℤ), 32≤X → boundedGraphData X D A B →
      ∀ inverse : Bool, ∀ S : Finset ℕ,
        (∀ n ∈ S, (n:ℝ)≤2*X ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧
          graphRulingCase inverse D A B (sourcePoint b d u v)) →
        (S.card:ℝ)≤C*X^ε

/-- The rounded original smooth class itself has uniformly subpower many
original starts. All actual CF11–14 localization hypotheses remain explicit;
no graph, factorization, determinant-size or source-count conclusion is assumed. -/
def CF15RoundedClassSourceSubpower : Prop :=
  StewartPrimitiveThue → ∀ δ : ℝ, 0<δ → δ≤1 → ∀ ε : ℝ, 0<ε →
    ∃ X₀ C : ℝ, 32≤X₀ ∧ 0<C ∧ ∀ X ψ B E a : ℝ,
      X₀≤X → 0≤ψ → ψ≤2/3 → 0<B → 0<E → 0<a → B*E=X^ψ →
      ∀ (F : SourcePolynomial) (p : ℕ) (z₀ : Fin 2 → ZMod p)
        (S : Finset ℕ) (b d u v : ℕ → ℕ),
        Nat.Prime p → roundedScale X ψ δ≤(p:ℝ) →
        (∀ n ∈ S, PairSource n (b n) (d n) (u n) (v n)) →
        (∀ n ∈ S, actualRealBox X B E n (b n) (d n)) →
        (∀ n ∈ S, actualDirectInterval a (roundedHeight X ψ δ:ℝ) (b n) (d n)) →
        (∀ n ∈ S, polynomialValue F (sourcePoint (b n) (d n) (u n) (v n))=0) →
        (∀ n ∈ S, goodSourcePrime F (b n) (d n) (u n) (v n) p) →
        (∀ n ∈ S, sourceReduction (b n) (d n) (u n) (v n) p=z₀) →
        (S.card:ℝ)≤C*X^ε

end
end P0365Subquarter
