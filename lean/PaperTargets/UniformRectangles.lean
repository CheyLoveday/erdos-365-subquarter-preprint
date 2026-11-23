import PaperTargets.HeightDeterminants

/-! Pre-proof proposal: uniform degree/slack selection with arbitrary finite
family of already fixed determinant constants. No source/count/vanishing premise. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Degrees precede every fixed determinant constant; the scale threshold may
then depend on their finite range. A varies only within the chosen finite range. -/
def CF04UniformRectangleSlack : Prop :=
  ∀ δ c₀ : ℝ, 0<δ → δ≤1 → 0<c₀ → c₀≤1 →
    ∃ C Amax : ℕ, 1≤C ∧ ∀ K : ℕ → ℝ,
      (∀ A : ℕ, A≤Amax → 1≤K A) →
      ∃ B₀ : ℝ, 1≤B₀ ∧ ∀ B S T a : ℝ, B₀≤B →
        c₀*B≤S → S≤2*B → c₀*B≤T → T≤2*B →
        0<a → a≤B → (9/8)*(1+δ)*S*T≤a*B →
        ∃ A : ℕ, A≤Amax ∧
          K A*Real.exp
            (((Fintype.card (RectangularIndex A C):ℝ)/2)*
              ((A:ℝ)*S+(C:ℝ)*T)-
              latticeDeterminantLower (Fintype.card (RectangularIndex A C)) a B)<1

/-- The same fixed finite degree range precedes every height, profile, box,
interval and tuple. All original cleared integer minors vanish at rounded M. -/
def CF04ActualUniformMinorVanishing : Prop :=
  ∀ δ : ℝ, 0<δ → δ≤1 → ∃ C Amax : ℕ, 1≤C ∧
    ∃ X₀ : ℝ, 32≤X₀ ∧ ∀ X ψ B E t : ℝ, X₀≤X →
      profileTheta/2≤ψ → ψ≤(2/3)*(1-profileTheta/2) →
      0<B → 0<E → 0<t → B*E=X^ψ →
      ∃ A : ℕ, A≤Amax ∧ ∀ n b d u v : RectangularIndex A C → ℕ,
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval t (roundedHeight X ψ δ:ℝ) (b i) (d i)) →
          (rectangularSourceMatrix A C b d u v).det=0

end
end P0365Subquarter
