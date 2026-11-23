import PaperTargets.MonomialDeterminants

/-! CF04 coefficient aggregation and actual-source rectangular determinant.
The uniform degree/slack choice and coarse-polynomial relation remain separate. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

abbrev RectangularIndex (A C : ℕ) := Fin (A+1) × Fin (C+1)

def rectangularRootMatrix (A C : ℕ) (α β : RectangularIndex A C → ℝ) :
    Matrix (RectangularIndex A C) (RectangularIndex A C) ℝ :=
  Matrix.of (fun i j => rootColumnValue j.1.val j.2.val (α i) (β i))

def rectangularSourceMatrix (A C : ℕ) (b d u v : RectangularIndex A C → ℕ) :
    Matrix (RectangularIndex A C) (RectangularIndex A C) ℤ :=
  Matrix.of (fun i j => rectangularIntegerEntry A C (b i) (d i) (u i) (v i)
    j.1.val j.2.val)

def rectangularRowScale (A C d u : ℕ) : ℝ := (d:ℝ)^A*(u:ℝ)^C

def rectangularColumnScale {A C : ℕ} (t : ℝ) (j : RectangularIndex A C) : ℝ :=
  t^j.1.val*(t^(3/2:ℝ))^j.2.val

def latticeDeterminantLower (H : ℕ) (a b : ℝ) : ℝ :=
  (2/3:ℝ)*(H:ℝ)*Real.sqrt (2*a*b*(H:ℝ))-2*(H:ℝ)*b

/-- The coefficient norm is aggregated internally before all weights/nodes. -/
def CF04RectangularRootDeterminant : Prop :=
  ∀ A C : ℕ, ∃ K : ℝ, 1≤K ∧ ∀ a b : ℝ, 0<a → a≤b →
    ∀ α β : RectangularIndex A C → ℝ,
      (∀ i, |α i|≤3*Real.exp (-a)) → (∀ i, |β i|≤8*Real.exp (-b)) →
        |(rectangularRootMatrix A C α β).det|≤
          K*Real.exp (-latticeDeterminantLower (Fintype.card (RectangularIndex A C)) a b)

/-- Every original integer minor is normalized and bounded here; no matrix
identity, coefficient census, determinant-size or bounded-relation premise. -/
def CF04ActualRectangularDeterminant : Prop :=
  ∀ A C : ℕ, ∃ K : ℝ, 1≤K ∧ ∀ X M t : ℝ,
    1≤X → 1<M → M≤X → 0<t →
    ∀ n b d u v : RectangularIndex A C → ℕ,
      (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
      (∀ i, X≤(n i:ℝ)) → (∀ i, actualDirectInterval t M (b i) (d i)) →
        |((rectangularSourceMatrix A C b d u v).det:ℝ)|≤
          (∏ i, rectangularRowScale A C (d i) (u i))*
          (∏ j : RectangularIndex A C, rectangularColumnScale t j)*
          K*Real.exp (-latticeDeterminantLower (Fintype.card (RectangularIndex A C))
            (Real.log M) (Real.log X))

end
end P0365Subquarter
