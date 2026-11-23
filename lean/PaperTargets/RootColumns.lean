import PaperTargets.DividedMinors

/-! CF04 generic rectangular source columns in the exact direct root chart.
This extends the already checked fixed-eight-column normalization to arbitrary
fixed natural degrees; it assumes no Taylor, determinant or relation theorem. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def rootColumnPolynomial (i j : ℕ) : SourcePolynomial :=
  (1+MvPolynomial.X (0:Fin 2))^(2*i)*
    ((1+MvPolynomial.X (0:Fin 2))^3+MvPolynomial.X (1:Fin 2))^j

def rootColumnValue (i j : ℕ) (α β : ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) ![α,β] (rootColumnPolynomial i j)

def rectangularIntegerEntry (A C b d u v i j : ℕ) : ℤ :=
  (b:ℤ)^i*(d:ℤ)^(A-i)*(v:ℤ)^j*(u:ℤ)^(C-j)

/-- All monomial support has the fixed rectangular root-chart degree bounds. -/
def CF04RootColumnSupport : Prop :=
  ∀ i j : ℕ, ∀ e ∈ (rootColumnPolynomial i j).support,
    e 0≤2*i+3*j ∧ e 1≤j

/-- One finite coefficient norm bound precedes every column in a fixed
rectangle and every actual scale/source. Its dependence on A,C is explicit. -/
def CF04RootColumnCoefficientBound : Prop :=
  ∀ A C : ℕ, ∃ K : ℝ, 1≤K ∧ ∀ i j : ℕ, i≤A → j≤C →
    (∑ e ∈ (rootColumnPolynomial i j).support,
      |((rootColumnPolynomial i j).coeff e:ℝ)|)≤K

/-- One actual source gives common alpha,beta for all rectangular exponents.
The integer row is exactly normalized; no truncated expansion or beta derivative
hypothesis is supplied. Degrees zero and unit coordinates remain included. -/
def CF04ActualRectangularRootColumns : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v → ∀ X M a : ℝ,
    1≤X → X≤(n:ℝ) → 1≤M → M≤X → 0<a → actualDirectInterval a M b d →
      ∃ α β : ℝ, 0≤α ∧ α≤3/M ∧ |β|≤8/X ∧
        ∀ A C i j : ℕ, i≤A → j≤C →
          (rectangularIntegerEntry A C b d u v i j:ℝ)=
            (d:ℝ)^A*(u:ℝ)^C*a^i*(a^(3/2:ℝ))^j*rootColumnValue i j α β

end
end P0365Subquarter
