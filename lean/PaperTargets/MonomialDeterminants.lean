import PaperTargets.RootColumns
import PaperTargets.WeightedMonomials

/-! CF04 finite column expansion and monomial-weight determinant estimate.
All exponent selections are explicit. Zero determinants and empty matrices
are included; no logarithm of a determinant is taken. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def bivariateMonomialValue (α β : ℝ) (e : Fin 2 →₀ ℕ) : ℝ :=
  α^(e 0)*β^(e 1)

/-- Expand actual integral polynomial columns over their own finite supports. -/
def CF04PolynomialColumnExpansion : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ (P : ι → SourcePolynomial) (α β : ι → ℝ),
      Matrix.det (fun i j => MvPolynomial.eval₂ (Int.castRingHom ℝ)
        ![α i,β i] (P j)) =
      ∑ r ∈ Fintype.piFinset (fun j => (P j).support),
        (∏ j : ι, ((P j).coeff (r j):ℝ))*
          Matrix.det (fun i j => bivariateMonomialValue (α i) (β i) (r j))

/-- A repeated exponent pair gives equal columns, including zero coordinates. -/
def CF04RepeatedExponentDeterminant : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ (r : ι → Fin 2 →₀ ℕ) (α β : ι → ℝ),
      ¬ Function.Injective (fun j => (r j 0,r j 1)) →
        Matrix.det (fun i j => bivariateMonomialValue (α i) (β i) (r j))=0

/-- Surviving distinct exponent pairs consume the proved sharp lattice moment.
The absolute exponential bound also covers repeated exponents and H=0. -/
def CF04MonomialWeightDeterminant : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∀ (D C : ℕ) (r : ι → Fin 2 →₀ ℕ) (α β : ι → ℝ) (a b : ℝ),
      0<a → a≤b → (∀ j, r j 0≤D ∧ r j 1≤C) →
      (∀ i, |α i|≤3*Real.exp (-a)) →
      (∀ i, |β i|≤8*Real.exp (-b)) →
      let H := Fintype.card ι
      |Matrix.det (fun i j => bivariateMonomialValue (α i) (β i) (r j))|≤
        (H.factorial:ℝ)*3^(H*D)*8^(H*C)*
          Real.exp (-((2/3:ℝ)*(H:ℝ)*Real.sqrt (2*a*b*(H:ℝ))-2*(H:ℝ)*b))

end
end P0365Subquarter
