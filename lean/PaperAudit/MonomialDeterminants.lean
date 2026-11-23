import PaperProofs.MonomialDeterminants

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04PolynomialColumnExpansion
#print CF04RepeatedExponentDeterminant
#print CF04MonomialWeightDeterminant
#check (polynomial_column_expansion : CF04PolynomialColumnExpansion)
#check (repeated_exponent_determinant : CF04RepeatedExponentDeterminant)
#check (monomial_weight_determinant : CF04MonomialWeightDeterminant)
#print axioms polynomial_column_expansion
#print axioms repeated_exponent_determinant
#print axioms monomial_weight_determinant
set_option pp.all false

example : CF04PolynomialColumnExpansion := by
  intro ι _ _ P α β
  exact polynomial_column_expansion ι P α β
example : CF04RepeatedExponentDeterminant := by
  intro ι _ _ r α β hn
  exact repeated_exponent_determinant ι r α β hn
example : CF04MonomialWeightDeterminant := by
  intro ι _ _ D C r α β a b ha hab hdeg hα hβ
  exact monomial_weight_determinant ι D C r α β a b ha hab hdeg hα hβ

-- More than eight columns, arbitrary zero/nonzero row coordinates, repeated pair.
example (α β : Fin 9 → ℝ) :
    Matrix.det (fun i j : Fin 9 => bivariateMonomialValue (α i) (β i)
      ((fun _ : Fin 9 => (0:Fin 2 →₀ ℕ)) j))=0 := by
  apply repeated_exponent_determinant (Fin 9) (fun _ => 0) α β
  intro hinj
  have hh : (0:Fin 9)=1 := hinj rfl
  exact (by decide : (0:Fin 9)≠1) hh

-- Empty matrices stay within the exact weighted theorem, with no Nonempty input.
example (r : Fin 0 → Fin 2 →₀ ℕ) (α β : Fin 0 → ℝ) :
    let H := Fintype.card (Fin 0)
    |Matrix.det (fun i j => bivariateMonomialValue (α i) (β i) (r j))|≤
      (H.factorial:ℝ)*3^(H*0)*8^(H*0)*
        Real.exp (-((2/3:ℝ)*(H:ℝ)*Real.sqrt (2*(1:ℝ)*1*(H:ℝ))-2*(H:ℝ)*1)) := by
  exact monomial_weight_determinant (Fin 0) 0 0 r α β 1 1 (by norm_num) (by norm_num)
    (fun j => Fin.elim0 j) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

end
end P0365Subquarter
