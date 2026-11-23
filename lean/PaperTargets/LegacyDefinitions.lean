import Mathlib.Data.Nat.Squarefree

/-!
Source-exact declaration port, not an import of historical scratch code.
`IsPrime`, `Powerful`, `pairCount`: BoundCore.lean, SHA-256
86edb4f9981755a2c7d49265fa0e8f8dc29bd94058e2cf6de8d2140e7761a896.
`PairSource`: CanonicalSources.lean, SHA-256
a03481f8a3dceb42eb478e2f274454dde4acd1a7fbf241922f2339fa87ca2f60.
Both donors live in docs/research/2026-10-13-p0365-bound/.
Only these four declaration blocks are ported, under their original namespace.
Historical source/proof files and their receipts remain unchanged.
-/

namespace P365Bound

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, IsPrime p → p ∣ n → p^2 ∣ n

noncomputable def pairCount (N : Nat) : Nat := by
  classical
  exact ((List.range (N+1)).filter (fun n => decide (Powerful n ∧ Powerful (n+1)))).length

def PairSource (n b d u v : ℕ) : Prop :=
  0 < b ∧ 0 < d ∧ 0 < u ∧ 0 < v ∧ Squarefree b ∧ Squarefree d ∧
    n = b^3*u^2 ∧ n+1 = d^3*v^2

end P365Bound
