import PaperTargets.SmallKernels
import PaperTargets.RulingCounts

/-! CF02 real shell-scale consumer of the proved finite Pell count. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Arbitrary real kernel cutoff, actual shell starts and one uniform epsilon
loss. No upper bound on Y or external counting premise is needed. -/
def CF02OriginalSmallKernelSubpower : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ X Y : ℝ, 32≤X → 0≤Y →
    ∀ S : Finset ℕ,
      (∀ n ∈ S, (n:ℝ)≤2*X ∧ ∃ b d u v : ℕ,
        PairSource n b d u v ∧ (b*d:ℝ)≤Y) →
      (S.card:ℝ)≤C*Y*X^ε

end
end P0365Subquarter
