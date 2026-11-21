import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fintype.BigOperators

/-! The sampled primal (6) and printed dual (7)–(9) of Bhat et al.
    A sample is indexed by its draws, including repeated observations. -/

namespace Kadp

open scoped BigOperators

structure SampledRSALP (S A H : Type*) [Fintype S] (N : ℕ) where
  sample : Fin N → S
  sample_pos : 0 < N
  feature : S → H
  cost : S → A → ℝ
  transition : S → A → S → ℝ
  transition_nonneg : ∀ x a y, 0 ≤ transition x a y
  transition_sum : ∀ x a, ∑ y, transition x a y = 1
  ν : S → ℝ
  π : S → ℝ
  ν_pos : ∀ x, 0 < ν x
  π_pos : ∀ x, 0 < π x
  π_sum : ∑ x, π x = 1
  α : ℝ
  α_pos : 0 < α
  α_lt_one : α < 1
  κ : ℝ
  κ_pos : 0 < κ
  Γ : ℝ
  Γ_pos : 0 < Γ

namespace SampledRSALP

variable {S A H : Type*} [Fintype S] [Fintype A] [DecidableEq S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {N : ℕ}
  (D : SampledRSALP S A H N)

noncomputable def weight (x : S) : ℝ := D.ν x / D.π x

noncomputable def value (z : H) (b : ℝ) (x : S) : ℝ :=
  inner ℝ (D.feature x) z + b

/-- Constraints of (6), including nonnegative slack at each draw. -/
def PrimalFeasible (z : H) (b : ℝ) (s : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ ∀ i a, D.value z b (D.sample i) ≤
    D.cost (D.sample i) a +
      D.α * (∑ y, D.transition (D.sample i) a y * D.value z b y) + s i

/-- Objective of (6). The offset has coefficient one. -/
noncomputable def primalObjective (z : H) (b : ℝ) (s : Fin N → ℝ) : ℝ :=
  (∑ i, D.weight (D.sample i) * inner ℝ (D.feature (D.sample i)) z) / N +
    b - D.κ / N * (∑ i, s i) - D.Γ / 2 * inner ℝ z z

def primalValues : Set ℝ :=
  {v | ∃ z b s, D.PrimalFeasible z b s ∧ D.primalObjective z b s = v}

/-- The coefficient vanishes off the paper's one-step neighborhood. This lets
    (7) and (8) sum over the entire finite state space. -/
noncomputable def q (x y : S) (a : A) : ℝ :=
  (if x = y then 1 else 0) - D.α * D.transition x a y

noncomputable def gramCoeff (i : Fin N) (a : A) (j : Fin N) (c : A) : ℝ :=
  ∑ y, ∑ y', D.q (D.sample i) y a * D.q (D.sample j) y' c *
    inner ℝ (D.feature y) (D.feature y')

noncomputable def linearCoeff (i : Fin N) (a : A) : ℝ :=
  D.Γ * D.cost (D.sample i) a -
    (∑ j, ∑ y, D.weight (D.sample j) * D.q (D.sample i) y a *
      inner ℝ (D.feature y) (D.feature (D.sample j))) / N

/-- The scalar S on p. 8, with the sign and normalization as printed. -/
noncomputable def dualConstant : ℝ :=
  -(∑ i, ∑ j, D.weight (D.sample i) * D.weight (D.sample j) *
    inner ℝ (D.feature (D.sample i)) (D.feature (D.sample j)))

def DualFeasible (l : Fin N → A → ℝ) : Prop :=
  (∀ i a, 0 ≤ l i a) ∧ (∀ i, ∑ a, l i a ≤ D.κ / N) ∧
    (∑ i, ∑ a, l i a) = 1 / (1 - D.α)

/-- Objective of (9), retaining the paper's scale and additive constant. -/
noncomputable def dualObjective (l : Fin N → A → ℝ) : ℝ :=
  (∑ i, ∑ a, ∑ j, ∑ c, l i a * D.gramCoeff i a j c * l j c) / 2 +
    (∑ i, ∑ a, D.linearCoeff i a * l i a) + D.dualConstant

def dualValues : Set ℝ :=
  {v | ∃ l, D.DualFeasible l ∧ D.dualObjective l = v}

end SampledRSALP
end Kadp
