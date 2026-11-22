import Approximation

/-! The cost-minimizing policies of §2.1 and the Bellman linear program (1). -/

namespace Kadp.BellmanLP

open Matrix SargentStachurski.MarkovDecisionProcesses Kadp.Occupancy Kadp.Approximation

variable {S A : Type*} [Fintype S] [Fintype A] (M : MDP S A)

def actionCost (J : S → ℝ) (x : S) (a : A) : ℝ := -M.B (-J) x a

omit [Fintype S] [Fintype A] in
theorem actionCost_ofCosts [Fintype S] [Fintype A] [Nonempty A]
    (α : ℝ) (hα : 0 < α) (hα' : α < 1) (g : S → A → ℝ) (p : S → A → S → ℝ)
    (hp : ∀ x a y, 0 ≤ p x a y) (hrow : ∀ x a, ∑ y, p x a y = 1)
    (J : S → ℝ) (x : S) (a : A) :
    actionCost (ofCosts α hα hα' g p hp hrow) J x a =
      g x a + α * ∑ y, p x a y * J y := by
  simp [actionCost, MDP.B, ofCosts, Finset.sum_neg_distrib, mul_comm, add_comm]

def Feasible (J : S → ℝ) : Prop := ∀ x, ∀ a ∈ M.Γ x, J x ≤ actionCost M J x a

variable [DecidableEq S] [DecidableEq A]

/-- A policy minimizes discounted cost simultaneously at every initial state
exactly when its actions minimize the one-step costs computed at the optimal value. -/
theorem cost_minimal_iff_greedy (μ : M.Policy) :
    (∀ (σ : M.Policy) x, policyCost M μ.1 x ≤ policyCost M σ.1 x) ↔
      ∀ x, ∀ a ∈ M.Γ x,
        actionCost M (optimalCost M) x (μ.1 x) ≤ actionCost M (optimalCost M) x a := by
  have hopt := M.isOptimal_iff μ.1
  have hgreedy := M.isOptimal_iff_isGreedy μ.1
  simp only [policyCost, optimalCost, actionCost, Pi.neg_apply, neg_neg, neg_le_neg_iff]
  exact ⟨fun h => (hgreedy.mp (hopt.mpr ⟨μ.2, h⟩)).2,
    fun h => (hopt.mp (hgreedy.mpr ⟨μ.2, h⟩)).2⟩

/-- The optimal value is the greatest feasible vector in (1). -/
theorem greatest_feasible : Feasible M (optimalCost M) ∧
    ∀ J, Feasible M J → J ≤ optimalCost M := by
  constructor
  · intro x a ha
    have h := M.B_le_T M.vstar ha
    rw [M.isFixedPt_T_vstar.eq] at h
    simpa [actionCost, optimalCost] using neg_le_neg h
  · intro J hJ
    have hstep : M.T (-J) ≤ -J := by
      intro x
      apply Finset.sup'_le
      intro a ha
      have hj : J x ≤ -(M.B (-J) x a) := hJ x a ha
      change M.B (-J) x a ≤ -(J x)
      linarith
    have hiter : ∀ k : ℕ, M.T^[k] (-J) ≤ -J := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (M.T_monotone ih).trans hstep
    intro x
    have hlim := le_of_tendsto' (tendsto_pi_nhds.1 (M.tendsto_iterate_T (-J)) x)
      (fun k => hiter k x)
    change M.vstar x ≤ -(J x) at hlim
    change J x ≤ -(M.vstar x)
    linarith

/-- With strictly positive weights, the unique maximizer of the linear program
is the optimal cost vector. No normalization of the weights is needed. -/
theorem maximizes_iff (ν : S → ℝ) (hν : ∀ x, 0 < ν x) (J : S → ℝ) :
    (Feasible M J ∧ ∀ V, Feasible M V → ν ⬝ᵥ V ≤ ν ⬝ᵥ J) ↔ J = optimalCost M := by
  obtain ⟨hfeas, hdom⟩ := greatest_feasible M
  constructor
  · rintro ⟨hJ, hmax⟩
    have hle := hdom J hJ
    have heq : ν ⬝ᵥ (optimalCost M - J) = 0 := by
      rw [dotProduct_sub, sub_eq_zero]
      exact le_antisymm (hmax _ hfeas)
        (dotProduct_le_dotProduct_of_nonneg_left hle fun x => (hν x).le)
    have hzero := Finset.sum_eq_zero_iff_of_nonneg
      (fun (x : S) (_ : x ∈ Finset.univ) => mul_nonneg (hν x).le (sub_nonneg.mpr (hle x)))
    funext x
    have hx := hzero.mp heq x (Finset.mem_univ x)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (hν x).ne')).symm
  · rintro rfl
    exact ⟨hfeas, fun V hV => dotProduct_le_dotProduct_of_nonneg_left (hdom V hV)
      fun x => (hν x).le⟩

/-- In one self-looping state, the two policies have discounted costs 0 and 2.
Greedy cost minimization and maximization of policy cost therefore disagree. -/
noncomputable def exampleModel : MDP Unit Bool :=
  ofCosts (1 / 2) (by norm_num) (by norm_num) (fun _ a => if a then 1 else 0)
    (fun _ _ _ => 1) (by simp) (by simp)

theorem policy_sign_example :
    policyCost exampleModel (fun _ => false) () = 0 ∧
    policyCost exampleModel (fun _ => true) () = 2 := by
  have h (a : Bool) : (fun _ : Unit => if a then (2 : ℝ) else 0) =
      policyCost exampleModel (fun _ => a) := by
    apply policyCost_unique
    funext x
    cases a <;> norm_num [costBellman, exampleModel, ofCosts, MDP.rσ, MDP.Pσ, mulVec, dotProduct]
  rw [← h false, ← h true]
  exact ⟨rfl, rfl⟩

end Kadp.BellmanLP
