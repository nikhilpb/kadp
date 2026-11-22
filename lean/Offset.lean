import Theorem1
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.Rev

/-! The free intercept in the idealized sampled program (18), §3.2. -/

namespace Kadp.Offset

open Matrix SargentStachurski.MarkovDecisionProcesses
open Kadp.Occupancy Kadp.Approximation Kadp.Idealized
open scoped BigOperators

variable {N : ℕ}

private def middle (hN : 0 < N) : Fin N := ⟨(N - 1) / 2, by omega⟩

/-- Endpoints of the closed median interval, counted with sample multiplicity. -/
noncomputable def lowerMedian (t : Fin N → ℝ) (hN : 0 < N) : ℝ :=
  t (Tuple.sort t (middle hN))

noncomputable def upperMedian (t : Fin N → ℝ) (hN : 0 < N) : ℝ :=
  t (Tuple.sort t (middle hN).rev)

private theorem between_iff_pair_min (u v b : ℝ) :
    |u - v| = |b - u| + |b - v| ↔ min u v ≤ b ∧ b ≤ max u v := by
  simp only [abs, max_def, min_def]
  split_ifs <;> constructor <;> intro h <;> (try constructor) <;> linarith

/-- Every minimizer of absolute deviation is a median, including all ties for even N. -/
theorem minimizes_abs_iff_median (t : Fin N → ℝ) (hN : 0 < N) (b : ℝ) :
    (∀ c : ℝ, ∑ i, |b - t i| ≤ ∑ i, |c - t i|) ↔
      lowerMedian t hN ≤ b ∧ b ≤ upperMedian t hN := by
  let y := t ∘ Tuple.sort t
  let k := middle hN
  have hy : Monotone y := Tuple.monotone_sort t
  have hk : k ≤ k.rev := by change (N - 1) / 2 ≤ N - ((N - 1) / 2 + 1); omega
  have hmid (i : Fin N) :
      min (y i) (y i.rev) ≤ y k ∧ y k.rev ≤ max (y i) (y i.rev) := by
    by_cases hi : i ≤ k
    · exact ⟨(min_le_left ..).trans (hy hi), (hy (Fin.rev_le_rev.mpr hi)).trans (le_max_right ..)⟩
    · have hi' : k.rev ≤ i := by
        change ¬i.val ≤ (N - 1) / 2 at hi
        change N - ((N - 1) / 2 + 1) ≤ i.val
        omega
      exact ⟨(min_le_right ..).trans (hy (by simpa using Fin.rev_le_rev.mpr hi')),
        (hy hi').trans (le_max_left ..)⟩
  let d (i : Fin N) := |y i - y i.rev|
  let p (c : ℝ) (i : Fin N) := |c - y i| + |c - y i.rev|
  have hbound (c : ℝ) (i : Fin N) : d i ≤ p c i := by
    simpa [d, p, abs_sub_comm (y i) c] using (abs_sub_le (y i) c (y i.rev))
  have hp (c : ℝ) : ∑ i, p c i = 2 * ∑ i, |c - t i| := by
    have hr : (∑ i : Fin N, |c - y i.rev|) = ∑ i, |c - y i| :=
      Equiv.sum_comp (Fin.revPerm (n := N)) (fun i => |c - y i|)
    have hs : (∑ i : Fin N, |c - y i|) = ∑ i, |c - t i| :=
      Equiv.sum_comp (Tuple.sort t) (fun i => |c - t i|)
    simp only [p, Finset.sum_add_distrib, hr, hs, two_mul]
  have heq (c : ℝ) : (∑ i, d i) = ∑ i, p c i ↔ y k ≤ c ∧ c ≤ y k.rev := by
    rw [Finset.sum_eq_sum_iff_of_le (fun i _ => hbound c i)]
    constructor
    · intro h
      have hc := (between_iff_pair_min ..).mp (h k (Finset.mem_univ _))
      simpa [min_eq_left (hy hk), max_eq_right (hy hk)] using hc
    · intro hc i _
      exact (between_iff_pair_min ..).mpr ⟨(hmid i).1.trans hc.1, hc.2.trans (hmid i).2⟩
  have hmin := (heq (y k)).mpr ⟨le_rfl, hy hk⟩
  change _ ↔ y k ≤ b ∧ b ≤ y k.rev
  constructor
  · intro h
    apply (heq b).mp
    apply le_antisymm (Finset.sum_le_sum fun i _ => hbound b i)
    rw [hmin, hp, hp]
    linarith only [h (y k)]
  · intro h c
    have hle := Finset.sum_le_sum (s := Finset.univ) fun i _ => hbound c i
    rw [(heq b).mpr h, hp, hp] at hle
    linarith only [hle]


variable {S A H : Type*} [Fintype S] [Fintype A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] (M : MDP S A)

/-- Threshold at which the least slack for this state first becomes positive. -/
noncomputable def breakpoint (V : S → ℝ) (x : S) : ℝ :=
  (optimalBellman M V x - V x) / (1 - M.β)

theorem bellman_shift (V : S → ℝ) (b : ℝ) (x : S) :
    optimalBellman M (fun y => V y + b) x = optimalBellman M V x + M.β * b := by
  have hB (a : A) : M.B (-(fun y => V y + b)) x a = M.B (-V) x a + -(M.β * b) := by
    simp only [MDP.B, Pi.neg_apply, neg_add_rev, add_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, M.P_rowsum, mul_one]
    ring
  change -((M.Γ x).sup' _ (M.B (-(fun y => V y + b)) x)) = -((M.Γ x).sup' _ (M.B (-V) x)) + _
  rw [show M.B (-(fun y => V y + b)) x = _ from funext hB, ← Finset.sup'_add]
  ring

theorem residual_shift (V : S → ℝ) (b : ℝ) (x : S) :
    bellmanResidual M (fun y => V y + b) x = (1 - M.β) * max (b - breakpoint M V x) 0 := by
  have hβ := sub_pos.mpr M.β_lt_one
  rw [bellmanResidual, bellman_shift, mul_max_of_nonneg _ _ hβ.le, mul_zero]
  congr 1
  unfold breakpoint
  field_simp [hβ.ne']
  ring

/-- Feasibility in (18) before eliminating the sampled slack variables. -/
theorem slackFeasible_shift_iff (X : Fin N → S) (V : S → ℝ) (b : ℝ) (s : Fin N → ℝ) :
    SlackFeasible M X (fun y => V y + b) s ↔
      ∀ i, (1 - M.β) * max (b - breakpoint M V (X i)) 0 ≤ s i := by
  simp only [slackFeasible_iff, residual_shift]

/-- In (18) the dependence on the intercept is the negative mean absolute deviation. -/
theorem sampleObjective_shift (ν : S → ℝ) (hν : IsDistribution ν) (X : Fin N → S)
    (hN : 0 < N) (V : S → ℝ) (b : ℝ) :
    sampleObjective M ν X (fun y => V y + b) =
      ν ⬝ᵥ V + sampleMean X (breakpoint M V) -
        (∑ i, |b - breakpoint M V (X i)|) / N := by
  have hd : ν ⬝ᵥ (fun y => V y + b) = ν ⬝ᵥ V + b := by
    simp only [dotProduct, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hν.sum_eq_one, one_mul]
  have habs (u : ℝ) : 2 * max (b-u) 0 = b - u + |b-u| := by
    rcases le_total u b with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [max_eq_right (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr h)]; ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => habs (breakpoint M V (X i)))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [sampleObjective, sampleMean, hd, residual_shift, ← Finset.mul_sum]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hN', (sub_pos.mpr M.β_lt_one).ne']
  linear_combination -hsum

/-- All optimal free intercepts for a fixed fit, with repeated draws allowed. -/
theorem maximizes_offset_iff (ν : S → ℝ) (hν : IsDistribution ν) (X : Fin N → S)
    (hN : 0 < N) (V : S → ℝ) (b : ℝ) :
    (∀ c : ℝ, sampleObjective M ν X (fun y => V y + c) ≤
      sampleObjective M ν X (fun y => V y + b)) ↔
      lowerMedian (breakpoint M V ∘ X) hN ≤ b ∧ b ≤ upperMedian (breakpoint M V ∘ X) hN := by
  simp only [sampleObjective_shift M ν hν X hN V, sub_le_sub_iff_left,
    div_le_div_iff_of_pos_right (show (0 : ℝ) < N by exact_mod_cast hN)]
  exact minimizes_abs_iff_median _ _ _

/-- A uniform radius for every free optimum in (18). The cost norm uses reward = -cost. -/
noncomputable def offsetRadius (Φ : S → H) (C : ℝ) : ℝ :=
  (‖M.r‖ + (1 + M.β) * ‖Φ‖ * C) / (1 - M.β)

theorem abs_breakpoint_le (Φ : S → H) {z : H} {C : ℝ} (hz : ‖z‖ ≤ C) (x : S) :
    |breakpoint M (fun y => inner ℝ (Φ y) z) x| ≤ offsetRadius M Φ C := by
  let V (y : S) := inner ℝ (Φ y) z
  let μ := M.greedy (-V)
  let p : Parameters H C 0 := ⟨(z,0), hz, by norm_num⟩
  have hfit : fit Φ p = V := by ext y; simp [fit, p, V]
  have hgreedy : costBellman M μ V = optimalBellman M V := by
    rw [costBellman_eq_neg_reward, optimalBellman, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy _)]
  have hr := fit_residual_eq Φ M μ p x
  rw [hfit, hgreedy] at hr
  change V x - optimalBellman M V x =
    inner ℝ (featureDifference Φ M μ x) z + (1 - M.β) * 0 - (-M.rσ μ x) at hr
  have hf := (abs_real_inner_le_norm (featureDifference Φ M μ x) z).trans
    (mul_le_mul (norm_featureDifference Φ M μ x) hz (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (by linarith only [M.β_pos])))
  have hg : |M.rσ μ x| ≤ ‖M.r‖ :=
    (norm_le_pi_norm (M.r x) (μ x)).trans (norm_le_pi_norm M.r x)
  change |(optimalBellman M V x - V x) / (1 - M.β)| ≤ _
  rw [abs_div, abs_of_pos (sub_pos.mpr M.β_lt_one), offsetRadius,
    div_le_div_iff_of_pos_right (sub_pos.mpr M.β_lt_one), abs_sub_comm]
  simp only [hr, mul_zero, add_zero, sub_neg_eq_add]
  calc
    _ ≤ _ := abs_add_le ..
    _ ≤ ‖Φ‖ * (1 + M.β) * C + ‖M.r‖ := add_le_add hf hg
    _ = _ := by ring

/-- Program (18) with the feature ball and the sampled slacks, and a free intercept. -/
def IsFreeOptimizer (Φ : S → H) (C : ℝ) (ν : S → ℝ) (X : Fin N → S)
    (z : H) (b : ℝ) (s : Fin N → ℝ) : Prop :=
  ‖z‖ ≤ C ∧ SlackFeasible M X (fun x => inner ℝ (Φ x) z + b) s ∧
    ∀ w : H, ‖w‖ ≤ C → ∀ c t, SlackFeasible M X (fun x => inner ℝ (Φ x) w + c) t →
      slackObjective M ν (fun x => inner ℝ (Φ x) w + c) t ≤
      slackObjective M ν (fun x => inner ℝ (Φ x) z + b) s

theorem freeOptimizer_abs_le (Φ : S → H) {C : ℝ} (ν : S → ℝ) (hν : IsDistribution ν)
    (X : Fin N → S) (hN : 0 < N) {z : H} {b : ℝ} {s : Fin N → ℝ}
    (h : IsFreeOptimizer M Φ C ν X z b s) : |b| ≤ offsetRadius M Φ C := by
  let V (x : S) := inner ℝ (Φ x) z
  have hmax := (maximizes_offset_iff M ν hν X hN V b).1 (fun c =>
    sampleObjective_le_of_maximizes M ν X _ _ s h.2.1 (h.2.2 z h.1 c))
  apply abs_le.mpr
  exact ⟨(abs_le.mp (abs_breakpoint_le M Φ h.1 _)).1.trans hmax.1,
    hmax.2.trans (abs_le.mp (abs_breakpoint_le M Φ h.1 _)).2⟩

/-- At and above the corrected radius the original slack problem and its free
version have identical maximizers; strict excess puts every optimizer in the interior. -/
theorem boxedOptimizer_iff_free (Φ : S → H) {C B : ℝ} (hB : offsetRadius M Φ C ≤ B)
    (ν : S → ℝ) (hν : IsDistribution ν) (X : Fin N → S) (hN : 0 < N)
    (p : Parameters H C B) (s : Fin N → ℝ) :
    Theorem1.IsOptimizer M Φ ν X p s ↔ IsFreeOptimizer M Φ C ν X p.val.1 p.val.2 s := by
  constructor
  · intro h
    refine ⟨p.property.1, h.1, ?_⟩
    intro w hw c t ht
    let V (x : S) := inner ℝ (Φ x) w
    let t₀ := breakpoint M V ∘ X
    let m := lowerMedian t₀ hN
    have hmB : |m| ≤ B := (abs_breakpoint_le M Φ hw _).trans hB
    let q : Parameters H C B := ⟨(w,m), hw, hmB⟩
    have hk : middle hN ≤ (middle hN).rev := by
      change (N - 1) / 2 ≤ N - ((N - 1) / 2 + 1); omega
    have hmed := (maximizes_offset_iff M ν hν X hN V m).2
      ⟨le_rfl, Tuple.monotone_sort t₀ hk⟩ c
    exact (slackObjective_le_sampleObjective M ν X _ _ ht).trans
      (hmed.trans (h.2 q (fun i => bellmanResidual M (fit Φ q) (X i))
        ((slackFeasible_iff ..).2 fun _ => le_rfl)))
  · intro h
    exact ⟨h.2.1, fun q t ht => h.2.2 q.val.1 q.property.1 q.val.2 t ht⟩

theorem boxedOptimizer_interior (Φ : S → H) {C B : ℝ} (hB : offsetRadius M Φ C < B)
    (ν : S → ℝ) (hν : IsDistribution ν) (X : Fin N → S) (hN : 0 < N)
    {p : Parameters H C B} {s : Fin N → ℝ} (h : Theorem1.IsOptimizer M Φ ν X p s) :
    |p.val.2| < B :=
  (freeOptimizer_abs_le M Φ ν hν X hN
    ((boxedOptimizer_iff_free M Φ hB.le ν hν X hN p s).1 h)).trans_lt hB

/-- The free problem attains a maximum, even in an infinite-dimensional feature space. -/
theorem exists_freeOptimizer (Φ : S → H) {C : ℝ} (hC : 0 ≤ C) (ν : S → ℝ)
    (hν : IsDistribution ν) (X : Fin N → S) (hN : 0 < N) :
    ∃ z b s, IsFreeOptimizer M Φ C ν X z b s := by
  have hR : 0 ≤ offsetRadius M Φ C := by unfold offsetRadius; positivity [M.β_pos, M.β_lt_one]
  obtain ⟨p, s, h⟩ := Theorem1.exists_optimizer M Φ ν X hC hR
  exact ⟨p.val.1, p.val.2, s, (boxedOptimizer_iff_free M Φ le_rfl ν hν X hN p s).1 h⟩


namespace Counterexample

/-- Both states move to the positive-feature state; the single action costs zero. -/
noncomputable def model : MDP Bool Unit :=
  ofCosts (1/2) (by norm_num) (by norm_num) (fun _ _ => 0)
    (fun _ _ y => if y then 1 else 0) (by intros; split <;> norm_num)
    (by intros; norm_num [Fintype.sum_bool])

def feature (x : Bool) : ℝ := if x then 1 else -1

noncomputable def initial (_ : Bool) : ℝ := 1/2

def draw (_ : Fin 1) : Bool := false

theorem initial_distribution : IsDistribution initial := by
  constructor <;> norm_num [initial, Fintype.sum_bool]

theorem draw_occupancy : discountedOccupancy model (fun _ => ()) initial false = 1/4 := by
  have h := congrFun (occupancy_balance model (fun _ => ()) initial) false
  norm_num [model, ofCosts, initial, vecMul, dotProduct, MDP.Pσ, Fintype.sum_bool] at h ⊢
  exact h

theorem feature_norm : ‖feature‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
    intro x; cases x <;> norm_num [feature]
  · simpa [feature] using norm_le_pi_norm feature true

private theorem slack_iff (z b : ℝ) (s : Fin 1 → ℝ) :
    SlackFeasible model draw (fun x => inner ℝ (feature x) z + b) s ↔
      0 ≤ s 0 ∧ b - 3*z ≤ 2*s 0 := by
  simp [SlackFeasible, draw, optimalBellman, model, ofCosts, MDP.T, MDP.B,
    feature]
  intro _
  constructor <;> intro h <;> linarith

private theorem objective_eq (z b : ℝ) (s : Fin 1 → ℝ) :
    slackObjective model initial (fun x => inner ℝ (feature x) z + b) s = b - 4*s 0 := by
  norm_num [slackObjective, model, ofCosts, initial, dotProduct, Fintype.sum_bool,
    feature, Real.inner_apply]
  ring

/-- Positive-probability counterexample: the printed test holds, but the free
maximum is 3 while the boxed maximum is 5/2. Both are attained with zero slacks. -/
theorem printed_threshold_changes_optimum :
    let C : ℝ := 1
    let B : ℝ := 5/2
    let boxed : Parameters ℝ C B := ⟨(1,B), by norm_num, by norm_num⟩
    2*C*‖feature‖ + ‖model.r‖ / (1-model.β) < B ∧
    offsetRadius model feature C = 3 ∧
    IsFreeOptimizer model feature C initial draw 1 3 (fun _ => 0) ∧
    slackObjective model initial (fun x => inner ℝ (feature x) (1:ℝ) + 3) (fun _ : Fin 1 => 0) = 3 ∧
    Theorem1.IsOptimizer model feature initial draw boxed (fun _ => 0) ∧
    slackObjective model initial (fit feature boxed) (fun _ : Fin 1 => 0) = B := by
  dsimp only
  have hr : model.r = 0 := by ext; simp [model, ofCosts]
  have hβ : model.β = 1/2 := rfl
  refine ⟨by norm_num [feature_norm, hr, hβ], by norm_num [offsetRadius, feature_norm, hr, hβ],
    ⟨by norm_num, (slack_iff ..).2 (by norm_num), ?_⟩, by rw [objective_eq]; norm_num,
    ⟨(slack_iff ..).2 (by norm_num), ?_⟩, ?_⟩
  · intro w hw c t ht
    rw [objective_eq, objective_eq]
    rcases (slack_iff ..).1 ht with ⟨h₀, h₁⟩
    have hw' := (le_abs_self w).trans hw
    linarith
  · intro q t ht
    change slackObjective model initial (fun x => inner ℝ (feature x) q.val.1 + q.val.2) t ≤
      slackObjective model initial (fun x => inner ℝ (feature x) (1:ℝ) + 5/2) (fun _ => 0)
    rw [objective_eq, objective_eq]
    have hb := (le_abs_self _).trans q.property.2
    have hs := ((slack_iff ..).1 ht).1
    linarith
  · change slackObjective model initial (fun x => inner ℝ (feature x) (1:ℝ) + 5/2)
      (fun _ : Fin 1 => 0) = 5/2
    rw [objective_eq]; norm_num

end Counterexample
end Kadp.Offset
