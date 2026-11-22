import Theorem1
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-! The population programs (5), (15) and the approximation error (16). -/

namespace Kadp.Regularization

open Matrix
open SargentStachurski.MarkovDecisionProcesses

noncomputable section

variable {S A H : Type*} [Fintype S] [Fintype A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Population data in Bellman-difference coordinates. `δ = 1 - α`, `m` is the
relevance-weighted mean feature, and `d` is the current minus discounted next feature. -/
structure Data (S A H : Type*) [Fintype S] where
  m : H
  d : S → A → H
  g : S → A → ℝ
  π : S → ℝ
  hπ : IsDistribution π
  δ : ℝ
  δ_pos : 0 < δ
  κ : ℝ
  κ_pos : 0 < κ
  Γ : ℝ
  Γ_pos : 0 < Γ

/-- Input to both population programs, with the full action set of the manuscript. -/
def fromMDP (M : MDP S A) (Φ : S → H) (ν π : S → ℝ) (hπ : IsDistribution π)
    (κ Γ : ℝ) (hκ : 0 < κ) (hΓ : 0 < Γ) : Data S A H where
  m := ∑ x, ν x • Φ x
  d := fun x a => Φ x - M.β • ∑ y, M.P x a y • Φ y
  g := fun x a => -M.r x a
  π := π
  hπ := hπ
  δ := 1 - M.β
  δ_pos := sub_pos.mpr M.β_lt_one
  κ := κ
  κ_pos := hκ
  Γ := Γ
  Γ_pos := hΓ

namespace Data
variable (D : Data S A H)

def Feasible (z : H) (b : ℝ) (s : S → ℝ) : Prop :=
  (∀ x, 0 ≤ s x) ∧ ∀ x a, inner ℝ (D.d x a) z + D.δ * b - D.g x a ≤ s x

def score (z : H) (b : ℝ) (s : S → ℝ) := inner ℝ D.m z + b - D.κ * (D.π ⬝ᵥ s)

def penalized (z : H) (b : ℝ) (s : S → ℝ) := D.score z b s - D.Γ / 2 * ‖z‖ ^ 2

def PenalizedOpt (z : H) (b : ℝ) (s : S → ℝ) : Prop :=
  D.Feasible z b s ∧ ∀ w e t, D.Feasible w e t → D.penalized w e t ≤ D.penalized z b s

def RadiusOpt (C B : ℝ) (z : H) (b : ℝ) (s : S → ℝ) : Prop :=
  D.Feasible z b s ∧ ‖z‖ ≤ C ∧ |b| ≤ B ∧ ∀ w e t, D.Feasible w e t → ‖w‖ ≤ C →
    |e| ≤ B → D.score w e t ≤ D.score z b s

/-- The row inequalities in the original MDP coordinates. -/
theorem fromMDP_feasible (M : MDP S A) (Φ : S → H) (ν π : S → ℝ) (hπ : IsDistribution π)
    (κ Γ : ℝ) (hκ : 0 < κ) (hΓ : 0 < Γ) (z : H) (b : ℝ) (s : S → ℝ) :
    (fromMDP M Φ ν π hπ κ Γ hκ hΓ).Feasible z b s ↔ (∀ x, 0 ≤ s x) ∧ ∀ x a,
      inner ℝ (Φ x) z + b ≤ -M.r x a + M.β * (∑ y, M.P x a y * (inner ℝ (Φ y) z + b)) + s x := by
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro a
  simp only [fromMDP, inner_sub_left, real_inner_smul_left, sum_inner, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, M.P_rowsum, one_mul]
  constructor <;> intro h <;> linarith

theorem fromMDP_score (M : MDP S A) (Φ : S → H) (ν π : S → ℝ) (hπ : IsDistribution π)
    (κ Γ : ℝ) (hκ : 0 < κ) (hΓ : 0 < Γ) (z : H) (b : ℝ) (s : S → ℝ) :
    (fromMDP M Φ ν π hπ κ Γ hκ hΓ).score z b s =
      (∑ x, ν x * inner ℝ (Φ x) z) + b - κ * (π ⬝ᵥ s) := by
  simp [score, fromMDP, sum_inner, real_inner_smul_left]

omit [Fintype A] in
private theorem shift {z : H} {b : ℝ} {s : S → ℝ} (h : D.Feasible z b s) {t : ℝ} (ht : 0 ≤ t) :
    D.Feasible z (b+t) (fun x => s x + D.δ*t) :=
  ⟨fun x => add_nonneg (h.1 x) (mul_nonneg D.δ_pos.le ht), fun x a => by linarith [h.2 x a]⟩

omit [Fintype A] in
private theorem shift_score (z : H) (b : ℝ) (s : S → ℝ) (t : ℝ) :
    D.score z (b+t) (fun x => s x + D.δ*t) = D.score z b s + (1-D.κ*D.δ)*t := by
  simp only [score, dotProduct, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    D.hπ.sum_eq_one, one_mul]
  ring

omit [Fintype A] in
/-- Every feasible point generates an objective ray below the sharp threshold. -/
theorem unbounded_of_subcritical {z : H} {b : ℝ} {s : S → ℝ} (hp : D.Feasible z b s)
    (hκ : D.κ * D.δ < 1) (v : ℝ) : ∃ e t, D.Feasible z e t ∧ v < D.penalized z e t := by
  let t := (|v - D.penalized z b s| + 1) / (1-D.κ*D.δ)
  have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  refine ⟨b+t, _, D.shift hp ht, ?_⟩
  have hc : (1-D.κ*D.δ)*t = |v - D.penalized z b s| + 1 := by
    dsimp [t]; field_simp [sub_ne_zero.mpr hκ.ne']
  simp only [penalized, D.shift_score, hc]
  linarith [le_abs_self (v - (D.score z b s - D.Γ / 2 * ‖z‖ ^ 2))]

omit [Fintype A] in
/-- At equality every optimizer generates optimizers with arbitrarily large intercept. -/
theorem critical_optimal_ray {z : H} {b : ℝ} {s : S → ℝ} (hp : D.PenalizedOpt z b s)
    (hκ : D.κ * D.δ = 1) {t : ℝ} (ht : 0 ≤ t) :
    D.PenalizedOpt z (b+t) (fun x => s x + D.δ*t) := by
  refine ⟨D.shift hp.1 ht, fun w e u hu => ?_⟩
  simpa only [penalized, D.shift_score, hκ, sub_self, zero_mul, add_zero] using hp.2 w e u hu

omit [Fintype A] in
/-- At the norm of an attained penalized optimum, the same point solves the radius program. -/
theorem radius_of_penalized {z : H} {b B : ℝ} {s : S → ℝ} (h : D.PenalizedOpt z b s)
    (hb : |b| ≤ B) : D.RadiusOpt ‖z‖ B z b s := by
  refine ⟨h.1, le_rfl, hb, fun w e t hf hw _ => ?_⟩
  have hn := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw 2) (by positivity [D.Γ_pos] : 0 ≤ D.Γ/2)
  have ho := h.2 w e t hf
  unfold penalized at ho
  linarith

omit [Fintype A] in
/-- Radius optimizers at the matching radius are exactly the penalized optimizers
inside the box which use that radius. Values differ by the indicated penalty. -/
theorem radius_opt_iff {z : H} {b B : ℝ} {s : S → ℝ} (h : D.PenalizedOpt z b s)
    (hb : |b| ≤ B) (w : H) (e : ℝ) (t : S → ℝ) :
    D.RadiusOpt ‖z‖ B w e t ↔ D.PenalizedOpt w e t ∧ ‖w‖ = ‖z‖ ∧ |e| ≤ B := by
  have hr := D.radius_of_penalized h hb
  constructor
  · rintro ⟨hf, hw, he, hmax⟩
    have hscore := le_antisymm (hr.2.2.2 w e t hf hw he) (hmax z b s h.1 le_rfl hb)
    have hpen := h.2 w e t hf
    unfold penalized at hpen
    rw [hscore] at hpen
    have hsquare : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2 := (mul_le_mul_iff_right₀ (by positivity [D.Γ_pos] : 0 < D.Γ/2)).mp (by linarith)
    have heq : ‖w‖ = ‖z‖ := le_antisymm hw (by nlinarith [norm_nonneg z, norm_nonneg w])
    refine ⟨⟨hf, fun u c r hu => ?_⟩, heq, he⟩
    simpa only [penalized, hscore, heq] using h.2 u c r hu
  · rintro ⟨hp, hw, he⟩
    simpa only [hw] using D.radius_of_penalized hp he

omit [Fintype A] in
theorem optimal_value_shift {z : H} {b B : ℝ} {s : S → ℝ} (h : D.PenalizedOpt z b s)
    (hb : |b| ≤ B) {w : H} {e : ℝ} {t : S → ℝ} (hr : D.RadiusOpt ‖z‖ B w e t) :
    D.score w e t = D.penalized z b s + D.Γ/2 * ‖z‖^2 := by
  have hz := D.radius_of_penalized h hb
  have heq := le_antisymm (hz.2.2.2 w e t hr.1 hr.2.1 hr.2.2.1) (hr.2.2.2 z b s h.1 le_rfl hb)
  simp [penalized, heq]

/-- An intercept interval containing all row breakpoints at weights of norm at most R. -/
def interceptBound (R : ℝ) := (‖D.d‖ * R + ‖D.g‖) / D.δ

omit [InnerProductSpace ℝ H] in
private theorem interceptBound_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ D.interceptBound R := by
  unfold interceptBound
  positivity [D.δ_pos]

private theorem margin_bound {z : H} {R : ℝ} (hz : ‖z‖ ≤ R) (x : S) (a : A) :
    |inner ℝ (D.d x a) z - D.g x a| ≤ D.δ * D.interceptBound R := by
  unfold interceptBound
  rw [mul_div_cancel₀ _ D.δ_pos.ne']
  have hd : ‖D.d x a‖ ≤ ‖D.d‖ := (norm_le_pi_norm _ _).trans (norm_le_pi_norm _ _)
  have hg : |D.g x a| ≤ ‖D.g‖ := (norm_le_pi_norm (D.g x) a).trans (norm_le_pi_norm _ _)
  exact (abs_sub _ _).trans (add_le_add ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul hd hz (norm_nonneg _) (norm_nonneg _))) hg)

omit [Fintype A] [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private theorem weighted_nonneg {s : S → ℝ} (hs : ∀ x, 0 ≤ s x) : 0 ≤ D.π ⬝ᵥ s :=
  Finset.sum_nonneg fun x _ => mul_nonneg (D.hπ.nonneg x) (hs x)

private theorem zero_feasible {R : ℝ} (hR : 0 ≤ R) :
    D.Feasible 0 (-D.interceptBound R) 0 := by
  refine ⟨fun _ => le_rfl, fun x a => ?_⟩
  have h := (abs_le.mp (D.margin_bound (z := 0) (by simpa using hR : ‖(0:H)‖ ≤ R) x a)).2
  simp only [inner_zero_right, Pi.zero_apply] at *
  linarith

/-- Outside the breakpoint interval the intercept objective is affine. At strict
supercritical penalty, clipping an outside intercept strictly improves its score. -/
private theorem clip [Nonempty A] (hκ : 1 ≤ D.κ*D.δ) {z : H} {b R : ℝ} {s : S → ℝ}
    (hf : D.Feasible z b s) (hz : ‖z‖ ≤ R) :
    ∃ e t, |e| ≤ D.interceptBound R ∧ D.Feasible z e t ∧ D.score z b s ≤ D.score z e t ∧
      (1 < D.κ*D.δ → D.interceptBound R < |b| → D.score z b s < D.score z e t) := by
  let T := D.interceptBound R
  have hT : 0 ≤ T := D.interceptBound_nonneg ((norm_nonneg z).trans hz)
  by_cases hlo : b < -T
  · have hp : D.Feasible z (-T) 0 := by
      refine ⟨fun _ => le_rfl, fun x a => ?_⟩
      have hm := (abs_le.mp (D.margin_bound hz x a)).2
      change _ ≤ D.δ * T at hm
      change _ ≤ 0
      linarith
    have hi : D.score z b s < D.score z (-T) 0 := by
      simp only [score, dotProduct_zero, mul_zero, sub_zero]
      linarith [mul_nonneg D.κ_pos.le (D.weighted_nonneg hf.1)]
    exact ⟨-T, 0, by simp only [abs_neg, abs_of_nonneg hT]; exact le_rfl, hp, hi.le, fun _ _ => hi⟩
  by_cases hhi : T < b
  · let t := fun x => s x - D.δ*(b-T)
    have hf' : D.Feasible z T t := by
      refine ⟨fun x => ?_, fun x a => ?_⟩
      · let a : A := Classical.arbitrary A
        have hm := (abs_le.mp (D.margin_bound hz x a)).1
        change -(D.δ*T) ≤ _ at hm
        dsimp [t]
        linarith [hf.2 x a]
      · dsimp [t]
        linarith [hf.2 x a]
    have heq : D.score z b s = D.score z T t + (1-D.κ*D.δ)*(b-T) := by
      convert D.shift_score z T t (b-T) using 2 <;> simp [t]
    have hprod := mul_nonpos_of_nonpos_of_nonneg (by linarith : 1-D.κ*D.δ ≤ 0) (sub_nonneg.mpr hhi.le)
    refine ⟨T, t, by simp only [abs_of_nonneg hT]; exact le_rfl, hf', by linarith, fun hstrict _ => ?_⟩
    linarith [mul_neg_of_neg_of_pos (by linarith : 1-D.κ*D.δ < 0) (sub_pos.mpr hhi)]
  · have hab : |b| ≤ T := abs_le.mpr ⟨le_of_not_gt hlo,le_of_not_gt hhi⟩
    exact ⟨b,s,hab,hf,le_rfl,fun _ h => (h.not_ge hab).elim⟩

/-- The finite, pointwise least slack for each state. -/
def slack [Nonempty A] (z : H) (b : ℝ) (x : S) : ℝ :=
  max (Finset.univ.sup' Finset.univ_nonempty (fun a => inner ℝ (D.d x a) z + D.δ*b - D.g x a)) 0

theorem feasible_iff_slack [Nonempty A] (z : H) (b : ℝ) (s : S → ℝ) :
    D.Feasible z b s ↔ ∀ x, D.slack z b x ≤ s x := by
  simp only [Feasible, slack, max_le_iff, Finset.sup'_le_iff, Finset.mem_univ, true_implies]
  constructor
  · rintro ⟨h₀,h⟩ x; exact ⟨h x, h₀ x⟩
  · intro h; exact ⟨fun x => (h x).2, fun x => (h x).1⟩

private theorem least_slack_score [Nonempty A] {z : H} {b : ℝ} {s : S → ℝ} (hf : D.Feasible z b s) :
    D.score z b s ≤ D.score z b (D.slack z b) := by
  unfold score
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left
    (dotProduct_le_dotProduct_of_nonneg_left ((D.feasible_iff_slack ..).mp hf) D.hπ.nonneg) D.κ_pos.le) _

private theorem continuous_penalized [Nonempty A] (U : Submodule ℝ H) :
    Continuous (fun p : U × ℝ => D.penalized p.1.val p.2 (D.slack p.1.val p.2)) := by
  have hw : Continuous (fun p : U × ℝ => p.1.val) := U.subtypeL.continuous.comp continuous_fst
  have hs (x : S) : Continuous (fun p : U × ℝ => D.slack p.1.val p.2 x) :=
    (Continuous.finset_sup'_apply Finset.univ_nonempty (fun a _ =>
      ((continuous_const.inner hw).add (continuous_const.mul continuous_snd)).sub continuous_const)).max continuous_const
  unfold penalized score dotProduct
  fun_prop

/-- Attainment for the original unrestricted population program, including equality.
The finite span of the data suffices, with no dimension bound on H. -/
theorem exists_penalizedOpt [Nonempty A] (hκ : 1 ≤ D.κ*D.δ) :
    ∃ z b s, D.PenalizedOpt z b s := by
  classical
  let L := ‖D.m‖ + ‖D.d‖ / D.δ
  let G := ‖D.g‖ / D.δ
  let R := 1 + (2 / D.Γ) * (L + 2*G)
  have hL : 0 ≤ L := by dsimp [L]; positivity [D.δ_pos]
  have hG : 0 ≤ G := by dsimp [G]; positivity [D.δ_pos]
  have hR : 1 ≤ R := by dsimp [R]; linarith [mul_nonneg (by positivity [D.Γ_pos] : 0 ≤ 2 / D.Γ) (show 0 ≤ L+2*G by linarith)]
  have hR₀ : 0 ≤ R := by linarith
  have hT : 0 ≤ D.interceptBound R := D.interceptBound_nonneg hR₀
  let rows : Option (S × A) → H := fun i => i.elim D.m fun p => D.d p.1 p.2
  let U := Submodule.span ℝ (Set.range rows)
  letI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range rows)
  let box := Metric.closedBall (0 : U) R ×ˢ Set.Icc (-D.interceptBound R) (D.interceptBound R)
  let F := fun p : U × ℝ => D.penalized p.1.val p.2 (D.slack p.1.val p.2)
  have hc : IsCompact box := (isCompact_closedBall _ _).prod isCompact_Icc
  have hzmem : (0 : U) ∈ Metric.closedBall (0 : U) R := by simpa
  have hGle : G ≤ D.interceptBound R := by
    unfold G interceptBound
    exact div_le_div_of_nonneg_right (by linarith [mul_nonneg (norm_nonneg D.d) hR₀]) D.δ_pos.le
  have hbase : ((0 : U),-G) ∈ box := ⟨hzmem, by constructor <;> linarith⟩
  obtain ⟨p,hp,hmax⟩ := hc.exists_isMaxOn ⟨_,hbase⟩ (D.continuous_penalized U).continuousOn
  have hcompare (q) (hq : q ∈ box) : F q ≤ F p := hmax hq
  refine ⟨p.1.val, p.2, D.slack p.1.val p.2, (D.feasible_iff_slack ..).mpr (fun _ => le_rfl), fun z b s hf => ?_⟩
  by_cases hz : ‖z‖ ≤ R
  · obtain ⟨e,t,he,hf',hs,_⟩ := D.clip hκ hf hz
    let w := U.orthogonalProjectionOnto z
    have hw : ‖w‖ ≤ ‖z‖ := U.norm_orthogonalProjectionOnto_apply_le z
    have hi (i) : inner ℝ (rows i) w.val = inner ℝ (rows i) z := by
      exact U.inner_orthogonalProjectionOnto_eq_of_mem_left
        ⟨rows i, Submodule.subset_span (Set.mem_range_self i)⟩ z
    have hm := hi none
    have hd (x a) := hi (some (x,a))
    change inner ℝ D.m w.val = inner ℝ D.m z at hm
    have hf'' : D.Feasible w.val e t := ⟨hf'.1, fun x a => by
      rw [show inner ℝ (D.d x a) w.val = inner ℝ (D.d x a) z from hd x a]
      exact hf'.2 x a⟩
    have hscore : D.score w.val e t = D.score z e t := by simp [score, hm]
    have hpen := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw 2) (by positivity [D.Γ_pos] : 0 ≤ D.Γ/2)
    have hobj : D.penalized z b s ≤ F (w,e) := by
      have hsl := D.least_slack_score hf''
      change D.score z b s - _ ≤ D.score w.val e (D.slack w.val e) - D.Γ/2*‖w‖^2
      linarith only [hs, hscore, hsl, hpen]
    exact hobj.trans (hcompare (w,e) ⟨by simpa using hw.trans hz, abs_le.mp he⟩)
  · obtain ⟨e,t,he,hf',hs,_⟩ := D.clip hκ hf (R := ‖z‖) le_rfl
    have hscore : D.score z b s ≤ L*‖z‖ + G := by
      have hπ := mul_nonneg D.κ_pos.le (D.weighted_nonneg hf'.1)
      have hoff := (le_abs_self e).trans he
      unfold score at hs ⊢
      dsimp only [L, G] at ⊢
      unfold interceptBound at hoff
      rw [add_div, mul_div_right_comm] at hoff
      linarith [real_inner_le_norm D.m z]
    have hbig : 1 ≤ ‖z‖ := hR.trans (le_of_not_ge hz)
    have hconst : L+2*G ≤ D.Γ/2 * ‖z‖ := by
      have h := mul_le_mul_of_nonneg_left (le_of_not_ge hz) (by positivity [D.Γ_pos] : 0 ≤ D.Γ/2)
      dsimp [R] at h
      have he : D.Γ/2 * (1 + 2/D.Γ * (L+2*G)) = D.Γ/2 + (L+2*G) := by field_simp [D.Γ_pos.ne']
      rw [he] at h
      linarith only [h,D.Γ_pos]
    have hquad := mul_le_mul_of_nonneg_right hconst (norm_nonneg z)
    have hfar : D.penalized z b s ≤ -G := by
      unfold penalized
      nlinarith only [hscore, hquad, mul_le_mul_of_nonneg_left hbig hG]
    have hfeas : D.Feasible (0:H) (-G) 0 := by
      have h := D.zero_feasible (R := 0) le_rfl
      simpa [interceptBound, G] using h
    have hbaseval : -G ≤ F (0,-G) := by
      simpa [F, penalized, score] using D.least_slack_score hfeas
    exact hfar.trans (hbaseval.trans (hcompare _ hbase))

/-- Every maximizer has a bounded offset when the threshold is strict. -/
theorem optimal_intercept_le [Nonempty A] {z : H} {b : ℝ} {s : S → ℝ}
    (h : D.PenalizedOpt z b s) (hκ : 1 < D.κ*D.δ) : |b| ≤ D.interceptBound ‖z‖ := by
  by_contra! hh
  obtain ⟨e,t,_,hf,_,hs⟩ := D.clip hκ.le h.1 (R := ‖z‖) le_rfl
  have hbad := h.2 z e t hf
  unfold penalized at hbad
  linarith [hs hκ hh]

omit [Fintype A] in
/-- Strict concavity in the weight forces all penalized optimal weights to agree. -/
theorem optimal_weight_unique {z w : H} {b e : ℝ} {s t : S → ℝ}
    (hz : D.PenalizedOpt z b s) (hw : D.PenalizedOpt w e t) : z = w := by
  let u := (1/2 : ℝ) • (z+w)
  let v := (b+e)/2
  let r := fun x => (s x + t x)/2
  have hf : D.Feasible u v r := by
    refine ⟨fun x => by dsimp [r]; linarith [hz.1.1 x, hw.1.1 x], fun x a => ?_⟩
    simp only [u, v, r, real_inner_smul_right, inner_add_right]
    linarith [hz.1.2 x a, hw.1.2 x a]
  have hs : D.score u v r = (D.score z b s + D.score w e t)/2 := by
    simp only [score, u, v, r, real_inner_smul_right, inner_add_right, dotProduct,
      ← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    ring
  have heq := le_antisymm (hz.2 w e t hw.1) (hw.2 z b s hz.1)
  have hmid := hz.2 u v r hf
  have hnorm : ‖u‖ = ‖z+w‖/2 := by
    rw [show ‖u‖ = |(1/2:ℝ)| * ‖z+w‖ from norm_smul _ _, abs_of_nonneg (by norm_num)]
    ring
  unfold penalized at hmid heq
  rw [hs, hnorm] at hmid
  have hpar := parallelogram_law_with_norm ℝ z w
  have hid : ‖z+w‖^2 = 2*(‖z‖^2+‖w‖^2) - ‖z-w‖^2 := by linarith
  rw [div_pow, hid] at hmid
  by_contra hne
  have hpos := mul_pos D.Γ_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  linarith only [hmid, heq, hpos]

/-- Existence is equivalent to the sharp penalty condition. -/
theorem exists_penalizedOpt_iff [Nonempty A] :
    (∃ z b s, D.PenalizedOpt z b s) ↔ 1 ≤ D.κ * D.δ := by
  refine ⟨?_, D.exists_penalizedOpt⟩
  rintro ⟨z,b,s,h⟩
  by_contra! hκ
  obtain ⟨e,t,hf,ht⟩ := D.unbounded_of_subcritical h.1 hκ (D.penalized z b s)
  exact ht.not_ge (h.2 z e t hf)

omit [Fintype A] in
/-- At any attaining penalty, cutting off intercepts retains exactly the penalized
optimizers in the box, provided one penalized optimizer fits. -/
theorem radius_opt_iff_in_box {z : H} {b B : ℝ} {s : S → ℝ}
    (h : D.PenalizedOpt z b s) (hb : |b| ≤ B) (w : H) (e : ℝ) (t : S → ℝ) :
    D.RadiusOpt ‖z‖ B w e t ↔ D.PenalizedOpt w e t ∧ |e| ≤ B := by
  rw [D.radius_opt_iff h hb]
  exact ⟨fun x => ⟨x.1,x.2.2⟩, fun x => ⟨x.1,congrArg norm (D.optimal_weight_unique x.1 h),x.2⟩⟩

/-- Above threshold a finite intercept bound preserves the entire optimizer set. -/
theorem supercritical_equivalence [Nonempty A] (hκ : 1 < D.κ*D.δ) :
    ∃ z b s, D.PenalizedOpt z b s ∧ ∀ B, D.interceptBound ‖z‖ ≤ B →
      ∀ w e t, D.RadiusOpt ‖z‖ B w e t ↔ D.PenalizedOpt w e t := by
  obtain ⟨z,b,s,h⟩ := D.exists_penalizedOpt hκ.le
  refine ⟨z,b,s,h,fun B hB w e t => ?_⟩
  rw [D.radius_opt_iff h ((D.optimal_intercept_le h hκ).trans hB)]
  refine ⟨fun hp => hp.1, fun hp => ?_⟩
  obtain rfl := D.optimal_weight_unique hp h
  exact ⟨hp,rfl,(D.optimal_intercept_le hp hκ).trans hB⟩

/-- At the threshold any fixed finite intercept bound omits a penalized optimizer. -/
theorem critical_missing_optimizer [Nonempty A] (hκ : D.κ*D.δ = 1) (B : ℝ) :
    ∃ z b s, D.PenalizedOpt z b s ∧ B < |b| := by
  obtain ⟨z,b,s,h⟩ := D.exists_penalizedOpt hκ.ge
  let t := |B-b|+1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  refine ⟨_,_,_,D.critical_optimal_ray h hκ ht, ?_⟩
  exact lt_of_lt_of_le (by dsimp [t]; linarith [le_abs_self (B-b)]) (le_abs_self (b+t))

end Data

namespace Example

/-- Two absorbing states, one action, costs and scalar features -1, +1. -/
def feature (x : Bool) : ℝ := if x then 1 else -1

def model : MDP Bool Unit := Kadp.Occupancy.ofCosts (1/2) (by norm_num) (by norm_num)
  (fun x _ => feature x) (fun x _ y => if x=y then 1 else 0)
  (by intros; split <;> norm_num) (by intro x a; simp)

def program : Data Bool Unit ℝ := fromMDP model feature (fun _ => 1/2) (fun _ => 1/2)
  ⟨by intros; norm_num, by norm_num [Fintype.sum_bool]⟩ 6 1 (by norm_num) (by norm_num)

private theorem score_eq (z b : ℝ) (s : Bool → ℝ) :
    program.score z b s = b - 3*(s true+s false) := by
  norm_num [Data.score, program, fromMDP, Fintype.sum_bool, feature, dotProduct]
  ring

private theorem feasible_iff (z b : ℝ) (s : Bool → ℝ) :
    program.Feasible z b s ↔ (∀ x, 0 ≤ s x) ∧
      z/2+b/2-1 ≤ s true ∧ -z/2+b/2+1 ≤ s false := by
  apply and_congr_right
  intro _
  norm_num [program, fromMDP, model, Kadp.Occupancy.ofCosts, Fintype.sum_bool,
    Bool.forall_bool, feature, RCLike.inner_apply]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- The shared optimizer has nonzero weight and strictly different optimal values. -/
theorem unequal_optimal_values (B : ℝ) (hB : 1 ≤ B) :
    program.PenalizedOpt 1 (-1) 0 ∧ program.RadiusOpt 1 B 1 (-1) 0 ∧
    program.penalized 1 (-1) 0 = -3/2 ∧ program.score 1 (-1) 0 = -1 := by
  have hf : program.Feasible 1 (-1) 0 := (feasible_iff ..).mpr (by norm_num)
  have hp : program.PenalizedOpt 1 (-1) 0 := by
    refine ⟨hf, fun z b s h => ?_⟩
    obtain ⟨hn, _, hl⟩ := (feasible_iff ..).mp h
    simp only [Data.penalized, score_eq, Real.norm_eq_abs, sq_abs, show program.Γ = 1 from rfl]
    change _ - 1 / 2 * z^2 ≤ _
    norm_num
    nlinarith [hn true,hn false,sq_nonneg (z-1)]
  refine ⟨hp, ?_, ?_, ?_⟩
  · simpa using program.radius_of_penalized hp (show |(-1:ℝ)| ≤ B by simpa using hB)
  · rw [Data.penalized, score_eq]
    norm_num [show program.Γ = 1 from rfl]
  · norm_num [score_eq]

/-- No choice of radii can simultaneously preserve a maximizer and its numerical value. -/
theorem no_radii_with_common_optimizer_and_value :
    ¬ ∃ (C B w e : ℝ) (t : Bool → ℝ), program.PenalizedOpt w e t ∧
      program.RadiusOpt C B w e t ∧ program.score w e t = program.penalized w e t := by
  rintro ⟨C,B,w,e,t,h,_,hv⟩
  obtain rfl := program.optimal_weight_unique h (unequal_optimal_values 1 le_rfl).1
  unfold Data.penalized at hv
  norm_num [show program.Γ = 1 from rfl] at hv
  linarith

end Example


/-- Invert the Gram matrix on the state space, even for an infinite dimensional feature space. -/
theorem interpolate (Φ : S → H) (hrank : (Set.range Φ).finrank ℝ = Fintype.card S) (J : S → ℝ) :
    ∃ z : H, ∀ x, inner ℝ (Φ x) z = J x := by
  classical
  let K := gram ℝ Φ
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr
    (det_gram_ne_zero_iff_linearIndependent.mpr (linearIndependent_iff_card_eq_finrank_span.mpr hrank.symm))
  let c := K⁻¹ *ᵥ J
  have hc : K *ᵥ c = J := by simp [c, mulVec_mulVec, mul_nonsing_inv _ hdet]
  refine ⟨∑ y, c y • Φ y, fun x => ?_⟩
  simpa only [inner_sum, real_inner_smul_right, mulVec, dotProduct, K, gram_apply, mul_comm] using congrFun hc x

/-- Equation (16) vanishes for all radii containing the interpolant, with any nonnegative B. -/
theorem bestError_zero_of_full_rank [DecidableEq S] [DecidableEq A] (M : MDP S A)
    (Φ : S → H) (hrank : (Set.range Φ).finrank ℝ = Fintype.card S) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C B : ℝ, C₀ ≤ C → 0 ≤ B → Kadp.Theorem1.bestError M Φ C B = 0 := by
  obtain ⟨z,hz⟩ := interpolate Φ hrank (Kadp.Approximation.optimalCost M)
  refine ⟨‖z‖, norm_nonneg _, fun C B hC hB => ?_⟩
  let p : Kadp.Idealized.Parameters H C B := ⟨(z,0), hC, by simpa using hB⟩
  have heq : Kadp.Idealized.fit Φ p = Kadp.Approximation.optimalCost M := funext fun x => by simp [Kadp.Idealized.fit,p,hz]
  letI : Nonempty (Kadp.Idealized.Parameters H C B) := ⟨p⟩
  apply le_antisymm _ (le_ciInf fun _ => norm_nonneg _)
  have h := ciInf_le (f := fun q : Kadp.Idealized.Parameters H C B =>
    ‖Kadp.Approximation.optimalCost M - Kadp.Idealized.fit Φ q‖)
    ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ p
  simpa only [heq, sub_self, norm_zero, Kadp.Theorem1.bestError] using h

/-- Enlarging either radius can only decrease the best approximation error. -/
theorem bestError_antitone [DecidableEq S] [DecidableEq A] (M : MDP S A) (Φ : S → H)
    {C B C' B' : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hCC : C ≤ C') (hBB : B ≤ B') :
    Kadp.Theorem1.bestError M Φ C' B' ≤ Kadp.Theorem1.bestError M Φ C B := by
  obtain ⟨p,hp⟩ := Kadp.Theorem1.exists_best_fit M Φ hC hB
  let q : Kadp.Idealized.Parameters H C' B' := ⟨p.val,p.property.1.trans hCC,p.property.2.trans hBB⟩
  rw [hp]
  exact ciInf_le (f := fun u : Kadp.Idealized.Parameters H C' B' =>
    ‖Kadp.Approximation.optimalCost M - Kadp.Idealized.fit Φ u‖)
    ⟨0,Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ q

end
end Kadp.Regularization
