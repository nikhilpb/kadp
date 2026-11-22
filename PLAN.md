# Kernel ADP in Lean 4

The goal is to determine which guarantees in *Non-parametric Approximate Dynamic Programming via the Kernel Method* follow from the published hypotheses. For each result, produce a Lean proof of the printed claim or a precise account of where it fails. When a correction is needed, preserve the original statement, prove the correction separately, and track which later results depend on it.

The target is the 36-page manuscript by Nikhil Bhat, Vivek F. Farias, Ciamac C. Moallemi, and Andy T. Zheng dated **August 29, 2022**. All page and equation numbers below refer to that version. Its SHA-256 is `0adfc02a9f5de7cb76d1f89e77ecb6e33f5c6ee431f6516a2105c33c9d4263ec`. [Manuscript](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf)

## Start with Proposition 1

The cheapest informative first proof uses one state, one action, one observation, a self-transition, zero features, and $\nu=\pi=1$. Set $\alpha=1/2$ and $\Gamma=2$. Two choices of cost and penalty isolate two claims on p. 8.

| Test | Program (6) | Program (9) | Certified conclusion |
| --- | --- | --- | --- |
| $g=0$, $\kappa=1$ | For every $t\ge0$, choose $z=0$, $b=t$ and $s=t/2$. The objective is $t/2$. | The only multiplier would have to satisfy both $\lambda=2$ and $\lambda\le1$. | The primal is unbounded above and the dual is infeasible under the stated positive-penalty hypothesis. |
| $g=1$, $\kappa=4$ | The maximum is $2$, attained at $b=2$, $s=0$, $z=0$. The constraint $b\le2+2s$ gives the matching upper bound. | $\lambda=2$, $Q=0$, $R=2$ and the constant term is zero. The printed minimum is $4$. | Even with a feasible dual, a positive rescaling can preserve the optimizer while changing the optimal value. |

Lean verifies both examples against the definitions of (6) and (9). The replacement theorem below gives the exact penalty threshold and normalization. Theorem 1 has its own proof for the idealized program (18), so the effect on that guarantee is a separate mathematical question. [Programs (6)–(10)](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=7) · [Theorem 1](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=13)

## Existing Lean proofs to reuse

The proof package pins both upstream libraries. The LeanEconomics MDP, policy-evaluation and Bellman modules compile unmodified against the project's Lean and mathlib 4.32.0. FoML uses the same toolchain and provides the statistical learning results used in Theorem 1. [Pinned LeanEconomics source](https://github.com/LeanEconomics/DynamicProgramming/tree/9d4783f3fb282444f8f3a91c4e6439293dd4bacc/FiniteStates/MarkovDecisionProcesses) · [Pinned FoML source](https://github.com/auto-res/lean-rademacher/tree/db9f18714b0b9934553c37db1b41250462dc7faa)

| Paper obligation | Proof reused | Application |
| --- | --- | --- |
| Bellman equation, greedy optimal policy and discounted occupancy | LeanEconomics policy evaluation, optimality and contraction | Translate reward to negative cost and derive the discounted occupancy and error bounds. [Occupancy](Kadp/Occupancy.lean) · [Approximation](Kadp/Approximation.lean) |
| Gram positivity and finite feature span | mathlib inner products and orthogonal projection | Identify the kernel coefficients, project to the span of the state features for compactness, and allow an arbitrary ambient Hilbert space. [Kernel policy](Kadp/KernelPolicy.lean) · [Idealized program](Kadp/Idealized.lean) |
| Uniform one-sided deviation | FoML symmetrization and bounded differences | Negate the residuals, convert the normalization, and reduce violating samples to a fixed finite family. [Sampling estimate](Kadp/UniformDeviation.lean) |
| Linear predictors and positive parts | FoML Hilbert predictor and coordinatewise contraction | Bound the affine residual with its offset and state-dependent cost shift. [Empirical bounds](Kadp/ResidualComplexity.lean) |
| Fixed-comparator tail | FoML bounded-differences theorem | A residual in $[0,D/2]$ has upper-tail probability at most $\delta^4$ at the printed sample threshold. [Fixed comparator](Kadp/UniformDeviation.lean) |
| Dual attainment and recovery in Proposition 1 | mathlib compact extrema and finite row cutoffs | Prove the exact quadratic expansion on a feasible segment and allocate mass across tied costs. [Allocation](Kadp/Allocation.lean) · [Primal attainment](Kadp/PrimalAttainment.lean) |

## Work plan

Each milestone has a result that can be reviewed on its own.

**Step 1 completed on November 21, 2026.** Lean 4.32.0 checked all four conclusions for the two instances. The [claim index](audit/claims.md) records the evidence and the [setup guide](README.md) gives the commands to reproduce it. The upstream dependencies for the approximation guarantee have also been integrated.

**Replacement for Proposition 1 completed on November 22, 2026.** The theorem `strongDuality` assumes the sharp lower bound on the penalty and applies to every realized sample. The companion theorem `correctedProposition1` also covers penalties below the threshold. The allocation proof handles cost ties and fully saturated rows. [Lean theorem](Kadp/PrimalAttainment.lean) · [Standalone proof](proofs/proposition-1.pdf)

**Kernel evaluation and the greedy policy completed on November 22, 2026.** Equations (11)–(14) recover the coefficients, fitted values up to the intercept, and all greedy actions in the finite-state feature model. The §2.5 neighborhood description needs to include the current state, as in §2.3. A checked example shows that omitting it changes both the matrix and the linear coefficient. [Standalone proof](proofs/kernel-policy.pdf) · [Lean theorem](Kadp/KernelPolicy.lean) · [Checked example](Kadp/Examples/KernelPolicy.lean)

**Discounted occupancy completed on November 22, 2026.** The inverse and convergent series in (17) give a distribution, uniquely characterized by its balance equation. The signed residual identity holds for every fixed policy and initial distribution. The clean build compiled and kernel-checked the two imported LeanEconomics modules on the project pin. [Occupancy lemma in the Theorem 1 writeup](proofs/theorem-1.pdf) · [Lean proofs](Kadp/Occupancy.lean) · [Dependency and example](audit/claims.md#discounted-occupancy-and-the-signed-residual)

**Theorem 1 completed on November 22, 2026.** Lean proves existence for (18), the original bound (19), and a stronger result with confidence $1-\delta$ and additive error $2\epsilon/(1-\alpha)$. Bellman contraction bounds the comparator residual pointwise by its sup-norm approximation error. A single uniform deviation therefore suffices. The proof uses the corrected comparator slack $(V-TV)_+$. [Lean theorem](Kadp/Theorem1.lean) · [Self-contained writeup](proofs/theorem-1.pdf) · [Claim index and sign correction](audit/claims.md#theorem-1-and-the-comparator-slack)

1. **First two claims (complete).** The package pins Lean, mathlib and the upstream libraries. The claim index maps numbered results and substantive unnumbered claims to their status. The two one-state examples for Proposition 1 verify unboundedness, infeasibility and the two different attained values. [Witnesses](Kadp/Examples/Proposition1.lean)

2. **Upstream compatibility (complete for Theorem 1).** Both the Bellman translation and FoML deviation inequality are instantiated in the full theorem. The claim index records the revisions, licenses and adapters.

3. **Weighted Theorem 2 (complete).** Lean verifies the weighted Bellman estimate for all $\psi\ge1$, the corrected residual comparison (26), and (25) at the printed sample size, additive error and confidence. The comparator minimizing the continuous population criterion is fixed before sampling. A two-state example shows why the joint infimum must allow nonattainment. [Lean theorem](Kadp/Theorem2.lean) · [Standalone note](proofs/theorem-2.pdf) · [Claim index](audit/claims.md#theorem-2-and-the-infimum-over-weights)

4. **Audit the remaining auxiliary probability statements.** Theorems 1 and 2 are complete. The manuscript's separate Theorem 3 uses a non-strict failure event, while the uniform event proved for (19) and (25) bounds deviations by $\epsilon$. Check the equality case explicitly, together with the general scope and degenerate envelopes of Lemma 1. [Appendix B](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=28) · [Verified finite-state sampling results](Kadp/UniformDeviation.lean)

5. **Audit the kernel formulas and the active-set proof.** The coefficient and greedy-policy checks for (11)–(14) are complete for the finite-state feature model. Audit the §3.1 claim about penalized and radius-constrained optima, including the objective values. In `Kadp/ActiveSet.lean`, prove Lemma 4, then show that a suboptimal feasible point of (9) admits an improving feasible two-coordinate transfer. Within a state, the row sum stays fixed even when its cap is saturated. Across states, prove that the receiving row has room and the donating coordinate has positive mass. Prove that absence of a transfer certifies global optimality, and check that the §4.1 selection rule searches the necessary pairs. State the stopping certificate using only the feasible set and the quadratic objective of (9), so its proof is independent of Proposition 1's value normalization. A finite-iteration guarantee would require a separate proof. [Appendix A](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=26) · [Appendix D](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=34)

## What counts as an audit result

Use `audit/claims.md` to distinguish **proved as printed**, **proof gap with a repaired proof**, **refuted as printed**, and **open**. For a refutation, link a Lean witness satisfying every printed hypothesis, the failed conclusion, a proposed correction, and the downstream claims affected. For a proof gap, say whether the original statement survived. A missing library lemma stays open.

For each completed milestone, run `lake build` from a clean checkout and inspect `#print axioms` for its public results, including imported dependencies. A checked claim must be free of `sorryAx` and unproved project axioms. Keep the Appendix B.3 remark on approximate sampling in its own ledger entry, with its coupling and total-variation assumptions made explicit. The numerical queueing study in §5 is outside this proof audit. The final deliverables include the reproducible Lean package, the paper-to-Lean claim index, and a short errata report distinguishing effects on the main guarantee from effects on its proofs or on the algorithm.

Keep a separate, independently compilable LaTeX note and PDF for each main result in `proofs/`. Keep each supporting lemma with the main theorem that uses it. Define the notation and hypotheses in that note, give the proof, link the corresponding Lean declaration, and explain any correction to the paper.
