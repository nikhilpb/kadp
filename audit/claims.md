# Claim index for the Kernel ADP manuscript

Page numbers below are the printed pages of the August 29, 2022 version. Status refers to the statement in that version. The evidence for Proposition 1 uses the [general program definitions](../Kadp/SampledRSALP.lean) and their [one-state instantiations](../Kadp/Examples/Proposition1.lean). [Manuscript](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf)

## Shared hypotheses and notation

- **Model.** Finite nonempty state and action spaces, stochastic transition rows, a real cost $g$, and $0<\alpha<1$. Features take values in a real Hilbert space. The value approximation is $J(x)=\langle\Phi(x),z\rangle+b$.
- **Sampled programs.** Equations (6) and (9) use $N>0$ draws from a positive distribution $\pi$, weights $w=\nu/\pi$, and $\Gamma,\kappa>0$. The theorem allows arbitrary strictly positive relevance weights $\nu$, including the distribution convention in §2.5. Indexing by draw retains multiplicities. Both examples have a single possible draw of probability one.
- **Idealized program.** For (18), $\nu$ is a distribution, $\mu^*$ is optimal, and the draws are independent from its discounted occupancy $\pi_{\mu^*,\nu}$ in (17). The admissible parameters obey $\|z\|\le C$ and $|b|\le B$. Define $K=\max_x\|\Phi(x)\|$, $D=4CK(1+\alpha)+4B(1-\alpha)+2\|g\|_\infty$, and $\Xi=D(1+\sqrt{2\ln(1/\delta)})$. In the rows below, the sample threshold is $N\ge\Xi^2/\epsilon^2$. Theorems 1 and 2 print $\epsilon,\delta>0$. The proof uses $0<\delta<1$ for the square root and handles $D=0$ directly. For $\delta\ge1$ the probability lower bound in (19) is nonpositive.
- **Classes.** With fixed policy $\mu$, write $L_\mu$ for the linear class in Lemma 2, $F_\mu$ for $(J-T_\mu J)^+$ and $F$ for $(J-TJ)^+$ with the admissible parameters above. $P$ and $P_N$ are population and empirical means. $R_N$ is the paper's expected one-sided Rademacher complexity with factor $2/N$.

## Numbered results

| Claim | Hypotheses and conclusion | Proof dependencies | Status |
| --- | --- | --- | --- |
| Proposition 1, p. 8 | For the sampled programs, both optima are finite, attained and equal. An optimal multiplier recovers a primal weight by (10). | (6)–(10), Appendix A | **Refuted as printed.** The replacement is proved in Lean, including equality at the threshold. |
| Theorem 1, p. 13 | At the sample threshold, an optimizer of (18) has $\nu$-weighted absolute error bounded by $(3+\alpha)/(1-\alpha)$ times the best admissible sup-norm error plus $4\epsilon/(1-\alpha)$, with probability at least $1-\delta-\delta^4$. | Discounted occupancy, optimality in (18), uniform fixed-policy deviation, Bellman contraction | **Proof gap with a repaired proof.** The original guarantee follows from the stronger result below. [Theorem and proof](../proofs/theorem-1.pdf) · [Lean](../Kadp/Theorem1.lean) |
| Proposition 2, p. 18 | Every feasible suboptimal point of (9) admits a feasible strict descent direction with exactly two nonzero coordinates. | Gram positivity in (7), row caps, mass equality, Lemma 4 and Appendix D | Open |
| Theorem 2, p. 28 | Same optimizer, sample threshold and confidence as Theorem 1. Bound (25) takes the infimum over admissible $z,b$ and $\psi\ge1$ of the weighted sup-error times $\nu^\top\psi+2(\pi_{\mu^*,\nu}^\top\psi)(1+\alpha\beta(\psi))/(1-\alpha)$, then adds $4\epsilon/(1-\alpha)$. Here $\beta(\psi)=\max_{x,a}(P_a\psi)(x)/\psi(x)$. | (17), (18), (26), Lemma 3, Theorem 3, SALP residual bounds | Open |
| Lemma 1, p. 29 | For an i.i.d. sample and class uniformly bounded in absolute value by $B$, the event $\sup_f(Pf-P_N f)\ge R_N+\sqrt{2B^2\ln(1/\delta)/N}$ has probability at most $\delta$. | Appendix C, symmetrization and bounded differences | The finite-state consequence used in (19) is proved. The general statement and its endpoint cases remain open. |
| Lemma 2, p. 29 | For a fixed policy $\mu$, feature bound $K$ and radius $C$, $L_\mu$ pairs $z$ with $\Phi(x)-\alpha E[\Phi(X')\mid x,\mu(x)]$. Its complexity is at most $2CK(1+\alpha)/\sqrt N$. | Signed Hilbert-space sum, norm bound | **Proved.** The empirical bound holds for each draw, hence also after expectation. See the normalization below. |
| Corollary 1, p. 30 | Under the class and sampling assumptions, $R_N(F_\mu)\le D/\sqrt N$. | Lemma 2, offset class and contraction | **Proved.** The empirical bound below implies the printed constant. |
| Lemma 3, p. 30 | For each fixed $f$ in either residual class, $\|f\|_\infty\le D/2$. At the sample threshold, $\Pr(P_Nf-Pf\ge\epsilon)\le\delta^4$. | Pointwise residual envelopes, bounded differences | **Proved** for both classes on the finite state space. Includes the zero envelope. |
| Theorem 3, p. 30 | At the sample threshold and for fixed $\mu$, $\Pr(\sup_{f\in F_\mu}(Pf-P_N f)\ge\epsilon)\le\delta$. | Lemmas 1 and 3, Corollary 1 | The good event $\forall f,\ Pf-P_N f\le\epsilon$ required for (19) is proved. A separate assertion for the printed $\ge\epsilon$ failure event remains open. |
| Lemma 4, p. 34 | For real finite vectors with $\sum_i x_i=0$ and $x^\top y<0$, there are $i,j$ with $y_i<y_j$, $x_i>0$ and $x_j<0$. | Positive and negative parts of a zero-sum vector | Open |

## Proposition 1 witnesses

Both instances use one state, action and draw, unit transition and distribution masses, the real feature space with feature value zero, $\alpha=1/2$ and $\Gamma=2$. The general definitions reduce the primal to maximizing $b-\kappa s-z^2$ subject to $s\ge0$ and $b\le g+b/2+s$. The dual minimizes $2g\lambda$ subject to $0\le\lambda\le\kappa$ and $\lambda=2$. The four declarations below are in `Kadp.Examples.Proposition1`.

| Case | Failed conclusion | Lean evidence |
| --- | --- | --- |
| $g=0$, $\kappa=1$ | The primal has no finite upper bound and the dual feasible set is empty. | `primal_unbounded`, `dual_infeasible` |
| $g=1$, $\kappa=4$ | The primal maximum is $2$ and the dual minimum is $4$. Both are attained. | `primal_maximum_two`, `dual_minimum_four` |

**Replacement proposition.** Assume $\kappa\ge 1/(1-\alpha)$. Both optima are attained, the normalized dual value equals the primal maximum, and every minimizing multiplier recovers the unique optimal primal weight by (10). The standalone proof note defines the programs, proves the theorem, and works an equality-case example with nonzero features. Its closing comparison gives the conversion between the objectives. [Standalone proof](../proofs/proposition-1.pdf)

**Lean verification.** The main theorem `Kadp.SampledRSALP.strongDuality` proves attainment, value equality and recovery under the penalty hypothesis. The companion theorem `correctedProposition1` also records unboundedness and dual infeasibility below the threshold.

| Step | Declaration |
| --- | --- |
| Feasibility threshold and unboundedness below it | `dualFeasible_iff_penalty`, `primal_unbounded_of_penalty_lt` in [Duality](../Kadp/Duality.lean) |
| Normalization, dual attainment, gap identity and weight recovery at zero gap | `dualObjective_normalization`, `exists_dual_minimizer`, `dualityGap`, `recoveredWeight_of_equal_values` in [Duality](../Kadp/Duality.lean) |
| Allocate the required mass under row caps, including ties and full capacity | `Kadp.exists_cutoff_allocation` in [Allocation](../Kadp/Allocation.lean) |
| Construct a feasible intercept and slacks for every minimizing multiplier | `primal_attains_of_dual_minimizer` in [PrimalAttainment](../Kadp/PrimalAttainment.lean) |
| Apply the result directly to a minimizer of the printed QP (9) | `dualObjective_le_iff`, `primal_attains_of_printed_dual_minimizer` in [PrimalAttainment](../Kadp/PrimalAttainment.lean) |

**Downstream effects.** Positive affine normalization preserves the optimizer, the improving directions and the stopping criterion for the QP of §4. In §2.5, dropping the additive constant is valid for computing a policy. The kernel proof below derives (11)–(14) from (7), (8) and (10). The experiment on p. 20 uses $\kappa=2/(1-\alpha)$, which clears the threshold. Theorem 1 uses the distinct program (18) and is proved independently below. [Algorithm](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=10) · [Approximation guarantee](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=12) · [Experiment](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=20)

## Kernel evaluation and the greedy policy

For a realized finite sample and a real feature kernel, (12) and (13) are the Gram and linear coefficients of the dual. Under the penalty condition of the replacement proposition, every kernel minimizer gives the same greedy action set as every optimal primal fit at every state. This includes ties and queries outside the sample. [Standalone proof](../proofs/kernel-policy.pdf) · [General Lean proofs](../Kadp/KernelPolicy.lean)

| Claim | Lean evidence |
| --- | --- |
| (12) and (13) agree with the feature coefficients, and the matrix is positive semidefinite | `kernelGram_eq`, `kernelLinear_eq`, `kernelGram_psd` |
| Setting the additive constant to zero preserves the minimizing set, and a minimum exists | `kernelObjective_add_constant`, `kernelObjective_normalization`, `exists_kernel_minimizer` |
| (11) and (14) differ by the intercept, and optimal fits agree on all greedy actions | `value_recovered_eq_kernel`, `actionScore_add_const`, `kernelPolicy_of_optima` |

**Neighborhood correction.** Section 2.3 includes the current state in each neighborhood. Section 2.5 describes only states reachable with positive probability. In the two-state witness, the sampled state has no self-transition under action $B$. Omitting the current state changes $Q(s,B,s,B)$ from $0$ to $1$ and $R(s,B)$ from $1$ to $5/2$. The formal witness is `successors_only_changes_coefficients`. [Checked example](../Kadp/Examples/KernelPolicy.lean) · [Neighborhood definition](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=7) · [Algorithm summary](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=10)

## Discounted occupancy and the signed residual

**Equation (17) holds as printed.** Let $P_\mu$ be the row-stochastic transition matrix of a fixed policy in a finite MDP, $0<\alpha<1$, and $\nu$ any initial probability vector. The two expressions for $\pi_{\mu,\nu}$ agree, their entries are nonnegative and sum to one, and the balance equation has a unique real row solution. For every candidate $J$, the signed initial error is $\nu^\top(J-J_\mu)=\pi_{\mu,\nu}^\top(J-T_\mu J)/(1-\alpha)$. Taking an optimal policy recovers the paper’s sampling law. [Occupancy lemma in the Theorem 1 writeup](../proofs/theorem-1.pdf) · [Lean module](../Kadp/Occupancy.lean)

| Claim | Lean declarations in `Kadp.Occupancy` |
| --- | --- |
| Inverse formula and convergence of the discounted visit series | `discountedOccupancy`, `hasSum_occupancy` |
| Probability, balance and uniqueness | `occupancy_isDistribution`, `occupancy_balance`, `occupancy_unique` |
| Reward-to-cost translation, fixed point and uniqueness | `ofCosts`, `costBellman_eq_neg_reward`, `costBellman_policyCost`, `policyCost_unique` |
| Signed initial error and occupancy-weighted Bellman residual | `residual_identity` |

**Proof reuse.** Robert Kirkby’s LeanEconomics chapter (Apache-2.0, commit `9d4783f3fb282444f8f3a91c4e6439293dd4bacc`) declares Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Its unmodified `Basics` and `MDP` modules built and replayed on this project's Lean 4.32.0 and mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`. The proof reuses `MDP.vσ_eq_inv` and `MDP.vσ_eq_tsum` with a state indicator to recover each resolvent column, and `MDP.isUnit_one_sub_smul_Pσ` to prove uniqueness. The cost adapter gives every action to every state and sets the reward to the negative cost. [Pinned upstream source](https://github.com/LeanEconomics/DynamicProgramming/blob/9d4783f3fb282444f8f3a91c4e6439293dd4bacc/FiniteStates/MarkovDecisionProcesses/MarkovDecisionProcesses/MDP.lean)

**Two-state check.** Starting at $s$, the occupancy row is $(2/3,1/3)$. The residuals $3/4$ and $-1$ give a weighted mean of $1/6$. With $\alpha=1/2$, the expected initial error is $1/3$. [Lean example](../Kadp/Examples/Occupancy.lean)

## Theorem 1 and the comparator slack

**The guarantee survives the sign correction.** The least feasible slack for a comparison function $V$ at draw $i$ is $(V-TV)_+(X_i)$. Appendix B.2 reverses this difference. With one state and action, zero cost, $\alpha=1/2$, and $V=1$, the printed slack is zero while feasibility requires at least $1/2$. [Checked witness](../Kadp/Examples/Theorem1.lean)

Every draw has an optimizer. On one event of probability at least $1-\delta$, every optimizer obeys (19) with additive error $2\epsilon/(1-\alpha)$ at the original sample size. The comparator residual is at most $(1+\alpha)\|J^*-V\|_\infty$ at every state. Only the fitted function's residual under the fixed optimal policy needs a uniform concentration bound. The weighted comparator in Theorem 2 requires a different estimate. [Self-contained proof](../proofs/theorem-1.pdf)

| Step | Lean evidence |
| --- | --- |
| Positive-part residual propagation, slack elimination, pathwise bound | `positive_error_le_resolvent`, `slackFeasible_iff`, `oracle_bound` in [Approximation](../Kadp/Approximation.lean) |
| Existence in an arbitrary feature Hilbert space | `compact_fits` in [Idealized](../Kadp/Idealized.lean), `exists_optimizer`, `exists_best_fit` in [Theorem1](../Kadp/Theorem1.lean) |
| Lemma 2 and Corollary 1 | `empirical_linear_le`, `empirical_residual_le`, `empirical_negative_residual_le` in [ResidualComplexity](../Kadp/ResidualComplexity.lean). With the paper's $2/N$ normalization, the residual complexity is at most $2[CK(1+\alpha)+B(1-\alpha)]/\sqrt N$. |
| Lemma 3 and uniform sampling | `abs_residual_le` in [Idealized](../Kadp/Idealized.lean), `abs_bellmanResidual_le` in [Theorem1](../Kadp/Theorem1.lean), `fixed_comparator_tail` and `uniform_population_le_empirical` in [UniformDeviation](../Kadp/UniformDeviation.lean) |
| Equation (19) and the sharper guarantee | `theorem1`, `strengthened` in [Theorem1](../Kadp/Theorem1.lean) |

**Proof reuse.** FoML (MIT, revision `db9f18714b0b9934553c37db1b41250462dc7faa`) supplies `hilbertPredictor_empiricalRademacherComplexity_le`, coordinatewise contraction, and the countable-class one-sided deviation theorem. Its normalization is $1/N$. To apply the last theorem to unrestricted parameters, select one violating fit for each possible failing sample. The resulting finite family is fixed over the whole sample space, has no greater complexity, and detects every failure. [Pinned FoML source](https://github.com/auto-res/lean-rademacher/tree/db9f18714b0b9934553c37db1b41250462dc7faa/FoML)

## Unnumbered claims to audit

| Location | Claim and assumptions to check | Status |
| --- | --- | --- |
| §2.1 and (1), p. 5 | The optimal policy and Bellman LP represent the same value under positive relevance weights. Resolve the policy's printed maximization convention against cost minimization. | Open |
| §2.3–2.5, pp. 7–10 | (7) gives a positive semidefinite Gram matrix. Equations (11)–(14) recover the sampled coefficients and policy from the multiplier. | **Proved as printed** in the finite-state feature model with the §2.3 neighborhood. The §2.5 prose needs the correction above. |
| §3.1, p. 11 | For each $\Gamma>0$ some $C\ge0$ gives (5) and (15) the same optimal solutions and values for sufficiently large $B$. Full feature rank gives zero best approximation error for a sufficiently large radius. | Open |
| §3.2, p. 12 | The inverse and series in (17) define the same probability distribution. | **Proved as printed.** See the discounted occupancy result above. |
| §3.2, p. 13 | The discussion after (18) gives a sufficient size of $B$ for the offset constraint to be nonbinding. | Open |
| §4.1–4.2, pp. 15–18 | The pair selection rule solves (20), and absence of a feasible improving pair certifies optimality. | Open |
| Appendix B.2, pp. 31–32 | Feasibility of the comparator and the residual inequalities in (26) yield the weighted error bound. Check the sign of the comparator slack. | **Comparator feasibility refuted as printed.** The corrected slack and the unweighted guarantee are proved. The weighted chain remains open. |
| Appendix B.3, pp. 32–33 | The empirical total-variation term controls the change of sampling law. The likelihood-ratio version also requires a coupling and a quantified high-probability statement. | Open |
