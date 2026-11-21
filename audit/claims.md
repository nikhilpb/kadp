# Claim index for the Kernel ADP manuscript

Page numbers below are the printed pages of the August 29, 2022 version. Status refers to the statement in that version. The evidence for Proposition 1 uses the [general program definitions](../Kadp/SampledRSALP.lean) and their [one-state instantiations](../Kadp/Examples/Proposition1.lean). [Manuscript](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf)

## Shared hypotheses and notation

- **Model.** Finite nonempty state and action spaces, stochastic transition rows, a real cost $g$, and $0<\alpha<1$. Features take values in a real Hilbert space. The value approximation is $J(x)=\langle\Phi(x),z\rangle+b$.
- **Sampled programs.** Equations (6) and (9) use $N>0$ draws from a positive distribution $\pi$, weights $w=\nu/\pi$, and $\Gamma,\kappa>0$. The Lean model normalizes $\nu$ as in §2.5. Both witnesses also satisfy the broader positive-weight convention on p. 5. Indexing by draw retains multiplicities. Both examples have a single possible draw of probability one.
- **Idealized program.** For (18), $\nu$ is a distribution, $\mu^*$ is optimal, and the draws are independent from its discounted occupancy $\pi_{\mu^*,\nu}$ in (17). The admissible parameters obey $\|z\|\le C$ and $|b|\le B$. Define $K=\max_x\|\Phi(x)\|$, $D=4CK(1+\alpha)+4B(1-\alpha)+2\|g\|_\infty$, and $\Xi=D(1+\sqrt{2\ln(1/\delta)})$. In the rows below, the sample threshold is $N\ge\Xi^2/\epsilon^2$. Theorems 1 and 2 print $\epsilon,\delta>0$. Check the domain of the square root and degenerate envelopes when formalizing the probability claims.
- **Classes.** With fixed policy $\mu$, write $L_\mu$ for the linear class in Lemma 2, $F_\mu$ for $(J-T_\mu J)^+$ and $F$ for $(J-TJ)^+$ with the admissible parameters above. $P$ and $P_N$ are population and empirical means. $R_N$ is the paper's expected one-sided Rademacher complexity with factor $2/N$.

## Numbered results

| Claim | Hypotheses and conclusion | Proof dependencies | Status |
| --- | --- | --- | --- |
| Proposition 1, p. 8 | For the sampled programs, both optima are finite, attained and equal. An optimal multiplier recovers a primal weight by (10). | (6)–(10), Appendix A | **Refuted as printed.** A replacement has a written proof. Its Lean verification status is detailed below. |
| Theorem 1, p. 13 | At the sample threshold, an optimizer of (18) has $\nu$-weighted absolute error bounded by $(3+\alpha)/(1-\alpha)$ times the best admissible sup-norm error plus $4\epsilon/(1-\alpha)$, with probability at least $1-\delta-\delta^4$. | Theorem 2 with $\psi=1$ | Open |
| Proposition 2, p. 18 | Every feasible suboptimal point of (9) admits a feasible strict descent direction with exactly two nonzero coordinates. | Gram positivity in (7), row caps, mass equality, Lemma 4 and Appendix D | Open |
| Theorem 2, p. 28 | Same optimizer, sample threshold and confidence as Theorem 1. Bound (25) takes the infimum over admissible $z,b$ and $\psi\ge1$ of the weighted sup-error times $\nu^\top\psi+2(\pi_{\mu^*,\nu}^\top\psi)(1+\alpha\beta(\psi))/(1-\alpha)$, then adds $4\epsilon/(1-\alpha)$. Here $\beta(\psi)=\max_{x,a}(P_a\psi)(x)/\psi(x)$. | (17), (18), (26), Lemma 3, Theorem 3, SALP residual bounds | Open |
| Lemma 1, p. 29 | For an i.i.d. sample and class uniformly bounded in absolute value by $B$, the event $\sup_f(Pf-P_N f)\ge R_N+\sqrt{2B^2\ln(1/\delta)/N}$ has probability at most $\delta$. | Appendix C, symmetrization and bounded differences | Open |
| Lemma 2, p. 29 | For a fixed policy $\mu$, feature bound $K$ and radius $C$, $L_\mu$ pairs $z$ with $\Phi(x)-\alpha E[\Phi(X')\mid x,\mu(x)]$. Its complexity is at most $2CK(1+\alpha)/\sqrt N$. | Signed Hilbert-space sum, norm bound | Open |
| Corollary 1, p. 30 | Under the class and sampling assumptions, $R_N(F_\mu)\le D/\sqrt N$. | Lemma 2, offset class and contraction | Open |
| Lemma 3, p. 30 | For each fixed $f$ in either residual class, $\|f\|_\infty\le D/2$. At the sample threshold, $\Pr(P_Nf-Pf\ge\epsilon)\le\delta^4$. | Pointwise envelope, Hoeffding's inequality | Open |
| Theorem 3, p. 30 | At the sample threshold and for fixed $\mu$, $\Pr(\sup_{f\in F_\mu}(Pf-P_N f)\ge\epsilon)\le\delta$. | Lemmas 1 and 3, Corollary 1 | Open |
| Lemma 4, p. 34 | For real finite vectors with $\sum_i x_i=0$ and $x^\top y<0$, there are $i,j$ with $y_i<y_j$, $x_i>0$ and $x_j<0$. | Positive and negative parts of a zero-sum vector | Open |

## Proposition 1 witnesses

Both instances use one state, action and draw, unit transition and distribution masses, the real feature space with feature value zero, $\alpha=1/2$ and $\Gamma=2$. The general definitions reduce the primal to maximizing $b-\kappa s-z^2$ subject to $s\ge0$ and $b\le g+b/2+s$. The dual minimizes $2g\lambda$ subject to $0\le\lambda\le\kappa$ and $\lambda=2$. The four declarations below are in `Kadp.Examples.Proposition1`.

| Case | Failed conclusion | Lean evidence |
| --- | --- | --- |
| $g=0$, $\kappa=1$ | The primal has no finite upper bound and the dual feasible set is empty. | `primal_unbounded`, `dual_infeasible` |
| $g=1$, $\kappa=4$ | The primal maximum is $2$ and the dual minimum is $4$. Both are attained. | `primal_maximum_two`, `dual_minimum_four` |

**Replacement proposition.** Below $\kappa=1/(1-\alpha)$, the primal is unbounded and the dual infeasible for every realized sample. At or above the threshold, both optima are attained, the normalized dual value equals the primal maximum, and every minimizing multiplier recovers the unique optimal primal weight by (10). Pages 3–4 derive the objective, prove the result, and work an equality-case example with nonzero features. [Proof note](../proofs/proposition-1.pdf)

**Lean verification.** In `Kadp.SampledRSALP`, `dualFeasible_iff_penalty` proves the sharp feasibility threshold, and `primal_unbounded_of_penalty_lt` proves the general unboundedness result. `dualObjective_normalization` proves the scale and offset identity with printed (9). `exists_dual_minimizer` proves attainment of the corrected dual minimum. `dualityGap`, `weakDuality`, and `recoveredWeight_of_equal_values` prove the exact gap identity, upper bound, and recovery for a feasible pair with equal values. **Open in Lean:** construct a feasible primal point attaining that upper bound for a minimizing multiplier, including tied costs and fully saturated rows at the threshold. [Lean declarations](../Kadp/Duality.lean)

**Downstream effects.** Positive affine normalization preserves the optimizer, the improving directions and the stopping criterion for the QP of §4. In §2.5, dropping the additive constant is valid for computing a policy. Use (10) and the coefficients of (7)–(8) as the reference when checking the kernel formulas (11)–(14). The experiment on p. 20 uses $\kappa=2/(1-\alpha)$, which clears the threshold. The approximation theorem uses the distinct program (18) and still needs its own proof audit. [Algorithm](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=10) · [Approximation guarantee](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=12) · [Experiment](https://moallemi.com/ciamac/papers/kernel-adp-2012.pdf#page=20)

## Unnumbered claims to audit

| Location | Claim and assumptions to check | Status |
| --- | --- | --- |
| §2.1 and (1), p. 5 | The optimal policy and Bellman LP represent the same value under positive relevance weights. Resolve the policy's printed maximization convention against cost minimization. | Open |
| §2.3–2.5, pp. 7–10 | (7) gives a positive semidefinite Gram matrix. Equations (11)–(14) recover the sampled coefficients and policy from the multiplier. Check indices, weights and invariance of greedy actions to the offset. | Open |
| §3.1, p. 11 | For each $\Gamma>0$ some $C\ge0$ gives (5) and (15) the same optimal solutions and values for sufficiently large $B$. Full feature rank gives zero best approximation error for a sufficiently large radius. | Open |
| §3.2, pp. 12–13 | (17) defines a probability distribution. The discussion after (18) gives a sufficient size of $B$ for the offset constraint to be nonbinding. | Open |
| §4.1–4.2, pp. 15–18 | The pair selection rule solves (20), and absence of a feasible improving pair certifies optimality. | Open |
| Appendix B.2, pp. 31–32 | Feasibility of the comparator and the residual inequalities in (26) yield the weighted error bound. Check the sign of the comparator slack. | Open |
| Appendix B.3, pp. 32–33 | The empirical total-variation term controls the change of sampling law. The likelihood-ratio version also requires a coupling and a quantified high-probability statement. | Open |
