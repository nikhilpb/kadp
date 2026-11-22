# Kernel approximate dynamic programming

**[Read the complete results and proofs (PDF)](writeups/kernel-adp.pdf)** · [LaTeX source](writeups/kernel-adp.tex) · [Paper-to-Lean claim index](audit/claims.md)

The combined document develops the model, sampled dual, kernel policy, regularization, concentration bounds and active-set algorithm from common definitions. Its final section collects the corrections to the 2022 manuscript. Lean sources are in `lean/`. Importing `Kadp` makes the full library available with declarations in the `Kadp` namespace.

## Individual results

The self-contained notes in `writeups/` group supporting lemmas with the results they establish. Each note includes LaTeX, a PDF and links to the corresponding Lean proofs.

**Strong duality for sampled value-function approximation.** The proof recovers a primal optimizer from any dual minimizer, works through an example at the penalty threshold, and explains the corrections to Proposition 1. [PDF](writeups/proposition-1.pdf) · [LaTeX source](writeups/proposition-1.tex) · [Lean theorem](lean/PrimalAttainment.lean)

**Kernel evaluation and the greedy policy.** The kernel program recovers the fitted value up to its intercept and gives every greedy action, including ties. A two-state example shows why the current state belongs in the neighborhood used to compute the coefficients. [PDF](writeups/kernel-policy.pdf) · [LaTeX source](writeups/kernel-policy.tex) · [Lean theorem](lean/KernelPolicy.lean) · [Checked example](lean/Examples/KernelPolicy.lean)

**Theorem 1. Approximation guarantee for the sampled value function.** The probability bound (19) holds simultaneously for all optimizers of (18). At the same sample size, the proof gives confidence $1-\delta$ and additive error $2\epsilon/(1-\alpha)$. The note proves existence, explains why one concentration event suffices, and gives a one-state example of the comparator slack correction. [PDF](writeups/theorem-1.pdf) · [LaTeX](writeups/theorem-1.tex) · [Lean theorem](lean/Theorem1.lean) · [Slack example](lean/Examples/Theorem1.lean)

**Theorem 2. A weighted approximation guarantee.** Equation (25) holds at the published confidence and sample size, including when no weight attains its infimum. The proof selects a comparator before sampling. A two-state example shows how a weight reduces the bound for the same fitted value function. [PDF](writeups/theorem-2.pdf) · [LaTeX](writeups/theorem-2.tex) · [Lean theorem](lean/Theorem2.lean) · [Checked example](lean/Examples/Theorem2.lean)

**Theorem 3. Uniform concentration for the sampled residual.** For any fixed policy and state sampling law, the probability that the largest population-minus-sample residual deviation reaches $\epsilon$ is at most $\delta$. The note gives the corrected positive-envelope version of Lemma 1 and a zero-function counterexample to its unrestricted closed tail. [PDF](writeups/theorem-3.pdf) · [LaTeX](writeups/theorem-3.tex) · [Lean theorem](lean/Theorem3.lean)

**Proposition 2. Two-coordinate descent for the sampled dual.** Every suboptimal feasible point of (9) admits a strictly improving transfer. The note proves the stopping certificate and pair search, corrects the restricted objective (22), and gives a sampled problem on which the printed update stalls. [PDF](writeups/proposition-2.pdf) · [LaTeX](writeups/proposition-2.tex) · [Lean proposition](lean/ActiveSet.lean) · [Checked example](lean/Examples/Proposition2.lean)

**Bellman linear program.** The optimal policy minimizes cost from every state. The linear program uniquely recovers the optimal cost vector for positive relevance weights. [PDF](writeups/bellman-lp.pdf) · [Lean](lean/BellmanLP.lean)

**Penalized and constrained regularization.** The population programs share a weight at the matching radius. Their optimal values differ by the penalty on that weight. The proof includes attainment, the critical intercept ray and full-rank interpolation. [PDF](writeups/regularization.pdf) · [Lean](lean/Regularization.lean)

**The intercept in the sampled fit.** Optimal free intercepts are the medians of the sample breakpoints. The note gives a sufficient radius for all optimizers and a two-state counterexample to the printed threshold. [PDF](writeups/offset.pdf) · [Lean](lean/Offset.lean)

**Approximate sampling.** Quantified bounds apply to fits trained on a different state law. The proofs give the empirical coupling, weighted bounds and a counterexample to the proposed empirical likelihood-ratio inequality. [PDF](writeups/sampling-law.pdf) · [Transport and counterexample](lean/SamplingLaw.lean) · [Empirical coupling](lean/SamplingCoupling.lean) · [Weighted bounds](lean/WeightedSampling.lean)

## Reproduce the proofs

On macOS with Homebrew, install Elan once. It provides the `lean` and `lake` commands and selects the Lean version from this project's `lean-toolchain` file. [Homebrew formula](https://formulae.brew.sh/formula/elan-init)

```sh
brew install elan-init
```

From the `kadp` directory, run these commands for a fresh checkout. The first command downloads the pinned Lean toolchain if needed. The second fetches the compiled mathlib modules used by the project. [Lean project documentation](https://leanprover-community.github.io/install/project.html)

```sh
lean --version
lake exe cache get Mathlib
lake build
```

After editing a proof, run `lake build` again. To replay every module in the project through Lean's kernel, run the following command from the repository root.

```sh
find lean -name '*.lean' | sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' | sort | xargs lake env leanchecker --verbose
```

To inspect the assumptions behind the main results, run the command below. Lean reports `propext`, `Classical.choice`, and `Quot.sound`.

```sh
printf '%s\n' 'import Kadp' '#print axioms Kadp.SampledRSALP.strongDuality' '#print axioms Kadp.SampledRSALP.kernelPolicy_of_optima' '#print axioms Kadp.Occupancy.hasSum_occupancy' '#print axioms Kadp.Occupancy.residual_identity' \
  '#print axioms Kadp.Theorem1.theorem1' '#print axioms Kadp.Theorem1.strengthened' \
  '#print axioms Kadp.Theorem2.theorem2' '#print axioms Kadp.Examples.Theorem2.infimum_not_attained' \
  '#print axioms Kadp.Theorem3.theorem3' '#print axioms Kadp.lemma1_populationDeviation_tail' \
  '#print axioms Kadp.SampledRSALP.proposition2' '#print axioms Kadp.Examples.Proposition2.printed22_stalls' \
  '#print axioms Kadp.BellmanLP.maximizes_iff' '#print axioms Kadp.Regularization.Data.supercritical_equivalence' \
  '#print axioms Kadp.Regularization.bestError_zero_of_full_rank' '#print axioms Kadp.Offset.boxedOptimizer_iff_free' \
  '#print axioms Kadp.SamplingLaw.tv_weighted_infimum' '#print axioms Kadp.SamplingLaw.ratio_weighted_infimum' \
  '#print axioms Kadp.SamplingLaw.Counterexample.coupling_failure_fitted' '#print axioms Kadp.SamplingCoupling.empirical_tv_positive_le' | lake env lean --stdin
```

The approximation proof reuses the Bellman contraction and optimal-policy results from LeanEconomics and the Hilbert predictor, contraction, and concentration results from FoML. The manifest fixes both revisions. [LeanEconomics](https://github.com/LeanEconomics/DynamicProgramming/tree/9d4783f3fb282444f8f3a91c4e6439293dd4bacc/FiniteStates/MarkovDecisionProcesses) · [FoML](https://github.com/auto-res/lean-rademacher/tree/db9f18714b0b9934553c37db1b41250462dc7faa)

## Build the writeups

Compile the combined document with Tectonic from the repository root. Each individual note in the same directory also compiles independently.

```sh
tectonic writeups/kernel-adp.tex
```

The [audit plan](PLAN.md) records the scope and verification procedure. The [claim index](audit/claims.md) links each numbered result and audited unnumbered claim to its proof or counterexample.
