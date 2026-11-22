# Checking the Kernel ADP proofs

The self-contained notes in `proofs/` group supporting lemmas with the results they establish. Each note includes LaTeX, a PDF and links to the corresponding Lean proofs.

**Strong duality for sampled value-function approximation.** The proof recovers a primal optimizer from any dual minimizer, works through an example at the penalty threshold, and explains the corrections to Proposition 1. [PDF](proofs/proposition-1.pdf) · [LaTeX source](proofs/proposition-1.tex) · [Lean theorem](Kadp/PrimalAttainment.lean)

**Kernel evaluation and the greedy policy.** The kernel program recovers the fitted value up to its intercept and gives every greedy action, including ties. A two-state example shows why the current state belongs in the neighborhood used to compute the coefficients. [PDF](proofs/kernel-policy.pdf) · [LaTeX source](proofs/kernel-policy.tex) · [Lean theorem](Kadp/KernelPolicy.lean) · [Checked example](Kadp/Examples/KernelPolicy.lean)

**Theorem 1. Approximation guarantee for the sampled value function.** The probability bound (19) holds simultaneously for all optimizers of (18). At the same sample size, the proof gives confidence $1-\delta$ and additive error $2\epsilon/(1-\alpha)$. The note proves existence, explains why one concentration event suffices, and gives a one-state example of the comparator slack correction. [PDF](proofs/theorem-1.pdf) · [LaTeX](proofs/theorem-1.tex) · [Lean theorem](Kadp/Theorem1.lean) · [Slack example](Kadp/Examples/Theorem1.lean)

**Theorem 2. A weighted approximation guarantee.** Equation (25) holds at the published confidence and sample size, including when no weight attains its infimum. The proof selects a comparator before sampling. A two-state example shows how a weight reduces the bound for the same fitted value function. [PDF](proofs/theorem-2.pdf) · [LaTeX](proofs/theorem-2.tex) · [Lean theorem](Kadp/Theorem2.lean) · [Checked example](Kadp/Examples/Theorem2.lean)

**Theorem 3. Uniform concentration for the sampled residual.** For any fixed policy and state sampling law, the probability that the largest population-minus-sample residual deviation reaches $\epsilon$ is at most $\delta$. The note gives the corrected positive-envelope version of Lemma 1 and a zero-function counterexample to its unrestricted closed tail. [PDF](proofs/theorem-3.pdf) · [LaTeX](proofs/theorem-3.tex) · [Lean theorem](Kadp/Theorem3.lean)

**Proposition 2. Two-coordinate descent for the sampled dual.** Every suboptimal feasible point of (9) admits a strictly improving transfer. The note proves the stopping certificate and pair search, corrects the restricted objective (22), and gives a sampled problem on which the printed update stalls. [PDF](proofs/proposition-2.pdf) · [LaTeX](proofs/proposition-2.tex) · [Lean proposition](Kadp/ActiveSet.lean) · [Checked example](Kadp/Examples/Proposition2.lean)

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

After editing a proof, run `lake build` again. To replay all project declarations through Lean's kernel, run `lake env leanchecker --verbose Kadp`.

To inspect the assumptions behind the main results, run the command below. Lean reports `propext`, `Classical.choice`, and `Quot.sound`.

```sh
printf '%s\n' 'import Kadp' '#print axioms Kadp.SampledRSALP.strongDuality' '#print axioms Kadp.SampledRSALP.kernelPolicy_of_optima' '#print axioms Kadp.Occupancy.hasSum_occupancy' '#print axioms Kadp.Occupancy.residual_identity' \
  '#print axioms Kadp.Theorem1.theorem1' '#print axioms Kadp.Theorem1.strengthened' \
  '#print axioms Kadp.Theorem2.theorem2' '#print axioms Kadp.Examples.Theorem2.infimum_not_attained' \
  '#print axioms Kadp.Theorem3.theorem3' '#print axioms Kadp.lemma1_populationDeviation_tail' \
  '#print axioms Kadp.SampledRSALP.proposition2' '#print axioms Kadp.Examples.Proposition2.printed22_stalls' | lake env lean --stdin
```

The approximation proof reuses the Bellman contraction and optimal-policy results from LeanEconomics and the Hilbert predictor, contraction, and concentration results from FoML. The manifest fixes both revisions. [LeanEconomics](https://github.com/LeanEconomics/DynamicProgramming/tree/9d4783f3fb282444f8f3a91c4e6439293dd4bacc/FiniteStates/MarkovDecisionProcesses) · [FoML](https://github.com/auto-res/lean-rademacher/tree/db9f18714b0b9934553c37db1b41250462dc7faa)

The [claim index](audit/claims.md) maps the verified results, counterexamples and open claims to their evidence. The [plan](PLAN.md) covers the remaining work.

Each note builds independently from the repository root with Tectonic.

```sh
tectonic proofs/proposition-1.tex
tectonic proofs/kernel-policy.tex
tectonic proofs/theorem-1.tex
tectonic proofs/theorem-2.tex
tectonic proofs/theorem-3.tex
tectonic proofs/proposition-2.tex
```
