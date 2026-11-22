# Checking the Kernel ADP proofs

Each proof has its own self-contained LaTeX source and PDF in `proofs/`, with a link to the corresponding Lean theorem.

**Strong duality for sampled value-function approximation.** The proof recovers a primal optimizer from any dual minimizer, works through an example at the penalty threshold, and explains the corrections to Proposition 1. [PDF](proofs/proposition-1.pdf) · [LaTeX source](proofs/proposition-1.tex) · [Lean theorem](Kadp/PrimalAttainment.lean)

**Kernel evaluation and the greedy policy.** The kernel program recovers the fitted value up to its intercept and gives every greedy action, including ties. A two-state example shows why the current state belongs in the neighborhood used to compute the coefficients. [PDF](proofs/kernel-policy.pdf) · [LaTeX source](proofs/kernel-policy.tex) · [Lean theorem](Kadp/KernelPolicy.lean) · [Checked example](Kadp/Examples/KernelPolicy.lean)

**Discounted state occupancy and the Bellman residual.** For any fixed policy, the discounted state distribution uniquely solves a balance equation. Averaging signed residuals under this distribution recovers the expected initial value error. The two-state example computes both sides. [PDF](proofs/discounted-occupancy.pdf) · [LaTeX source](proofs/discounted-occupancy.tex) · [Lean theorems](Kadp/Occupancy.lean) · [Checked example](Kadp/Examples/Occupancy.lean)

On macOS with Homebrew, install Elan once. It provides the `lean` and `lake` commands and selects the Lean version from this project's `lean-toolchain` file. [Homebrew formula](https://formulae.brew.sh/formula/elan-init)

```sh
brew install elan-init
```

From the `kadp` directory, run these commands for a fresh checkout. The first command downloads the pinned Lean toolchain if needed. The second fetches the compiled mathlib modules used by the project. [Lean project documentation](https://leanprover-community.github.io/install/project.html)

```sh
lean --version
lake exe cache get \
  Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Data.Fintype.BigOperators \
  Mathlib.Tactic.Linarith Mathlib.Tactic.Module Mathlib.Tactic.NormNum Mathlib.Tactic.Ring \
  Mathlib.LinearAlgebra.Matrix.Stochastic Mathlib.LinearAlgebra.Matrix.NonsingularInverse \
  Mathlib.Topology.Algebra.Module.FiniteDimension Mathlib.Topology.Algebra.InfiniteSum.Module \
  Mathlib.Algebra.BigOperators.Intervals Mathlib.Topology.MetricSpace.Contracting \
  Mathlib.Dynamics.FixedPoints.Basic Mathlib.Analysis.SpecificLimits.Basic
lake build
```

After editing a proof, run `lake build` again. To replay all project declarations through Lean's kernel, run `lake env leanchecker --verbose Kadp`.

To inspect the assumptions behind the main results, run the command below. Lean reports `propext`, `Classical.choice`, and `Quot.sound`.

```sh
printf '%s\n' 'import Kadp' '#print axioms Kadp.SampledRSALP.strongDuality' '#print axioms Kadp.SampledRSALP.kernelPolicy_of_optima' '#print axioms Kadp.Occupancy.hasSum_occupancy' '#print axioms Kadp.Occupancy.residual_identity' | lake env lean --stdin
```

The [claim index](audit/claims.md) maps the verified results, counterexamples and open claims to their evidence. The [plan](PLAN.md) covers the remaining work.

Each note builds independently from the repository root with Tectonic.

```sh
tectonic proofs/proposition-1.tex
tectonic proofs/kernel-policy.tex
tectonic proofs/discounted-occupancy.tex
```
