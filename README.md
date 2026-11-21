# Checking the Kernel ADP proofs

*Kernel Approximate Dynamic Programming: Formalized Results and Corrections* collects the mathematical results from the paper as their proofs are checked in Lean. [Collected results (PDF)](proofs/kernel-adp-results.pdf) · [LaTeX source](proofs/kernel-adp-results.tex)

The first section proves strong duality for the sampled value-function approximation problem and recovers a primal optimizer from any dual minimizer. It includes a worked example and explains the corrections to the paper's Proposition 1. [Lean theorem](Kadp/PrimalAttainment.lean)

On macOS with Homebrew, install Elan once. It provides the `lean` and `lake` commands and selects the Lean version from this project's `lean-toolchain` file. [Homebrew formula](https://formulae.brew.sh/formula/elan-init)

```sh
brew install elan-init
```

From the `kadp` directory, run these commands for a fresh checkout. The first command downloads the pinned Lean toolchain if needed. The second fetches the compiled mathlib modules used by the project. [Lean project documentation](https://leanprover-community.github.io/install/project.html)

```sh
lean --version
lake exe cache get Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Data.Fintype.BigOperators Mathlib.Tactic.Linarith Mathlib.Tactic.Module Mathlib.Tactic.NormNum Mathlib.Tactic.Ring
lake build
```

After editing a proof, run `lake build` again. To replay all project declarations through Lean's kernel, run `lake env leanchecker --verbose Kadp`.

To inspect the assumptions behind the replacement theorem, run the command below. Lean reports `propext`, `Classical.choice`, and `Quot.sound`.

```sh
printf '%s\n' 'import Kadp' '#print axioms Kadp.SampledRSALP.strongDuality' | lake env lean --stdin
```

The [claim index](audit/claims.md) maps the two counterexamples, the corrected proposition, and the open claims to their evidence. The [plan](PLAN.md) covers the remaining work.

To rebuild the PDF from the repository root, run `tectonic proofs/kernel-adp-results.tex`.
