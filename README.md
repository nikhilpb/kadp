# Checking the Kernel ADP proofs

The replacement for Proposition 1 is proved in Lean. For every realized sample, the primal is unbounded and the dual infeasible when $\kappa<1/(1-\alpha)$. At or above the threshold, both optima are attained and the corrected dual value equals the primal maximum. Every minimizing multiplier of the printed QP recovers the unique optimal primal weight. The four-page note states the original claim, gives two counterexamples, and proves the replacement. [Proof note](proofs/proposition-1.pdf) · [LaTeX source](proofs/proposition-1.tex) · [Main Lean theorem](Kadp/PrimalAttainment.lean)

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
printf '%s\n' 'import Kadp' '#print axioms Kadp.SampledRSALP.correctedProposition1' | lake env lean --stdin
```

The [claim index](audit/claims.md) maps the two counterexamples, the corrected proposition, and the open claims to their evidence. The [plan](PLAN.md) covers the remaining work.

To rebuild the PDF from the repository root, run `tectonic proofs/proposition-1.tex`.
