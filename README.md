# Checking the Kernel ADP proofs

The main proposition assumes $\kappa\ge 1/(1-\alpha)$. For every realized sample, the primal and normalized dual attain the same finite value. Every minimizing multiplier recovers the unique optimal primal weight. The standalone note proves the result and works through an example at equality. Its closing comparison explains the penalty hypothesis and how to convert the objective value of the printed quadratic program. [Proof note](proofs/proposition-1.pdf) · [LaTeX source](proofs/proposition-1.tex) · [Main Lean theorem](Kadp/PrimalAttainment.lean)

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

To rebuild the PDF from the repository root, run `tectonic proofs/proposition-1.tex`.
