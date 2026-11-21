# Checking the Kernel ADP proofs

The [proof note](proofs/proposition-1.pdf) states the printed Proposition 1, gives two counterexamples, and proves a replacement with the exact penalty threshold and corrected dual objective. The general attainment argument is on page 4. [LaTeX source](proofs/proposition-1.tex) · [Lean counterexamples](Kadp/Examples/Proposition1.lean) · [Lean duality results](Kadp/Duality.lean)

On macOS with Homebrew, install Elan once. It provides the `lean` and `lake` commands and selects the Lean version from this project's `lean-toolchain` file. [Homebrew formula](https://formulae.brew.sh/formula/elan-init)

```sh
brew install elan-init
```

From the `kadp` directory, run these commands for a fresh checkout. The first command downloads the pinned Lean toolchain if needed. The second fetches the compiled mathlib modules used in step 1. [Lean project documentation](https://leanprover-community.github.io/install/project.html)

```sh
lean --version
lake exe cache get Mathlib.Analysis.InnerProductSpace.Basic Mathlib.Data.Fintype.BigOperators Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum
lake build
```

After editing a proof, run `lake build` again. To replay all project declarations through Lean's kernel, run `lake env leanchecker --verbose Kadp`.

The [claim index](audit/claims.md) gives the two counterexamples and their Lean theorem names. The [plan](PLAN.md) covers the remaining work.

To rebuild the PDF from the repository root, run `tectonic proofs/proposition-1.tex`.
