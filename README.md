<p align="center">
  <a href="https://timon.gutleb.com/LeanFun/">
    <img src="assets/leanfun-revolver-readme.png" alt="Click for the LeanFun RevOLVER" width="300">
  </a>
</p>

<p align="center">
  <a href="https://github.com/TSGut/LeanFun/actions/workflows/ci.yml">
    <img src="https://github.com/TSGut/LeanFun/actions/workflows/ci.yml/badge.svg?branch=main" alt="LeanFun and RevOLVER CI">
  </a>
  <a href="LICENSE">
    <img src="https://img.shields.io/badge/License-MIT-blue.svg" alt="License: MIT">
  </a>
  <a href="https://doi.org/10.5281/zenodo.23590194">
    <img src="https://zenodo.org/badge/DOI/10.5281/zenodo.23590194.svg" alt="DOI">
  </a>
</p>

LeanFun is an experimental [Lean 4](https://lean-lang.org/) library for orthogonal polynomials, special functions and spectral
approximation, built on [Mathlib](https://github.com/leanprover-community/mathlib4). It formalises the mathematics behind methods used
in [Chebfun](https://www.chebfun.org/) and
[ApproxFun](https://github.com/JuliaApproximation/ApproxFun.jl): polynomial bases,
spectral expansions, structured operators, interpolation and quadrature.

This repository hosts two things:

- **LeanFun**, the Lean formalisation itself: definitions, theorems and
  machine-checked proofs.
- **The LeanFun RevOLVER**, a living, browsable book grown from the project's
  leanblueprint graph. Expository prose is written around the blueprint's
  dependency graph, and every stated result links to its checked Lean
  declaration.

The project is still evolving. Contributions and discussion of the
scope, definitions and API design are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md).


## Selected formalised results

- **Orthogonal polynomials:** classical Jacobi, Gegenbauer, Legendre and Chebyshev
  theory, plus general orthogonality, recurrence and root-interlacing results.
- **Spectral approximation:** coefficient decay, convergence and error bounds,
  interpolation, Gaussian quadrature, banded operators and Clenshaw evaluation.
- **Measure modification and multivariate families:** Gram/Cholesky conversion,
  sparse Proriol triangle conversions, Zernike disk bases and semiclassical Jacobi operators.

See the [LeanFun RevOLVER](https://timon.gutleb.com/LeanFun/) for precise statements, hypotheses and the [interactive dependency graph](https://timon.gutleb.com/LeanFun/dep_graph_document.html).

Planned operator applications include Volterra integration through Proriol triangle
bases and one-dimensional power-law integral operators in weighted Gegenbauer
bases. Equilibrium-minimizer results are outside this scope. Higher-dimensional
power-law operators are deferred until the Meijer G foundations are available.

As the orthogonal-polynomial theory matures, eventual stretch directions include
special functions useful in numerical analysis and the special functions
community: generalised hypergeometric functions ${}_pF_q$, Appell series,
Meijer G functions and Fox H functions.

## Language Models and Human Review

As with most Lean projects that live outside Mathlib, LLMs are used as part of the LeanFun project. While the structure of Lean ensures proofs that compile are correct, whether a statement actually logically represents what it should is something humans have to check (LLMs can be used to flag violations but a lack of such flags is weak evidence at best that a statement is accurately captured).

The balance in LeanFun and the LeanFun RevOLVER is thus as follows:

* **Proofs** are mostly written by LLM agents. Lean’s kernel checks them, and CI rejects sorry and non-standard axioms.
* **Statements**, **Definitions**, etc. are reviewed by hand as the project grows. Each review is tied to a hashed fingerprint of the Lean statement and to the book's text for that statement, so a later change to either voids it.
* LLM audits may flag problems, but they never count as review.

The RevOLVER marks every LeanFun statement explicitly, both in the book and in its dependency graph:

* 🙂 **human-reviewed**: a person has checked that the Lean statement says what the mathematics claims.
* 🫥 **human review stale**: a review exists, but the Lean statement or the book text has changed since, so it needs a fresh review.
* 🤖 **LLM only**: formalised and checked by Lean, but the statement is not yet human-reviewed.

Results imported from Mathlib carry neither marker. The current balance, updated with every RevOLVER build:

<p align="center">
  <a href="https://timon.gutleb.com/LeanFun/">
    <img src="https://timon.gutleb.com/LeanFun/review-status.svg" alt="Human-reviewed, stale and LLM-only statements in the LeanFun RevOLVER" width="640">
  </a>
</p>

## Building and checking

You need Git and [elan](https://github.com/leanprover/elan), which installs the
pinned Lean toolchain automatically.

```sh
git clone https://github.com/TSGut/LeanFun.git
cd LeanFun
lake exe cache get   # download prebuilt Mathlib
lake build           # check every proof
```

To build the RevOLVER locally, you also need Python 3.12, Graphviz (with
development headers) and a TeX installation:

```sh
pip install -r requirements-blueprint.txt
leanblueprint web    # HTML book in blueprint/web
leanblueprint pdf    # PDF in blueprint/print
python3 -m http.server -d blueprint/web   # then open http://localhost:8000
```

The dependency graph needs the HTTP server; opening the HTML files directly
leaves it blank.

The repository pins its Lean and Mathlib versions but will be kept up to date. Eventually the plan is to join [LeanPool](https://github.com/LeanPool/lean-pool). All mathematical source
modules are reachable from `LeanFun.lean`, so the build checks the whole library.
The proofs use Lean's standard axioms; no `sorry` placeholders are used for
planned results.
