# Numerical code for data-driven control in infinite-dimensional spaces

Numerical experiments supporting *Data-Driven Control in Infinite-Dimensional
Spaces: Fundamental Lemma and Applications* (D. López-Montero).
Running the suite regenerates every figure and table of the paper's numerical
section directly into the paper source tree.

Three examples, each an instance of one of the families in Pritchard--Salamon,
*The linear quadratic control problem for infinite dimensional systems with
unbounded input and output operators*, §4:

| example | module | control | observation |
| --- | --- | --- | --- |
| heat equation | `ddinf.systems.heat` | Neumann–Neumann boundary | interior point value |
| wave equation | `ddinf.systems.wave` | Dirichlet boundary | smooth distributed |
| retarded equation | `ddinf.systems.delay` | bounded, in-domain | delayed state component |

They differ in the ways the theory predicts should matter: the heat semigroup is
analytic and smoothing, the wave semigroup is a nonanalytic group, and the
retarded system has a bounded control operator but an unbounded observation.
Each example also carries a symmetric-control variant whose obstruction is known
in closed form; those are the uncontrollable comparisons.

## Quick start

Requires Python ≥ 3.11 and [uv](https://docs.astral.sh/uv/). Everything is dense
NumPy/SciPy; there is no GPU or MPI path.

```bash
uv sync                                     # pinned by uv.lock
uv run ruff check .                         # lint
uv run pytest                               # 42 tests
uv run python -m experiments.run_all        # quick defaults
```

Every experiment takes a `--quality` flag. `quick` uses coarser meshes and time
steps so the suite can be rerun while editing the paper; `paper` uses the finer
grids the committed figures and tables came from, and is the only setting that
reproduces the committed numbers:

```bash
uv run python -m experiments.run_all --quality paper   # ~4 min on 14 cores
uv run python -m experiments.lqr --quality paper       # one experiment
```

Run from a source checkout: `ddinf.paper` locates the paper tree as
`<repo>/paper/` relative to its own file, so an installed copy would write
elsewhere. `git submodule update --init paper` is enough to let the experiments
deposit their output.

## What each experiment produces

| experiment | figure | table | paper |
| --- | --- | --- | --- |
| `experiments/controllability.py` | `figures/controllability.pdf` | `tables/controllability.tex` | Fig. 1, Tab. 1 |
| `experiments/lqr.py` | `figures/lqr.pdf` | `tables/lqr.tex` | Fig. 2, Tab. 2 |
| `experiments/conditioning.py` | `figures/conditioning.pdf` | `tables/conditioning.tex` | Fig. 3 |

- **controllability.** Both data-driven Fattorini–Hautus tests, run on each
  example twice: once approximately controllable (every candidate must be
  rejected) and once with an obstruction known in closed form (it must be
  recovered). The `i-s` rows read `(u, x)`, the `i-o` rows read `(u, y)`.
- **lqr.** The two fundamental lemmas of the paper on the same regulator: the
  state-record synthesis method and the input–output windowed method. Both are
  scored against a separately computed Riccati solution, and each recovered
  input is replayed on the plant.
- **conditioning.** Gramian spectra for three probing inputs on the heat
  equation (analytic, covered by the sufficiency theorem) and the wave equation
  (nonanalytic, not covered). Its table is not `\input` by the paper; the prose
  quotes numbers from it.

`run_all.py` runs the three in that order.

## Repository layout

```
├── src/ddinf/        the library; the only installed package
│   ├── systems/      the plants (base, fem, heat, wave, delay, modal)
│   ├── data/         records, probing signals, moments, informativity
│   ├── controllability/   the data-driven Fattorini–Hautus tests
│   ├── lqr/          riccati (reference), graph (i-s-o), window (i-o)
│   └── paper.py      figure and table output into <repo>/paper/
├── experiments/      the three drivers, one per figure-and-table pair
├── tests/            pytest suite, run against the library alone
├── paper/            paper source, an Overleaf submodule -- the experiments
│                     write their figures and tables into it
└── paper_submission/ the journal-formatted version, a second submodule
```

Nothing in the library knows which PDE it is looking at beyond the
`ddinf.systems.LinearSystem` interface. Modules are grouped by what they read,
which is how the paper distinguishes its results: `i-s` (input–state), `i-s-o`
(input–state–output), `i-o` (input–output). Each subpackage re-exports its main
entry points, so `from ddinf.lqr import solve_io_lqr` and
`from ddinf.lqr.window import solve_io_lqr` are equivalent.

No model quantity enters a data-driven routine. Riccati solutions, Hautus modes,
closed-form eigenvalues and dynamics residuals are computed separately and used
only to score the results.

## Where the details are

Module docstrings carry the derivations and the design rationale — the closed-form
Riccati flow (`ddinf.lqr.riccati`), the quadrature conventions and why the control
term uses trapezoid weights (`ddinf.data.moments`), the window construction and the
junction sample (`ddinf.lqr.window`). Cross-references of the form ``thm:...``,
``eq:...`` in a docstring name a `\label` that exists in `paper/sections/`; a
renamed label in the paper should be renamed here too. Both invariants are
guarded by `tests/test_documentation.py`.

## Reproducibility

Every random draw is seeded, and no routine uses unseeded randomness or
threading-dependent reductions. Rerunning `--quality paper` reproduces the three
`tables/*.tex` byte for byte, and the figures byte for byte apart from the PDF
timestamp metadata matplotlib stamps with the time of the run:

```bash
uv run python -m experiments.run_all --quality paper
git -C paper diff --stat -- tables         # must be empty
```

Environment used for the committed artifacts: Python 3.11.14, NumPy 2.4.1,
SciPy 1.17.0, Matplotlib 3.10.8, pinned in `uv.lock`. The tables have also been
reproduced byte for byte on Python 3.11.13 and under `OMP_NUM_THREADS=1`, so
neither the patch release nor the BLAS thread count affects the numbers.
