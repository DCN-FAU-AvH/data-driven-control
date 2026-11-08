# Lean formalisation of *Data-Driven Control in Infinite-Dimensional Spaces*

A Lean 4 / Mathlib formalisation of *Data-Driven Control in Infinite-Dimensional Spaces:
Fundamental Lemma and Applications* (`../paper/main.tex`): Sections 2–6 with the proofs of the
appendix, the three examples of the introduction (heat, wave and delay equations), and the two
theorems the paper cites without proof, the Fattorini–Hautus test and the Riccati theorem.
Section 7 (numerics) is not formalised.

## Status

* 92 files under `DataDrivenControl/`, about 39,000 lines, on Lean and Mathlib v4.35.0.
  The library builds with no errors and no warnings.
* No `sorry`, `admit` or `axiom`.  `AxiomAudit.lean` prints the axioms of 170 results (every
  theorem, proposition and lemma of the paper, the examples, the cited theorems); each depends
  only on `propext`, `Classical.choice` and `Quot.sound`.
* [`STATEMENTS.md`](STATEMENTS.md) maps every label of the paper to its Lean declarations.

## Building

```
cd lean
lake exe cache get                 # once: Mathlib binaries (about 7 GB in .lake/)
scripts/build.sh                   # build the library, one module at a time
scripts/check.sh AxiomAudit.lean   # print the axioms of the main results
```

Every Lean process loads Mathlib and needs several GB of memory, so `scripts/build.sh` compiles
the modules one at a time in import order; with enough memory, `lake build` does the same faster.
`scripts/build.sh Some.Module` builds one module and its missing dependencies, and
`scripts/check.sh File.lean` elaborates one file against the built imports without writing
anything.  Both run Lean inside `scripts/slot.sh`, which caps the number of concurrent Lean
processes on the machine (`LEAN_SLOTS`, or `.lake/lean-slots/limit`).

Every file is a Lean `module` (`module`, `public import …`, `@[expose] public section`), which
loads only the public part of Mathlib and halves the memory per process.  A module's `.olean`
records the axioms of its declarations when it is compiled, so the axiom audit is meaningful only
after a complete rebuild.

## Layout

All declarations live in the namespace `DataDrivenControl`.

| Directory | Content | Paper |
|---|---|---|
| `Signal/` | signals on `(0, T]` (`L2 E T`), annihilators and closed spans, the Gramian and its trace, test functions and derivative moments, `H¹` in integral form, windows and the synthesis operators `𝒵`, `𝒴` | Sec. 3–4 |
| `Analysis/` | mathematics missing from Mathlib: the Riesz representation of bounded maps on `C([-h, 0]; E)` by measures, bounded-below operators, unique minimisers of coercive quadratic functionals, complexification with the bilinear pairing, uniqueness for exponential and trigonometric series, Bohr means, the Laplace transform, trace-class operators, `\|T\|` and the polar decomposition, the cosine and sine bases of `L²(0, 1)`, `H¹₀(0, 1)` and `H⁻¹(0, 1)` | tools |
| `Semigroup/` | C₀-semigroups, generators, resolvents, adjoints, mild and weak solutions (Ball), analytic semigroups, the extrapolation space, diagonal and modal semigroups, time rescaling, bounded perturbations, `D(A)` with the graph norm, compact resolvents, rotation groups | Sec. 2 |
| `System/` | the setting `W ↪ X ↪ V`, `hyp:H1`, `hyp:H2`, `hyp:compat`, mild solutions, `𝓕_τ`, `𝓞_τ`, controllability and observability, `B_X` and `B^⋆`, time rescaling | Sec. 2 |
| `Informativity/` | informativity, window informativity, persistency of excitation, harmonic inputs, universal sufficiency for analytic semigroups (`Analytic/`: the steps of its proof) | Sec. 3 |
| `FundamentalLemma/` | graph and synthesis operators, Willems' fundamental lemma, the input–output parametrisation | Sec. 4 |
| `Controllability/` | the Fattorini–Hautus test and its proof (`FH*`), the data-driven controllability tests | Sec. 5 |
| `LQR/` | the regulators and the proof of the Riccati theorem | Sec. 6 |
| `Examples/` | the examples of the introduction (`Heat/`, `Wave/`, `Delay/`) and of Section 3 (`WindowStrict`, `PECounterexample`, `InformativityConverse`) | Sec. 1, 3 |

## Main results

`System.foo` is a statement about `sys : System U W X V Y` (real Hilbert spaces).  Theorems take
the paper's hypotheses explicitly, e.g. `(hH1 : sys.H1 T) (hT : 0 < T)`.

| Paper | Lean |
|---|---|
| `lem:informative-gramian` | `informative_iff_injective_gramian` |
| `lem:window-implies-informative` | `System.informative_of_windowInformative` |
| `prop:hilbert-pe-necessary` | `persistentlyExciting_of_forall_informative`, `persistentlyExcitingInfinite_of_forall_informative` |
| `lem:window-pe-necessary` | `WindowInformative.persistentlyExcitingInfinite` |
| `prop:finite-pe-sufficient` | `System.informative_of_persistentlyExciting` |
| `prop:infinite-pe-insufficient` | `PECounterexample.approxControllable`, `.persistentlyExcitingInfinite`, `.not_informative` |
| `lem:harmonic-pe`, `lem:harmonic-pe-implies-pe` | `exists_isHarmonicPE`, `HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite` |
| `thm:analytic-universal-sufficiency` | `System.analytic_universal_sufficiency` |
| `thm:willems-gramian` | `System.willems_tfae`, `System.graph_identification` |
| `thm:windowed-io-fundamental-lemma` | `System.closure_range_ioWindowSynth` |
| `prop:fattorini-hautus` (cited) | `System.fattoriniHautusTheorem` |
| `thm:data-fattorini-hautus` | `System.approxControllable_iff_forall_not_exp` |
| `thm:io-window-controllability` | `System.approxControllable_iff_forall_not_io_exp` |
| `thm:lqr-riccati` (cited) | `System.riccatiIntegralTheorem` |
| `thm:lqr-data` | `System.lqr_data`, `System.lqr_data_riccati_of_H1_H2` |
| `thm:lqr-data-io` | `System.lqr_data_io` |
| `ex:window-strictly-stronger` | `WindowStrict.informative`, `.not_windowInformative` |
| `ex:intro-pde`, `ex:boundary-heat-informative` (every `ν > 0`) | `BoundaryHeat.exists_boundaryHeat` |
| `ex:intro-wave` | `Wave.PDE.exists_wave` |
| `ex:intro-delay` | `Delay.exists_model` (bounded `L`, `M`, `C`), `Delay.Model.H1`, `.H2`, `.compat`, `.not_exists_bound_C` |

## Differences from the paper

No step of the paper's own proofs was found to be false.  Where a Lean proof takes a different
route from the paper's argument, its module docstring says so.

### The cited theorems

* **Fattorini–Hautus (`prop:fattorini-hautus`), corrected hypothesis.**  The test needs a complete
  system of root vectors of `A`, not of `A^⋆` as in Boyer (Thm III.3.7), which the paper first
  followed; the paper now states it for `A` (as Badra–Takahashi, Thm 1.3).  Completeness for `A`
  is necessary for the test to hold for every bounded `B`: with `M` the closed span of the root
  vectors of `A` and `B` mapping onto a dense subset of `M`, the Hautus condition holds while
  `M^⊥` is orthogonal to the reachable set.  Completeness for `A^⋆` does not suffice: there is an
  analytic `A` with compact resolvent whose adjoint has complete root vectors while all root
  vectors of `A` lie in a proper invariant subspace (a block-triangular construction with a
  quasinilpotent Riemann–Liouville block).  Neither argument is formalised.  The proof
  (`System.fattoriniHautusProperty_of_hypotheses`) is contour-free: the unobservable subspace is
  invariant under one compact resolvent of `A^⋆`, and Mathlib's Fredholm alternative shows it is
  orthogonal to all root vectors of `A`.  The graph-norm bound on `B^⋆` that the paper lists as a
  hypothesis holds for every system (`System.exists_norm_Bstar_le`).  The Section-5 theorems
  take `sys.FattoriniHautusProperty T` as a hypothesis, which the theorem supplies.
* **Riccati (`thm:lqr-riccati`, Pritchard–Salamon Thm 2.7) without `hyp:compat`.**
  `System.riccatiIntegralTheorem` needs only `hyp:H1` and `hyp:H2`: the integral Riccati
  equation has a unique solution on `[0, T]` (`System.IsRiccatiIntegralSolution`, as bilinear
  forms on `V`), it is the value operator, and it gives the optimal feedback and cost.
  Pritchard and Salamon use `hyp:compat` only in their Lemma 2.5, which the adjoint formula
  `System.coeFn_adjoint_input` (proved by needle variations) replaces.  Hence also
  `System.lqr_data_riccati_of_H1_H2`, the second part of `thm:lqr-data` without `hyp:compat`.

### Stronger statements

* `prop:hilbert-pe-necessary` quantifies only over systems that are approximately controllable
  in every time, a weaker hypothesis.
* `thm:willems-gramian`, last sentence: `System.eq_mild_of_trajectory` needs only condition (i)
  and `hyp:H1`.
* `thm:analytic-universal-sufficiency`, "moreover": `System.approxControllable_of_informative_zero`
  and `System.approxControllable_of_windowInformative_zero` hold for every `L²` input.
* `thm:data-fattorini-hautus` (`κ ≠ 0`) and `thm:io-window-controllability` (`g ≠ 0`): the
  nondegeneracy parts hold without the Fattorini–Hautus property
  (`System.exp_coeff_eq_and_ne_zero`, `System.ne_zero_of_io_exp`).
* `eq:hilbert-gramian`: also `tr 𝒢(z) = ∫ ‖z‖²` (`trace_gramian`).
* `ex:boundary-heat-informative` holds for every diffusivity `ν > 0`, not only `ν = 1`.
* The approximate controllability of the explicit examples (`app:pe-necessity`,
  `prop:infinite-pe-insufficient`, the heat equation) is proved directly from their modal
  structure (`approxControllable_diag`, `System.approxControllable_of_modal`), without
  `prop:fattorini-hautus`, compact resolvents or root vectors.
* The remark after `lem:informative-gramian` says that informativity in `U × X` does not imply
  informativity in `U × W` in general; `InformativityConverse.exists_informative_not_informativeW`
  gives an example (the paper gives none): the delay system `ẋ = u`, `y(t) = x(t - 2π)` with the
  record of `x(t) = ∑ₙ 2^{-n} cos(n t)`.

### Modelling conventions

* **Signals** are functions `ℝ → E`, square integrable on `(0, T]` (`MemLp u 2 (μI T)`); operators
  act on `L2 E T = Lp E 2 (μI T)`.  Products of Hilbert spaces are `WithLp 2 (E × F)`.
* **Closed spans**: `cspan 𝕜 μ z` is defined as `(annihilator 𝕜 μ z)ᗮ`; `isLeast_cspan` shows it
  is the smallest closed subspace containing `z t` for a.e. `t`.
* **Distributions and `H₀¹`** are replaced by test functions (smooth, compact support in
  `(0, T)`): `⟨Dᵏū, φ⟩ = (-1)ᵏ ∫ φ⁽ᵏ⁾ ū` (`derivMoment`), and the synthesis operator `𝒲` of
  Section 4 is evaluated on test functions.  This changes no statement: its image has the same
  closure, and the paper's proof only tests against `C_c^∞`.
* **`H¹`** is in integral form: `HasWeakDeriv T x g` means `g ∈ L²` and
  `x t = x 0 + ∫₀ᵗ g` on `[0, T]`.  Record derivatives are explicit arguments with this
  hypothesis.
* **Semigroups** `C0Semigroup 𝕜 E` are indexed by `ℝ≥0`; the generator is a Mathlib
  `LinearPMap`, `A†` is `LinearPMap.adjoint`.  A `System` carries three consistent semigroups
  `SW`, `SX`, `SV`.  `IsAnalytic S` is the characterisation `S t (E) ⊆ D(A)`,
  `‖A S(t)‖ ≤ C/t` on `(0, 1]` (Pazy, Thm 2.5.2), which needs no complexification.
* **The extrapolation space** `V₋₁` is the graph of `A_V†` (the dual model, `C0Semigroup.Extrap`),
  so that `ẋ = A₋₁ x + f` in integral form is literally Ball's weak formulation.  The conditions
  of Section 4 do not depend on which equivalent Hilbert norm `V₋₁` carries.
* **Complex scalars.**  As in the paper, systems are real and spectra live on `X_ℂ =
  Complexification X`, with the paper's complex-*bilinear* pairing `⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ`.
  `A^⋆` on `X_ℂ` is `sys.A.adjoint.complexify`, `ρ(A)` is `resolventSet sys.A.complexify`.
  The paper's `W'` is modelled by `W` through the Riesz map.
* **Weights and Riccati operators** `G, P(t) ∈ L(V, V')` are bounded symmetric bilinear forms on
  `V`; `B^⋆P(t)x` is the Riesz representer of `v ↦ P(t)(x, B v)`, and `R⁻¹` is `Ring.inverse R`.
* **Trace class** is defined by nuclear representations `T = ∑ₙ aₙ ⊗ bₙ`,
  `∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞` (Mathlib has none); `TraceClass.isTraceClass_iff_summable_realAbs` proves it
  equivalent to the textbook `tr |T| < ∞`, and `tr |T|` is the nuclear norm.
* **Junk values.**  Definitions take no hypotheses: `L_t`, `𝓕_τ`, `𝓞_τ` are `0` where `hyp:H1` or
  `hyp:H2` fails, `resolvent` is `0` off the resolvent set.  No junk value makes a theorem
  vacuous; every theorem assumes `0 < T` and `[CompleteSpace]`.
* **Indexing.**  Sequences in the examples count from `0` (the paper's `eₙ`, `n ≥ 1`, is
  `e (n - 1)`), except the heat modes, which the paper also counts from `0`.

### The examples

* **Heat equation** (`Examples/Heat`, namespace `BoundaryHeat`).  `X = L²(0, 1)` with the cosine
  basis, `V` the paper's `χ`-localised space (`eq:heat-localized-V`: the closed graph of
  `z ↦ e^{-t} χ S(t) z` in `X₋₁ × L²(0, ∞; H¹)`, with the paper's norm by `norm_V_sq_eq`) and
  `W = D(A_V)`.  `exists_boundaryHeat` states `ex:boundary-heat-informative` for every
  diffusivity `ν > 0`, together with the ties to the PDE: `A` is `ν` times the Neumann Laplacian on
  `H²_N(0, 1)`, `B^⋆η = -ν η(0)`, `C w = w(ξ₀)`, and `B` and `C` are unbounded on `X`.  The system
  is the unit-diffusivity system rescaled in time (`System.timeScale`: semigroups `S(νt)`,
  `B ↦ ν B`), with the spaces `V` and `W` of `ν = 1`.  Differences: `C ∈ L(W, ℝ)` is defined by the
  trace formula in time `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds`, `g = (S(·) w)(ξ₀)`, rather than
  through `H¹(0, 1) ↪ C[0, 1]`; the cut-off `χ` need only be `C¹`; approximate controllability is
  proved from the modal coordinates rather than with `prop:fattorini-hautus`.
* **Wave equation** (`Examples/Wave`, namespace `Wave`).  The paper names no spaces.
  `Wave.PDE.exists_wave` takes `W = X = L²(0, 1) × H⁻¹(0, 1)` (`W = X` is forced, since the wave
  equation is exactly controllable for `T ≥ 2/c`) and `V = ℓ² × ℓ²` with the modal weight
  `(1 + ωₙ²)⁻¹ + qₙ²`, which puts `B` into `V` and makes `hyp:H2` hold.  `H⁻¹(0, 1)` is the dual of
  `H¹₀(0, 1)` (`Analysis/Sobolev01`), and the velocity is `c • x₂`, which absorbs the paper's norm
  `c⁻¹‖·‖_{H⁻¹}`.  The theorem states `D(A) = H¹₀ × L²`, `A (φ, v) = (c v, c ∂_ξξ φ)`,
  `B^⋆η = ζ'(0)` with `-ζ'' = c η₂`, `C x = ∫₀¹ q w`, `hyp:H1`, `hyp:H2`, `hyp:compat`, and that
  the group is not analytic.  `hyp:H1` and `hyp:H2` follow from Bessel's inequality at
  `T = 2/c`; no Ingham inequality is needed.
* **Delay system** (`Examples/Delay`, namespace `Delay`).  The neutral system on
  `X = E × L²(0, h; E)` with state `(x(t) - M x_t, x_t)` (Burns–Herdman–Stech 1983; Staffans 1986
  for measures); the history lives on `(0, h]`.  A delay functional (`DelayOp`) is `ψ ↦ ∑ₖ Pₖ ∫ ψ(h - δ) dμₖ(δ) + D ψ` with
  finitely many finite measures `μₖ` on `[0, h]` and `D` bounded on the `L²` history; point delays
  are Dirac measures, and `M` has no atom at `0`.  For this model (`E`, `U`, `Y` real Hilbert
  spaces): `W = D(A)` with the graph norm, `V = X`, `D(A) = {(g(h) - M g, g) : g ∈ H¹}`,
  `A (g(h) - M g, g) = (L g, g')`, `B = (B₀, 0)`, `Model.H1`, `Model.H2`, `Model.compat`, and `C`
  is unbounded on `X` when `C({θ}) + C({0}) M({θ}) ≠ 0` for some `θ ∈ (0, h]`
  (`Model.not_exists_bound_C`).  The paper's `L`, `M`, `C`, bounded maps on `C([-h, 0]; ℝⁿ)`, are
  such functionals by the Riesz representation (`Analysis/MeasureRepresentation`; "no mass at
  `0`" is the intrinsic condition `NoMassAtZero`), and `exists_model` builds the system from
  them for finite-dimensional `E` and `Y`.  The retarded case is `M = 0`.

## Not formalised

* Section 7 (numerics).
