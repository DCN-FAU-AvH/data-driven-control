# Lean formalisation of the infinite-dimensional fundamental lemma

This directory is a Lean 4 / Mathlib project formalising Sections 2–6 and the appendix proofs of
*Data-Driven Control in Infinite-Dimensional Spaces: Fundamental Lemma and Applications*
(`../paper/main.tex`), together with the three examples of the introduction (the
boundary-controlled heat equation, the wave equation and the delay system) and the two theorems
the paper cites without proof:

* the standing setting `W ↪ X ↪ V` with Assumptions `hyp:H1`, `hyp:H2`, `hyp:compat`, mild
  solutions and the finite-horizon operators (Section 2, `app:finite-horizon-output`,
  `app:control-realization`);
* the delay system with delayed output (`ex:intro-delay`), retarded (`M = 0`) and neutral
  (`M ≠ 0`, the semigroup of Burns–Herdman–Stech 1983), as a system on
  `W ↪ X ↪ V` that satisfies `hyp:H1`, `hyp:H2` and `hyp:compat`, with `B` bounded and `C`
  unbounded on `X` (Section 1);
* the wave equation with Dirichlet control (`ex:intro-wave`) as a system on `W = X ↪ V` that
  satisfies `hyp:H1`, `hyp:H2` and `hyp:compat`, with `B` unbounded and `C` bounded on `X` and a
  non-analytic group (Section 1);
* informativity, window informativity and persistency of excitation in Hilbert spaces, a
  record that is informative in `U × X` but not in `U × W`, the Gramian and its trace-class
  property (with the equivalence of the nuclear trace class and `tr |T| < ∞`), the three examples (among them the boundary-controlled
  heat equation, `ex:intro-pde`, `ex:boundary-heat-informative`), and universal sufficiency of
  harmonic inputs for analytic semigroups (Section 3);
* Willems' fundamental lemma and its windowed input–output version (Section 4);
* the Fattorini–Hautus theorem and the data-driven controllability tests (Section 5);
* the Riccati theorem and the data-driven linear–quadratic regulators (Section 6).

Mathlib has no C₀-semigroups, extrapolation spaces, complexification of real Hilbert spaces,
Laplace transform, Bohr means or trace-class operators; `Semigroup/` and `Analysis/` build what
the paper uses of them.  The two results the paper cites without proof are proved: the
Fattorini–Hautus test (`prop:fattorini-hautus`) and the Pritchard–Salamon Riccati theorem
(`thm:lqr-riccati`).  The Fattorini–Hautus test is proved under a corrected hypothesis: the root
vectors of `A`, not of `A^⋆`, must be complete.  Boyer's statement, which names `A^⋆`, does not
suffice, and the paper now states the hypothesis for `A`.  The Riccati theorem is proved without
`hyp:compat`.  The heat equation is formalised in modal coordinates, tied to `L²(0, 1)` (cosine basis,
Neumann Laplacian, point evaluation, boundary trace), and on the paper's own spaces
(the `χ`-localised `H¹` norm of `eq:heat-localized-V`).  The delay system is formalised for
retarded and neutral equations with finitely many point delays (the neutral ones in `(0, h]`)
and distributed parts that are bounded on the `L²` history.  The wave equation is formalised
in modal coordinates and tied to `L²(0, 1) × H⁻¹(0, 1)` (sine basis, `H⁻¹ = (H¹₀)'`, the
function form of `A`, `B^⋆` and `C`).  The numerics of Section 7 are not formalised.

## Status

**Complete** as of 2026-11-07: Sections 2–6, the appendix proofs, both counterexamples of
Section 3 and a counterexample for the remark after `lem:informative-gramian`, the trace-class
claim of `eq:hilbert-gramian` (also in the textbook form `tr |𝒢| < ∞`, and the equivalence of
the nuclear trace class with `tr |T| < ∞` for every bounded `T`), the boundary-controlled heat
equation (`ex:intro-pde`, `ex:boundary-heat-informative`, in modal form, on `L²(0, 1)`, and with
the paper's localised `V`), the wave equation (`ex:intro-wave`, modal form and on
`L²(0, 1) × H⁻¹(0, 1)`), the delay system (`ex:intro-delay`, retarded and neutral), and proofs
of the two theorems the paper cites, the Riccati theorem in full (integral Riccati equation and
uniqueness).

* 100 files under `DataDrivenControl/`, about @LINES@ lines.  The sequential build
  (`scripts/build.sh`) succeeds: all 100 modules, @WARN@.  A clean build
  (after deleting `.lake/build`) took about 28 minutes when the library had 70 modules.
* No `sorry`, no `admit`, no `axiom`.
* `AxiomAudit.lean` prints the axioms of 193 main results.  It covers every theorem,
  proposition and lemma of Sections 2–6, the examples, the cited theorems, the trace class and
  the key semigroup results.  Every one depends only on `propext`, `Classical.choice` and
  `Quot.sound`.  Check it with `scripts/check.sh AxiomAudit.lean` after a full build.  Module
  `.olean`s record axiom sets at compile time, so the audit is only meaningful after a full
  rebuild.
* The two theorems the paper cites without proof are proved:
  * the Fattorini–Hautus test, `System.fattoriniHautusTheorem`;
  * the Pritchard–Salamon Riccati theorem, `System.riccatiTheorem`, which does not need
    `hyp:compat`; in full, with the integral Riccati equation and the uniqueness of its
    solution, `System.riccatiIntegralTheorem`.

  The Fattorini–Hautus hypothesis is corrected: completeness of the root vectors of `A`, not
  of `A⋆` (see "The cited theorems, now proved").  The paper's `prop:fattorini-hautus` was
  changed to match.
* Not formalised: Section 7 (numerics), a general diffusivity `ν` in the heat example, and
  delay operators given by general measures (see the last section).
* `STATEMENTS.md` maps every paper label to its Lean declaration.

## Building and checking

```
cd lean
lake exe cache get   # once: downloads the Mathlib binaries (about 7 GB in .lake/)
scripts/build.sh     # compiles the library one module at a time
```

The toolchain (`lean-toolchain`) is Lean v4.35.0 with Mathlib tag v4.35.0, the same Mathlib
commit as the sibling project `neuralode/lean`.  `lakefile.toml` sets `autoImplicit = false`.
Open any file under `DataDrivenControl/` in VS Code with the Lean 4 extension; it finds
`lakefile.toml` in this directory.

**`scripts/build.sh` or `lake build`.**  Both build the same library, since the root file
`DataDrivenControl.lean` imports every file.  `lake build` compiles every module whose imports
are ready in parallel, and each of these Lean processes loads Mathlib and needs several GB of
memory; on the development machine (WSL with 11 GB) a parallel build swaps.  `scripts/build.sh`
computes the import order and compiles one module at a time, each inside a slot of
`scripts/slot.sh` (at most `LEAN_SLOTS` Lean processes on the machine), and finishes with
`lake build DataDrivenControl`.  `scripts/build.sh Some.Module` builds one module and,
sequentially, its missing dependencies.  With enough memory, plain `lake build` gives the same
result faster.

**Checking one file.**  `scripts/check.sh DataDrivenControl/X/Y.lean` elaborates a file against
the installed `.olean`s of its imports and writes nothing.

**Modules.**  Every file is a Lean `module`:

```lean
module

public import Mathlib
public import DataDrivenControl.Signal.Basic

@[expose] public section
```

Importing a module loads only the public part of Mathlib's `.olean`s, which roughly halves the
memory per Lean process and makes checks about three times faster.  `@[expose] public section`
makes every declaration public and every definition unfoldable downstream.  Proofs of theorems
are not exported, so a file sees only the statements of the files it imports.

**Axiom audit.**  A module's `.olean` records the axioms of each declaration when the file is
compiled.  `#print axioms` is therefore reliable only after a complete rebuild in import order
(delete `.lake/build`, then run `scripts/build.sh`; Mathlib's binaries in `.lake/packages` are
not affected), not against `.olean`s that were installed while an upstream file still had a
`sorry`.

## Layout

All declarations live in the namespace `DataDrivenControl`.

| Directory | Files | Content | Paper |
|---|---|---|---|
| `Signal/` | `Basic`, `Span`, `Gramian`, `GramianTrace`, `TestFunction`, `WeakDerivative`, `Shift` | Signals on `(0, T]` (`μI T`, `L2 E T`); annihilators and closed spans; the Gramian, and its trace-class property with `tr 𝒢(z) = ∫ ‖z‖²`; test functions and derivative moments `⟨Dᵏū, φ⟩`; `H¹` in integral form, du Bois-Reymond, variation of constants in weak form; windows, continuity of translation in `L²`, the window synthesis operators `𝒵`, `𝒴`, restriction, tails and concatenation | `eq:hilbert-gramian`, `eq:gramian-kernel`, `rmk:gramian-not-coercive`, `eq:io-window-synthesis` |
| `Analysis/` | `BoundedBelow`, `Quadratic`, `Complexification`, `ExpSums`, `BohrMean`, `Laplace`, `TraceClass`, `PolarDecomposition`, `TraceClassAbs`, `CosineBasis`, `SineBasis`, `Sobolev01` | Mathematics missing from Mathlib: bounded-below operators; unique minimisers of coercive quadratic functionals; the complexification `X_ℂ` with the paper's bilinear pairing; uniqueness for exponential sums, Dirichlet, power, Laurent and trigonometric series; Bohr means; the Laplace transform and its uniqueness; Hilbert–Schmidt and trace-class operators and the trace; `|T|` on real and complex Hilbert spaces, the polar decomposition, and the trace class as `tr |T| < ∞` with `tr |T|` the nuclear norm; the cosine Hilbert basis of `L²(0, 1)` and uniformly convergent cosine series; the sine Hilbert basis, `H¹₀(0, 1)` and `H⁻¹(0, 1) = (H¹₀)'` as Hilbert spaces, the `H⁻¹` norm in sine coefficients, the Dirichlet problem | tools of the appendix, `eq:hilbert-gramian`, the heat and wave examples |
| `Semigroup/` | `Basic`, `Generator`, `Resolvent`, `Adjoint`, `Inhomogeneous`, `Analytic`, `Extrapolation`, `Diagonal`, `Perturbation`, `DomainSpace`, `Modal`, `CompactResolvent`, `Rotation` | C₀-semigroups and generators; resolvents as Laplace transforms and the finite-time Laplace identity; the adjoint semigroup; mild and weak solutions and Ball's theorem; analytic semigroups; the dual-model extrapolation space; diagonal semigroups with a direct controllability test; bounded perturbations and feedback invariance; `D(A)` with the graph norm as a Hilbert space, with the restricted semigroup; diagonal maps between modal spaces, resolvents of real diagonal generators, and approximate controllability from modal coordinates for unbounded `B`; compact resolvents (root vectors independent of the resolvent point, the Fredholm alternative on an invariant subspace); isometric block-rotation groups and block-diagonal maps | `sec:setting`, Ball (1977), tools for `prop:fattorini-hautus`, the heat and wave examples |
| `System/` | `Setting`, `Mild`, `Controllability`, `ControlRealization` | The structure `System U W X V Y`; `hyp:H1`, `hyp:H2`, `hyp:compat`; mild solutions, `L_t`, `𝓕_τ`, `𝓞_τ`; controllability and observability; `B_X`, `B†` on `D(A†)`, `eq:weak-mild-diff` | Sec. 1–2, `app:finite-horizon-output`, `app:control-realization` |
| `Informativity/` | `Informative`, `Window`, `PE`, `FiniteDim`, `Necessity`, `Harmonic`, `AnalyticSufficiency` | Informative and window-informative data, persistency of excitation (necessity, finite-dimensional sufficiency), harmonic excitation, universal sufficiency for analytic semigroups | Sec. 3 |
| `Informativity/Analytic/` | `Transfer`, `Expansion`, `Bohr` | The steps of `app:analytic-universal-sufficiency`: the transfer map `𝐇(s)`, the state expansion of a harmonic record, `lem:bohr-annihilator`, `lem:transfer-laplace` | `app:analytic-universal-sufficiency` |
| `FundamentalLemma/` | `Graph`, `Willems`, `InputOutput` | Graph and synthesis operators, Willems' fundamental lemma, the input–output parametrisation and fundamental lemma | Sec. 4 |
| `Controllability/` | `FattoriniHautus`, `FHObservation`, `FHResolvent`, `FHSpectral`, `InputState`, `InputOutput` | The Fattorini–Hautus statement and its easy direction; its proof (the unobservable subspace, one compact resolvent of `A^⋆`, the Fredholm alternative); input–state and input–output controllability tests | Sec. 5 |
| `LQR/` | `ModelBased`, `InputStateOutput`, `InputOutput`, `TailOperators`, `ValueOperator`, `DynamicProgramming`, `Feedback`, `RiccatiExistence`, `RiccatiEquation`, `RiccatiIntegralDeriv`, `RiccatiIntegral` | Model-based cost and the Riccati interface, input–state–output and input–output regulators; the proof of the Riccati theorem: tail problems on a fixed control space, the value operator and its strong continuity, dynamic programming, the adjoint of the input map, existence; the integral Riccati equation, its uniqueness, and the value operator as its solution | Sec. 6 |
| `Examples/` | `WindowStrict`, `PECounterexample`, `BoundaryHeat`, `InformativityConverse` (with `InformativityConverse/Trig`) | The three examples of Sec. 3; `BoundaryHeat` states the heat example's main theorems; a record of a delay system that is informative in `U × X` but not in `U × W` (with the trigonometric tools it needs: completeness in `L²(0, 2π)`, Riemann–Lebesgue) | `ex:window-strictly-stronger`, `prop:infinite-pe-insufficient`, `ex:boundary-heat-informative`, remark after `lem:informative-gramian` |
| `Examples/Heat/` | `Kernel`, `Input`, `Spaces`, `Estimates`, `System`, `PDE`, `LocalizedKernel`, `LocalizedCutoff`, `LocalizedOrbit`, `LocalizedSpaces`, `LocalizedControl`, `LocalizedSystem` | The boundary-controlled heat equation in modal form: eigenvalues, modal coefficients and the impulse response (method of images); the exciting input `ū`; the spaces `X₋₁`, `V`, `W`; the trace formula in time and the control estimate; the `System` with `hyp:H1`, `hyp:H2`, `hyp:compat`; the dictionary to `L²(0, 1)` (`H²_N`, the Neumann Laplacian, point evaluation, boundary trace); the paper's `χ`-localised `V` and `W = D(A_V)` on `L²(0, 1)`, the kernel bounds on `supp χ`, and the system on these spaces | `ex:intro-pde`, `app:boundary-heat-informative`, `eq:heat-localized-V` |
| `Examples/Delay/` | `Solution`, `Translation`, `Semigroup`, `System`, `Unbounded` | The retarded delay system with delayed output: existence, uniqueness and bounds for the delay equation; translation of `H¹` signals in `L²`; the delay semigroup on `E × L²` and its generator; the `System` with `W = D(A)`, `X = V`, `hyp:H1`, `hyp:H2`, `hyp:compat`; `C` unbounded on `X` | `ex:intro-delay` |
| `Examples/NeutralDelay/` | `Operator`, `Weighted`, `Solution`, `Regularity`, `Semigroup`, `System`, `Retarded`, `Unbounded` | The neutral delay system: delay functionals `∑ₖ Pₖ φ(-δₖ) + D φ`; weighted `L²` norms and invertibility of the neutral Volterra operator; existence, uniqueness, linearity, time shift and `L²` bounds for the a.e. integral form; `H¹` regularity for compatible `H¹` data; the semigroup `S(t)(r, ψ) = (x(t) - M x_t, x_t)` on `E × L²` and its generator; the `System` with `W = D(A)`, `X = V`, `hyp:H1`, `hyp:H2`, `hyp:compat`; consistency with the retarded system; `C` unbounded on `X` | `ex:intro-delay` |
| `Examples/Wave/` | `Fourier`, `Spaces`, `System`, `PDE` | The wave equation with Dirichlet control in energy coordinates: orthogonality of `cos(ωₙ·)`, `sin(ωₙ·)` on `(0, 2/c]`, Bessel and its dual; the weighted `V`, `B`, `C` and the `System` with `W = X`; `hyp:H1`, `hyp:H2`, `hyp:compat`, the modal formulas for `L_T` and `B^⋆`, non-analyticity; the dictionary to `L²(0, 1) × H⁻¹(0, 1)` (`C = ∫ q w`, `D(A) = H¹₀ × L²`, `B^⋆ η = ζ'(0)`) | `ex:intro-wave` |

`scripts/` holds the build tools: `build.sh`, `check.sh` and `slot.sh`.

## Main results

Names are relative to the namespace `DataDrivenControl`.  `System.foo` is a declaration about a
system `sys : System U W X V Y`; all spaces are real Hilbert spaces (`[CompleteSpace]` is a
hypothesis of every theorem about a system).  A *record generated by* `(x₀, ū)` on `[0, τ]` has
state `sys.mild x₀ ū` and output `sys.output τ x₀ ū` (a representative of `𝓞_τ x₀ + 𝓕_τ ū`)
for `x₀ ∈ X`, and state `sys.mildW x₀ ū` (values in `W`) and output `sys.outputW x₀ ū = C x̄`
for `x₀ ∈ W`.  Theorems take the paper's assumptions at the paper's horizon,
`(hH1 : sys.H1 T) (hT : 0 < T)`.

### Section 2: setting

| Paper | Lean | File |
|---|---|---|
| `eq:hilbert-control-formal`, `eq:intro-WXV` | `System`, `System.bounded` (the case `W = X = V`) | `System/Setting` |
| `hyp:H1`, `hyp:H2`, `hyp:compat` | `System.H1`, `System.H2`, `System.Compat` | `System/Setting` |
| `eq:hilbert-mild` | `System.mild`, `System.mildW`, `System.outputW`, `System.L`, `System.Lop` | `System/Mild` |
| `lem:finite-horizon-output` | `System.𝓕`, `System.𝓞`, `System.output_ae_eq`, `System.output_shift`, `System.H1.of_pos`, `System.H2.of_pos` | `System/Mild` |
| `def:controllability` | `System.reachable`, `System.ExactlyControllable`, `System.ApproxControllable` | `System/Controllability` |
| `def:observability` | `System.ApproxObservable`, `System.ExactlyObservable` | `System/Controllability` |
| `app:control-realization` (and the paragraph after `lem:finite-horizon-output`) | `System.Q`, `System.QSpec`, `System.BX`, `System.BX_eq`, `System.toExtrap_L`, `System.Bstar`, `System.exists_norm_Bstar_le`, `System.inner_Bstar_of_dual`, `System.inner_L_eq_integral`, `System.adjoint_Lop_ae_eq` | `System/ControlRealization` |
| `eq:control-resolvent-decay` | `System.Q_decay` | `System/ControlRealization` |
| `eq:weak-mild-diff` | `System.inner_mild_eq` | `System/ControlRealization` |

### Section 3: informativity and persistency of excitation

| Paper | Lean | File |
|---|---|---|
| `def:hilbert-informative`, `eq:informative-span` | `Informative`, `informative_iff_annihilator`, `informative_iff` | `Informativity/Informative` |
| `eq:hilbert-gramian`, `eq:gramian-kernel` | `gramian`, `isPositive_gramian`, `ker_gramian_eq_orthogonal_cspan`, `orthogonal_ker_gramian` | `Signal/Gramian` |
| `eq:hilbert-gramian` (trace class) | `isTraceClass_gramian`, `trace_gramian` (`tr 𝒢(z) = ∫ ‖z‖²`); the textbook form `hasSum_inner_gramian`, `hasSum_re_inner_gramian`; the definitions `TraceClass.IsTraceClass`, `TraceClass.IsHilbertSchmidt`, `TraceClass.trace` | `Signal/GramianTrace`, `Analysis/TraceClass` |
| trace class = `tr \|T\| < ∞` | `TraceClass.isTraceClass_iff_summable_realAbs`, `TraceClass.isTraceClass_iff_isTraceClass_realAbs`, `TraceClass.isLeast_nuclearSums_realAbs` (`tr \|T\|` is the nuclear norm; real Hilbert spaces); `TraceClass.isTraceClass_iff_summable_cfcAbs`, `TraceClass.isTraceClass_iff_isTraceClass_cfcAbs`, `TraceClass.isLeast_nuclearSums_cfcAbs` (complex, `\|T\| = CFC.abs T`); `TraceClass.isTraceClass_complexify_iff`, `TraceClass.trace_complexify` | `Analysis/TraceClassAbs` |
| `\|𝒢(z)\| = 𝒢(z)` | `TraceClass.realAbs_gramian`, `TraceClass.cfcAbs_gramian`, `TraceClass.hasSum_inner_realAbs_gramian`, `TraceClass.hasSum_re_inner_cfcAbs_gramian` | `Analysis/TraceClassAbs` |
| (`\|T\|` and the polar decomposition) | `TraceClass.realAbs`, `TraceClass.realSqrt`, `TraceClass.realAbs_unique`, `TraceClass.complexify_realAbs`, `TraceClass.polar_decomposition_realAbs` (real); `TraceClass.cfcAbs_unique`, `TraceClass.norm_cfcAbs_apply`, `TraceClass.polar_decomposition_cfcAbs` (complex); `TraceClass.polarPart` (any `RCLike 𝕜`) | `Analysis/PolarDecomposition` |
| `lem:informative-gramian` | `informative_iff_injective_gramian` | `Informativity/Informative` |
| `rmk:gramian-not-coercive` | `gramian_injective_iff_coercive` | `Signal/Gramian` |
| remark after `lem:informative-gramian` (`U × W` ⇒ `U × X`) | `Informative.map_of_denseRange`, `System.Informative.mild_of_mildW` | `Informativity/Informative` |
| remark after `lem:informative-gramian` ("the converse fails in general") | `InformativityConverse.exists_informative_not_informativeW`, `InformativityConverse.not_forall_informativeW_of_informative`; the record: `InformativityConverse.informative_X`, `InformativityConverse.informative_mild` (informative in `U × X`, every `T > 0`), `InformativityConverse.not_informative_W` (not informative in `U × W`, every `T`); see below | `Examples/InformativityConverse` |
| (completeness of the trigonometric system, Riemann–Lebesgue) | `InformativityConverse.ae_eq_zero_of_moments_eq_zero`, `InformativityConverse.tendsto_cosMoment`, `InformativityConverse.tendsto_sinMoment` | `Examples/InformativityConverse/Trig` |
| `def:window-informative` | `WindowInformative`, `windowInformative_iff` | `Informativity/Window` |
| `lem:window-implies-informative` | `System.informative_of_windowInformative` | `Informativity/Window` |
| `ex:window-strictly-stronger` | `WindowStrict.informative`, `WindowStrict.not_windowInformative`, `WindowStrict.exactlyControllable` | `Examples/WindowStrict` |
| `def:PE` | `PersistentlyExciting`, `PersistentlyExcitingInfinite` | `Informativity/PE` |
| remark after `def:PE` (regular inputs) | `persistentlyExciting_iff_injective_gramian` | `Informativity/PE` |
| `prop:hilbert-pe-necessary` | `persistentlyExciting_of_forall_informative` (`N < ∞`), `persistentlyExcitingInfinite_of_forall_informative` (`N = ∞`) | `Informativity/Necessity` |
| `lem:window-pe-necessary` | `WindowInformative.persistentlyExcitingInfinite` | `Informativity/PE` |
| `prop:finite-pe-sufficient` | `System.informative_of_persistentlyExciting` | `Informativity/FiniteDim` |
| `prop:infinite-pe-insufficient` | `PECounterexample.approxControllable`, `PECounterexample.persistentlyExcitingInfinite`, `PECounterexample.not_informative` | `Examples/PECounterexample` |
| `def:harmonic-signal` | `HarmonicSignal`, `IsHarmonic` | `Informativity/Harmonic` |
| `def:harmonic-pe` | `HarmonicSignal.IsHarmonicPE` | `Informativity/Harmonic` |
| text after `def:harmonic-pe` (the counterexample input is not harmonic) | `PECounterexample.not_isHarmonic` | `Examples/PECounterexample` |
| `lem:harmonic-pe` | `isHarmonicPE_hpeSignal`, `exists_isHarmonicPE` | `Informativity/Harmonic` |
| `lem:harmonic-pe-implies-pe` | `HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite` | `Informativity/Harmonic` |
| `thm:analytic-universal-sufficiency` | `System.analytic_universal_sufficiency` (TFAE); (i) ⇒ (ii) `System.informative_of_approxControllable_harmonic`; (i) ⇒ (iii) `System.windowInformative_of_approxControllable_harmonic`; "moreover": `System.approxControllable_of_informative_zero`, `System.approxControllable_of_windowInformative_zero` | `Informativity/AnalyticSufficiency` |
| `ex:boundary-heat-informative` | `BoundaryHeat.exists_boundaryHeat` (the paper's existential form); for the concrete system `BoundaryHeat.heatSystem e hξ₀`: `heatSystem_approxControllable`, `heatSystem_TFAE` (`thm:analytic-universal-sufficiency` with `σ = 0`, `M = 1`), `heatSystem_informative` (in `U × W`, every `x̄₀ ∈ W`), `heatSystem_windowInformative` (every `x̄₀ ∈ X`); the input `heatInput`, `isHarmonicPE_heatInput`.  Details in the heat table below | `Examples/BoundaryHeat`, `Examples/Heat/Input` |

**The converse of "informative in `U × W` ⇒ informative in `U × X`" fails**
(`Examples/InformativityConverse`).  The system is the retarded delay system of
`ex:intro-delay` (`Delay.Model.sys`, `W = D(A)` with the graph norm, `X = V = ℝ × L²(0, 2π)`)
with `h = 2π`, `E = U = Y = ℝ`, no state delays and `B₀ = 1`, i.e. `ẋ(t) = u(t)`, and the
output `y(t) = x(t - 2π)`; `hyp:H1`, `hyp:H2` (every horizon) and `hyp:compat` hold, and `C` is
unbounded on `X`.  The record is generated by the `2π`-periodic signal
`x(t) = ∑ₙ 2^{-n} cos(n t)`: `ū = ẋ`, `x̄₀ = (x(0), x_0) ∈ W`, and the state is
`x̄(t) = (x(t), x_t)` (`ιW_mildW_eq_state`, a strong solution, hence the mild one).  *Not
informative in `U × W`*: `(g(2π), g) ↦ g(2π) - g(0) = ∫₀^{2π} (A v)₂` is continuous on `W`, not
on `X`, and vanishes on `x̄(t)` because `x` is periodic; its nonzero Riesz representer `β ∈ W`
gives the annihilator `(0, β)`.  *Informative in `U × X`*: an annihilator `(α, (β₁, β₂))` turns
`α ū(t) + β₁ x(t) + ⟪β₂, x_t⟫ = 0` into a trigonometric series in `t` with geometrically
decaying coefficients `2^{-n}(β₁ + Cₙ)`, `2^{-n}(α n + Sₙ)` (`Cₙ`, `Sₙ` the cosine and sine
moments of `β₂`), which vanish by `trigSeries_coeff_eq_zero` on any interval; Riemann–Lebesgue
gives `α = β₁ = 0`, and completeness of the trigonometric system in `L²(0, 2π)` (both from
Mathlib's Parseval identity on `AddCircle`) gives `β₂ = 0`.
`not_forall_informativeW_of_informative` states the failure of the converse of
`System.Informative.mild_of_mildW` over all systems satisfying the standing assumptions.

### Section 4: the fundamental lemma

| Paper | Lean | File |
|---|---|---|
| `eq:graph-operator` | `System.GraphSpace`, `System.graphOp`, `System.isBoundedBelow_graphOp`, `System.isClosed_range_graphOp` | `FundamentalLemma/Graph` |
| synthesis operator `𝒲`, `eq:synthesis-factorization` | `System.synth`, `System.synth_eq_graphOp` | `FundamentalLemma/Graph` |
| `thm:willems-gramian`, `eq:graph-identification` | `System.graph_identification`, `System.willems_tfae` ((i) ⇔ (ii) ⇔ (iii)), `System.eq_mild_of_trajectory` (last sentence) | `FundamentalLemma/Willems` |
| `eq:record-dynamics` | `System.hasWeakDeriv_mildW` | `FundamentalLemma/Willems` |
| `rmk:input-state-case` | `System.inputState`, `System.H1.inputState`, `System.inputState_mildW` | `FundamentalLemma/Willems` |
| `def:io-behavior` | `System.ioBehavior` | `FundamentalLemma/InputOutput` |
| `eq:io-window-synthesis` | `ioWindowSynth` | `Signal/Shift` |
| `lem:io-parametrization` (stated in the appendix), `eq:io-state-recovery`, `eq:window-factorization` | `System.ioParam`, `System.range_ioParam`, `System.ioParam_injective`, `System.isBoundedBelow_ioParam`, `System.isClosed_ioBehavior`, `System.eq_ioStateRecovery`, `System.ioWindowSynth_eq_ioParam_comp` | `FundamentalLemma/InputOutput` |
| `thm:windowed-io-fundamental-lemma`, `eq:io-behavior-identification` | `System.closure_range_ioWindowSynth` | `FundamentalLemma/InputOutput` |

### Section 5: controllability tests

| Paper | Lean | File |
|---|---|---|
| `prop:fattorini-hautus` (cited; proved, root vectors of `A`) | `System.fattoriniHautusProperty_of_hypotheses` (under `FattoriniHautusHypotheses T`, the property at every `T' > 0`); `System.fattoriniHautusTheorem : sys.FattoriniHautusTheorem` (every system); the hypotheses `System.FattoriniHautusHypotheses`; the conclusion `System.FattoriniHautusProperty`; easy direction `System.hautusCondition_of_approxControllable`; independence of `T` `System.approxControllable_iff_of_fattoriniHautusProperty` | `Controllability/FattoriniHautus`, `Controllability/FHSpectral` |
| `thm:data-fattorini-hautus`, `eq:data-fh` | (i) `System.approxControllable_of_forall_not_exp`; (ii) `System.approxControllable_iff_forall_not_exp`; `κ = ⟨η, x₀⟩ ≠ 0` `System.exp_coeff_eq_and_ne_zero` | `Controllability/InputState` |
| `eq:data-fh-exponential` | `System.exp_of_isHautusEigenvector` | `Controllability/InputState` |
| `thm:io-window-controllability`, `eq:io-window-fh` | (i) `System.approxControllable_of_forall_not_io_exp`; (ii) `System.approxControllable_iff_forall_not_io_exp`; `g ≠ 0` `System.ne_zero_of_io_exp`; the window functional `ioWindowPairing` | `Controllability/InputOutput` |

### Section 6: linear–quadratic regulators

| Paper | Lean | File |
|---|---|---|
| `eq:lqr-cost` | `LQRWeights`, `System.lqrCost`; unique minimiser `System.existsUnique_isMinOn_lqrCost` | `LQR/ModelBased` |
| `thm:lqr-riccati` (cited; proved, without `hyp:compat`), `eq:lqr-feedback` | `System.riccatiTheorem : sys.RiccatiTheorem wts T` (every system, weights and horizon); `System.nonempty_riccatiSolution` (`hyp:H1` and `hyp:H2` suffice); the interface `System.RiccatiSolution`, `System.RiccatiTheorem`; the operator `System.riccatiP` (`P(t)`, the value operator) and the feedback `System.feedback_ae`; `System.bStarP` (`B^⋆P(t)x`); the integral Riccati equation `System.IsRiccatiIntegralSolution` and the full theorem `System.riccatiIntegralTheorem`, `System.riccatiIntegralTheorem_of_pos` (existence, uniqueness, feedback, cost; no `hyp:compat`) | `LQR/ModelBased`, `LQR/RiccatiExistence`, `LQR/ValueOperator`, `LQR/RiccatiEquation`, `LQR/RiccatiIntegral` |
| `eq:lqr-cost-traj`, `eq:lqr-admissible`, `eq:lqr-data-problem` | `System.trajCost`, `System.dataAdmissible`, `IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T 𝒢 x₀)` | `LQR/InputStateOutput` |
| `thm:lqr-data` | `System.lqr_data` (first part); `System.lqr_data_riccati` (second part, from any `RiccatiSolution`); `System.lqr_data_riccati_of_riccatiTheorem` (second part, in the paper's form); `System.lqr_data_riccati_of_H1_H2` (second part with no Riccati hypothesis, from `hyp:H1` and `hyp:H2`) | `LQR/InputStateOutput`, `LQR/RiccatiExistence` |
| `eq:lqr-data-io-problem` | `ioRegulatorCost`, `ioRegulatorFeasible` | `LQR/InputOutput` |
| `thm:lqr-data-io` | `System.lqr_data_io` | `LQR/InputOutput` |

### Appendix: intermediate results of `app:analytic-universal-sufficiency`

| Paper | Lean | File |
|---|---|---|
| the transfer map `𝐇(s) = (s - A_{X,-1})⁻¹ B_X`, its holomorphy and decay, `Ω_⋆` | `System.transferX`, `System.transfer`, `System.transferX_spec`, `System.differentiableOn_transfer`, `System.transfer_decay`, `System.resolventSet_complexify_subset_W`, `System.exists_isPreconnected_resolventSet` | `Informativity/Analytic/Transfer` |
| `eq:analytic-W-growth-bound` | `System.exists_growth_W` | `Semigroup/Analytic` |
| `eq:analytic-exp-convolution`, `eq:analytic-qsummable` | `System.Lc_cexp_smul`, `System.summable_stateCoeff` | `Informativity/Analytic/Expansion` |
| `eq:analytic-state-expansion`, `eq:analytic-annihilator-expansion` | `System.mild_harmonic`, `System.mildW_harmonic`, `System.annihilator_expansion`, `System.window_expansion` | `Informativity/Analytic/Expansion` |
| `lem:bohr-annihilator` | `C0Semigroup.bohr_annihilator`, `System.analyticOnNhd_SW` (the case `E = W`) | `Informativity/Analytic/Bohr` |
| `lem:transfer-laplace`, `eq:analytic-transfer-laplace` | `System.psi`, `System.analyticOnNhd_psi`, `System.memLp_psi`, `System.inner_transfer_eq_laplace`, `System.psiC_eq_zero_of_inner_transfer_eq_zero`, `System.denseRange_Lop_W` | `Informativity/Analytic/Bohr` |

### The boundary-controlled heat equation (`ex:intro-pde`, `app:boundary-heat-informative`)

Names are relative to `DataDrivenControl.BoundaryHeat`.  `X` is any real Hilbert space with a
Hilbert basis `e : HilbertBasis ℕ ℝ X` (the cosine basis of `L²(0, 1)` in the paper), and
`hξ₀ : ξ₀ ∈ Ioo 0 1`.  `ModalData` and `ControlData` bundle the modal data the construction uses;
`heatData hξ₀` instantiates them with the heat equation's.

| Paper | Lean | File |
|---|---|---|
| `ex:intro-pde` (with `ν = 1`) | `heatSystem e hξ₀ : System ℝ W X V ℝ`, tied to the PDE by `heatSystem_SX` (`S_X` is the diagonal semigroup with `λₙ = -(nπ)²`), `hasSum_heatSystem_C` (`C` is point evaluation at `ξ₀` on `D(A)`), `hasSum_heatSystem_Bstar` (`B^⋆η = -η(0)` on `D(A^⋆)`), `heatSystem_B_not_mem_range` and `heatSystem_C_unbounded` (`B` and `C` are unbounded on `X`) | `Examples/BoundaryHeat` |
| eigenvalues and modal coefficients | `eig`, `ctrlCoeff` (`bₙ = -eₙ(0)`), `obsCoeff` (`cₙ = eₙ(ξ₀)`), `not_summable_ctrlCoeff_sq`, `not_summable_obsCoeff_sq` | `Examples/Heat/Kernel` |
| `eq:heat-separated-kernel` (scalar form) | `kernel` (`h = C S(·) b`), `kernelDeriv` (`h'`), `kernel_eq_images` (method of images, by Poisson summation), `exists_abs_kernel_le`, `exists_abs_kernelDeriv_le` (`h` and `h'` are bounded on `(0, ∞)`) | `Examples/Heat/Kernel` |
| `eq:heat-localized-V` (scalar observation norm, see below) | `Xm1` (`X₋₁ = ℓ²`), `ModalData.V` (the graph of the free output in `WithLp 2 (Xm1 × L2 ℝ 1)`), `ModalData.SV`, `ModalData.ιV` (`X ↪ V`: `memLp_obs_toXm1`, `denseRange_ιV`, `consistent_ιV`) | `Examples/Heat/Spaces` |
| `W = D(A_V)`, `eq:heat-W-domain` | `ModalData.W` (`= d.SV.Dom`), `ModalData.ιW`, `mem_SV_generator_domain_iff`, `SV_generator_ιV`, `range_ιW`; the generic `C0Semigroup.Dom`, `C0Semigroup.domSemigroup` | `Examples/Heat/Spaces`, `Semigroup/DomainSpace` |
| the point observation, `C ∈ L(W, ℝ)` | `ControlData.C` (the trace formula in time `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds`, `g = C S(·) w`), `ModalData.hasSum_trace`, `ControlData.hasSum_C` | `Examples/Heat/System`, `Examples/Heat/Estimates` |
| `eq:heat-control-X`, `hyp:H1` | `ModalData.exists_control_bound`, `ControlData.H1`, `heatSystem_H1` (every horizon) | `Examples/Heat/Estimates`, `Examples/Heat/System`, `Examples/BoundaryHeat` |
| `hyp:H2`, `hyp:compat` | `heatSystem_H2` (every horizon), `heatSystem_compat` | `Examples/BoundaryHeat` |
| approximate controllability | `heatSystem_approxControllable`, from `ControlData.inner_ιW_Lop` and `System.approxControllable_of_modal` | `Examples/BoundaryHeat`, `Semigroup/Modal` |
| "Excitation and informativity": `ū`, `iω ∈ ρ(A)`, the growth bound | `heatInput`, `heatInput_apply`, `isHarmonicPE_heatInput`, `abs_mem_closure_range_freq_heatInput`, `mem_resolventSet_heatSystem`, `norm_heatSystem_SX_le`, `heatSystem_isAnalytic` | `Examples/Heat/Input`, `Examples/BoundaryHeat` |
| the dictionary to `L²(0, 1)`: the eigenbasis | `DataDrivenControl.CosineBasis.cosBasis : HilbertBasis ℕ ℝ (L2 ℝ 1)` (`e₀ = 1`, `eₙ = √2 cos(nπξ)`), `PDE.obsCoeff_eq_cosFun`, `PDE.ctrlCoeff_eq_neg_cosFun`, `PDE.eig_eq_cosEig`; `PDE.heatSystemL2 hξ₀ = heatSystem cosBasis hξ₀` | `Analysis/CosineBasis`, `Examples/Heat/PDE` |
| the dictionary: `A` is the Neumann Laplacian | `PDE.IsNeumannH2` (`H²(0, 1)` in integral form, `φ'(0) = φ'(1) = 0`), `PDE.mem_graph_generator_iff`, `PDE.heatSystemL2_A_graph`, `PDE.heatSystemL2_A_adjoint` (`A⋆ = A`) | `Examples/Heat/PDE` |
| the dictionary: `B` is the Neumann control, `C` the point observation | `PDE.inner_cosBasis_neumann_control` (`⟪eₙ, φ''⟫ = λₙ⟪eₙ, φ⟫ + bₙ φ'(0)` if `φ'(1) = 0`), `PDE.heatSystemL2_Bstar` (`B⋆η = -η(0)`), `PDE.heatSystemL2_C` (`C w = φ(ξ₀)`) | `Examples/Heat/PDE` |
| `ex:boundary-heat-informative` on `L²(0, 1)` | `PDE.exists_boundaryHeat_L2`: `exists_boundaryHeat` for `X = L2 ℝ 1`, with the ties in function language | `Examples/Heat/PDE` |
| the cut-off `χ ∈ C_c^∞(0, 1)`, `χ = 1` near `ξ₀` | `Localized.Cutoff` (`χ ∈ C¹`, `tsupport χ ⊆ Ioo 0 1`), `Cutoff.exists_pos_le` (`d_χ > 0`), `Localized.exists_smooth_cutoff` (a `C^∞` cut-off exists, `ContDiffBump`) | `Examples/Heat/LocalizedCutoff` |
| `F_z(t) = e^{-t} χ S(t) z ∈ H¹(0, 1)`; `∫₀^∞ e^{-2t} ‖S(t) z‖²_{H¹} dt = ½ ‖z‖²_X`; `‖χ f‖_{H¹} ≤ c_χ ‖f‖_{H¹}` | `Localized.orbit` (`S(t) z` as a function), `Localized.H1sq` (`‖f‖²_{H¹} = ∫₀¹ f² + ∫₀¹ (f')²`), `Localized.orbitH`, `norm_orbitH_sq_eq`, `orbitH_Sm` (`F_{S(s)z}(t) = e^s F_z(t + s)`), `integral_H1sq_orbit`, `norm_orbitH_sq_le`, `abs_orbit_le` | `Examples/Heat/LocalizedOrbit` |
| `eq:heat-localized-V` (the paper's `V`) | `Localized.V χ` (closed graph of `z ↦ F_z` in `WithLp 2 (Xm1 × L²(0, ∞; L² × L²))`), `norm_V_sq_eq` (the norm in function language), `exists_fstV_eq_iff` (`V = {z : ‖z‖_V < ∞}`), `Localized.SV χ`; `X ↪ V`: `Localized.ιV χ`, `norm_ιV_sq_le`, `ιV_injective`, `denseRange_ιV` | `Examples/Heat/LocalizedSpaces` |
| `W = D(A_V)`, `eq:heat-W-domain` (paper's `V`) | `Localized.W χ`, `ιW`, `mem_SV_generator_domain_iff`, `SV_generator_ιV`, `range_ιW` | `Examples/Heat/LocalizedSpaces` |
| `eq:heat-separated-kernel` on `supp χ` | `Localized.kernelDerivX_eq_tsum` (image series of `∂_ξ q'`), `exists_abs_kernelDeriv_le_unif` (`q'`, `∂_ξ q'` bounded on `(0, ∞) × [d, 1)`) | `Examples/Heat/LocalizedKernel` |
| `eq:heat-control-X`, `hyp:H1` (paper's `V`) | `Localized.exists_control_bound_loc`, `orbit_genXm1_eq`, `ctrlVec_eq`, `memLp_orbitH_ctrlVec`, `heatSystemLoc_H1` (every horizon) | `Examples/Heat/LocalizedControl`, `Examples/Heat/LocalizedSystem` |
| `C ∈ L(W, ℝ)`, `hyp:H2`, `hyp:compat` (paper's `V`) | `Localized.J` (`V ↪ V_scalar`), `Localized.JW`, `Localized.C`, `heatSystemLoc_C` (`C w = φ(ξ₀)` on `H²_N`), `heatSystemLoc_H2` (every horizon), `heatSystemLoc_compat` | `Examples/Heat/LocalizedSystem` |
| `ex:boundary-heat-informative` with the paper's spaces | `Localized.heatSystemLoc hξ₀ χ hχ : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ`, `heatSystemLoc_Bstar`, `heatSystemLoc_B_not_mem_range`, `heatSystemLoc_C_unbounded`, `heatSystemLoc_approxControllable`, `heatSystemLoc_TFAE`, `heatSystemLoc_informative`, `heatSystemLoc_windowInformative`, **`Localized.exists_boundaryHeat_loc`** | `Examples/Heat/LocalizedSystem` |

### The delay system with delayed output (`ex:intro-delay`)

Names are relative to `DataDrivenControl.Delay`.  `E`, `U`, `Y` are real Hilbert spaces (the
paper's `ℝⁿ`, `ℝᵐ`, `ℝᵖ`), and the history lives on `(0, h]`: `ψ(s) = φ(s - h)`.

| Paper | Lean | File |
|---|---|---|
| the delay equation (`M = 0`) | `Equation h E` (point delays `Aₖ`, `hₖ ∈ [0, h]`, and a distributed part `L_d : L2 E h →L[ℝ] E`); `kernelOp`, `kernelOp_apply` (the kernel form `∫_{-h}^0 A_d(θ) x(t + θ) dθ`); `traj` (history followed by solution); `Equation.IsSolOn` (integral form) | `Examples/Delay/Solution` |
| solutions | `Equation.sol`, existence `Equation.isSolOn_sol`, uniqueness `Equation.IsSolOn.eqOn` and `Equation.eqOn_sol`, linearity `Equation.sol_add`, `Equation.sol_smul`, time shift `Equation.sol_add_time`, Grönwall bound `Equation.norm_sol_le`, `H¹` regularity `Equation.hasWeakDeriv_traj` | `Examples/Delay/Solution` |
| the state space `X = ℝⁿ × L²(-h, 0; ℝⁿ)` and the semigroup | `State h E` (`WithLp 2 (E × L2 E h)`), `Equation.semigroup` (`S(t)(r, ψ) = (x(t), x_t)`, `semigroup_apply`), `Equation.norm_semigroup_le`, `Equation.exists_norm_semigroup_le` | `Examples/Delay/Semigroup` |
| the generator | `Equation.mem_generator_domain_iff` (`D(A) = {(g(h), g) : g ∈ H¹(0, h; E)}`), `Equation.generator_apply` (`A(g(h), g) = (∑ₖ Aₖ g(h - hₖ) + L_d g, g')`), `Equation.mem_generator_domain_of_hasWeakDeriv`; translation of `H¹` signals in `L²`: `window_sub_window_eq_integral`, `tendsto_diffQuot_window`, `exists_ae_eq_of_tendsto_diffQuot_window` | `Examples/Delay/Semigroup`, `Examples/Delay/Translation` |
| the system | `Model h E U Y` (adds `B₀`, the output delays `Cₖ`, `h'ₖ ∈ [0, h]` and `C_d`), `Model.sys : System U W X X Y` with `W = D(A)` (`C0Semigroup.Dom`) and `X = V = State h E`, `Model.Bop` (`B = (B₀, 0)`, bounded), `Model.Cop` (`C ∈ L(W, Y)`), `Model.Cop_apply` (`C (g(h), g) = ∑ₖ Cₖ g(h - h'ₖ) + C_d g` on `D(A)`) | `Examples/Delay/System` |
| `L_T`, `hyp:H1`, `hyp:H2`, `hyp:compat` | `Model.ctrlState_eq_conv`, `Model.ιW_L` (`L_T u = (x(T), x_T)` for the zero history), `Model.H1`, `Model.H2` (every horizon), `Model.compat` | `Examples/Delay/System` |
| "a discrete output delay generally makes `C` unbounded on `X`" | `Model.not_exists_bound_C` (if `∑_{h'ₖ = θ} Cₖ ≠ 0` for some `θ ∈ (0, h]`), `Model.not_exists_bound_C_of_ne_zero` | `Examples/Delay/Unbounded` |

### The neutral delay system (`ex:intro-delay`, `M ≠ 0`)

Names are relative to `DataDrivenControl.NeutralDelay`.  Conventions as for the retarded system
(history on `(0, h]`, `ψ(s) = φ(s - h)`, `traj`, `window`, `Delay.State h E`).

| Paper | Lean | File |
|---|---|---|
| the operators `L`, `M`, `C` on the history | `DelayOp h E F` (`∑ₖ Pₖ φ(-δₖ) + D φ`, `δₖ ∈ [0, h]`, `D` bounded on `L²`), `DelayOp.eval`, `DelayOp.eLpNorm_eval_le`, `DelayOp.hasWeakDeriv_eval`, `DelayOp.opL` (zero history, on `L²(0, τ)`), `primL` | `Examples/NeutralDelay/Operator` |
| the neutral equation `d/dt (x(t) - M x_t) = L x_t + f` | `Equation h E` (extends `Delay.Equation` by `Mₖ`, `mₖ ∈ (0, h]` ("no mass at `0`") and `M_d`), `Equation.L`, `Equation.M`, `Equation.prim` (`x(t) - M x_t = r + ∫₀ᵗ (L x_s + f)`), `Equation.IsSolOn` (a.e. integral form, `x ∈ L²`) | `Examples/NeutralDelay/Solution` |
| solutions | `Equation.isUnit_opK` (weighted contraction: `isUnit_one_sub_of_wnorm_le`, `wnorm_shift_le`, `wnorm_window_le`, `wnorm_primL_le`), existence `Equation.isSolOn_solL`, `Equation.isSolOn_sol`, uniqueness `Equation.IsSolOn.ae_eq`, `IsSolOn.add`, `IsSolOn.smul`, time shift `IsSolOn.shift`, `Equation.prim_shift`, the `L²` bound `Equation.norm_solL_le` | `Examples/NeutralDelay/Weighted`, `Examples/NeutralDelay/Solution` |
| regularity | `Equation.exists_hasWeakDeriv`, `Equation.IsSolOn.exists_hasWeakDeriv` (`H¹` history `g`, `r = g(h) - M g`, `L²` forcing ⇒ `H¹` trajectory) | `Examples/NeutralDelay/Regularity` |
| the state `(x(t) - M x_t, x_t) ∈ ℝⁿ × L²` and the semigroup (Burns–Herdman–Stech 1983) | `Equation.semigroup` (`semigroup_apply`), `Equation.norm_semigroup_le`, `Equation.stateAt_stateAt` | `Examples/NeutralDelay/Semigroup` |
| the generator | `Equation.mem_generator_domain_iff` (`D(A) = {(g(h) - M g, g) : g ∈ H¹(0, h; E)}`), `Equation.generator_apply` (`A (g(h) - M g, g) = (L g, g')`) | `Examples/NeutralDelay/Semigroup` |
| the system | `Model h E U Y` (adds `B₀`, `Cₖ`, `h'ₖ ∈ [0, h]`, `C_d`), `Model.sys : System U W X X Y` with `W = D(A)`, `X = V = Delay.State h E`, `Model.Bop`, `Model.Cop`, `pointEval_eq`, `Model.evalOp` (`H¹` point evaluation from `(g, g')`), `Model.Cop_apply` (`C (g(h) - M g, g) = ∑ₖ Cₖ g(h - h'ₖ) + C_d g`) | `Examples/NeutralDelay/System` |
| `L_T`, `hyp:H1`, `hyp:H2`, `hyp:compat` | `Model.ctrlState_eq_conv`, `Model.ιW_L` (`L_T u = (x(T) - M x_T, x_T)`), `Model.H1`, `Model.H2` (every horizon), `Model.compat` | `Examples/NeutralDelay/System` |
| consistency with `M = 0` | `Equation.semigroup_eq_of_M_eq_zero` (`= Delay.Equation.semigroup`), `Equation.isSolOn_of_retarded` | `Examples/NeutralDelay/Retarded` |
| "a discrete output delay generally makes `C` unbounded on `X`" | `Model.not_exists_bound_C` (if `∑_{h'ₖ = θ} Cₖ ≠ 0` for some `θ ∈ (0, h]` and no `mₖ = θ`) | `Examples/NeutralDelay/Unbounded` |

### The wave equation with Dirichlet control (`ex:intro-wave`)

Names are relative to `DataDrivenControl.Wave`.  `X₁`, `X₂` are real Hilbert spaces with Hilbert
bases `s, f : HilbertBasis ℕ ℝ _`, standing for `sₙ = √2 sin(nπξ)` in `L²(0, 1)` and `ωₙ sₙ` in
`H⁻¹(0, 1)` (with the norm `c⁻¹‖·‖_{H⁻¹}`); the state space is `X = WithLp 2 (X₁ × X₂)`, with energy
coordinates `aₙ = ⟪sₙ, w⟫`, `bₙ = ⟪fₙ, v⟫`.  Modes count from `0`: `ωₙ = freq c n = c(n + 1)π`.
`q : X₁` is the observation weight, `qₙ = ⟪sₙ, q⟫`.

| Paper | Lean | File |
|---|---|---|
| `ex:intro-wave` | `waveSystem s f c q : System ℝ X X Vsp ℝ` (`W = X`, `ιW = id`); `exists_wave` (existential form, with the ties below in the statement) | `Examples/Wave/Spaces`, `Examples/Wave/System` |
| the first-order system | `waveSystem_SX` (`S_X` is `Rotation.rotGroup s f (freq c)`), `inner_fst_waveSystem_SX`, `inner_snd_waveSystem_SX`; `inner_waveSystem_Lop` (`aₙ' = ωₙ bₙ`, `bₙ' = -ωₙ aₙ + c√2 u`, in integrated form) | `Examples/Wave/Spaces`, `Examples/Wave/System` |
| "Dirichlet control makes `B` unbounded on `X`" | `waveSystem_B_not_mem_range`, `waveSystem_B_apply_not_mem_range` (`B u ∉ X` for `u ≠ 0`); `hasSum_waveSystem_Bstar` (`B^⋆η = ∑ c√2 ⟪fₙ, η₂⟫` on `D(A^⋆)`) | `Examples/Wave/Spaces`, `Examples/Wave/System` |
| "the observation is bounded on `X`" | `hasSum_waveSystem_C` (`C x = ∑ qₙ aₙ = ⟪q, w⟫`), `norm_waveSystem_C_le` | `Examples/Wave/Spaces` |
| `hyp:H1`, `hyp:H2`, `hyp:compat` | `waveSystem_H1`, `waveSystem_H2` (every horizon, from `T = 2/c`), `waveSystem_compat` | `Examples/Wave/System`, `Examples/Wave/Spaces` |
| Section 7: the wave group is not analytic | `waveSystem_not_isAnalytic`, `Rotation.not_isAnalytic` | `Examples/Wave/System`, `Semigroup/Rotation` |
| the dictionary to `L²(0, 1)`: the sine basis | `SineBasis.sinBasis : HilbertBasis ℕ ℝ (L2 ℝ 1)` (`sₙ = √2 sin((n + 1)πξ)`), `SineBasis.inner_sinBasis` (`⟪sₙ, f⟫ = ∫₀¹ sₙ f`), `SineBasis.hasDerivAt_sinFun`, `SineBasis.integral_sinFun_mul_deriv` | `Analysis/SineBasis` |
| the dictionary: `H¹₀(0, 1)` and `H⁻¹(0, 1)` | `Sobolev01.H10` (mean-zero classes `φ'`, the function `h10Fun φ = ∫₀^· φ'`, `exists_H10`), `Sobolev01.Hm1 = StrongDual ℝ H10` (the dual norm, Hilbert through Riesz), `Sobolev01.riesz : H10 ≃ₗᵢ[ℝ] Hm1` (`-∂_ξξ` in weak form), `Sobolev01.hm1Basis` (`(n + 1)π sₙ`) | `Analysis/Sobolev01` |
| the dictionary: the `H⁻¹` norm in sine coefficients, `L² ↪ H⁻¹` | `Sobolev01.hasSum_norm_sq` (`‖ℓ‖² = ∑ₙ ℓ(sₙ)² / ((n + 1)π)²`), `Sobolev01.hasSum_norm_embed_sq`, `Sobolev01.embed`, `norm_embed_le`, `injective_embed`, `denseRange_embed` | `Analysis/Sobolev01` |
| the dictionary: `H⁻¹` with the norm `c⁻¹‖·‖` and `fₙ = ωₙ sₙ` | `PDE.smul_hm1Basis`, `PDE.norm_eq_inv_mul_norm_smul`, `PDE.scaledInner_freq_smul`, `PDE.hasSum_scaledInner_sq` | `Examples/Wave/PDE` |
| `ex:intro-wave` on `L²(0, 1) × H⁻¹(0, 1)` | `PDE.waveSystemL2 c q = waveSystem sinBasis hm1Basis c q`, `PDE.waveSystemL2_C` (`C x = ∫₀¹ q w`), `PDE.waveSystemL2_Lop`, `PDE.waveSystemL2_A_domain` (`D(A) = H¹₀ × L²`), `PDE.waveSystemL2_A_apply` (`A (φ, v) = (c v, c ∂_ξξ φ)`), `PDE.waveSystemL2_Bstar` (`B⋆η = ζ'(0)`, `-ζ'' = η₂`, Dirichlet), `PDE.exists_isDirichletH2_of_mem_adjoint_domain`; `PDE.exists_wave_L2` | `Examples/Wave/PDE`, `Analysis/Sobolev01` |

### The proofs of the cited theorems

The module docstrings refer to these steps by their labels.  The proof routes are described
under "Proofs that take a different route".

| Step | Lean | File |
|---|---|---|
| FH1: the unobservable subspace `N = ⋂_{τ>0} ℛ_τ(0)^⊥`; `η ⊥ ℛ_{T'}(0)` for one `T' > 0` gives `η ∈ N` | `FH.unobs`, `FH.mem_unobs_of_forall`, `FH.adjoint_resolvent_mem_unobs`, `FH.bstar_eq_zero_of_mem_unobs` | `Controllability/FHObservation` |
| FH2: compact resolvents | `isCompactOperator_resolvent`, `mem_domain_of_resolvent_eq_smul`, `dense_iSup_maxGenEigenspace_resolvent`, `resolvent_adjoint`, `le_orthogonal_iSup_maxGenEigenspace_adjoint`, `eq_bot_of_dense_iSup_maxGenEigenspace_adjoint` | `Semigroup/CompactResolvent` |
| FH3: `N_ℂ` is invariant under `K = R(μ₀, A^⋆)` and, under the Hautus condition, contains no eigenvector of `K` | `FH.unobsC`, `FH.exists_real_resolvent`, `FH.resolvent_mem_unobsC`, `FH.eq_zero_of_resolvent_eq_smul` | `Controllability/FHResolvent` |
| FH4–FH5: `N_ℂ = 0` | `FH.unobsC_eq_bot` | `Controllability/FHSpectral` |
| R1: tail problems on the fixed control space `L²(0, T; U)` | `Riccati.cut`, `Riccati.LQ`, `System.𝓞V`, `System.tailA` (and `tailB`, `tailC`, `tailD`), `System.lqTail`, `System.lqrCost_eq_cost` | `LQR/TailOperators` |
| R2–R3: the value operator and its strong continuity | `Riccati.LQ.WF.cost_eq`, `Riccati.LQ.scont_Pop`, `System.riccatiP`, `System.continuousOn_riccatiP`, `System.riccatiP_terminal` | `LQR/ValueOperator` |
| R4: dynamic programming | `System.uopt_lqTail_eq_cut`, `System.Pop_lqTail_mildW` | `LQR/DynamicProgramming` |
| R5: the adjoint of the input map | `System.coeFn_adjoint_input` | `LQR/Feedback` |
| R6: existence | `System.feedback_ae`, `System.riccatiSolution_of_pos`, `System.riccatiSolution_of_nonpos`, `System.nonempty_riccatiSolution` | `LQR/RiccatiExistence` |
| R7: the integral Riccati equation and its uniqueness | `System.IsRiccatiIntegralSolution`, `System.bStarPV`, `System.IsRiccatiIntegralSolution.eqOn` | `LQR/RiccatiEquation` |
| R8: the right derivative along the free motion | `System.reducedValue`, `System.exists_costate_uopt`, `System.hasDerivWithinAt_reducedValue` | `LQR/RiccatiIntegralDeriv` |
| R9: the value operator solves the integral equation | `System.riccatiP_self_eq`, `System.isRiccatiIntegralSolution_riccatiP`, `System.riccatiIntegralTheorem` | `LQR/RiccatiIntegral` |

## How the formal statements relate to the paper

This section lists every difference between a Lean statement and the paper.  Before the proofs
were written, an independent review compared the statements of Sections 2–6 and the appendix
with the paper and found no blocking or major issue.  The differences fall into five groups:
modelling choices, which fix how the paper's objects are represented;
the two cited theorems, which are proved, one under a corrected hypothesis; statements that are
stronger than the paper's or have a different but equivalent form; proofs that take a different
route; and corrections to the formal statements that were made during the work.  No step of the
paper's own proofs was found to be false.  One hypothesis of a cited theorem was: Boyer's
root-vector hypothesis on `A^⋆` does not suffice for the Fattorini–Hautus test, and the paper now
states it for `A`.  The route changes fill in sketched or implicit steps, or avoid machinery the
formalisation does not have, such as a semigroup on the extrapolation space, the adjoint
semigroup, `H¹(0, 1)` or contour integrals.

### Modelling choices

* **Signals.**  A signal is a function `ℝ → E`, square integrable on the window
  `I = (0, T]`: `MemLp u 2 (μI T)` with `μI T = volume.restrict (Ioc 0 T)`.  The paper's `(0, T)`
  differs by a null set.  Operators (`𝓕_τ`, `𝓞_τ`, `𝓜_T`, `𝒵`, `𝒴`, `L_t`) act on Mathlib's
  `Lp E 2 (μI T)`, abbreviated `L2 E T`.  Definitions such as `Informative`, `WindowInformative`
  and `PersistentlyExciting` take raw functions; square integrability is a hypothesis of the
  lemmas that need it.  A window `ū(s + ·)` is `window T ū s : L2 U T`.
* **Products.**  Products of Hilbert spaces are `WithLp 2 (E × F)`, nested for
  `U × W × V₋₁ × Y` (`System.GraphSpace`), and `U^L` is `PiLp 2 (fun _ : Fin L => U)`, so that
  orthogonal complements and Gramians are the paper's.
* **Closed spans.**  `cspan 𝕜 μ z` is *defined* as `(annihilator 𝕜 μ z)ᗮ`, with
  `annihilator 𝕜 μ z = {ζ | ∀ᵐ t ∂μ, ⟪ζ, z t⟫ = 0}`.  `isLeast_cspan` proves that it is the
  paper's "smallest closed subspace containing `z t` for a.e. `t`".  Informativity is
  `cspan = ⊤`, equivalently `annihilator = ⊥`.  The scalar field is an explicit argument, because
  a complex space is also a real inner product space.
* **Test functions instead of distributions and `H₀¹`.**  A test function on `(0, T)` is a
  smooth `φ : ℝ → ℝ` with `tsupport φ ⊆ Ioo 0 T` (`IsTestFunction T φ`).  `⟨Dᵏū, φ⟩` is the
  moment `derivMoment k ū φ = (-1)ᵏ ∫ φ⁽ᵏ⁾ ū`, and "`R = 0` in `𝒟'(I)`" means "for every test
  function".  The synthesis operator `𝒲` of Section 4 is evaluated on test functions instead of
  `H₀¹(I)` (`System.synth`).  Its image has the same closure, and condition (iii) of
  `thm:willems-gramian` is equivalent: "on `H₀¹`" ⇒ "on `C_c^∞`" is trivial, and the paper's
  Step 3 only tests against `C_c^∞`.
* **`H¹` in integral form.**  `HasWeakDeriv T x g` means `g ∈ L²(0, T; E)` and
  `x t = x 0 + ∫₀ᵗ g` for every `t ∈ [0, T]`, which also fixes the continuous representative.
  In `thm:willems-gramian` the record derivative `ẋ̄ ∈ L²(I; V₋₁)` is an explicit argument `xd`
  with this hypothesis; all such derivatives agree a.e. and give the same Gramian, and one
  exists by `System.hasWeakDeriv_mildW`.
* **Semigroups.**  `C0Semigroup 𝕜 E` is indexed by `ℝ≥0`, with strong continuity on all of
  `ℝ≥0`; on a Banach space this is equivalent to continuity at `0⁺`
  (`C0Semigroup.ofTendsto`).  `S.real t` extends it to real times by the identity for `t ≤ 0`,
  for convolutions `S(t - r)`.  The generator is a Mathlib `LinearPMap`, and `A†` is Mathlib's
  `LinearPMap.adjoint`.  A `System` carries three consistent semigroups `SW`, `SX`, `SV`, one
  per state space.  `hyp:compat` uses the equivalent graph norm `‖v‖ + ‖A_V v‖`.
* **The extrapolation space: dual model.**  `V₋₁` is the graph of `A_V†`, a closed subspace of
  `WithLp 2 (V × V)` and hence a Hilbert space (`C0Semigroup.Extrap`).  `V ↪ V₋₁` and
  `A₋₁ ∈ L(V, V₋₁)` are the Hilbert adjoints of the two projections, so
  `⟪A₋₁ x, (η, A†η)⟫ = ⟪x, A†η⟫`, and the norm is that of `D(A†)'`, i.e. the usual extrapolation
  norm.  With this choice "`ẋ = A₋₁ x + f` in `L²(I; V₋₁)`" in integral form is literally Ball's
  weak formulation (`C0Semigroup.isWeakSol_iff_extrap`).  The Gramian `𝒢` of Section 4 depends
  on the inner product of `V₋₁`, but `(ker 𝒢)ᗮ` is the closed span of the record, a topological
  notion, so the conditions of `thm:willems-gramian` do not depend on which equivalent Hilbert
  norm `V₋₁` carries.
* **Analytic semigroups.**  `IsAnalytic S` is the scalar-agnostic characterisation (Pazy,
  Thm 2.5.2 (d), local form): `S t` maps into `D(A)` for `t > 0` and `‖A S(t)‖ ≤ C/t` on
  `(0, 1]`.  It is equivalent to holomorphy on a sector and needs no complexification; for a
  real space it is equivalent to analyticity of the complexified semigroup.
* **Weights and Riccati operators.**  `G ∈ L(V, V')` and `P(t) ∈ L(V, V')` are bounded
  symmetric bilinear forms on `V`, which avoids pivot duals.  `B^⋆P(t)x` is the Riesz
  representer of `v ↦ P(t)(x, Bv)` (`System.bStarP`), and `R⁻¹` is `Ring.inverse R`.
* **Junk values.**  Definitions never take hypotheses.  `L t u` (the `W`-preimage of the
  `V`-valued convolution), `Lop`, `𝓕` and `𝓞` are `0` where `hyp:H1` or `hyp:H2` fails;
  `resolvent` is `0` off the resolvent set; `window` returns `0` on a non-`L²` signal;
  `derivMoment` is `0` for a non-integrable signal.  No junk value makes a
  theorem vacuous: on junk data, informativity, window informativity, persistency of
  excitation and observability are *false* (except on zero spaces), never vacuously true.  Two
  further conventions are harmless for the same reason.  The `System` structure does not
  require completeness, but every theorem about systems assumes `[CompleteSpace]` for all five
  spaces.  `hyp:H1` and `hyp:H2` hold vacuously for `T ≤ 0`, but every theorem also assumes
  `0 < T`.
* **Complex scalars.**  The paper states every theorem for real Hilbert spaces and passes to
  `X_ℂ` where complex spectra enter (Sections 3.5 and 5); so does the formalisation.
  `Complexification X` is a complex Hilbert space with the Hermitian product `⟪·, ·⟫_ℂ`, and
  the paper's complex-*bilinear* pairing is `⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ`.  The bilinear
  convention matters: with a Hermitian product, Step 1 of `app:data-fattorini-hautus` would give
  `conj λ` instead of `λ`.  `A^⋆` on `X_ℂ` is `sys.A.adjoint.complexify`, `B^⋆` is
  `sys.Bstar.complexify`, `ρ(A)` is `resolventSet sys.A.complexify`, and `S(t)` acts on `X_ℂ`
  as `(sys.SX.real t).complexify`.  The paper's `W'` (and `E'_ℂ` in `lem:bohr-annihilator`) is
  modelled by `W` (`E_ℂ`) through the Riesz map, with `X ↪ W'` given by `ιW†`.  No complexified
  extrapolation space is needed.
* **Indexing in the examples.**  The examples count from `0`: the paper's `eₙ`, `n ≥ 1`, is
  `e (n - 1)`.  So `PECounterexample.lam n = -(n + 1)` is the paper's `-n`, and the input of
  `ex:window-strictly-stronger` is `∑ₙ 2^{-(n+1)} sin((n+1)t) e n`.  In `lem:harmonic-pe` the
  orthonormal basis is any `HilbertBasis J ℝ U` with an injective numbering `n : J → ℕ`; the
  paper's `j` is `n j + 1` and its `k ≥ 1` is `k + 1`.  `PECounterexample.input` is only
  meaningful for `t ≥ 0` (the series diverges for `t < -log 4`, where `input` is `0`); every
  statement reads it on `t ≥ 0` only.  The heat example numbers its modes from `0`, as the paper
  does (`λ₀ = 0`, `e₀ = 1`): the paper's `eₙ` is `e n`.  Its input index `k ≥ 1` is `k + 1` in
  `heatInput`, so `heatFreq k = 1 + 1/(k + 2)` is the paper's `ω_{k+1}`.
* **Trace class: nuclear representations, and `tr |T| < ∞`.**
  `TraceClass.IsTraceClass T` means `T = ∑ₙ aₙ ⊗ bₙ`, convergent in operator norm, with
  `∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`, where `a ⊗ b = ⟪b, ·⟫ • a` (`InnerProductSpace.rankOne`).
  `TraceClass.trace T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` in a Hilbert basis `stdHilbertBasis` chosen once; for a
  trace-class `T` the same sum is obtained in every Hilbert basis (`IsTraceClass.hasSum_trace`)
  and equals `∑ₙ ⟪bₙ, aₙ⟫` for every representation (`trace_eq_tsum_of_hasSum`).  The definition
  is validated in finite dimension (`trace_eq_linearMap_trace`) and by `trace (a ⊗ b) = ⟪b, a⟫`,
  and it is the textbook one (`Analysis/TraceClassAbs`): `T` is trace class iff
  `∑ᵢ ⟪bᵢ, |T| bᵢ⟫ < ∞` in every Hilbert basis (nonnegative terms), iff `|T|` is trace class, and
  `tr |T|` is the nuclear norm, the least `∑ₙ ‖aₙ‖ ‖bₙ‖` over all representations, attained
  (`isTraceClass_iff_summable_realAbs`, `isLeast_nuclearSums_realAbs`, and the `cfcAbs`
  versions).  On a complex Hilbert space `|T|` is Mathlib's `CFC.abs T`.  Mathlib has no `|T|` on
  real Hilbert spaces and no polar decomposition, so `Analysis/PolarDecomposition` builds both:
  `realAbs T` is the restriction to `X ⊆ X_ℂ` of `(T_ℂ† T_ℂ)^{1/2}`, which commutes with the
  conjugation by uniqueness of the positive square root; it is the unique positive square root
  of `T† T` (`realAbs_unique`).  The polar part sends `|T| x ↦ T x`, extends by continuity to
  `closure (range |T|)` and by `0` to its orthogonal complement; it is a partial isometry with
  `T = U |T|` and `U† T = |T|`.  A trace-class `T` has `|T| = U† T` trace class; conversely a
  summable diagonal makes `|T|^{1/2}` Hilbert–Schmidt, so `|T| = (|T|^{1/2})† |T|^{1/2}` and
  `T = U |T|` are trace class.  The nuclear-norm identity needs no singular value decomposition:
  `T = ∑ⱼ U |T|^{1/2} fⱼ ⊗ |T|^{1/2} fⱼ` in any Hilbert basis `f` attains `tr |T|`.  Lean does not
  synthesise the `CFC` instances on `Complexification X →L[ℂ] Complexification X` (it fails on
  `IsScalarTower ℝ (X_ℂ →L[ℂ] X_ℂ) (X_ℂ →L[ℂ] X_ℂ)`), so the real construction uses
  `sqrtOp A`, which is `CFC.sqrt A` by definition with only Hilbert-space instance arguments.
  For the Gramian, `|𝒢(z)| = 𝒢(z)` (`realAbs_gramian`), and the equivalence specialises to
  `hasSum_re_inner_gramian`.  The names live in the namespace `TraceClass`, apart from Mathlib's
  `LinearMap.trace` and `CFC.abs`.
* **Modal models.**  The heat equation is built in eigenfunction coordinates.  `X`
  is any real Hilbert space with a Hilbert basis `e : HilbertBasis ℕ ℝ X`, and `A` generates the
  diagonal semigroup with the Neumann eigenvalues `λₙ = -(nπ)²`.  `X₋₁` is `ℓ²` in the
  coordinates `⟪eₙ, x⟫ / (1 - λₙ)`, and the embeddings are diagonal maps (`Diagonal.diagMap`).
  Four facts tie the model to the PDE: `S_X` is the diagonal semigroup with the
  paper's eigenvalues; `C` on `D(A)` is the modal formula `∑ₙ eₙ(ξ₀) xₙ`, i.e. point evaluation
  at `ξ₀`; `B^⋆` on `D(A^⋆)` is the modal formula `∑ₙ bₙ ηₙ`, i.e. `-η(0)`, which states that
  `B` is the Neumann control without an `X₋₁`-valued `B`; and `B` and `C` are unbounded on `X`.
  The dictionary to `L²(0, 1)` is formalised in `Analysis/CosineBasis` and `Examples/Heat/PDE`.
  The cosine family `e₀ = 1`, `eₙ = √2 cos(nπξ)` is a Hilbert basis of `L2 ℝ 1` (`cosBasis`;
  complete by Stone–Weierstrass, since the span of the cosines is a point-separating subalgebra
  of `C[0, 1]`).  With `e = cosBasis` (`heatSystemL2`), the generator is the Neumann Laplacian
  (`D(A) = H²_N(0, 1)` in the integral form of `HasWeakDeriv`, `A φ = φ''`, `A⋆ = A`),
  `C w = φ(ξ₀)`, `B⋆η = -η(0)`, and `⟪eₙ, φ''⟫ = λₙ⟪eₙ, φ⟫ + bₙ φ'(0)` is the weak form of the
  Neumann control; `exists_boundaryHeat_L2` states the example on `L²(0, 1)` with these ties.  The model has diffusivity `ν = 1`, as `ex:boundary-heat-informative` does.
* **The wave model.**  As for heat, the wave equation is built in modal coordinates:
  `X = WithLp 2 (X₁ × X₂)` with Hilbert bases `s` (the sines `sₙ` in `L²`) and `f` (`ωₙ sₙ` in
  `H⁻¹`, norm `c⁻¹‖·‖_{H⁻¹}`, so that the energy norm `‖w‖² + c⁻²‖v‖²_{H⁻¹}` is used, equivalent
  to that of `L² × H⁻¹`).  The paper makes no formal claim, so the spaces are a choice.
  `W = X` is forced: the wave equation is exactly controllable for `T ≥ 2/c`, and `hyp:H1` maps
  `L_T` boundedly into `W`.  `V` is `ℓ² × ℓ²` with the weight `(1 + ωₙ²)⁻¹ + qₙ²` on both
  coordinates of mode `n`: the first term puts `B` into `V`, the second makes `hyp:H2` hold
  (with `V = X₋₁`, `hyp:H2` fails for some `q ∈ L²`).  `hyp:H1` and `hyp:H2` are proved at
  `T = 2/c` by Bessel's inequality and its dual for `cos(ωₙ·)` and `sin(ωₙ·)`, which are
  orthogonal on `(0, 2/c]` because `ωₙ = c(n + 1)π`; no Ingham inequality is needed.
  The dictionary to functions on `(0, 1)` is formalised in `Analysis/SineBasis`,
  `Analysis/Sobolev01` and `Examples/Wave/PDE`.  `sₙ = √2 sin((n + 1)πξ)` is a Hilbert basis of
  `L2 ℝ 1` (`sinBasis`; complete by integration by parts against the cosine basis: if `f ⊥ sₙ`
  for all `n`, then `F = ∫₀^· f` is orthogonal to every `e_{n+1}`, hence constant, hence `0`).
  `H¹₀(0, 1)` is modelled by derivatives: `H10` is the closed subspace of mean-zero classes of
  `L²(0, 1)`, and `φ : H10` stands for the function `h10Fun φ = ∫₀^· φ` with the norm `‖φ'‖_{L²}`,
  so the coercion `H10 → L2 ℝ 1` is the derivative; every `x ∈ H¹` with `x(0) = x(1) = 0`
  arises (`exists_H10`).  `H⁻¹(0, 1)` is literally the dual `Hm1 = StrongDual ℝ H10` with its
  dual norm, made a Hilbert space by `⟪ℓ, ℓ'⟫ = ⟪riesz⁻¹ ℓ, riesz⁻¹ ℓ'⟫`, where
  `riesz : H10 ≃ₗᵢ[ℝ] Hm1` is the Dirichlet Laplacian `-∂_ξξ` in weak form.
  `waveSystemL2 c q = waveSystem sinBasis hm1Basis c q` takes `X₂ = Hm1` with its own norm and
  the basis `hm1Basis n = (n + 1)π sₙ`; the factor `c⁻¹` of the paper's velocity norm sits in the
  identification of the state instead of in a type (which would need `c > 0` at the type level):
  the velocity of `(w, x₂)` is `∂ₜw = c • x₂`, and `x₂ ↦ c • x₂` is an isometry onto `H⁻¹` with
  the norm `c⁻¹‖·‖` that sends `hm1Basis n` to the paper's `fₙ = ωₙ sₙ`.  With this,
  `C x = ∫₀¹ q w`; `D(A) = H¹₀ × L²` with `A (φ, v) = (c v, c ∂_ξξ φ)`, which is the paper's
  `A (w, v) = (v, c² ∂_ξξ w)` in the velocity `c • x₂`; and on `D(A⋆)`, `B⋆η = ζ'(0)` for the
  solution `ζ ∈ H¹₀ ∩ H²` of `-ζ'' = c • η.snd`.
* **Graph-norm spaces.**  Every new Hilbert space is a closed submodule of a
  `WithLp 2` product, as `C0Semigroup.Extrap` is.  `D(A)` with the graph norm is the graph of
  `A` (`C0Semigroup.Dom`, with the restricted semigroup `domSemigroup`); it is the `W` of the
  heat example (`W = D(A_V)`) and of the delay example (`W = D(A)`).  The heat `V` is the graph
  of `z ↦ C S(·) z` in `WithLp 2 (X₋₁ × L²(0, 1))`.
* **The heat `V`: the scalar observation norm (modal model).**  The paper
  (`eq:heat-localized-V`) measures
  the orbit `χ S(t) z` in `H¹(0, 1)`, with
  a cut-off `χ` near `ξ₀` and the weight `e^{-2t}` on `(0, ∞)`.  The formalisation observes the
  orbit at `ξ₀` instead: `‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀¹ |C S(t) z|² dt`.  This needs neither
  `H¹(0, 1)` nor `H¹ ↪ C[0, 1]`, `hyp:H2` holds by construction, and the claims of
  `ex:boundary-heat-informative` are unchanged.  `W = D(A_V)` carries the graph norm, as in the
  paper.  No diagonal (weighted `ℓ²`) choice of `W` works for this example, so some
  non-diagonal `V` is needed.  With weights `wₙ`, `C ∈ L(W, ℝ)` needs `∑ cₙ²/wₙ < ∞`, while
  `hyp:H1`, tested on `u = ε^{-1/2} 1_{[T-ε, T]}`, gives `∑_{n ≤ N} wₙ ≲ N²`.  Since
  `cₙ² = 2 cos²(nπξ₀)` does not decay, the inequality between arithmetic and harmonic means
  makes the two incompatible on dyadic blocks (the borderline case `H^{1/2}`).
* **The heat `V`: the paper's localised norm.**  `Examples/Heat/Localized*` formalise
  `eq:heat-localized-V` literally on `X = L²(0, 1)` with the cosine basis; the modal model with
  the scalar norm (`exists_boundaryHeat`, `exists_boundaryHeat_L2`) is kept, and the localised
  spaces give `exists_boundaryHeat_loc`.  For `z ∈ X₋₁` and `t > 0`, `orbit z t` is the smooth
  function `S(t) z`, and `F_z(t) = e^{-t} χ S(t) z ∈ H¹(0, 1)` is recorded as the pair
  `e^{-t} ([χ S(t) z], [∂_ξ (χ S(t) z)]) ∈ L²(0, 1) × L²(0, 1)` (`orbitH χ t`), so that
  `‖F_z(t)‖² = e^{-2t} ‖χ S(t) z‖²_{H¹(0, 1)}` with `‖f‖²_{H¹} = ∫₀¹ f² + ∫₀¹ (f')²` (`H1sq`).
  `V χ` is the closed graph `{(z, F) : F = F_z a.e. on (0, ∞)}` in
  `WithLp 2 (Xm1 × L²(0, ∞; L² × L²))`, and `norm_V_sq_eq` states
  `‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} ‖χ S(t) z‖²_{H¹(0, 1)} dt`.  `S_V(s)(z, F) = (S(s) z, e^s F(· + s))`
  is strongly continuous by continuity of right translations in `L²(0, ∞)`; `W = D(A_V)` carries
  the graph norm.  The cut-off is only assumed `C¹` with `tsupport χ ⊆ (0, 1)` (`Cutoff`), which
  every `χ ∈ C_c^∞(0, 1)` satisfies (`exists_smooth_cutoff` builds one equal to `1` near `ξ₀`);
  `exists_boundaryHeat_loc` assumes the paper's `χ = 1` near `ξ₀`, of which only `χ(ξ₀) = 1` is
  used.  `C` and `hyp:H2` are transported rather than rebuilt: since `χ(0) = 0` and `χ(ξ₀) = 1`,
  `(S(t) z)(ξ₀) = ∫₀^{ξ₀} ∂_ξ(χ S(t) z)`, so `|C S(t) z| ≤ eᵗ ‖F_z(t)‖` (`abs_orbit_le`), the
  localised norm dominates the scalar one, and `J : V χ → V_scalar`, `JW : W χ → W_scalar` are
  continuous; `C = C_scalar ∘ JW` equals `w ↦ w(ξ₀)` on `D(A) = H²_N`.  The paper uses the time
  trace of `F_w ∈ H¹(0, ∞; H¹)` and `H¹ ↪ C[0, 1]` instead; that `D(A)` is dense in `W` (which
  would make `C` the unique continuous extension) is not formalised.  `hyp:H1` follows the
  paper: `χ S(s) A_{X,-1} L_T u` is the convolution of `u` with `q'(s + T - ·)`, and `q'` and
  `∂_ξ q'` are bounded uniformly on `(0, ∞) × [d_χ, 1)` (`exists_abs_kernelDeriv_le_unif`: image
  series for `τ < 1`, modal series for `τ ≥ 1`), a pointwise strengthening of
  `eq:heat-separated-kernel`; `b ∈ V` follows from `b = S(1) b - A_{X,-1} L_1 1`.
* **The delay class.**  The paper's `L`, `M` and `C` are
  bounded operators on `C([-h, 0]; ℝⁿ)`, i.e. given by matrix measures, with a neutral term
  `M`.  `Examples/Delay` covers retarded systems, `M = 0`; `Examples/NeutralDelay` adds the
  neutral term (next bullets).  `L x_t = ∑ₖ Aₖ x(t - hₖ) + L_d x_t`
  and `C x_t = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` have finitely many point delays in `[0, h]` and
  distributed parts `L_d`, `C_d` that are arbitrary bounded operators on the `L²` history.  This
  contains the kernel form `∫_{-h}^0 A_d(θ) x(t + θ) dθ` with `A_d ∈ L²` (`Delay.kernelOp`), and
  for finite-dimensional `E` it is equivalent to that form by the Riesz representation.  `E`,
  `U` and `Y` are arbitrary real Hilbert spaces instead of `ℝⁿ`, `ℝᵐ`, `ℝᵖ`.  The history lives
  on `(0, h]`, with `ψ(s) = φ(s - h)`, so that the signal library (`L2`, `window`,
  `HasWeakDeriv`) applies; the state is `(x(t), x_t) ∈ E × L²(0, h; E)` (`Delay.State`).  The
  system has `W = D(A)` with the graph norm and `V = X`; `B = (B₀, 0)` is bounded, and
  `hyp:compat` is trivial because `D_V(A) = D(A) = W`.  The point evaluations in `C` are not
  defined on `L²` classes, so `C` is defined on the graph,
  `C (v, A v) = ∑ₖ Cₖ (v₁ - ∫_{(h - h'ₖ, h]} (A v)₂) + C_d v₂`, which is the paper's output on
  `D(A)` (`Model.Cop_apply`).
* **The neutral delay class.**  `NeutralDelay.Equation` extends the retarded `Delay.Equation`
  (the same `L`) by `M x_t = ∑ₖ Mₖ x(t - mₖ) + M_d x_t` with finitely many point delays
  `mₖ ∈ (0, h]` and `M_d` an arbitrary bounded operator on the `L²` history.  Strict positivity of
  the `mₖ` is the paper's "the measure representing `M` has no mass at `0`".  `M_d` needs no
  smallness condition: any bounded operator on `L²(0, h; E)` contributes `‖M_d‖ / √(2γ)` to the
  weighted norm (Tonelli).  `L`, `M` and `C` are instances of the common shape `DelayOp`
  (`∑ₖ Pₖ φ(-δₖ) + D φ`).
* **Solutions of the neutral equation.**  Solutions are only square integrable, so the solution
  concept is the integral form `x(t) = M x_t + r + ∫₀ᵗ (L x_s + f)` for a.e. `t ∈ (0, τ]` with
  `x ∈ L²(0, τ)` (`Equation.IsSolOn`), where `r = x(0) - M x_0`; the first state component
  `prim = r + ∫₀ᵗ (L x_s + f)` is continuous.  Picard iteration with `Kⁿ tⁿ / n!` bounds does not
  apply (the neutral term is not an integral); instead `1 - 𝒦`, `𝒦 x = M x_· + ∫₀^· L x_s ds` with
  zero history, is invertible on `L²(0, τ)`: in the weighted norm
  `‖x‖_γ² = ∫₀^τ e^{-2γt} ‖x(t)‖²` the point delays of `M` contribute `‖Mₖ‖ e^{-γ mₖ}`, `M_d`
  contributes `‖M_d‖ / √(2γ)` and the integral `O(1/√γ)`, so `‖𝒦ⁿ‖ < 1` for some `n`.  The
  solution for all times (`Equation.sol`) is glued from the solutions on `(0, n + 1]` and assumes
  a locally integrable forcing.  Regularity (`H¹` history `g` with the compatible
  `r = g(h) - M g`) solves the differentiated equation `y = M y_· + L (∫₀^· y)_· + w'` in `L²` and
  integrates.
* **The neutral state space and semigroup.**  The state is `(x(t) - M x_t, x_t)` in
  `Delay.State h E`, as in the paper (Burns–Herdman–Stech 1983).  `D(A) = {(g(h) - M g, g)}`, so
  the first component of a domain element is not a point value of the history; `C` on
  `W = D(A)` recovers the point values from `(v₂, (A v)₂) = (g, g')` by the bounded `H¹` point
  evaluation `g(a) = h⁻¹ ∫₀ʰ g + ∫₀ʰ g' - h⁻¹ ∫₀ʰ ∫₀^σ g' - ∫_{(a, h]} g'` (`pointEval_eq`,
  `Model.evalOp`).  `hyp:compat` is trivial and `B = (B₀, 0)` is bounded.  Unboundedness of `C`
  on `X` (`Model.not_exists_bound_C`) is proved when no neutral delay equals the output delay
  `θ`; otherwise the first state component of the one-bump test functions does not tend to `0`,
  and a two-bump argument (not formalised) would be needed.

### The cited theorems, now proved

* **Fattorini–Hautus (`prop:fattorini-hautus`; Boyer Thm III.3.7, Badra–Takahashi Thm 1.3).**
  `System.fattoriniHautusProperty_of_hypotheses` proves it: under
  `sys.FattoriniHautusHypotheses T` (`0 < T`, `hyp:H1`, an analytic semigroup, a compact
  resolvent of `A^⋆`, and a complete system of root vectors of `A`), the property
  `ApproxControllable T' ↔ HautusCondition` holds for every `T' > 0`.
  `System.fattoriniHautusTheorem` is the same in the `Prop` form `sys.FattoriniHautusTheorem`,
  for every system.  A complete system of root vectors means that the generalised eigenspaces
  of one resolvent `R(μ, A_ℂ)` span a dense subspace of `X_ℂ`; this does not depend on
  `μ ∈ ρ(A_ℂ)` (`dense_iSup_maxGenEigenspace_resolvent`).  The graph-norm bound on `B^⋆` that
  the paper lists among the hypotheses holds for every system satisfying `hyp:H1`
  (`System.exists_norm_Bstar_le`), so it is not a field of the structure.
  * **The root-vector hypothesis was corrected.**  Boyer's statement, which the paper followed,
    and the first version of the field `completeRootVectors` asked for complete root vectors of
    `A^⋆`.  That does not suffice.  Completeness for `A` is sufficient (it is what the proof
    uses), and it is necessary for the equivalence to hold for every bounded `B`.
    Badra–Takahashi assume it for `A` (their (H2)).  The field `completeRootVectors` now names
    `sys.A.complexify`.  The paper's `prop:fattorini-hautus` now reads "`A^⋆` has compact
    resolvent and `A` has a complete system of root vectors" and also cites Badra–Takahashi,
    ESAIM: COCV 20 (2014) 924–956, Thm 1.3.  The two arguments below are on paper only; they are
    not formalised.
    * *Necessity.*  Let `M` be the closed span of the root vectors of `A_ℂ`.  It is
      `S(t)`-invariant, and by Riesz theory for `R(μ, A^⋆)` no eigenvector of `A^⋆` is
      orthogonal to `M`.  Take `bⱼ` dense in the unit ball of `M`, `U = ℓ²` and
      `Bu = ∑ⱼ 2^{-j} uⱼ bⱼ`.  Then `B^⋆φ = 0` iff `φ ⊥ M`, so the Hautus condition holds, but
      every real `η ⊥ M` is orthogonal to the reachable set.  So if the root vectors of `A` are
      incomplete, the theorem fails for some bounded `B`.
    * *Complete root vectors of `A^⋆` do not suffice.*  On `N = L²(0, 1)` let `A_N = -K₀⁻¹`
      with `K₀ = J^{3/4}` (Riemann–Liouville).  `K₀` is Hilbert–Schmidt, injective, with dense
      range, and quasinilpotent, so `σ(A_N) = ∅`, the resolvent `R_N` is entire and compact, and
      `A_N` is sectorial.  On a second space `M` let `A_M` be normal, with an orthonormal
      eigenbasis `mⱼ` and conjugate-symmetric eigenvalues `λⱼ` on left arcs `|λ| = L_s → ∞`,
      `|arg λ| ∈ [θ, π]` with `θ ∈ (π/2, 5π/8)`.  Set `A^⋆ = [[A_N, C], [0, A_M]]` with a
      Hilbert–Schmidt `C mⱼ = εⱼ c_{s(j)}`, where the targets `c_s` run through a dense sequence.
      This is a bounded perturbation of `diag(A_N, A_M)`, so it is real, analytic and has
      compact resolvent.  Its root vectors are `vⱼ = (εⱼ R_N(λⱼ) c_{s(j)}, mⱼ)`.  Deforming the
      Dunford integral of `S_N(t)` onto the arcs (allowed because `R_N` is entire) shows that
      `span{vⱼ}` is dense, so the root vectors of `A^⋆` are complete.  But `N ⊕ 0` is
      `A^⋆`-invariant and `σ(A_N) = ∅`, so every root vector of `A` lies in `0 ⊕ M`.  With
      `B^⋆ = ⟪(0, β), ·⟫` and `⟪β, mⱼ⟫ ≠ 0` for all `j`, the Hautus condition holds, but
      `N ⊕ 0` is orthogonal to the reachable set.
  * **Use in Section 5.**  The theorems of Section 5 still take `sys.FattoriniHautusProperty T`
    as a hypothesis, together with the other hypotheses their proofs use.  This is weaker than
    the paper's hypotheses, and `fattoriniHautusProperty_of_hypotheses` derives it from them, so
    each Section-5 theorem composed with it is the paper's statement with nothing assumed.  The
    easy direction (`hautusCondition_of_approxControllable`) needs only `hyp:H1`.  The Section-5
    theorems conclude `ApproxControllable T` at the window horizon `T`; under the property,
    approximate controllability does not depend on `T`
    (`approxControllable_iff_of_fattoriniHautusProperty`).
* **The Riccati theorem (`thm:lqr-riccati`, Pritchard–Salamon Thm 2.7).**  The structure
  `System.RiccatiSolution wts T` records what the paper uses from the theorem: a family `P(t)`
  of bounded symmetric nonnegative bilinear forms on `V`, strongly continuous on `[0, T]`, with
  `P(T) = G`, such that for every `x₀ ∈ W` the minimiser of `J(·; x₀)` is the feedback
  `u(t) = -R⁻¹ B^⋆ P(t) x(t)` (`eq:lqr-feedback`) and the minimum is `P(0)(x₀, x₀)`.
  `System.RiccatiTheorem` states the theorem as a `Prop`
  (`H1 → H2 → Compat → Nonempty (RiccatiSolution wts T)`), and `System.riccatiTheorem` proves it
  for every system, weights and horizon.  `P(t)` is the value operator `System.riccatiP`; for
  `T ≤ 0` the theorem is trivial, with `P ≡ G` (`riccatiSolution_of_nonpos`).
  * **Without `hyp:compat`.**  `System.nonempty_riccatiSolution` needs only
    `hyp:H1` and `hyp:H2`.  Pritchard–Salamon use `hyp:compat` (their (H3)) only in their
    Lemma 2.5, a Fubini argument against the unbounded `C`.  The formalisation replaces that
    lemma by the adjoint formula `System.coeFn_adjoint_input`, proved by needle variations.
    Hence `System.lqr_data_riccati_of_H1_H2`: the second part of `thm:lqr-data` with no Riccati
    hypothesis and no `hyp:compat`.
  * **The integral Riccati equation and uniqueness.**  `System.IsRiccatiIntegralSolution wts T P`
    (`LQR/RiccatiEquation`) states the equation in the open-loop form
    `P(t) = S(T - t)^⋆ G S(T - t) + ∫ₜᵀ S(s - t)^⋆ (C^⋆C - P(s) B R⁻¹ B^⋆ P(s)) S(s - t) ds`
    as bilinear forms on `V`: for `x, y ∈ V`,
    `P(t)(x, y) = G(S_V(T - t) x, S_V(T - t) y) + ∫ₜᵀ (⟪(𝓞_V x)(s - t), (𝓞_V y)(s - t)⟫ - ⟪R⁻¹ B^⋆P(s) S_V(s - t) x, B^⋆P(s) S_V(s - t) y⟫) ds`,
    together with symmetry and strong continuity of `P` on `[0, T]`.  `B^⋆P x` for `x ∈ V` is
    `System.bStarPV`, which agrees with `bStarP` on `W`.  Two solutions agree on `[0, T]`, with
    no hypothesis on the system and without assuming nonnegativity
    (`IsRiccatiIntegralSolution.eqOn`).  Under `hyp:H1` and `hyp:H2` the value operator
    `riccatiP` is a solution (`isRiccatiIntegralSolution_riccatiP`), and every solution is a
    `RiccatiSolution` (`IsRiccatiIntegralSolution.toRiccatiSolution`).
    `System.riccatiIntegralTheorem` (every horizon) and `System.riccatiIntegralTheorem_of_pos`
    (with the unique optimal control) state the cited theorem in full, without `hyp:compat`.
    The structure `RiccatiSolution` still records only what the paper uses, and
    `lqr_data_riccati` holds for every `RiccatiSolution`; by uniqueness, "the Riccati operator"
    of `thm:lqr-data` is now the unique solution of the integral equation.

### Approximate controllability of the explicit examples

The paper applies `prop:fattorini-hautus` to three explicit systems: in Step 3 of
`app:pe-necessity`, in `prop:infinite-pe-insufficient` and in `app:boundary-heat-informative`.
The formalisation proves their approximate controllability directly, from their modal
structure.
`approxControllable_diag` (`Semigroup/Diagonal`): for a Hilbert basis `(eₙ)`, distinct real
eigenvalues `λₙ` that are bounded above, and bounded `B` with `B† eₙ ≠ 0`, the diagonal system is
approximately controllable in every time `T > 0`.  If `η ⊥ im L_T`, the input
`u(r) = B† S(T - r)† η` gives `∫₀ᵀ ‖u‖² = 0`, hence `∑ₙ ηₙ e^{λₙ t} B† eₙ = 0` on `(0, T)`.  The
`λₙ` may accumulate, so the uniqueness of this Dirichlet series is proved by holomorphic
continuation to `Re z > 0` and Bohr coefficients on `Re z = 1`
(`Diagonal.coeff_eq_zero_of_tsum_eq_zero`).  For `prop:infinite-pe-insufficient`, where
`A = A₀ + BK`, feedback invariance of the reachable set (`System.approxControllable_perturb_iff`)
reduces to the diagonal `A₀`.  Neither compact resolvent nor complete root vectors are needed.
For the heat example, `System.approxControllable_of_modal` (`Semigroup/Modal`) extends the test
to unbounded `B`: if `⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪βₙ, u(r)⟫ dr` with distinct `λₙ`,
`∑ₙ e^{λₙ s} < ∞` for `s > 0`, and a bounded family `βₙ ≠ 0` that need not be square summable,
then the system is approximately controllable.  The proof tests with the inputs `1_{(0, b]} βₘ`
and ends with the same Dirichlet-series uniqueness.  The heat equation has `βₙ = bₙ ∈ {-1, -√2}`.

### Stronger statements

| Paper | Lean | Why it holds |
|---|---|---|
| `prop:hilbert-pe-necessary`: the hypothesis quantifies over every approximately controllable pair `(A, B)` with `B ∈ L(U, X)` and every `x₀` | only over those approximately controllable in every time `τ > 0`; `0 < T` is not used | The hypothesis is weaker, so the theorem is stronger and implies the paper's.  The proof (Step 3) only uses diagonal systems, which are approximately controllable in every time (`approxControllable_diag`). |
| `thm:willems-gramian`, last sentence ("then `(x, y)` is the mild solution") | `System.eq_mild_of_trajectory` needs only condition (i) and `hyp:H1`; no record, no informativity | The paper's Step 4 uses nothing else. |
| `thm:analytic-universal-sufficiency`, "moreover" ((ii) or (iii) at `x₀ = 0` ⇒ (i)) | `approxControllable_of_informative_zero`, `approxControllable_of_windowInformative_zero` hold for any `L²` input; no harmonic signal, `σ` or growth bound | The paper's proof does not use the form of the input there.  (ii) ⇒ (i) does not need analyticity either (the Lean statement keeps `hA`, `hc`). |
| `thm:data-fattorini-hautus` (ii), `κ = ⟨η, x₀⟩ ≠ 0` | `exp_coeff_eq_and_ne_zero` holds for every nonzero `η ∈ X_ℂ`, without the Fattorini–Hautus property or `hyp:H1` | Evaluation at `t = 0` and informativity suffice.  The "only if" of (ii) uses only the easy direction, and Step 2 (`isHautusEigenvector_of_exp`) needs neither `η ≠ 0` nor the property. |
| `thm:io-window-controllability` (ii), `g ≠ 0` | `ne_zero_of_io_exp` without the Fattorini–Hautus property or exact observability | With `g = 0`, Step 3 applied to inputs supported in a window gives `v = 0`, contradicting `κ ≠ 0`; this needs only `hyp:H1`, `hyp:H2` and the input–output fundamental lemma. |
| `eq:hilbert-gramian`: `𝒢(z)` is trace class | also `tr 𝒢(z) = ∫ ‖z‖²` (`trace_gramian`) | `𝒢(z) = M† M` for the analysis operator `M`, whose squared Hilbert–Schmidt norm is `∫ ‖z‖²`. |
| `thm:lqr-riccati`: assumes `hyp:H1`, `hyp:H2`, `hyp:compat` | `nonempty_riccatiSolution` assumes only `hyp:H1` and `hyp:H2`, at every horizon | Pritchard–Salamon need `hyp:compat` only for their Lemma 2.5, which the adjoint formula `coeFn_adjoint_input` replaces.  The integral Riccati equation and the uniqueness of its solution are also proved without `hyp:compat` (`riccatiIntegralTheorem`). |
| `thm:lqr-data`, second part | `lqr_data_riccati` holds for every `RiccatiSolution`; `lqr_data_riccati_of_H1_H2` needs only `hyp:H1` and `hyp:H2` (no `hyp:compat`, no Riccati hypothesis) | The minimiser of `J(·; x₀)` is unique, so the feedback transfers to the data-driven minimiser; the Riccati theorem is proved without `hyp:compat`. |
| `def:harmonic-signal`, indexed by `ℓ ≥ 1` | any countable index type, so finite trigonometric polynomials are harmonic too | Harmless: a harmonically persistently exciting signal has infinitely many frequencies, so `IsHarmonicPE` and every theorem about it are unaffected. |

Three hypotheses remain in the statements although their proofs do not use them: separability
of `U` in `psiC_eq_zero_of_inner_transfer_eq_zero` (`lem:transfer-laplace`; the weak Laplace
uniqueness works in any Hilbert space), `[Nontrivial U]` in `exists_isHarmonicPE`
(`lem:harmonic-pe`), and `hyp:compat` in the `Prop` `System.RiccatiTheorem`, which
`riccatiTheorem` proves by discarding it.  `lem:harmonic-pe-implies-pe` does not use the limit
`νⱼ` of `def:harmonic-pe`, only infinitely many distinct frequencies per direction.

### Statements in a different but equivalent form

* **Horizons.**  `hyp:H1` and `hyp:H2` are stated at a fixed horizon, and `H1.of_pos`,
  `H2.of_pos` extend them to every horizon (`app:finite-horizon-output`).  The positivity of
  the horizon, implicit in the paper, is an explicit hypothesis.  It is needed: for `T = 0`,
  `lem:window-pe-necessary` is false (`X = 0`, `U ≠ 0`).
* **`prop:finite-pe-sufficient`.**  "Controllable" is `ApproxControllable T`, the weakest of the
  finite-dimensional notions, which are all equivalent to the Kalman condition
  (`approxControllable_bounded_iff_kalman`, `exactlyControllable_bounded_iff_kalman`).  The
  theorem also assumes `hyp:H1`, which is part of the paper's standing assumptions and holds
  automatically in finite dimensions.
* **`thm:willems-gramian`.**  (i) ⇔ (ii) ⇔ (iii) is a `List.TFAE`; `graph_identification`
  states `(ker 𝒢)ᗮ = closure (𝒲 '' test functions)` as sets and `(ker 𝒢)ᗮ = range Γ` as
  submodules.  `rmk:input-state-case` is the theorem applied to `sys.inputState Y₀`
  (`W := X`, `C := 0`).
* **`prop:hilbert-pe-necessary`** is two theorems, `N < ∞` (order `finrank + 1`) and `N = ∞`
  (`X` separable and infinite-dimensional, infinite order).  **`thm:analytic-universal-sufficiency`**
  is a `List.TFAE` proved from its four implications.
* **Exponential identities.**  `eq:data-fh` is stated for every `t ∈ [0, T]`, equivalent to the
  paper's `t ∈ I` by continuity; `eq:io-window-fh` for every `s` in the open window, as in the
  paper.
* **Regulators.**  The minimiser of `thm:lqr-data` is unique up to `TrajEquiv`, i.e. as an
  element of `L²(I; U) × C(I; W) × L²(I; Y)`.  `thm:lqr-data-io` states the value identity for
  every minimiser next to `∃!`, which is the paper's "the two problems have the same optimal
  value"; the conditioning window is `uini : L2 U T₀`, `yini : L2 Y T₀` with
  `yini = sys.outputW xini uini` a.e.
* **`def:PE`.**  Order `0` is vacuous (`persistentlyExciting_zero`), so "every order `L`" in
  `PersistentlyExcitingInfinite` equals the paper's "every `L ≥ 1`".
* **`ex:boundary-heat-informative`.**  `exists_boundaryHeat` has the paper's existential form:
  for the given `X`, `e` and `ξ₀`, there are Hilbert spaces `W` and `V` and a system on
  `W ↪ X ↪ V` with all the listed properties.  The ties to the PDE (the semigroup, `B^⋆` and `C`
  in modal form) are part of the statement, so an unrelated system cannot witness it.  The
  `heatSystem_*` theorems state the same properties for the concrete system `heatSystem e hξ₀`.
  `hyp:H1` and `hyp:H2` hold at every horizon.

### Proofs that take a different route

The statements are unchanged; only the arguments differ.  Each entry names the paper's step.

* **`app:control-realization`.**  The paper identifies the control convolution of `B_X` with
  `L_t` by "equality of Laplace transforms in `X₋₁`, first for compactly supported inputs".
  The formalisation needs no Laplace transform: commuting `R(a, A_V)` with the `V`-valued
  convolution gives `R(a, A) L_t u = ∫₀ᵗ S(t - r) Q_a u(r) dr` in `X`
  (`System.resolvent_ιW_L`), and pairing with `(η, A†η)` gives `toExtrap_L` and the duality
  formula `(L_t†η)(r) = B† S(t - r)† η`.  Agreement of `B_X†` with the `V'`-adjoint on
  `D(A^⋆) ∩ V'` follows from `B v = (a - A_V) Q_a v` and difference quotients of
  `t ↦ ⟨η, S(t)x⟩`, instead of the limit `t⁻¹ L_t v → Bv`.  `eq:weak-mild-diff` applies Ball's
  theorem in `X` to `R(a, A) L_· u`, which takes values in `D(A)`.  The graph-norm bound on
  `B^⋆` is immediate in the dual model.
* **`lem:window-implies-informative`.**  The paper tests the annihilator identity against each
  `φ ∈ L²(0, T)` and represents two functionals, by `ξ_φ = ∫ φ(t) S(t)^⋆β dt` (which needs the
  adjoint semigroup) and by a Riesz vector `g_φ`.  The formalisation packages all `φ` at once in
  one bounded operator `𝒜(v, ξ) = (t ↦ ⟨α, v(t)⟩ + ⟨β, x(t; ξ, v)⟩)`, whose adjoint sends `φ`
  to `(φα + g_φ, ξ_φ)`.  The flow property gives `𝒜 ∘ 𝒵 = 0`, window informativity gives
  `𝒜 = 0`.  Then `𝒜(0, β) = 0` gives `β = 0` (continuity of `t ↦ ⟨β, S(t)β⟩` at `0`), and
  `𝒜(α, 0) = 0` for the constant input `α` gives `α = 0`.  No adjoint semigroup is used.
* **`app:willems-gramian`, Steps 1 and 4.**  The paper views the mild formula on `V₋₁`, uses
  `W ⊂ V = D(A₋₁)` and the density of `D(A₋₁^⋆)` (Step 1), and treats `x` as a strong solution
  on `V₋₁` (Step 4).  The formalisation stays on `V`, where the forcing `Bū` already lives.  In
  Step 1 the record embedded in `V` is the `S_V`-mild solution, hence a weak solution by Ball's
  theorem, and Ball's weak form is the `H¹(I; V₋₁)` integral form in the dual model
  (`hasWeakDeriv_toExtrap_mildW`).  In Step 4 the integral form in `V₋₁` is Ball's weak
  formulation on `V`, so `IsWeakSol.eq_mildSol` makes `ιWV ∘ x` the `V`-mild solution, which is
  `ιWV` of `sys.mildW (x 0) u` under `hyp:H1`.  No semigroup on `V₋₁` and no strong solutions
  are needed.  **Step 2:** the density of the moment space `𝒩` uses the fundamental lemma on
  test functions instead of the density of `H₀¹(I)` in `L²(I)`.
* **`app:pe-necessity`, Steps 2–4.**  These are made rigorous along the paper's lines, and no
  gap in the paper's argument was found.  Step 2: the `U`-valued identity `p Ξ = Ψ` is proved
  coefficientwise by pairing with every `v ∈ U`, which reduces it to scalar interpolation at the
  `r` nodes.  Step 3: the orthonormal basis is any Hilbert basis on a countable index type
  (`Fin N`, or a Hilbert basis of the separable space), the completing eigenvalues are
  `-(enc i + 1)` and the completing columns `B† eᵢ = 2^{-enc i} ζ_r` for an injection `enc` into
  `ℕ` (paper: `-(n - r)` and `2^{-n} c`), and `B = ∑ᵢ ⟨B† eᵢ, ·⟩ eᵢ` converges in operator
  norm.  Approximate controllability is `approxControllable_diag`.  Step 4: the modes
  `yₙ = ∫₀ᵗ e^{λₙ(t-s)} ⟨bₙ, ū(s)⟩ ds` are `H¹` solutions of `ẏₙ = λₙ yₙ + ⟨bₙ, ū⟩`, so
  `p(D) w = ∑ₖ ⟨ζₖ, Dᵏū⟩ = 0` holds in the test-function sense, `w = ∑ κₙ e^{λₙ t}` a.e., and
  the initial state `x₀ = -∑ κₙ e_{jₙ}` cancels it; uniqueness of that choice is not needed.
* **`app:analytic-universal-sufficiency`.**
  * `𝐇(s)` is defined as `Q_a - (s - a) R(s, A) Q_a` for an admissible real `a` and
    characterised weakly (`transferX_spec`); `Ω_⋆` is an open preconnected subset of `ρ(A)`
    containing `{Re s > σ}` and `σ + i{ωₗ}‾` (`exists_isPreconnected_resolventSet`), which is all
    the identity theorem needs.
  * `eq:analytic-exp-convolution`: instead of the finite-time Laplace identity on `X₋₁` applied
    to `B_X v`, both sides are mapped by the injective `R(a, A) ∘ ιW`, and the identity is used
    on `X_ℂ` for the complexified semigroup.
  * `eq:analytic-state-expansion`: the harmonic series is interchanged with `L_t` pointwise in
    `t` (termwise integration of the `V`-valued convolution, `W`-summability from the bound of
    `hyp:H1`, injectivity of `ιWV`) rather than through convergence of the partial sums in
    `C([0, τ]; W)`.
  * `lem:bohr-annihilator`: as in the paper (identity theorem from "a.e." to "every `t > 0`",
    the free response averaged away), with the finite-time Laplace identity of `S_ℂ` and
    `d = R(s, A_ℂ) c`, so no `D(A) ↪ E` step is needed.
  * `lem:transfer-laplace`: the duality `(L_t^⋆η)(τ) = ψ_η(t - τ)` for `η ∈ W'` is obtained from
    the `X`-duality at `S(ε)^⋆η ∈ D(A^⋆)` and the limit `ε → 0⁺`, instead of "controls supported
    away from the terminal time, then `hyp:H1`".  The density of `im L_T` in `W` pairs the final
    limit with `η` itself (strong continuity of `S_W`), with no adjoint semigroup on `W`.
  * (i) ⇒ (iii): the integral term of the annihilator identity is entire because it is a Laplace
    transform evaluated at `-z`; uniqueness of the Laplace transform on `(-T, ∞)`, reflection and
    totality of the directions give `g = 0`, and then `ξ = 0` by
    `psiC_eq_zero_of_inner_transfer_eq_zero`.
  * (ii) at `x₀ = 0` ⇒ (i) needs neither `ψ_β` nor analyticity: for `η ⊥ im L_T`, the pair
    `(0, ιW†η)` annihilates the zero-state record because `L_t u = L_T u_t` with `u_t` the input
    translated to the end of `(0, T)` (`L_eq_Lop_windowL`), so `ιW†η = 0`, and `η = 0` by
    density of `W` in `X`.
  * (iii) at `x₀ = 0` ⇒ (i) follows the paper; its step "`ψ_β = 0` on `(0, T)`" is made explicit
    by testing the annihilator identity with `v(r) = ψ_β(T - r)`.
* **`app:io-window-controllability`.**  `g` is never fed to a complexified `𝓞_T`: `v` and `g`
  enter through their real and imaginary parts, and Step 1 uses `𝓜_T†`, which is onto because
  `𝓜_T` is bounded below.  Step 3 proves the shift eigenrelation for every `r ∈ [0, 2T]`, which
  gives `S(τ)^⋆η = e^{λτ}η` for `τ ∈ [0, T]` directly; `A^⋆η = λη` follows from difference
  quotients of `⟨η, S(h)x⟩` for `x ∈ D(A)` (no adjoint semigroup), and `B^⋆η = 0` from the weak
  derivative of `t ↦ ⟨η, x(t; 0, b)⟩ ≡ 0` for constant inputs `b`.
* **`lem:harmonic-pe-implies-pe`.**  `ū` is never differentiated.  The derivative moments of
  `⟨ζₖ, ū⟩ = ∑ₗ e^{sₗ t} ⟨ζₖ, vₗ⟩` are computed termwise, which turns the relation into
  `∫ φ G = 0` for a continuous `G`; then the fundamental lemma, the identity theorem and Bohr
  uniqueness give vanishing coefficients, and a polynomial with infinitely many roots vanishes.
* **`app:infinite-pe-insufficient`.**  The trajectory `x̄(t) = e^{tA₀} b` comes from feedback
  invariance of mild solutions (`System.mild_perturb_iff`: it is the mild solution of `(A₀, B)`
  with input `ū + K x̄ = 0`), instead of "`x̄` is smooth and `ẋ̄ = A₀ x̄ = A x̄ + B ū`".  The
  excitation proof differentiates `ū` termwise on `(-1, ∞)` and uses uniqueness of the Dirichlet
  series `∑ₙ cₙ e^{-(n+1)t}` instead of the power series in `q = e^{-t}`.
* **`app:window-strictly-stronger`.**  The route is the paper's.  The coefficients of the
  trigonometric series are recovered by integrating over a period after analytic continuation
  (`trigSeries_coeff_eq_zero`), instead of quoting uniqueness of Laurent coefficients.  The
  paper's "`dim L²(0, T) = ∞` gives `ψ ≠ 0` orthogonal to `sin` and `cos`" is made explicit
  (`WindowStrict.exists_orth`): `ψ = ∑_{k=0}^{2} gₖ e^{kt}` with `g ≠ 0` in the kernel of the
  moment map `ℝ³ → ℝ²`.
* **`app:finite-pe-sufficiency`.**  The general system is first reduced to a matrix system
  (`System.exists_matrix_of_finiteDimensional`).  The recursion `eq:finite-suff-recursion` is
  run on the vector moments `Xⱼ = ⟨Dʲx̄, φ⟩ ∈ X`, `Uⱼ = ⟨Dʲū, φ⟩`, with
  `X_{j+1} = A Xⱼ + B Uⱼ` (from `ẋ = Ax + Bu` in weak form, by Ball's theorem) and
  Cayley–Hamilton for `A`, instead of the scalars `⟨(A†)ᵏβ, x̄⟩` and the characteristic
  polynomial of `A†`; the coefficients `ζᵢ` are the paper's.  The equivalence of the Kalman
  condition with approximate controllability, which the paper uses without proof, is proved
  (`System.approxControllable_bounded_iff_kalman`), as is the equivalence of exact and
  approximate controllability in finite dimensions.
* **`app:lqr-data`, `app:lqr-data-io`.**  The unique minimiser of the coercive quadratic cost is
  obtained directly, since minimising sequences are Cauchy by the midpoint identity, instead of
  through Lax–Milgram; the bilinear form need not be symmetric.
* **`eq:hilbert-gramian` (trace class).**  The paper states it without proof.  `𝒢(z) = M† M` for
  the analysis operator `M ζ = ⟪z(·), ζ⟫ ∈ L²(μ; 𝕜)`, and `∑ᵢ ‖M eᵢ‖² = ∫ ‖z‖²` in every Hilbert
  basis (Parseval pointwise and `lintegral_tsum`).  The basis may be uncountable: an a.e.
  strongly measurable signal meets only countably many basis vectors.  So `M` is
  Hilbert–Schmidt, and `A† B` is trace class for Hilbert–Schmidt `A` and `B`.
* **`app:boundary-heat-informative`.**
  * Approximate controllability comes from the modal coordinates of `L_T`
    (`approxControllable_of_modal`: the `λₙ` are simple and `bₙ ≠ 0`), not from
    `prop:fattorini-hautus`.
  * `C ∈ L(W, ℝ)` is the trace formula in time, `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds` with
    `g = C S(·) w` and `g' = C S(·) A_V w`; on `D(A)` it equals `∑ₙ cₙ xₙ`
    (`ModalData.hasSum_trace`).  The paper uses the time trace `F_w(0) = χ w` in `H¹` and
    `H¹ ↪ C[0, 1]` instead.
  * The kernel bound `eq:heat-separated-kernel` is used in scalar form: `h = C S(·) b` and `h'`
    are bounded on `(0, ∞)`.  The proof is the paper's method of images (Poisson summation,
    Mathlib's `Complex.tsum_exp_neg_quadratic`) on `(0, 1]` and the modal series on `[1, ∞)`.
  * `X ↪ V` follows from a Schur test, `∑ₘ 1/(1 - λₙ - λₘ) ≤ ∑ₘ 1/(1 - λₘ)`, and the closed
    graph theorem, instead of the identity `∫₀^∞ e^{-2t} ‖S(t) z‖²_{H¹} dt = ½ ‖z‖²_X`.
  * `hyp:H1`: `eq:heat-control-X` by Cauchy–Schwarz in each coordinate, as in the paper; the free
    output of `A_{X,-1} L_T u` is `∫₀ᵀ h'(s + T - r) u(r) dr`, bounded through `|h'| ≤ M`; then
    `eq:heat-W-domain` puts `L_T u` in `W`.
* **`ex:intro-delay`.**  The paper states its claims without proof.
  * The equation is solved by Picard (Volterra) iteration with `Kⁿ tⁿ / n!` bounds, as for the
    Dyson–Phillips series, and uniqueness and a Grönwall bound follow the same way.
  * `D(A) = {(g(h), g) : g ∈ H¹}`: one inclusion uses the `H¹` regularity of trajectories and the
    `L²` convergence of difference quotients of `H¹` signals; the other passes from `L²`
    convergence of difference quotients to a weak derivative through test functions and
    du Bois-Reymond (`Delay/Translation`).
  * `hyp:H1`: `t ↦ (x(t), x_t)` for the zero history is a strong solution, so it is the mild
    solution by uniqueness of weak solutions (Ball), hence `L_T u = (x(T), x_T) ∈ D(A)`; the
    graph-norm bound follows from the closed graph theorem.
  * Unboundedness of `C` on `X`: smooth bumps `φ_ε e` centred at `h - θ` have `L²` norm
    `O(√ε)` while `C` maps them to `(∑_{h'ₖ = θ} Cₖ) e + O(√ε)`.
  * Neutral case (`Examples/NeutralDelay`): a contraction in the weighted `L²` norm replaces the
    Picard iteration, regularity comes from the differentiated equation, and `hyp:H1` follows as
    in the retarded case (strong solution, Ball, closed graph).
* **`prop:fattorini-hautus`.**  The paper cites the theorem;
  the formalisation's proof is contour-free.  It needs no Laplace representation of
  `B^⋆ R(z, A^⋆)`, no analytic continuation in `z`, and no Riesz projections or theory of
  isolated eigenvalues.
  * FH1: a state `η ⊥ ℛ_{T'}(0)` lies in `N = ⋂_{τ>0} ℛ_τ(0)^⊥`, because `r ↦ B† S(r)† η` is
    real analytic.  Analyticity of the semigroup enters here and nowhere else.
  * `N` is closed and invariant under one compact `K = R(μ₀, A^⋆)`, with `μ₀` real and beyond
    the growth bound.  The Hautus condition excludes eigenvectors of `K` in `N_ℂ` for nonzero
    eigenvalues.
  * Mathlib's Fredholm alternative for `K` restricted to `N_ℂ` gives `(K - ν) N_ℂ = N_ℂ` for
    `ν ≠ 0`, so `N_ℂ` is orthogonal to every root vector of `K† = R(μ₀, A_ℂ)`.  These are
    complete, so `N = 0`.
* **`thm:lqr-riccati`.**  The paper cites the
  theorem; the formalisation proves it through the value operator, not through Pritchard and
  Salamon's closed-loop evolution operators and iteration.
  * The control space is `L²(0, T; U)` for every starting time `s`: controls before `s` are cut
    off and only pay the input penalty, so the space does not change with `s`.
  * Completing the square gives the optimal tail control and the value operator
    `P(s) = Q_s - M_s† K_s⁻¹ M_s`.  The four tail maps and their adjoints are strongly
    continuous in `s`, hence so is `P`; weak continuity is never used.
  * Dynamic programming uses first-order conditions instead of comparing costs: the cut-off
    optimal control satisfies the first-order condition of the tail problem, so `P(t) x(t)` is
    the costate.
  * The feedback follows from the adjoint formula
    `((ιWV ∘ L_T)† z + 𝓕_T† y)(t) = B† (S_V(T - t)† z + c_t† y)` for a.e. `t`, proved by
    needle variations, the fundamental theorem of calculus and Lebesgue differentiation.  It
    replaces Lemma 2.5 of Pritchard–Salamon and does not need `hyp:compat`.
  * The integral equation is derived for the value operator, not through the closed-loop
    evolution operator and its perturbation formulas.  Along the free motion
    `z(τ) = S_V(τ - t) x`, `x ∈ V`, the function `F(τ) = P(τ)(z, z) - ‖c_τ z‖²` has the right
    derivative `⟪R⁻¹ B^⋆P(τ) z, B^⋆P(τ) z⟫`.  This comes from completing the square with two
    competitors, the cut-off optimal control and the optimal control from the later time; by the
    adjoint formula the optimal tail control is `-R⁻¹ B† p` with a continuous costate `p`, so
    the remainder is `O((σ - τ)²)`.  The fundamental theorem of calculus with right derivatives
    and polarisation give the equation for all `x, y ∈ V`, with no density argument.
    Uniqueness follows from the iteration `‖Δ(t)‖ ≤ D Kⁿ (T - t)ⁿ / n!`, with bounds from
    Banach–Steinhaus.

### Corrections to the formal statements during the work

Three statements were false as first written and were corrected before their proofs.  The
first two, in the semigroup library, do not affect the paper, which works in Hilbert spaces and
only at nonnegative times.  The third is a hypothesis of a cited theorem, and the paper was
changed with it.

* **Completeness.**  On an incomplete normed space, uniform boundedness of a C₀-semigroup fails
  (on the algebraic direct sum `⊕ₙ ℝ²`, the blockwise semigroup
  `S(t) = e^{-nt} (1 + n² t N)`, `N = [[0, 1], [0, 0]]`, has `‖S(1/n)‖ ≥ n/e`), Bochner
  integrals vanish, and `D(A)` need not be dense.  The lemmas that
  depend on these facts (in `Semigroup/Basic`: `ofTendsto`, `exists_norm_le_exp`,
  `continuous_apply₂`, `integrableOn_conv` and relatives; in `Semigroup/Generator`:
  `dense_generator_domain`, `generator_isClosed`, `hasDerivAt_real_apply`, `generator_integral`,
  `real_apply_sub_eq_integral`, `ext_of_generator`) now assume `[CompleteSpace E]`.
* **Negative times.**  `real_apply_sub_eq_integral`, `S(t)x - x = ∫₀ᵗ S(s) A x ds`, was stated
  for all real `t`; it is false for `t < 0`, where `S.real t = 1` but the integral is
  `t • A x`.  It now assumes `0 ≤ t`.
* **Root vectors of `A`, not `A^⋆`** (`prop:fattorini-hautus`).  The field
  `FattoriniHautusHypotheses.completeRootVectors` followed Boyer and named `A^⋆`.  A check made
  before the proof showed that this hypothesis is insufficient and that the theorem as
  stated was false; the field now names `A`, and the paper's proposition was changed to match
  (see "The cited theorems, now proved").

## What is not formalised

* **Section 7** (numerics).
* **General measures in the delay example** (`ex:intro-delay`).  `L`, `M` and `C` have finitely
  many point delays and distributed parts bounded on the `L²` history; general matrix measures
  would need the Riesz representation on `C([-h, 0])`.  In the neutral case, unboundedness of
  `C` on `X` is proved only when no neutral delay equals the output delay (see the modelling
  choices).
* **A general diffusivity `ν`** in the heat example.  The paper's `ex:boundary-heat-informative`
  takes `ν = 1`, as the formalisation does.
<!-- Items that are commented out in the paper's source (`rmk:counterexample-analytic`,
  `cor:lqr-regulators-agree`, `rmk:lqr-riccati-data`) are not part of the paper and are not
  formalised. -->
