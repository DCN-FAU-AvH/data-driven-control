# Paper label ↔ Lean declaration

Every declaration below is proved; `AxiomAudit.lean` checks the axioms of the main ones.  Names
are relative to the namespace `DataDrivenControl`, and `System.foo` is a statement about
`sys : System U W X V Y`.  Notes record how a statement differs from the paper; the conventions
behind them are in the [README](README.md).

## Section 2: setting

| Paper | Lean | File | Note |
|---|---|---|---|
| `eq:hilbert-control-formal`, `eq:intro-WXV` | `System`, `System.bounded`, `System.bounded_H2` | System/Setting, System/Mild | `System.bounded`: the classical case `W = X = V` |
| `hyp:H1`, `hyp:H2`, `hyp:compat` | `System.H1`, `System.H2`, `System.Compat` | System/Setting | at a fixed horizon |
| `eq:hilbert-mild` | `System.mild`, `System.mildW`, `System.outputW`, `System.L`, `System.Lop`, `System.output_ιW` | System/Mild | |
| `lem:finite-horizon-output` | `System.𝓕`, `System.𝓞`, `System.eq_𝓕`, `System.output_ae_eq`, `System.output_shift`, `System.H1.of_pos`, `System.H2.of_pos` | System/Mild | |
| `def:controllability` | `System.reachable`, `System.ExactlyControllable`, `System.ApproxControllable` | System/Controllability | |
| `def:observability` | `System.ApproxObservable`, `System.ExactlyObservable` | System/Controllability | |
| `app:control-realization` | `System.Q`, `System.L_exp`, `System.BX`, `System.BX_eq`, `System.toExtrap_L`, `System.Bstar`, `System.exists_norm_Bstar_le`, `System.inner_Bstar_of_dual`, `System.inner_L_eq_integral`, `System.adjoint_Lop_ae_eq` | System/ControlRealization | `V₋₁`, `X₋₁` in the dual model (graph of `A†`) |
| `eq:control-resolvent-decay` | `System.Q_decay` | System/ControlRealization | |
| `eq:weak-mild-diff` | `System.inner_mild_eq` | System/ControlRealization | |

## Section 3: informativity and persistency of excitation

| Paper | Lean | File | Note |
|---|---|---|---|
| `def:hilbert-informative`, `eq:informative-span` | `Informative`, `informative_iff_annihilator`, `informative_iff`, `toLp_mem_annihilator_pair`, `cspan`, `isLeast_cspan` | Informativity/Informative, Signal/Span | `cspan` is defined as the orthogonal complement of the annihilator |
| `eq:hilbert-gramian`, `eq:gramian-kernel` | `gramian`, `isPositive_gramian`, `ker_gramian_eq_orthogonal_cspan`, `orthogonal_ker_gramian` | Signal/Gramian | |
| `eq:hilbert-gramian` (trace class) | `isTraceClass_gramian`, `trace_gramian`, `hasSum_inner_gramian` | Signal/GramianTrace | also `tr 𝒢(z) = ∫ ‖z‖²` |
| `lem:informative-gramian` | `informative_iff_injective_gramian` | Informativity/Informative | |
| `rmk:gramian-not-coercive` | `gramian_injective_iff_coercive` | Signal/Gramian | |
| remark after `lem:informative-gramian` | `Informative.map_of_denseRange`, `System.Informative.mild_of_mildW`; the converse fails: `InformativityConverse.exists_informative_not_informativeW`, `InformativityConverse.not_forall_informativeW_of_informative`, `InformativityConverse.informative_X`, `InformativityConverse.not_informative_W` | Informativity/Informative, Examples/InformativityConverse | the paper gives no example of the failure |
| `def:window-informative` | `WindowInformative`, `windowInformative_iff`, `windowSynth_eq_integral` | Informativity/Window, Signal/Shift | |
| `lem:window-implies-informative` | `System.informative_of_windowInformative` | Informativity/Window | |
| `ex:window-strictly-stronger` | `WindowStrict.informative`, `WindowStrict.not_windowInformative`, `WindowStrict.exactlyControllable`, `WindowStrict.input` | Examples/WindowStrict | `A = 0` (`generator_idSemigroup`), `B = id` on `ℓ²` |
| `def:PE` | `PersistentlyExciting`, `PersistentlyExcitingInfinite` | Informativity/PE | order `0` is vacuous |
| remark after `def:PE` | `persistentlyExciting_iff_injective_gramian` | Informativity/PE | |
| `prop:hilbert-pe-necessary` | `persistentlyExciting_of_forall_informative` (`N < ∞`), `persistentlyExcitingInfinite_of_forall_informative` (`N = ∞`) | Informativity/Necessity | hypothesis only over systems approximately controllable in every time |
| `lem:window-pe-necessary` | `WindowInformative.persistentlyExcitingInfinite` | Informativity/PE | |
| `prop:finite-pe-sufficient` | `System.informative_of_persistentlyExciting`, `System.approxControllable_bounded_iff_kalman`, `System.exactlyControllable_bounded_iff_kalman` | Informativity/FiniteDim | "controllable" is `ApproxControllable T`; the Kalman equivalences are proved |
| `prop:infinite-pe-insufficient`, `eq:pe-counterexample`, `eq:pe-counterexample-input` | `PECounterexample.approxControllable`, `PECounterexample.persistentlyExcitingInfinite`, `PECounterexample.not_informative`, `PECounterexample.not_isHarmonic`, `PECounterexample.sys`, `PECounterexample.sys_A`, `PECounterexample.input` | Examples/PECounterexample | modes from `0`: `lam n = -(n + 1)` |
| `def:harmonic-signal` | `HarmonicSignal`, `IsHarmonic` | Informativity/Harmonic | any countable index set |
| `def:harmonic-pe` | `HarmonicSignal.IsHarmonicPE` | Informativity/Harmonic | |
| `lem:harmonic-pe` | `isHarmonicPE_hpeSignal`, `exists_isHarmonicPE` | Informativity/Harmonic | |
| `lem:harmonic-pe-implies-pe` | `HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite` | Informativity/Harmonic | |
| `thm:analytic-universal-sufficiency` | `System.analytic_universal_sufficiency`, `System.informative_of_approxControllable_harmonic`, `System.windowInformative_of_approxControllable_harmonic`, `System.approxControllable_of_informative_zero`, `System.approxControllable_of_windowInformative_zero` | Informativity/AnalyticSufficiency | the "moreover" converses hold for every `L²` input |
| `ex:boundary-heat-informative` | `BoundaryHeat.exists_boundaryHeat`, `BoundaryHeat.heatSystem_TFAE`, `BoundaryHeat.heatSystem_informative`, `BoundaryHeat.heatSystem_windowInformative`, `BoundaryHeat.heatSystem_approxControllable`, `BoundaryHeat.heatInput`, `BoundaryHeat.isHarmonicPE_heatInput` | Examples/Heat/System, Examples/Heat/Input | every `ν > 0`; `σ = 0`, `M = 1`; approximate controllability from the modal coordinates |

## Section 4: the fundamental lemma

| Paper | Lean | File | Note |
|---|---|---|---|
| `eq:graph-operator` | `System.GraphSpace`, `System.graphOp`, `System.isBoundedBelow_graphOp`, `System.isClosed_range_graphOp` | FundamentalLemma/Graph | |
| `𝒲`, `eq:synthesis-factorization` | `System.synth`, `System.synth_eq_graphOp` | FundamentalLemma/Graph | `𝒲` on test functions instead of `H₀¹(I)` |
| `thm:willems-gramian`, `eq:graph-identification` | `System.willems_tfae`, `System.graph_identification`, `System.eq_mild_of_trajectory` | FundamentalLemma/Willems | the record derivative is an explicit argument; the last sentence needs only (i) and `hyp:H1` |
| `eq:record-dynamics` | `System.hasWeakDeriv_mildW` | FundamentalLemma/Willems | |
| `rmk:input-state-case` | `System.inputState`, `System.H1.inputState`, `System.inputState_mildW` | FundamentalLemma/Willems | |
| `def:io-behavior` | `System.ioBehavior` | FundamentalLemma/InputOutput | |
| `eq:io-window-synthesis` | `ioWindowSynth`, `ioWindowSynth_eq_integral` | Signal/Shift | |
| `lem:io-parametrization`, `eq:io-state-recovery`, `eq:window-factorization` | `System.ioParam`, `System.range_ioParam`, `System.ioParam_injective`, `System.isBoundedBelow_ioParam`, `System.isClosed_ioBehavior`, `System.eq_ioStateRecovery`, `System.ioWindowSynth_eq_ioParam_comp` | FundamentalLemma/InputOutput | |
| `thm:windowed-io-fundamental-lemma`, `eq:io-behavior-identification` | `System.closure_range_ioWindowSynth` | FundamentalLemma/InputOutput | |

## Section 5: controllability tests

| Paper | Lean | File | Note |
|---|---|---|---|
| `prop:fattorini-hautus` | `System.fattoriniHautusTheorem`, `System.fattoriniHautusProperty_of_hypotheses`, `System.FattoriniHautusHypotheses`, `System.FattoriniHautusProperty`, `System.hautusCondition_of_approxControllable`, `System.approxControllable_iff_of_fattoriniHautusProperty` | Controllability/FattoriniHautus, Controllability/FHSpectral | cited; proved with complete root vectors of `A` (not `A^⋆`) |
| `thm:data-fattorini-hautus`, `eq:data-fh`, `eq:data-fh-exponential` | `System.approxControllable_of_forall_not_exp`, `System.approxControllable_iff_forall_not_exp`, `System.exp_coeff_eq_and_ne_zero`, `System.exp_of_isHautusEigenvector`, `Informative.complex` | Controllability/InputState | hypothesis `FattoriniHautusProperty T`; `κ ≠ 0` without it |
| `thm:io-window-controllability`, `eq:io-window-fh` | `System.approxControllable_of_forall_not_io_exp`, `System.approxControllable_iff_forall_not_io_exp`, `System.ne_zero_of_io_exp`, `ioWindowPairing` | Controllability/InputOutput | hypothesis `FattoriniHautusProperty T`; `g ≠ 0` without it |

## Section 6: linear–quadratic regulators

| Paper | Lean | File | Note |
|---|---|---|---|
| `eq:lqr-cost` | `LQRWeights`, `System.lqrCost`, `System.existsUnique_isMinOn_lqrCost` | LQR/ModelBased | `G`, `P(t)` are bilinear forms on `V` |
| `thm:lqr-riccati`, `eq:lqr-feedback` | `System.riccatiIntegralTheorem`, `System.riccatiIntegralTheorem_of_pos`, `System.IsRiccatiIntegralSolution`, `System.IsRiccatiIntegralSolution.eqOn`, `System.riccatiTheorem`, `System.nonempty_riccatiSolution`, `System.RiccatiSolution`, `System.riccatiP`, `System.feedback_ae`, `System.bStarP` | LQR/RiccatiIntegral, LQR/RiccatiEquation, LQR/RiccatiExistence, LQR/ModelBased | cited; proved without `hyp:compat` |
| `eq:lqr-cost-traj`, `eq:lqr-admissible`, `eq:lqr-data-problem` | `System.trajCost`, `System.dataAdmissible` | LQR/InputStateOutput | |
| `thm:lqr-data` | `System.lqr_data`, `System.lqr_data_riccati`, `System.lqr_data_riccati_of_riccatiTheorem`, `System.lqr_data_riccati_of_H1_H2` | LQR/InputStateOutput, LQR/RiccatiExistence | minimiser unique up to `TrajEquiv`; second part also without `hyp:compat` |
| `eq:lqr-data-io-problem` | `ioRegulatorCost`, `ioRegulatorFeasible` | LQR/InputOutput | |
| `thm:lqr-data-io` | `System.lqr_data_io` | LQR/InputOutput | |

## Appendix: `app:analytic-universal-sufficiency`

| Paper | Lean | File |
|---|---|---|
| `𝐇(s) = (s - A_{X,-1})⁻¹ B_X`, `Ω_⋆` | `System.transferX`, `System.transfer`, `System.transferX_spec`, `System.eq_transferX`, `System.differentiableOn_transfer`, `System.transfer_decay`, `System.exists_isPreconnected_resolventSet` | Informativity/Analytic/Transfer |
| `eq:analytic-growth-bound`, `eq:analytic-W-growth-bound` | hypothesis `hS` of the theorems; `System.exists_growth_W` | Semigroup/Analytic |
| `eq:analytic-exp-convolution`, `eq:analytic-qsummable` | `System.Lc_cexp_smul`, `System.summable_stateCoeff` | Informativity/Analytic/Expansion |
| `eq:analytic-state-expansion`, `eq:analytic-annihilator-expansion` | `System.mild_harmonic`, `System.mildW_harmonic`, `System.annihilator_expansion`, `System.window_expansion` | Informativity/Analytic/Expansion |
| `lem:bohr-annihilator` | `C0Semigroup.bohr_annihilator`, `System.analyticOnNhd_SW` | Informativity/Analytic/Bohr |
| `lem:transfer-laplace`, `eq:analytic-transfer-laplace` | `System.psi`, `System.analyticOnNhd_psi`, `System.memLp_psi`, `System.inner_transfer_eq_laplace`, `System.psiC_eq_zero_of_inner_transfer_eq_zero`, `System.denseRange_Lop_W` | Informativity/Analytic/Bohr |

## Section 1: examples

### The heat equation (`ex:intro-pde`, `app:boundary-heat-informative`)

| Paper | Lean | File | Note |
|---|---|---|---|
| `ex:intro-pde` | `BoundaryHeat.heatSystem`, `heatSystem_SX`, `heatSystem_A_graph`, `heatSystem_A_domain`, `heatSystem_A_apply`, `heatSystem_A_adjoint`, `heatSystem_Bstar`, `heatSystem_C`, `heatSystem_B_not_mem_range`, `heatSystem_C_unbounded` | Examples/Heat/System | `X = L²(0, 1)`, diffusivity `ν > 0`; `A` is `ν` times the Neumann Laplacian on `H²_N(0, 1)`, `B^⋆η = -ν η(0)`, `C w = w(ξ₀)` |
| diffusivity `ν` by time rescaling | `C0Semigroup.timeScale`, `C0Semigroup.generator_timeScale`, `System.timeScale`, `System.mild_timeScale`, `System.H1.timeScale`, `System.H2.timeScale`, `System.Compat.timeScale`, `System.approxControllable_timeScale`, `System.Bstar_timeScale`, `BoundaryHeat.unitHeatSystem` | Semigroup/TimeScale, System/TimeScale, Examples/Heat/UnitSystem | `heatSystem … ν` is the `ν = 1` system with semigroups `S(νt)` and `B ↦ ν B` |
| eigenbasis, modal coefficients | `CosineBasis.cosBasis`, `BoundaryHeat.eig`, `BoundaryHeat.obsCoeff_eq_cosFun`, `BoundaryHeat.ctrlCoeff_eq_neg_cosFun`, `BoundaryHeat.PDE.inner_cosBasis_neumann_control` | Analysis/CosineBasis, Examples/Heat/Kernel, Examples/Heat/PDE | modes from `0`, as in the paper |
| `eq:heat-separated-kernel` | `BoundaryHeat.kernel_eq_images`, `BoundaryHeat.exists_abs_kernelDeriv_le_unif` | Examples/Heat/Kernel | method of images; a pointwise bound on `(0, ∞) × [d_χ, 1)` |
| `eq:heat-localized-V` | `BoundaryHeat.V`, `BoundaryHeat.norm_V_sq_eq`, `BoundaryHeat.exists_fstV_eq_iff`, `BoundaryHeat.SV`, `BoundaryHeat.ιV`, `BoundaryHeat.Cutoff`, `BoundaryHeat.exists_smooth_cutoff`, `BoundaryHeat.integral_H1sq_orbit` | Examples/Heat/Spaces, Examples/Heat/Orbit, Examples/Heat/Cutoff | `χ ∈ C¹` suffices |
| `eq:heat-W-domain` | `BoundaryHeat.W`, `BoundaryHeat.ιW`, `BoundaryHeat.range_ιW` | Examples/Heat/Spaces | `W = D(A_V)` with the graph norm |
| `eq:heat-control-X`, `hyp:H1` | `BoundaryHeat.ModalData.exists_control_bound`, `BoundaryHeat.exists_control_bound`, `BoundaryHeat.heatSystem_H1` | Examples/Heat/Modal, Examples/Heat/Control, Examples/Heat/System | every horizon |
| `C ∈ L(W, ℝ)`, `hyp:H2`, `hyp:compat` | `BoundaryHeat.C`, `BoundaryHeat.hasSum_C`, `BoundaryHeat.heatSystem_H2`, `BoundaryHeat.heatSystem_compat` | Examples/Heat/UnitSystem, Examples/Heat/System | `C` by the trace formula in time, equal to `w(ξ₀)` on `D(A)` |

### The wave equation (`ex:intro-wave`)

| Paper | Lean | File | Note |
|---|---|---|---|
| `ex:intro-wave` | `Wave.PDE.exists_wave`, `Wave.PDE.waveSystemL2`, `Wave.PDE.waveSystemL2_A_domain`, `Wave.PDE.waveSystemL2_A_apply`, `Wave.PDE.waveSystemL2_Bstar`, `Wave.PDE.waveSystemL2_C`, `Wave.waveSystem_B_apply_not_mem_range`, `Wave.waveSystem_H1`, `Wave.waveSystem_H2`, `Wave.waveSystem_compat` | Examples/Wave/PDE, Examples/Wave/System | `W = X = L²(0, 1) × H⁻¹(0, 1)`, `V` a weighted `ℓ² × ℓ²`; modes from `0`, `ωₙ = c (n + 1) π` |
| the wave group is not analytic (Section 7) | `Wave.waveSystem_not_isAnalytic` | Examples/Wave/System | |
| `L²(0, 1)`, `H¹₀(0, 1)`, `H⁻¹(0, 1)` | `SineBasis.sinBasis`, `Sobolev01.H10`, `Sobolev01.exists_H10`, `Sobolev01.Hm1`, `Sobolev01.riesz`, `Sobolev01.riesz_eq_embed`, `Sobolev01.hasSum_norm_sq`, `Sobolev01.embed` | Analysis/SineBasis, Analysis/Sobolev01 | `H⁻¹ = (H¹₀)'`; the velocity `c • x₂` absorbs the norm `c⁻¹‖·‖_{H⁻¹}` (`Wave.PDE.scaledInner_freq_smul`) |

### The delay system (`ex:intro-delay`)

| Paper | Lean | File | Note |
|---|---|---|---|
| the neutral equation | `Delay.DelayOp`, `Delay.DelayOp.ofPoints`, `Delay.DelayOp.eval_ofPoints`, `Delay.mconv`, `Delay.eLpNorm_mconv_le`, `Delay.Equation`, `Delay.Equation.IsSolOn`, `Delay.Equation.isSolOn_sol`, `Delay.Equation.IsSolOn.ae_eq`, `Delay.Equation.IsSolOn.exists_hasWeakDeriv` | Examples/Delay/Convolution, Examples/Delay/Operator, Examples/Delay/Solution, Examples/Delay/Regularity | finite measures on `[0, h]` plus parts bounded on the `L²` history; `M` has no atom at `0` |
| the state `(x(t) - M x_t, x_t)` and the semigroup | `Delay.State`, `Delay.Equation.semigroup`, `Delay.Equation.mem_generator_domain_iff`, `Delay.Equation.generator_apply` | Examples/Delay/Semigroup | `D(A) = {(g(h) - M g, g) : g ∈ H¹}`, `A (g(h) - M g, g) = (L g, g')` |
| the system | `Delay.Model`, `Delay.Model.sys`, `Delay.Model.Bop_apply`, `Delay.Model.Cop_apply`, `Delay.Model.ιW_L`, `Delay.Model.H1`, `Delay.Model.H2`, `Delay.Model.compat` | Examples/Delay/System | `W = D(A)`, `V = X`, `B = (B₀, 0)` bounded |
| "a discrete output delay generally makes `C` unbounded on `X`" | `Delay.Model.not_exists_bound_C`, `Delay.Model.not_exists_bound_C_of_atom_zero`, `Delay.DelayOp.atom` | Examples/Delay/Unbounded | `θ ∈ (0, h]` with `C({θ}) + C({0}) M({θ}) ≠ 0` |
| `L`, `M`, `C` bounded on `C([-h, 0]; ℝⁿ)`; "no mass at `0`" | `exists_eq_integral_sub_integral`, `exists_eq_sum_integral_delay`, `NoMassAtZero`, `noMassAtZero_iff`, `Delay.exists_model` | Analysis/MeasureRepresentation, Examples/Delay/Bounded | Riesz representation (Jordan decomposition and Riesz–Markov–Kakutani); `E`, `Y` finite-dimensional |

## Proofs of the cited theorems

The module docstrings refer to these steps by their labels.

| Step | Lean | File |
|---|---|---|
| FH1: `η ⊥ ℛ_{T'}(0)` for one `T' > 0` puts `η` in the unobservable subspace `N = ⋂_{τ>0} ℛ_τ(0)^⊥` (analyticity enters only here) | `FH.unobs`, `FH.mem_unobs_of_forall`, `FH.adjoint_resolvent_mem_unobs`, `FH.bstar_eq_zero_of_mem_unobs` | Controllability/FHObservation |
| FH2: compact resolvents; root vectors do not depend on the resolvent point; the Fredholm alternative on an invariant subspace | `isCompactOperator_resolvent`, `dense_iSup_maxGenEigenspace_resolvent`, `resolvent_adjoint`, `le_orthogonal_iSup_maxGenEigenspace_adjoint`, `eq_bot_of_dense_iSup_maxGenEigenspace_adjoint` | Semigroup/CompactResolvent |
| FH3: `N_ℂ` is invariant under `K = R(μ₀, A^⋆)` and contains no eigenvector of `K` | `FH.unobsC`, `FH.exists_real_resolvent`, `FH.resolvent_mem_unobsC`, `FH.eq_zero_of_resolvent_eq_smul` | Controllability/FHResolvent |
| FH4–FH5: `N_ℂ = 0` | `FH.unobsC_eq_bot` | Controllability/FHSpectral |
| R1: tail problems on the fixed control space `L²(0, T; U)` | `Riccati.cut`, `Riccati.LQ`, `System.𝓞V`, `System.lqTail`, `System.lqrCost_eq_cost` | LQR/TailOperators |
| R2–R3: the value operator `P(s) = Q_s - M_s† K_s⁻¹ M_s` and its strong continuity | `Riccati.LQ.WF.cost_eq`, `Riccati.LQ.scont_Pop`, `System.riccatiP`, `System.continuousOn_riccatiP` | LQR/ValueOperator |
| R4: dynamic programming through first-order conditions | `System.foc_lqTail_cut`, `System.Pop_lqTail_mildW` | LQR/DynamicProgramming |
| R5: the adjoint of the input map, by needle variations (replaces Pritchard–Salamon's Lemma 2.5) | `System.coeFn_adjoint_input` | LQR/Feedback |
| R6: existence of a Riccati solution | `System.feedback_ae`, `System.nonempty_riccatiSolution` | LQR/RiccatiExistence |
| R7: the integral Riccati equation and uniqueness of its solution | `System.IsRiccatiIntegralSolution`, `System.bStarPV`, `System.bStarP_eq_bStarPV`, `System.IsRiccatiIntegralSolution.eqOn` | LQR/RiccatiEquation |
| R8: the right derivative of the value along the free motion | `System.reducedValue`, `System.exists_costate_uopt`, `System.hasDerivWithinAt_reducedValue` | LQR/RiccatiIntegralDeriv |
| R9: the value operator solves the integral equation | `System.isRiccatiIntegralSolution_riccatiP`, `System.riccatiIntegralTheorem` | LQR/RiccatiIntegral |

## Trace class

Mathlib has no trace-class operators.  `Analysis/TraceClass` defines them by nuclear
representations, `Analysis/PolarDecomposition` builds `|T|` (on real Hilbert spaces through the
complexification) and the polar decomposition, and `Analysis/TraceClassAbs` proves the textbook
characterisation.

| Statement | Lean |
|---|---|
| `T = ∑ₙ aₙ ⊗ bₙ` with `∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`; the trace is the same in every Hilbert basis and for every representation | `TraceClass.IsTraceClass`, `TraceClass.trace`, `TraceClass.IsTraceClass.hasSum_trace`, `TraceClass.trace_eq_tsum_of_hasSum` |
| validation | `TraceClass.trace_rankOne`, `TraceClass.isTraceClass_of_finiteDimensional`, `TraceClass.trace_eq_linearMap_trace` |
| trace class iff `tr \|T\| < ∞`, and `tr \|T\|` is the nuclear norm | `TraceClass.isTraceClass_iff_summable_realAbs`, `TraceClass.isLeast_nuclearSums_realAbs` (real); `TraceClass.isTraceClass_iff_summable_cfcAbs`, `TraceClass.isLeast_nuclearSums_cfcAbs` (complex) |
| `\|T\|` and the polar decomposition | `TraceClass.realAbs`, `TraceClass.realAbs_unique`, `TraceClass.polar_decomposition_realAbs`, `TraceClass.polar_decomposition_cfcAbs` |
| `\|𝒢(z)\| = 𝒢(z)` | `TraceClass.realAbs_gramian`, `TraceClass.hasSum_inner_realAbs_gramian` |
