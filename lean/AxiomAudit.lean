module

public import DataDrivenControl.Informativity.AnalyticSufficiency
public import DataDrivenControl.Informativity.FiniteDim
public import DataDrivenControl.Informativity.Necessity
public import DataDrivenControl.FundamentalLemma.Willems
public import DataDrivenControl.FundamentalLemma.InputOutput
public import DataDrivenControl.Controllability.InputState
public import DataDrivenControl.Controllability.InputOutput
public import DataDrivenControl.LQR.InputStateOutput
public import DataDrivenControl.LQR.InputOutput
public import DataDrivenControl.Examples.WindowStrict
public import DataDrivenControl.Examples.PECounterexample
public import DataDrivenControl.Signal.GramianTrace
public import DataDrivenControl.Examples.BoundaryHeat
public import DataDrivenControl.Examples.Heat.PDE
public import DataDrivenControl.Controllability.FHSpectral
public import DataDrivenControl.LQR.RiccatiExistence
public import DataDrivenControl.LQR.RiccatiIntegral
public import DataDrivenControl.Examples.Delay.Unbounded
public import DataDrivenControl.Examples.Wave.System
public import DataDrivenControl.Analysis.TraceClassAbs
public import DataDrivenControl.Examples.Heat.LocalizedSystem
public import DataDrivenControl.Examples.NeutralDelay.Unbounded
public import DataDrivenControl.Examples.NeutralDelay.Retarded
public import DataDrivenControl.Examples.Wave.PDE
public import DataDrivenControl.Examples.InformativityConverse

/-!
# Axiom audit

Not part of the library (it is not imported by `DataDrivenControl.lean`).  Check it after a full
`scripts/build.sh` with

    scripts/check.sh AxiomAudit.lean

Every main result of the paper must depend only on `propext`, `Classical.choice` and
`Quot.sound`.  Module `.olean`s record axiom sets when they are compiled, so this audit is only
meaningful after a full rebuild.
-/

open DataDrivenControl

-- Section 2: setting, mild solutions, control realisation
#print axioms System.H1.of_pos
#print axioms System.output_ae_eq
#print axioms System.output_shift
#print axioms System.Q_decay
#print axioms System.BX_eq
#print axioms System.inner_mild_eq

-- Section 3.1–3.2: informativity
#print axioms informative_iff_injective_gramian
#print axioms gramian_injective_iff_coercive
#print axioms ker_gramian_eq_orthogonal_cspan
#print axioms System.informative_of_windowInformative
-- Remark after lem:informative-gramian: the converse fails
#print axioms InformativityConverse.exists_informative_not_informativeW
#print axioms InformativityConverse.not_forall_informativeW_of_informative
#print axioms InformativityConverse.informative_X
#print axioms InformativityConverse.informative_mild
#print axioms InformativityConverse.not_informative_W
#print axioms InformativityConverse.ae_eq_zero_of_moments_eq_zero

-- Section 3.1: the Gramian is trace class (eq:hilbert-gramian)
#print axioms isTraceClass_gramian
#print axioms trace_gramian
#print axioms hasSum_inner_gramian
#print axioms hasSum_re_inner_gramian
-- trace class = tr |T| < ∞ (polar decomposition), and |𝒢(z)| = 𝒢(z)
#print axioms TraceClass.polar_decomposition_cfcAbs
#print axioms TraceClass.polar_decomposition_realAbs
#print axioms TraceClass.cfcAbs_unique
#print axioms TraceClass.realAbs_unique
#print axioms TraceClass.complexify_realAbs
#print axioms TraceClass.isTraceClass_iff_summable_cfcAbs
#print axioms TraceClass.isTraceClass_iff_isTraceClass_cfcAbs
#print axioms TraceClass.isLeast_nuclearSums_cfcAbs
#print axioms TraceClass.isTraceClass_iff_summable_realAbs
#print axioms TraceClass.isTraceClass_iff_isTraceClass_realAbs
#print axioms TraceClass.trace_realAbs_le
#print axioms TraceClass.isLeast_nuclearSums_realAbs
#print axioms TraceClass.isTraceClass_complexify_iff
#print axioms TraceClass.trace_complexify
#print axioms TraceClass.realAbs_gramian
#print axioms TraceClass.hasSum_inner_realAbs_gramian

-- Section 3.3–3.5: persistency of excitation, harmonic excitation, analytic sufficiency
#print axioms persistentlyExciting_iff_injective_gramian
#print axioms WindowInformative.persistentlyExcitingInfinite
#print axioms persistentlyExciting_of_forall_informative
#print axioms persistentlyExcitingInfinite_of_forall_informative
#print axioms System.informative_of_persistentlyExciting
#print axioms isHarmonicPE_hpeSignal
#print axioms exists_isHarmonicPE
#print axioms HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite
#print axioms C0Semigroup.bohr_annihilator
#print axioms System.informative_of_approxControllable_harmonic
#print axioms System.windowInformative_of_approxControllable_harmonic
#print axioms System.approxControllable_of_informative_zero
#print axioms System.approxControllable_of_windowInformative_zero
#print axioms System.analytic_universal_sufficiency

-- Examples of Section 3
#print axioms WindowStrict.exactlyControllable
#print axioms WindowStrict.informative
#print axioms WindowStrict.not_windowInformative
#print axioms PECounterexample.approxControllable
#print axioms PECounterexample.persistentlyExcitingInfinite
#print axioms PECounterexample.not_informative
#print axioms PECounterexample.not_isHarmonic

-- Example of Section 3: the boundary-controlled heat equation (ex:boundary-heat-informative)
#print axioms BoundaryHeat.exists_boundaryHeat
#print axioms BoundaryHeat.heatSystem_TFAE
#print axioms BoundaryHeat.heatSystem_informative
#print axioms BoundaryHeat.heatSystem_windowInformative
#print axioms BoundaryHeat.heatSystem_approxControllable
#print axioms BoundaryHeat.heatSystem_H1
#print axioms BoundaryHeat.heatSystem_H2
#print axioms BoundaryHeat.heatSystem_compat
-- the dictionary to L²(0, 1)
#print axioms CosineBasis.cosBasis
#print axioms CosineBasis.hasSum_cosFun_mul_inner
#print axioms BoundaryHeat.PDE.inner_cosBasis_neumann_control
#print axioms BoundaryHeat.PDE.mem_graph_generator_iff
#print axioms BoundaryHeat.PDE.heatSystemL2_A_adjoint
#print axioms BoundaryHeat.PDE.heatSystemL2_C
#print axioms BoundaryHeat.PDE.heatSystemL2_Bstar
#print axioms BoundaryHeat.PDE.exists_boundaryHeat_L2
-- the paper's localised V (eq:heat-localized-V)
#print axioms BoundaryHeat.Localized.exists_boundaryHeat_loc
#print axioms BoundaryHeat.Localized.exists_smooth_cutoff
#print axioms BoundaryHeat.Localized.exists_abs_kernelDeriv_le_unif
#print axioms BoundaryHeat.Localized.kernelDerivX_eq_tsum
#print axioms BoundaryHeat.Localized.norm_orbitH_sq_eq
#print axioms BoundaryHeat.Localized.integral_H1sq_orbit
#print axioms BoundaryHeat.Localized.norm_V_sq_eq
#print axioms BoundaryHeat.Localized.exists_fstV_eq_iff
#print axioms BoundaryHeat.Localized.SV
#print axioms BoundaryHeat.Localized.denseRange_ιV
#print axioms BoundaryHeat.Localized.range_ιW
#print axioms BoundaryHeat.Localized.exists_control_bound_loc
#print axioms BoundaryHeat.Localized.heatSystemLoc_H1
#print axioms BoundaryHeat.Localized.heatSystemLoc_H2
#print axioms BoundaryHeat.Localized.heatSystemLoc_compat
#print axioms BoundaryHeat.Localized.heatSystemLoc_C
#print axioms BoundaryHeat.Localized.heatSystemLoc_Bstar
#print axioms BoundaryHeat.Localized.heatSystemLoc_C_unbounded
#print axioms BoundaryHeat.Localized.heatSystemLoc_informative
#print axioms BoundaryHeat.Localized.heatSystemLoc_windowInformative

-- Example of the introduction: the delay system with delayed output (ex:intro-delay, M = 0)
#print axioms Delay.kernelOp_apply
#print axioms Delay.Equation.isSolOn_sol
#print axioms Delay.Equation.IsSolOn.eqOn
#print axioms Delay.Equation.sol_add_time
#print axioms Delay.Equation.norm_sol_le
#print axioms Delay.Equation.hasWeakDeriv_traj
#print axioms Delay.Equation.semigroup
#print axioms Delay.Equation.mem_generator_domain_iff
#print axioms Delay.Equation.generator_apply
#print axioms Delay.Model.Cop_apply
#print axioms Delay.Model.ctrlState_eq_conv
#print axioms Delay.Model.ιW_L
#print axioms Delay.Model.H1
#print axioms Delay.Model.H2
#print axioms Delay.Model.compat
#print axioms Delay.Model.not_exists_bound_C
#print axioms Delay.Model.not_exists_bound_C_of_ne_zero

-- Example of the introduction: the neutral delay system (ex:intro-delay, M ≠ 0)
#print axioms NeutralDelay.isUnit_one_sub_of_wnorm_le
#print axioms NeutralDelay.wnorm_window_le
#print axioms NeutralDelay.Equation.isUnit_opK
#print axioms NeutralDelay.Equation.isSolOn_sol
#print axioms NeutralDelay.Equation.IsSolOn.ae_eq
#print axioms NeutralDelay.Equation.norm_solL_le
#print axioms NeutralDelay.Equation.IsSolOn.exists_hasWeakDeriv
#print axioms NeutralDelay.Equation.semigroup
#print axioms NeutralDelay.Equation.mem_generator_domain_iff
#print axioms NeutralDelay.Equation.generator_apply
#print axioms NeutralDelay.Equation.semigroup_eq_of_M_eq_zero
#print axioms NeutralDelay.Model.Cop_apply
#print axioms NeutralDelay.Model.ιW_L
#print axioms NeutralDelay.Model.H1
#print axioms NeutralDelay.Model.H2
#print axioms NeutralDelay.Model.compat
#print axioms NeutralDelay.Model.not_exists_bound_C

-- Example of the introduction: the wave equation with Dirichlet control (ex:intro-wave)
#print axioms Rotation.rotGroup
#print axioms Rotation.adjoint_rotGroup
#print axioms Rotation.hasSum_sq_generator
#print axioms Rotation.not_isAnalytic
#print axioms Wave.tsum_sq_integral_cos_le
#print axioms Wave.tsum_sq_integral_sin_le
#print axioms Wave.eLpNorm_tsum_le
#print axioms Wave.waveSystem_SX
#print axioms Wave.waveSystem_H1
#print axioms Wave.waveSystem_H2
#print axioms Wave.waveSystem_compat
#print axioms Wave.hasSum_waveSystem_C
#print axioms Wave.inner_waveSystem_Lop
#print axioms Wave.hasSum_waveSystem_Bstar
#print axioms Wave.waveSystem_B_apply_not_mem_range
#print axioms Wave.waveSystem_not_isAnalytic
#print axioms Wave.exists_wave
-- the dictionary to L²(0, 1) × H⁻¹(0, 1)
#print axioms SineBasis.sinBasis
#print axioms Sobolev01.hasSum_norm_sq
#print axioms Sobolev01.hasSum_norm_embed_sq
#print axioms Sobolev01.denseRange_embed
#print axioms Sobolev01.exists_isDirichletH2_toH10
#print axioms Wave.PDE.hasSum_scaledInner_sq
#print axioms Wave.PDE.waveSystemL2_C
#print axioms Wave.PDE.waveSystemL2_Bstar
#print axioms Wave.PDE.waveSystemL2_A_domain
#print axioms Wave.PDE.waveSystemL2_A_apply
#print axioms Wave.PDE.exists_wave_L2

-- Section 4: fundamental lemmas
#print axioms System.hasWeakDeriv_mildW
#print axioms System.synth_eq_graphOp
#print axioms System.graph_identification
#print axioms System.willems_tfae
#print axioms System.eq_mild_of_trajectory
#print axioms System.inputState_mildW
#print axioms System.isClosed_ioBehavior
#print axioms System.closure_range_ioWindowSynth

-- Section 5: the Fattorini–Hautus theorem (prop:fattorini-hautus, root vectors of A)
#print axioms System.fattoriniHautusProperty_of_hypotheses
#print axioms System.fattoriniHautusTheorem

-- Section 5: controllability tests
#print axioms System.hautusCondition_of_approxControllable
#print axioms System.approxControllable_iff_of_fattoriniHautusProperty
#print axioms System.approxControllable_of_forall_not_exp
#print axioms System.approxControllable_iff_forall_not_exp
#print axioms System.exp_coeff_eq_and_ne_zero
#print axioms System.approxControllable_of_forall_not_io_exp
#print axioms System.approxControllable_iff_forall_not_io_exp
#print axioms System.ne_zero_of_io_exp

-- Section 6: the Riccati theorem (thm:lqr-riccati, without hyp:compat)
#print axioms System.riccatiTheorem
#print axioms System.nonempty_riccatiSolution

-- Section 6: LQR
#print axioms System.existsUnique_isMinOn_lqrCost
#print axioms System.lqr_data
#print axioms System.lqr_data_riccati
#print axioms System.lqr_data_riccati_of_riccatiTheorem
#print axioms System.lqr_data_riccati_of_H1_H2
-- the integral Riccati equation and uniqueness (thm:lqr-riccati in full)
#print axioms System.IsRiccatiIntegralSolution.eqOn
#print axioms System.isRiccatiIntegralSolution_riccatiP
#print axioms System.IsRiccatiIntegralSolution.eqOn_riccatiP
#print axioms System.IsRiccatiIntegralSolution.toRiccatiSolution
#print axioms System.riccatiIntegralTheorem
#print axioms System.riccatiIntegralTheorem_of_pos
#print axioms System.lqr_data_io

-- Semigroup library: Ball's theorem, extrapolation, adjoint, diagonal and modal systems
#print axioms C0Semigroup.isWeakSol_iff
#print axioms C0Semigroup.integral_eq_iff_weak
#print axioms C0Semigroup.generator_adjoint
#print axioms C0Semigroup.resolvent_eq_integral
#print axioms C0Semigroup.IsAnalytic.analyticOnNhd
#print axioms System.approxControllable_of_modal
