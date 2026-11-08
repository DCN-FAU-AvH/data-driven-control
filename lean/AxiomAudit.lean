module

public import DataDrivenControl

/-!
# Axiom audit

Not part of the library.  After a full `scripts/build.sh`, run

    scripts/check.sh AxiomAudit.lean

Every result below must depend only on `propext`, `Classical.choice` and `Quot.sound`.  Module
`.olean`s record axioms when they are compiled, so the audit is meaningful only after a complete
rebuild.
-/

open DataDrivenControl

-- Section 2: setting
#print axioms System.H1.of_pos
#print axioms System.H2.of_pos
#print axioms System.bounded_H2
#print axioms System.output_ae_eq
#print axioms System.output_shift
#print axioms System.output_ιW
#print axioms System.eq_𝓕
#print axioms System.Q_decay
#print axioms System.L_exp
#print axioms System.BX_eq
#print axioms System.toExtrap_L
#print axioms System.exists_norm_Bstar_le
#print axioms System.inner_Bstar_of_dual
#print axioms System.adjoint_Lop_ae_eq
#print axioms System.inner_mild_eq

-- Section 3: informativity, the Gramian
#print axioms informative_iff_annihilator
#print axioms informative_iff
#print axioms isLeast_cspan
#print axioms informative_iff_injective_gramian
#print axioms ker_gramian_eq_orthogonal_cspan
#print axioms gramian_injective_iff_coercive
#print axioms isTraceClass_gramian
#print axioms trace_gramian
#print axioms hasSum_inner_gramian
#print axioms System.Informative.mild_of_mildW
#print axioms InformativityConverse.exists_informative_not_informativeW
#print axioms InformativityConverse.not_forall_informativeW_of_informative
#print axioms InformativityConverse.informative_X
#print axioms InformativityConverse.informative_mild
#print axioms InformativityConverse.not_informative_W
#print axioms InformativityConverse.model_standing
#print axioms InformativityConverse.model_not_exists_bound_C
#print axioms InformativityConverse.ιW_mildW_eq_state

-- Section 3: window informativity, persistency of excitation
#print axioms windowInformative_iff
#print axioms windowSynth_eq_integral
#print axioms System.informative_of_windowInformative
#print axioms WindowStrict.informative
#print axioms WindowStrict.not_windowInformative
#print axioms WindowStrict.exactlyControllable
#print axioms persistentlyExciting_iff_injective_gramian
#print axioms WindowInformative.persistentlyExcitingInfinite
#print axioms persistentlyExciting_of_forall_informative
#print axioms persistentlyExcitingInfinite_of_forall_informative
#print axioms System.informative_of_persistentlyExciting
#print axioms System.approxControllable_bounded_iff_kalman
#print axioms System.exactlyControllable_bounded_iff_kalman
#print axioms PECounterexample.approxControllable
#print axioms PECounterexample.persistentlyExcitingInfinite
#print axioms PECounterexample.not_informative
#print axioms PECounterexample.not_isHarmonic

-- Section 3: harmonic excitation, universal sufficiency for analytic semigroups
#print axioms isHarmonicPE_hpeSignal
#print axioms exists_isHarmonicPE
#print axioms HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite
#print axioms System.transferX_spec
#print axioms System.eq_transferX
#print axioms System.exists_growth_W
#print axioms C0Semigroup.bohr_annihilator
#print axioms System.inner_transfer_eq_laplace
#print axioms System.psiC_eq_zero_of_inner_transfer_eq_zero
#print axioms System.informative_of_approxControllable_harmonic
#print axioms System.windowInformative_of_approxControllable_harmonic
#print axioms System.approxControllable_of_informative_zero
#print axioms System.approxControllable_of_windowInformative_zero
#print axioms System.analytic_universal_sufficiency

-- Section 4: the fundamental lemma
#print axioms System.isBoundedBelow_graphOp
#print axioms System.synth_eq_graphOp
#print axioms System.hasWeakDeriv_mildW
#print axioms System.graph_identification
#print axioms System.willems_tfae
#print axioms System.eq_mild_of_trajectory
#print axioms System.inputState_mildW
#print axioms ioWindowSynth_eq_integral
#print axioms System.range_ioParam
#print axioms System.ioParam_injective
#print axioms System.isBoundedBelow_ioParam
#print axioms System.isClosed_ioBehavior
#print axioms System.eq_ioStateRecovery
#print axioms System.ioWindowSynth_eq_ioParam_comp
#print axioms System.closure_range_ioWindowSynth

-- Section 5: the Fattorini–Hautus test (root vectors of `A`) and the controllability tests
#print axioms System.fattoriniHautusProperty_of_hypotheses
#print axioms System.fattoriniHautusTheorem
#print axioms System.hautusCondition_of_approxControllable
#print axioms System.approxControllable_iff_of_fattoriniHautusProperty
#print axioms System.approxControllable_of_forall_not_exp
#print axioms System.approxControllable_iff_forall_not_exp
#print axioms System.exp_coeff_eq_and_ne_zero
#print axioms System.exp_of_isHautusEigenvector
#print axioms System.approxControllable_of_forall_not_io_exp
#print axioms System.approxControllable_iff_forall_not_io_exp
#print axioms System.ne_zero_of_io_exp

-- Section 6: the Riccati theorem (without `hyp:compat`) and the regulators
#print axioms System.existsUnique_isMinOn_lqrCost
#print axioms System.riccatiIntegralTheorem
#print axioms System.riccatiIntegralTheorem_of_pos
#print axioms System.IsRiccatiIntegralSolution.eqOn
#print axioms System.isRiccatiIntegralSolution_riccatiP
#print axioms System.riccatiTheorem
#print axioms System.nonempty_riccatiSolution
#print axioms System.bStarP_eq_bStarPV
#print axioms System.lqr_data
#print axioms System.lqr_data_riccati
#print axioms System.lqr_data_riccati_of_riccatiTheorem
#print axioms System.lqr_data_riccati_of_H1_H2
#print axioms System.lqr_data_io

-- Trace class: the nuclear definition is the textbook one
#print axioms TraceClass.trace_rankOne
#print axioms TraceClass.trace_eq_linearMap_trace
#print axioms TraceClass.isTraceClass_iff_summable_realAbs
#print axioms TraceClass.isLeast_nuclearSums_realAbs
#print axioms TraceClass.isTraceClass_iff_summable_cfcAbs
#print axioms TraceClass.isLeast_nuclearSums_cfcAbs
#print axioms TraceClass.polar_decomposition_realAbs
#print axioms TraceClass.realAbs_gramian

-- Time rescaling (the diffusivity `ν` of the heat example)
#print axioms C0Semigroup.generator_timeScale
#print axioms System.mild_timeScale
#print axioms System.approxControllable_timeScale
#print axioms System.H1.timeScale
#print axioms System.H2.timeScale
#print axioms System.Compat.timeScale
#print axioms System.Bstar_timeScale

-- Example: the heat equation (`ex:intro-pde`, `ex:boundary-heat-informative`, every `ν > 0`)
#print axioms BoundaryHeat.exists_boundaryHeat
#print axioms BoundaryHeat.heatSystem_TFAE
#print axioms BoundaryHeat.heatSystem_informative
#print axioms BoundaryHeat.heatSystem_windowInformative
#print axioms BoundaryHeat.heatSystem_approxControllable
#print axioms BoundaryHeat.heatSystem_H1
#print axioms BoundaryHeat.heatSystem_H2
#print axioms BoundaryHeat.heatSystem_compat
#print axioms BoundaryHeat.heatSystem_SX
#print axioms BoundaryHeat.heatSystem_A_graph
#print axioms BoundaryHeat.heatSystem_A_domain
#print axioms BoundaryHeat.heatSystem_A_apply
#print axioms BoundaryHeat.heatSystem_A_adjoint
#print axioms BoundaryHeat.heatSystem_Bstar
#print axioms BoundaryHeat.heatSystem_C
#print axioms BoundaryHeat.exists_heatSystem_ιW_ae_eq
#print axioms BoundaryHeat.heatSystem_B_not_mem_range
#print axioms BoundaryHeat.heatSystem_C_unbounded
#print axioms BoundaryHeat.PDE.inner_cosBasis_neumann_control
#print axioms BoundaryHeat.kernel_eq_images
#print axioms BoundaryHeat.exists_abs_kernelDeriv_le_unif
#print axioms BoundaryHeat.exists_smooth_cutoff
#print axioms BoundaryHeat.norm_V_sq_eq
#print axioms BoundaryHeat.exists_fstV_eq_iff
#print axioms BoundaryHeat.range_ιW
#print axioms BoundaryHeat.integral_H1sq_orbit
#print axioms BoundaryHeat.heatInput_apply
#print axioms BoundaryHeat.isHarmonicPE_heatInput
#print axioms CosineBasis.cosBasis

-- Example: the wave equation (`ex:intro-wave`)
#print axioms Wave.PDE.exists_wave
#print axioms Wave.PDE.waveSystemL2_A_domain
#print axioms Wave.PDE.waveSystemL2_A_apply
#print axioms Wave.PDE.waveSystemL2_Bstar
#print axioms Wave.PDE.waveSystemL2_C
#print axioms Wave.PDE.scaledInner_freq_smul
#print axioms Wave.waveSystem_H1
#print axioms Wave.waveSystem_H2
#print axioms Wave.waveSystem_compat
#print axioms Wave.waveSystem_not_isAnalytic
#print axioms SineBasis.sinBasis
#print axioms Sobolev01.exists_H10
#print axioms Sobolev01.hasSum_norm_sq
#print axioms Sobolev01.riesz_eq_embed

-- Bounded maps on `C([-h, 0]; E)` are given by measures (the delay example's `L`, `M`, `C`)
#print axioms exists_eq_integral_sub_integral
#print axioms exists_eq_sum_integral_delay
#print axioms noMassAtZero_iff

-- Example: the delay system (`ex:intro-delay`)
#print axioms Delay.kernelOp_apply
#print axioms Delay.Equation.isUnit_opK
#print axioms Delay.Equation.isSolOn_sol
#print axioms Delay.Equation.IsSolOn.ae_eq
#print axioms Delay.Equation.norm_solL_le
#print axioms Delay.Equation.IsSolOn.exists_hasWeakDeriv
#print axioms Delay.Equation.semigroup
#print axioms Delay.Equation.mem_generator_domain_iff
#print axioms Delay.Equation.generator_apply
#print axioms Delay.Model.Bop_apply
#print axioms Delay.Model.Cop_apply
#print axioms Delay.Model.ιW_L
#print axioms Delay.Model.H1
#print axioms Delay.Model.H2
#print axioms Delay.Model.compat
#print axioms Delay.Model.not_exists_bound_C
#print axioms Delay.Model.not_exists_bound_C_of_atom_zero
#print axioms Delay.DelayOp.eval_ofPoints
#print axioms Delay.DelayOp.eLpNorm_eval_le
#print axioms Delay.DelayOp.tendsto_wconst
#print axioms Delay.eLpNorm_mconv_le
#print axioms Delay.hasWeakDeriv_mconv
#print axioms Delay.wnorm_mconv_le
#print axioms Delay.Equation.semigroup_apply
-- the paper's bounded `L`, `M`, `C` on `C([-h, 0]; ℝⁿ)`
#print axioms Delay.exists_model
