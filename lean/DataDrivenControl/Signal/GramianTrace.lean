module

public import DataDrivenControl.Analysis.TraceClass
public import DataDrivenControl.Signal.Gramian

/-!
# The Gramian is trace class

Paper: `eq:hilbert-gramian` — the Gramian `𝒢(z) = ∫ z(t) ⊗ z(t) dt` of a square-integrable signal
is self-adjoint, nonnegative (`Signal/Gramian`) and **trace class**, with `tr 𝒢(z) = ‖z‖²_{L²}`.

Route: the analysis operator `M : E →L[𝕜] L²(μ; 𝕜)`, `M ζ = (t ↦ ⟪z t, ζ⟫)`
(`TraceClass.analysisOp`), satisfies
* `𝒢(z) = M† M` (`gramian_eq_adjoint_comp`, from `inner_gramian_apply`);
* `∑ᵢ ‖M eᵢ‖² = ∫ ‖z‖²` in every Hilbert basis (`TraceClass.tsum_enorm_analysisOp_sq`): Parseval
  pointwise and `lintegral_tsum`.  The basis may be uncountable; an a.e. strongly measurable signal
  is a.e. separably valued and so meets only countably many basis vectors
  (`TraceClass.exists_countable_ae_inner_eq_zero`);

so `M` is Hilbert–Schmidt (`TraceClass.isHilbertSchmidt_analysisOp`) and
`TraceClass.isTraceClass_adjoint_comp` applies.

## Main results

* `isTraceClass_gramian`: `TraceClass.IsTraceClass (gramian 𝕜 μ z)` for `MemLp z 2 μ`;
* `trace_gramian`: `TraceClass.trace (gramian 𝕜 μ z) = ∫ ‖z t‖² ∂μ`;
* `hasSum_inner_gramian`, `hasSum_re_inner_gramian`: the textbook form — `∑ᵢ ⟪eᵢ, 𝒢(z) eᵢ⟫ = ∫ ‖z‖²`
  in every Hilbert basis, with nonnegative terms.  As `𝒢(z) ≥ 0`, `|𝒢(z)| = 𝒢(z)` and this is
  `tr |𝒢(z)| < ∞` directly.  The general equivalence of the trace class with `tr |T| < ∞` is
  `Analysis/TraceClassAbs` (`TraceClass.hasSum_inner_realAbs_gramian` restates this with `|𝒢(z)|`).

As in `Signal/Gramian`, the Gramian needs `[NormedSpace ℝ E]`; the trace needs `[CompleteSpace E]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct ENNReal NNReal

noncomputable section

namespace DataDrivenControl

namespace TraceClass

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {z : α → E}

/-- An a.e. strongly measurable signal meets only countably many vectors of an orthonormal family:
there is a countable `I` with `⟪vᵢ, z t⟫ = 0` for all `i ∉ I`, for a.e. `t` (the signal is a.e.
separably valued, and every vector meets only countably many `vᵢ` by Bessel's inequality). -/
theorem exists_countable_ae_inner_eq_zero {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hz : AEStronglyMeasurable z μ) :
    ∃ I : Set ι, I.Countable ∧ ∀ᵐ t ∂μ, ∀ i ∉ I, ⟪v i, z t⟫_𝕜 = 0 := by
  obtain ⟨s, hs, hae⟩ := hz.isSeparable_ae_range
  obtain ⟨C, hCc, hsC⟩ := hs
  refine ⟨⋃ c ∈ C, Function.support fun i => ⟪v i, c⟫_𝕜, hCc.biUnion fun c _ => ?_, ?_⟩
  · have h := (hv.inner_products_summable c).countable_support
    convert h using 1
    ext i
    simp
  · filter_upwards [hae] with t ht i hi
    simp only [mem_iUnion, Function.mem_support, not_exists, not_not] at hi
    have hcl : IsClosed {x : E | ⟪v i, x⟫_𝕜 = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    exact hcl.closure_subset_iff.2 (fun c hc => hi c hc) (hsC ht)

/-- `∫ ‖z‖² = ‖z‖²_{L²}` in `ℝ≥0∞`. -/
theorem lintegral_enorm_sq_eq_eLpNorm_sq (hz : AEStronglyMeasurable z μ) :
    ∫⁻ t, ‖z t‖ₑ ^ 2 ∂μ = eLpNorm z 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hz
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h
  exact h.symm

/-- Parseval under the integral: `∑ᵢ ∫ |⟪eᵢ, z t⟫|² = ∫ ‖z t‖²` in `ℝ≥0∞`, for every Hilbert basis
(of any cardinality) and every a.e. strongly measurable `z`. -/
theorem tsum_lintegral_enorm_inner_sq {ι : Type*} (e : HilbertBasis ι 𝕜 E)
    (hz : AEStronglyMeasurable z μ) :
    ∑' i, ∫⁻ t, ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2 ∂μ = ∫⁻ t, ‖z t‖ₑ ^ 2 ∂μ := by
  obtain ⟨I, hI, hae⟩ := exists_countable_ae_inner_eq_zero e.orthonormal hz
  have : Countable I := hI.to_subtype
  have hmeas : ∀ i, AEMeasurable (fun t => ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2) μ := fun i =>
    ((aestronglyMeasurable_const.inner hz).enorm).pow_const 2
  have hzero : ∀ i ∉ I, ∫⁻ t, ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2 ∂μ = 0 := fun i hi => by
    rw [lintegral_congr_ae (g := fun _ => 0) (by filter_upwards [hae] with t ht; simp [ht i hi]),
      lintegral_zero]
  calc ∑' i, ∫⁻ t, ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2 ∂μ
      = ∑' i : I, ∫⁻ t, ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2 ∂μ :=
        (tsum_subtype_eq_of_support_subset fun i hi =>
          Classical.byContradiction fun h => hi (hzero i h)).symm
    _ = ∫⁻ t, ∑' i : I, ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2 ∂μ := (lintegral_tsum fun (i : I) => hmeas i).symm
    _ = ∫⁻ t, ‖z t‖ₑ ^ 2 ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with t ht
        rw [enorm_sq_eq_tsum e (z t)]
        exact tsum_subtype_eq_of_support_subset (f := fun i => ‖⟪e i, z t⟫_𝕜‖ₑ ^ 2) (s := I)
          fun i hi => Classical.byContradiction fun h => hi (by simp [ht i h])

variable (𝕜) in
/-- The linear map underlying `analysisOp`. -/
def analysisLin (hz : MemLp z 2 μ) : E →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun ζ := (hz.inner_const (𝕜 := 𝕜) ζ).toLp _
  map_add' ζ ξ := by
    ext1
    filter_upwards [MemLp.coeFn_toLp (hz.inner_const (𝕜 := 𝕜) (ζ + ξ)),
      Lp.coeFn_add ((hz.inner_const (𝕜 := 𝕜) ζ).toLp _) ((hz.inner_const (𝕜 := 𝕜) ξ).toLp _),
      MemLp.coeFn_toLp (hz.inner_const (𝕜 := 𝕜) ζ),
      MemLp.coeFn_toLp (hz.inner_const (𝕜 := 𝕜) ξ)] with t h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, inner_add_right]
  map_smul' c ζ := by
    ext1
    filter_upwards [MemLp.coeFn_toLp (hz.inner_const (𝕜 := 𝕜) (c • ζ)),
      Lp.coeFn_smul c ((hz.inner_const (𝕜 := 𝕜) ζ).toLp _),
      MemLp.coeFn_toLp (hz.inner_const (𝕜 := 𝕜) ζ)] with t h1 h2 h3
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, inner_smul_right, smul_eq_mul]

/-- `‖M ζ‖ ≤ ‖z‖_{L²} ‖ζ‖`. -/
theorem norm_analysisLin_le (hz : MemLp z 2 μ) (ζ : E) :
    ‖analysisLin 𝕜 hz ζ‖ ≤ (eLpNorm z 2 μ).toReal * ‖ζ‖ := by
  change ‖(hz.inner_const (𝕜 := 𝕜) ζ).toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  have h : eLpNorm (fun t => ⟪z t, ζ⟫_𝕜) 2 μ ≤ ENNReal.ofReal ‖ζ‖ * eLpNorm z 2 μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hz.inner_const (𝕜 := 𝕜) ζ).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [mul_comm]; exact norm_inner_le_norm _ _) 2
  calc (eLpNorm (fun t => ⟪z t, ζ⟫_𝕜) 2 μ).toReal
      ≤ (ENNReal.ofReal ‖ζ‖ * eLpNorm z 2 μ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hz.eLpNorm_ne_top) h
    _ = (eLpNorm z 2 μ).toReal * ‖ζ‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), mul_comm]

variable (𝕜) in
/-- The **analysis operator** `M ζ = (t ↦ ⟪z t, ζ⟫)` of a square-integrable signal, as a bounded
operator `E → L²(μ; 𝕜)`.  It satisfies `M† M = 𝒢(z)` (`gramian_eq_adjoint_comp`). -/
def analysisOp (hz : MemLp z 2 μ) : E →L[𝕜] Lp 𝕜 2 μ :=
  (analysisLin 𝕜 hz).mkContinuous _ (norm_analysisLin_le hz)

/-- `M ζ` is the `L²` class of `t ↦ ⟪z t, ζ⟫`. -/
theorem analysisOp_apply (hz : MemLp z 2 μ) (ζ : E) :
    analysisOp 𝕜 hz ζ = (hz.inner_const (𝕜 := 𝕜) ζ).toLp _ :=
  rfl

/-- `M ζ = ⟪z ·, ζ⟫` almost everywhere. -/
theorem coeFn_analysisOp (hz : MemLp z 2 μ) (ζ : E) :
    (analysisOp 𝕜 hz ζ : α → 𝕜) =ᵐ[μ] fun t => ⟪z t, ζ⟫_𝕜 := by
  rw [analysisOp_apply]
  exact MemLp.coeFn_toLp _

/-- `⟪M ζ, M ξ⟫_{L²} = ∫ ⟪ζ, z t⟫ ⟪z t, ξ⟫`. -/
theorem inner_analysisOp (hz : MemLp z 2 μ) (ζ ξ : E) :
    ⟪analysisOp 𝕜 hz ζ, analysisOp 𝕜 hz ξ⟫_𝕜 = ∫ t, ⟪ζ, z t⟫_𝕜 * ⟪z t, ξ⟫_𝕜 ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_analysisOp (𝕜 := 𝕜) hz ζ, coeFn_analysisOp (𝕜 := 𝕜) hz ξ] with t h1 h2
  rw [h1, h2, RCLike.inner_apply, inner_conj_symm, mul_comm]

/-- `‖M ζ‖² = ∫ |⟪z t, ζ⟫|²` in `ℝ≥0∞`. -/
theorem enorm_analysisOp_sq (hz : MemLp z 2 μ) (ζ : E) :
    ‖analysisOp 𝕜 hz ζ‖ₑ ^ 2 = ∫⁻ t, ‖⟪z t, ζ⟫_𝕜‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (coeFn_analysisOp (𝕜 := 𝕜) hz ζ),
    lintegral_enorm_sq_eq_eLpNorm_sq (hz.inner_const (𝕜 := 𝕜) ζ).aestronglyMeasurable]

/-- The Hilbert–Schmidt sum of the analysis operator: `∑ᵢ ‖M eᵢ‖² = ∫ ‖z‖²` in `ℝ≥0∞`, in every
Hilbert basis. -/
theorem tsum_enorm_analysisOp_sq {ι : Type*} (e : HilbertBasis ι 𝕜 E) (hz : MemLp z 2 μ) :
    ∑' i, ‖analysisOp 𝕜 hz (e i)‖ₑ ^ 2 = ∫⁻ t, ‖z t‖ₑ ^ 2 ∂μ := by
  rw [← tsum_lintegral_enorm_inner_sq e hz.aestronglyMeasurable]
  refine tsum_congr fun i => ?_
  rw [enorm_analysisOp_sq]
  refine lintegral_congr fun t => ?_
  rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]

/-- The analysis operator of a square-integrable signal is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_analysisOp [CompleteSpace E] (hz : MemLp z 2 μ) :
    IsHilbertSchmidt (analysisOp 𝕜 hz) := by
  rw [isHilbertSchmidt_iff_tsum_ne_top (stdHilbertBasis 𝕜 E), tsum_enorm_analysisOp_sq,
    lintegral_enorm_sq_eq_eLpNorm_sq hz.aestronglyMeasurable]
  exact ENNReal.pow_ne_top hz.eLpNorm_ne_top

end TraceClass

open TraceClass

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {z : α → E}

/-- `𝒢(z) = M† M` for the analysis operator `M ζ = ⟪z ·, ζ⟫`. -/
theorem gramian_eq_adjoint_comp (hz : MemLp z 2 μ) :
    gramian 𝕜 μ z = ContinuousLinearMap.adjoint (analysisOp 𝕜 hz) ∘L analysisOp 𝕜 hz := by
  ext ζ
  refine ext_inner_right 𝕜 fun ξ => ?_
  rw [inner_gramian_apply hz, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_analysisOp]

/-- `eq:hilbert-gramian`: the Gramian of a square-integrable signal is **trace class**. -/
theorem isTraceClass_gramian (hz : MemLp z 2 μ) : TraceClass.IsTraceClass (gramian 𝕜 μ z) := by
  rw [gramian_eq_adjoint_comp hz]
  exact isTraceClass_adjoint_comp (isHilbertSchmidt_analysisOp hz) (isHilbertSchmidt_analysisOp hz)

/-- `eq:hilbert-gramian`: `tr 𝒢(z) = ‖z‖²_{L²} = ∫ ‖z t‖²`. -/
theorem trace_gramian (hz : MemLp z 2 μ) :
    TraceClass.trace (gramian 𝕜 μ z) = ((∫ t, ‖z t‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
  have hM := isHilbertSchmidt_analysisOp (𝕜 := 𝕜) hz
  have h := hasSum_inner_trace_adjoint_comp hM hM (stdHilbertBasis 𝕜 E)
  rw [gramian_eq_adjoint_comp hz, ← h.tsum_eq]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, ← RCLike.ofReal_tsum]
  congr 1
  rw [tsum_norm_sq_eq_toReal, tsum_enorm_analysisOp_sq,
    integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖z t‖ ^ 2)
      (Eventually.of_forall fun t => sq_nonneg ‖z t‖) (hz.aestronglyMeasurable.norm.pow 2)]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
/-- `eq:hilbert-gramian` in the textbook form of the trace class: in **every** Hilbert basis `e`,
the diagonal sum `∑ᵢ ⟪eᵢ, 𝒢(z) eᵢ⟫` converges to `∫ ‖z‖²`.  Since `𝒢(z)` is nonnegative and
self-adjoint (`isPositive_gramian`), `|𝒢(z)| = 𝒢(z)`, so this is the condition `tr |𝒢(z)| < ∞`;
the general equivalence of `Analysis/TraceClassAbs` is not needed for the Gramian. -/
theorem hasSum_inner_gramian (hz : MemLp z 2 μ) {ι : Type*} (e : HilbertBasis ι 𝕜 E) :
    HasSum (fun i => ⟪e i, gramian 𝕜 μ z (e i)⟫_𝕜) ((∫ t, ‖z t‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
  rw [← trace_gramian hz]
  exact (isTraceClass_gramian hz).hasSum_trace e

/-- The real form of `hasSum_inner_gramian`: the diagonal entries `re ⟪eᵢ, 𝒢(z) eᵢ⟫` are
nonnegative and sum to `∫ ‖z‖²` in every Hilbert basis. -/
theorem hasSum_re_inner_gramian (hz : MemLp z 2 μ) {ι : Type*} (e : HilbertBasis ι 𝕜 E) :
    (∀ i, 0 ≤ RCLike.re ⟪e i, gramian 𝕜 μ z (e i)⟫_𝕜) ∧
      HasSum (fun i => RCLike.re ⟪e i, gramian 𝕜 μ z (e i)⟫_𝕜) (∫ t, ‖z t‖ ^ 2 ∂μ) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [← inner_conj_symm, RCLike.conj_re]
    exact (isPositive_gramian (𝕜 := 𝕜) (μ := μ) (z := z)).re_inner_nonneg_left (e i)
  · simpa using (hasSum_inner_gramian hz e).mapL RCLike.reCLM

end DataDrivenControl
