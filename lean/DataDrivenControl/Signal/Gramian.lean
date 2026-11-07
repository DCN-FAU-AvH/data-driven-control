module

public import DataDrivenControl.Signal.Span

/-!
# The Gramian of a signal

Paper: `eq:hilbert-gramian`, `eq:gramian-kernel`, `rmk:gramian-not-coercive`,
`app:informative-gramian`.

* `gramian 𝕜 μ z = ∫ z t ⊗ z t ∂μ`, a Bochner integral in `E →L[𝕜] E` of the rank-one operators
  `z t ⊗ z t = (ζ ↦ ⟪z t, ζ⟫ • z t)` (`InnerProductSpace.rankOne 𝕜 (z t) (z t)`); it is
  integrable for `MemLp z 2 μ` (`integrable_rankOne_self`);
* `gramian_apply`, `inner_gramian_apply_self`, `re_inner_gramian_apply_self`:
  `⟪𝒢 ζ, ζ⟫ = ∫ |⟪z t, ζ⟫|²`;
* `isPositive_gramian`, `isSelfAdjoint_gramian`, `gramian_nonneg`: self-adjoint and nonnegative;
* `ker_gramian` (`ker 𝒢 = annihilator z`), `ker_gramian_eq_orthogonal_cspan`
  (`eq:gramian-kernel`, `ker 𝒢 = (cspan z)ᗮ`), `orthogonal_ker_gramian` (`(ker 𝒢)ᗮ = cspan z`),
  `topologicalClosure_range_gramian` (`closure (range 𝒢) = cspan z`);
* `gramian_injective_iff`, `gramian_injective_iff_cspan_eq_top` (the core of
  `lem:informative-gramian`);
* `gramian_injective_iff_coercive`: in finite dimensions injectivity is equivalent to
  coercivity (`rmk:gramian-not-coercive`).

The trace-class assertion of `eq:hilbert-gramian` is proved in `Signal/GramianTrace`.

The Bochner integral needs a real structure on `E`; it is the hypothesis `[NormedSpace ℝ E]`,
automatic for `𝕜 = ℝ` and `𝕜 = ℂ` (Mathlib's pattern, `Real.isScalarTower` makes it compatible).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

namespace DataDrivenControl

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E]
  {α : Type*} {mα : MeasurableSpace α}

variable (𝕜) in
/-- The **Gramian** of a signal (`eq:hilbert-gramian`): `𝒢(z) = ∫ z t ⊗ z t ∂μ`, where
`a ⊗ b = (ζ ↦ ⟪b, ζ⟫ • a)`.  It is the Bochner integral in `E →L[𝕜] E`, hence `0` if the
integrand is not integrable; it is integrable for `MemLp z 2 μ`. -/
def gramian (μ : Measure α) (z : α → E) : E →L[𝕜] E :=
  ∫ t, InnerProductSpace.rankOne 𝕜 (z t) (z t) ∂μ

variable {μ : Measure α} {z w : α → E}

omit [NormedSpace ℝ E] in
/-- The integrand of the Gramian is integrable for square-integrable signals. -/
theorem integrable_rankOne_self (hz : MemLp z 2 μ) :
    Integrable (fun t => InnerProductSpace.rankOne 𝕜 (z t) (z t)) μ := by
  have hc : Continuous fun v : E => InnerProductSpace.rankOne 𝕜 v v := by
    have h1 : Continuous fun v : E => ContinuousLinearMap.smulRightL 𝕜 E E (innerSL 𝕜 v) :=
      (ContinuousLinearMap.smulRightL 𝕜 E E).continuous.comp
        (innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜).continuous
    convert h1.clm_apply continuous_id using 1
    ext v w
    simp [InnerProductSpace.rankOne_apply]
  have h2 : Integrable (fun t => ‖z t‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hz.aestronglyMeasurable).1 hz
  refine h2.mono' (hc.comp_aestronglyMeasurable hz.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  simp [sq]

theorem gramian_congr (h : z =ᵐ[μ] w) : gramian 𝕜 μ z = gramian 𝕜 μ w := by
  rw [gramian, gramian]
  exact integral_congr_ae (h.mono fun t ht => by simp only [ht])

variable [CompleteSpace E]

private theorem inner_integral_left {f : α → E} (hf : Integrable f μ) (ξ : E) :
    ⟪∫ t, f t ∂μ, ξ⟫_𝕜 = ∫ t, ⟪f t, ξ⟫_𝕜 ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
  simp_rw [inner_conj_symm]

omit [CompleteSpace E] in
private theorem gramian_apply_of_integrable
    (hz : Integrable (fun t => InnerProductSpace.rankOne 𝕜 (z t) (z t)) μ) (ζ : E) :
    gramian 𝕜 μ z ζ = ∫ t, ⟪z t, ζ⟫_𝕜 • z t ∂μ := by
  rw [gramian, ContinuousLinearMap.integral_apply hz]
  simp only [InnerProductSpace.rankOne_apply]

private theorem inner_gramian_apply_of_integrable
    (hz : Integrable (fun t => InnerProductSpace.rankOne 𝕜 (z t) (z t)) μ) (ζ ξ : E) :
    ⟪gramian 𝕜 μ z ζ, ξ⟫_𝕜 = ∫ t, ⟪ζ, z t⟫_𝕜 * ⟪z t, ξ⟫_𝕜 ∂μ := by
  have hi : Integrable (fun t => ⟪z t, ζ⟫_𝕜 • z t) μ := by
    simpa only [InnerProductSpace.rankOne_apply] using hz.apply_continuousLinearMap ζ
  rw [gramian_apply_of_integrable hz, inner_integral_left hi]
  congr 1 with t
  rw [inner_smul_left, inner_conj_symm]

private theorem inner_gramian_apply_self_of_integrable
    (hz : Integrable (fun t => InnerProductSpace.rankOne 𝕜 (z t) (z t)) μ) (ζ : E) :
    ⟪gramian 𝕜 μ z ζ, ζ⟫_𝕜 = ((∫ t, ‖⟪z t, ζ⟫_𝕜‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
  rw [inner_gramian_apply_of_integrable hz, ← integral_ofReal]
  congr 1 with t
  rw [← inner_conj_symm ζ (z t), RCLike.conj_mul, RCLike.ofReal_pow]

omit [CompleteSpace E] in
/-- `𝒢(z) ζ = ∫ ⟪z t, ζ⟫ • z t`. -/
theorem gramian_apply (hz : MemLp z 2 μ) (ζ : E) :
    gramian 𝕜 μ z ζ = ∫ t, ⟪z t, ζ⟫_𝕜 • z t ∂μ :=
  gramian_apply_of_integrable (integrable_rankOne_self hz) ζ

/-- `⟪𝒢(z) ζ, ξ⟫ = ∫ ⟪ζ, z t⟫ ⟪z t, ξ⟫`. -/
theorem inner_gramian_apply (hz : MemLp z 2 μ) (ζ ξ : E) :
    ⟪gramian 𝕜 μ z ζ, ξ⟫_𝕜 = ∫ t, ⟪ζ, z t⟫_𝕜 * ⟪z t, ξ⟫_𝕜 ∂μ :=
  inner_gramian_apply_of_integrable (integrable_rankOne_self hz) ζ ξ

/-- `⟪𝒢(z) ζ, ζ⟫ = ∫ |⟪z t, ζ⟫|²` (`app:informative-gramian`). -/
theorem inner_gramian_apply_self (hz : MemLp z 2 μ) (ζ : E) :
    ⟪gramian 𝕜 μ z ζ, ζ⟫_𝕜 = ((∫ t, ‖⟪z t, ζ⟫_𝕜‖ ^ 2 ∂μ : ℝ) : 𝕜) :=
  inner_gramian_apply_self_of_integrable (integrable_rankOne_self hz) ζ

/-- `re ⟪𝒢(z) ζ, ζ⟫ = ∫ |⟪z t, ζ⟫|²`. -/
theorem re_inner_gramian_apply_self (hz : MemLp z 2 μ) (ζ : E) :
    RCLike.re ⟪gramian 𝕜 μ z ζ, ζ⟫_𝕜 = ∫ t, ‖⟪z t, ζ⟫_𝕜‖ ^ 2 ∂μ := by
  rw [inner_gramian_apply_self hz, RCLike.ofReal_re]

/-- The Gramian is a positive operator (symmetric and `0 ≤ re ⟪𝒢 ζ, ζ⟫`). -/
theorem isPositive_gramian : (gramian 𝕜 μ z).IsPositive := by
  by_cases hz : Integrable (fun t => InnerProductSpace.rankOne 𝕜 (z t) (z t)) μ
  · refine ⟨fun ζ ξ => ?_, fun ζ => ?_⟩
    · change ⟪gramian 𝕜 μ z ζ, ξ⟫_𝕜 = ⟪ζ, gramian 𝕜 μ z ξ⟫_𝕜
      rw [← inner_conj_symm ζ (gramian 𝕜 μ z ξ), inner_gramian_apply_of_integrable hz,
        inner_gramian_apply_of_integrable hz, ← integral_conj]
      congr 1 with t
      simp only [map_mul, inner_conj_symm]
      ring
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_gramian_apply_self_of_integrable hz,
        RCLike.ofReal_re]
      exact integral_nonneg fun t => sq_nonneg _
  · rw [gramian, integral_undef hz]
    exact ContinuousLinearMap.isPositive_zero

/-- The Gramian is self-adjoint. -/
theorem isSelfAdjoint_gramian : IsSelfAdjoint (gramian 𝕜 μ z) :=
  isPositive_gramian.isSelfAdjoint

/-- The Gramian is nonnegative in the Loewner order. -/
theorem gramian_nonneg : 0 ≤ gramian 𝕜 μ z :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr isPositive_gramian

/-- `re ⟪𝒢(z) ζ, ζ⟫ = 0` iff `ζ` annihilates `z`. -/
theorem re_inner_gramian_apply_self_eq_zero_iff (hz : MemLp z 2 μ) {ζ : E} :
    RCLike.re ⟪gramian 𝕜 μ z ζ, ζ⟫_𝕜 = 0 ↔ ζ ∈ annihilator 𝕜 μ z := by
  have hm : MemLp (fun t => ⟪z t, ζ⟫_𝕜) 2 μ := hz.inner_const ζ
  have hint : Integrable (fun t => ‖⟪z t, ζ⟫_𝕜‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  rw [re_inner_gramian_apply_self hz, integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hint,
    mem_annihilator']
  constructor <;> intro h <;> filter_upwards [h] with t ht
  · simpa using ht
  · simp [ht]

/-- The kernel of the Gramian is the annihilator of the signal. -/
theorem ker_gramian (hz : MemLp z 2 μ) : (gramian 𝕜 μ z).ker = annihilator 𝕜 μ z := by
  ext ζ
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    rw [← re_inner_gramian_apply_self_eq_zero_iff hz, h, inner_zero_left, map_zero]
  · intro h
    rw [mem_annihilator'] at h
    have h0 : (fun t => ⟪z t, ζ⟫_𝕜 • z t) =ᵐ[μ] fun _ => (0 : E) :=
      h.mono fun t ht => by simp [ht]
    rw [gramian_apply hz, integral_congr_ae h0, integral_zero]

/-- `eq:gramian-kernel`: `ker 𝒢(z) = (cspan z)ᗮ`. -/
theorem ker_gramian_eq_orthogonal_cspan (hz : MemLp z 2 μ) :
    (gramian 𝕜 μ z).ker = (cspan 𝕜 μ z)ᗮ := by
  rw [ker_gramian hz, orthogonal_cspan]

/-- `(ker 𝒢(z))ᗮ = cspan z` (the form used in `thm:willems-gramian`). -/
theorem orthogonal_ker_gramian (hz : MemLp z 2 μ) : (gramian 𝕜 μ z).kerᗮ = cspan 𝕜 μ z := by
  rw [ker_gramian hz, cspan_def]

/-- The closure of the range of the Gramian is the closed span of the signal. -/
theorem topologicalClosure_range_gramian (hz : MemLp z 2 μ) :
    (gramian 𝕜 μ z).range.topologicalClosure = cspan 𝕜 μ z := by
  rw [← orthogonal_ker_gramian hz, ContinuousLinearMap.orthogonal_ker,
    isSelfAdjoint_gramian.adjoint_eq]

/-- The Gramian is injective iff only `0` annihilates the signal. -/
theorem gramian_injective_iff (hz : MemLp z 2 μ) :
    Function.Injective (gramian 𝕜 μ z) ↔ annihilator 𝕜 μ z = ⊥ := by
  rw [← ker_gramian hz, LinearMap.ker_eq_bot, ContinuousLinearMap.coe_coe]

/-- The Gramian is injective iff the signal spans a dense subspace (`lem:informative-gramian`,
applied on a product space in `Informativity/Informative`). -/
theorem gramian_injective_iff_cspan_eq_top (hz : MemLp z 2 μ) :
    Function.Injective (gramian 𝕜 μ z) ↔ cspan 𝕜 μ z = ⊤ := by
  rw [gramian_injective_iff hz, cspan_eq_top_iff]

/-- `rmk:gramian-not-coercive`: in finite dimensions the Gramian is injective iff it is
coercive, `𝒢(z) ≥ c` for some `c > 0`. -/
theorem gramian_injective_iff_coercive [FiniteDimensional 𝕜 E] (hz : MemLp z 2 μ) :
    Function.Injective (gramian 𝕜 μ z) ↔
      ∃ c > 0, ∀ ζ : E, c * ‖ζ‖ ^ 2 ≤ RCLike.re ⟪gramian 𝕜 μ z ζ, ζ⟫_𝕜 := by
  set G := gramian 𝕜 μ z with hG
  have key : ∀ ζ, RCLike.re ⟪G ζ, ζ⟫_𝕜 = G.reApplyInnerSelf ζ := fun ζ =>
    (G.reApplyInnerSelf_apply ζ).symm
  simp only [key]
  constructor
  · intro hinj
    rcases subsingleton_or_nontrivial E with hE | hE
    · refine ⟨1, one_pos, fun ζ => ?_⟩
      rw [Subsingleton.elim ζ 0]
      simp [ContinuousLinearMap.reApplyInnerSelf_apply]
    have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
    obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) G.reApplyInnerSelf_continuous.continuousOn
    have hζ₀1 : ‖ζ₀‖ = 1 := by simpa using hζ₀
    have hζ₀0 : ζ₀ ≠ 0 := by
      rintro rfl
      simp at hζ₀1
    have hpos : 0 < G.reApplyInnerSelf ζ₀ := by
      refine lt_of_le_of_ne (isPositive_gramian.2 ζ₀) (Ne.symm fun h0 => hζ₀0 ?_)
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, hG, re_inner_gramian_apply_self_eq_zero_iff hz,
        ← ker_gramian hz, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at h0
      exact hinj (h0.trans (map_zero _).symm)
    refine ⟨_, hpos, fun ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [ContinuousLinearMap.reApplyInnerSelf_apply]
    have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
    have hu : ((‖ζ‖⁻¹ : ℝ) : 𝕜) • ζ ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm,
        inv_mul_cancel₀ hn.ne']
    have h1 := isMinOn_iff.1 hmin _ hu
    rw [ContinuousLinearMap.reApplyInnerSelf_smul, RCLike.norm_ofReal, abs_inv, abs_norm] at h1
    calc G.reApplyInnerSelf ζ₀ * ‖ζ‖ ^ 2 ≤ ‖ζ‖⁻¹ ^ 2 * G.reApplyInnerSelf ζ * ‖ζ‖ ^ 2 := by
          gcongr
      _ = G.reApplyInnerSelf ζ := by field_simp
  · rintro ⟨c, hc, h⟩
    refine (injective_iff_map_eq_zero G).2 fun ζ hζ => ?_
    have h2 := h ζ
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hζ, inner_zero_left, map_zero] at h2
    by_contra hne
    have : 0 < c * ‖ζ‖ ^ 2 := by have := norm_pos_iff.2 hne; positivity
    linarith

end DataDrivenControl
