module

public import DataDrivenControl.Signal.Shift
public import DataDrivenControl.Signal.WeakDerivative

/-!
# Translation of `H¹` signals in `L²`

Helper file for the delay example (`ex:intro-delay`): the generator of the
delay semigroup acts on the history by differentiation.  Both inclusions of the domain
characterisation reduce to the two facts below about windows `window T z t = z (t + ·)` in
`L²(0, T; E)` (`Signal/Shift`):

* `window_sub_window_eq_integral`: for `z ∈ H¹(0, T₁)` with weak derivative `z'`
  (`HasWeakDeriv T₁ z z'`), the window difference is the `L²`-valued integral of the windows of
  `z'`: `z (t + ·) - z = ∫₀ᵗ z' (u + ·) du` in `L²(0, T; E)`; hence
  `tendsto_diffQuot_window`: the difference quotients `t⁻¹ (z (t + ·) - z)` converge to `z'` in
  `L²(0, T; E)` as `t → 0⁺`.
* `exists_ae_eq_of_tendsto_diffQuot_window`: conversely, if the difference quotients of the
  windows of `z ∈ L²(0, T + δ)` converge in `L²(0, T; E)` to some `G`, then `z` is a.e. on
  `(0, T]` an `H¹` function with derivative `G`: `z = c + ∫₀^· G`.

## Proof notes

* `window_sub_window_eq_integral`: test against `Φ ∈ L²(0, T; E)` (`ext_inner_left`).  The right
  side gives `∫₀ᵗ ∫₀ᵀ ⟪Φ σ, z'(u + σ)⟫ dσ du` (`ContinuousLinearMap.intervalIntegral_comp_comm`,
  `inner_window`); the left side gives `∫₀ᵀ ⟪Φ σ, z(t + σ) - z σ⟫ dσ` and
  `z(t + σ) - z σ = ∫₀ᵗ z'(u + σ) du` (`HasWeakDeriv.eq_add_integral`,
  `intervalIntegral.integral_comp_add_right`).  Swap with `integral_integral_swap`; to get joint
  measurability first replace `z'` by the strongly measurable
  `(Ioc 0 T₁).indicator (AEStronglyMeasurable.mk z')` (`HasWeakDeriv.congr`, `window_congr_ae`),
  and use `Lp.stronglyMeasurable Φ`.  Integrability on the product: `integrable_prod_iff` with
  the bound `‖Φ σ‖ ‖z'(u + σ)‖`.
* `tendsto_diffQuot_window`: on `[0, T₁ - T]`, `u ↦ window T z' u` agrees with the windows of
  the zero extension `(Ioc 0 T₁).indicator z'`, which are continuous on `ℝ`
  (`continuous_window`), so the averages `t⁻¹ ∫₀ᵗ` converge
  (`Continuous.integral_hasStrictDerivAt`, `HasDerivAt.tendsto_slope_zero_right`).
* `exists_ae_eq_of_tendsto_diffQuot_window`: for a test function `φ` (`IsTestFunction T φ`) the
  map `F ↦ ∫₀ᵀ φ • F` is a continuous linear map `L²(0, T; E) → E` (`LinearMap.mkContinuous`,
  `norm_integral_smul_le`).  On the windows it is `M t = ∫ φ(σ - t) • z̃ σ dσ` for `0 ≤ t < δ`,
  `z̃ = (Ioc 0 (T + δ)).indicator z` (translation invariance of `volume`), and `M` is
  differentiable with `M'(0) = -∫ φ' • z` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
  Uniqueness of limits along `𝓝[>] 0` gives `∫ φ' • z = -∫ φ • G`; conclude with
  `exists_ae_eq_of_integral_deriv_smul` (du Bois-Reymond, `Signal/WeakDerivative`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace Delay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `window_sub_window_eq_integral` for a strongly measurable weak derivative that is integrable
on `ℝ` (testing against `Φ ∈ L²(0, T; E)` and Fubini). -/
private theorem window_sub_window_eq_integral_aux {T T₁ t : ℝ} {z g : ℝ → E}
    (hz : HasWeakDeriv T₁ z g) (hgm : StronglyMeasurable g) (hgi : Integrable g)
    (ht : 0 ≤ t) (htT : T + t ≤ T₁) :
    window T z t - window T z 0 = ∫ u in (0 : ℝ)..t, window T g u := by
  have hgL : MemLp g 2 (μI (T + t)) := memLp_μI_of_le hz.memLp_deriv htT
  have hint : IntervalIntegrable (window T g) volume 0 t :=
    (continuousOn_window hgL).intervalIntegrable_of_Icc ht
  have hzL := hz.memLp
  refine ext_inner_left ℝ fun Φ => ?_
  have hR : ⟪Φ, ∫ u in (0 : ℝ)..t, window T g u⟫_ℝ =
      ∫ u in Ioc 0 t, ∫ σ in Ioc 0 T, ⟪Φ σ, g (u + σ)⟫_ℝ := by
    have h := (innerSL ℝ Φ).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [← h, intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    exact inner_window hz.memLp_deriv hu.1.le (by linarith [hu.2]) Φ
  have hi : ∀ s, 0 ≤ s → s + T ≤ T₁ → Integrable (fun σ => ⟪Φ σ, z (s + σ)⟫_ℝ) (μI T) :=
    fun s hs hsT => (L2.integrable_inner Φ (window T z s)).congr (by
      filter_upwards [coeFn_window_of_memLp hzL hs hsT] with σ hσ
      rw [hσ])
  have hL : ⟪Φ, window T z t - window T z 0⟫_ℝ =
      ∫ σ in Ioc 0 T, (⟪Φ σ, z (t + σ)⟫_ℝ - ⟪Φ σ, z (0 + σ)⟫_ℝ) := by
    rw [inner_sub_right, inner_window hzL ht (by linarith) Φ,
      inner_window hzL le_rfl (by linarith) Φ,
      integral_sub (hi t ht (by linarith)) (hi 0 le_rfl (by linarith))]
  have hpt : ∀ σ ∈ Ioc 0 T, ⟪Φ σ, z (t + σ)⟫_ℝ - ⟪Φ σ, z (0 + σ)⟫_ℝ =
      ∫ u in Ioc 0 t, ⟪Φ σ, g (u + σ)⟫_ℝ := by
    intro σ hσ
    have hgi' : Integrable (fun u => g (u + σ)) (volume.restrict (Ioc 0 t)) :=
      (hgi.comp_add_right σ).restrict
    have e1 : z (t + σ) = z 0 + ∫ x in (0 : ℝ)..t + σ, g x :=
      hz.eq_add_integral (t + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have e2 : z σ = z 0 + ∫ x in (0 : ℝ)..σ, g x :=
      hz.eq_add_integral σ ⟨hσ.1.le, by linarith [hσ.2]⟩
    rw [← inner_sub_right, integral_inner hgi' (Φ σ), ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_add_right, zero_add, e1, e2, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left
        (hz.intervalIntegrable_deriv ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
        (hz.intervalIntegrable_deriv ⟨hσ.1.le, by linarith [hσ.2]⟩)]
  rw [hL, setIntegral_congr_fun measurableSet_Ioc hpt, hR]
  refine integral_integral_swap ?_
  have hmeas : StronglyMeasurable (Function.uncurry fun σ u => ⟪(Φ : ℝ → E) σ, g (u + σ)⟫_ℝ) :=
    ((Lp.stronglyMeasurable Φ).comp_measurable measurable_fst).inner
      (hgm.comp_measurable (measurable_snd.add measurable_fst))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun σ => ((hgi.comp_add_right σ).restrict).const_inner (Φ σ), ?_⟩
  refine Integrable.mono' (((Lp.memLp Φ).integrable one_le_two).norm.mul_const (∫ x, ‖g x‖))
    (hmeas.aestronglyMeasurable.norm.integral_prod_right') (ae_of_all _ fun σ => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc ∫ u in Ioc 0 t, ‖⟪(Φ : ℝ → E) σ, g (u + σ)⟫_ℝ‖
      ≤ ∫ u in Ioc 0 t, ‖Φ σ‖ * ‖g (u + σ)‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          (((hgi.comp_add_right σ).norm.const_mul _).restrict)
          (ae_of_all _ fun u => norm_inner_le_norm _ _)
    _ = ‖Φ σ‖ * ∫ u in Ioc 0 t, ‖g (u + σ)‖ := integral_const_mul _ _
    _ ≤ ‖Φ σ‖ * ∫ u, ‖g (u + σ)‖ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral (hgi.comp_add_right σ).norm
          (ae_of_all _ fun _ => norm_nonneg _)) (norm_nonneg _)
    _ = ‖Φ σ‖ * ∫ x, ‖g x‖ := by rw [integral_add_right_eq_self (fun x => ‖g x‖) σ]

set_option linter.unusedVariables false in
/-- **Windows of an `H¹` signal**: for `z ∈ H¹(0, T₁; E)` with weak derivative `z'`,
`z (t + ·) - z = ∫₀ᵗ z' (u + ·) du` in `L²(0, T; E)` whenever `T + t ≤ T₁` (an identity between
an `L²`-valued Bochner integral and pointwise integrals; used for the generator of the delay
semigroup, `ex:intro-delay`). -/
theorem window_sub_window_eq_integral {T T₁ t : ℝ} {z z' : ℝ → E} (hz : HasWeakDeriv T₁ z z')
    (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : T + t ≤ T₁) :
    window T z t - window T z 0 = ∫ u in (0 : ℝ)..t, window T z' u := by
  have hm := hz.memLp_deriv.aestronglyMeasurable
  set g : ℝ → E := (Ioc 0 T₁).indicator (hm.mk z') with hg_def
  have hgz : z' =ᵐ[μI T₁] g :=
    hm.ae_eq_mk.trans (indicator_ae_eq_restrict measurableSet_Ioc.nullMeasurableSet).symm
  have hgm : StronglyMeasurable g := hm.stronglyMeasurable_mk.indicator measurableSet_Ioc
  have hgi : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioc).2 (hz.integrable_deriv.congr hm.ae_eq_mk)
  have hzg : HasWeakDeriv T₁ z g := hz.congr (fun _ _ => rfl) hgz
  rw [window_sub_window_eq_integral_aux hzg hgm hgi ht htT]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht] at hu
  exact (window_congr_ae hgz hu.1 (by linarith [hu.2])).symm

/-- **Difference quotients of an `H¹` signal converge in `L²`**: for `z ∈ H¹(0, T₁; E)` with
weak derivative `z'` and `T < T₁`, `t⁻¹ (z (t + ·) - z) → z'` in `L²(0, T; E)` as `t → 0⁺`. -/
theorem tendsto_diffQuot_window {T T₁ : ℝ} {z z' : ℝ → E} (hz : HasWeakDeriv T₁ z z')
    (hT : 0 ≤ T) (hTT : T < T₁) :
    Tendsto (fun t : ℝ => t⁻¹ • (window T z t - window T z 0)) (𝓝[>] 0)
      (𝓝 (window T z' 0)) := by
  set g : ℝ → E := (Ioc 0 T₁).indicator z' with hg_def
  have hgc : Continuous (window T g) :=
    continuous_window (memLp_indicator_Ioc hz.memLp_deriv) T
  have hW : ∀ u ∈ Icc 0 (T₁ - T), window T g u = window T z' u := by
    intro u hu
    refine window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => ?_)
    exact indicator_of_mem (show u + σ ∈ Ioc 0 T₁ from
      ⟨by linarith [hu.1, hσ.1], by linarith [hu.2, hσ.2]⟩) _
  have hd := (hgc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  rw [hW 0 ⟨le_rfl, by linarith⟩] at hd
  refine hd.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < T₁ - T by linarith)] with t ht
  simp only [zero_add, intervalIntegral.integral_same, sub_zero]
  rw [window_sub_window_eq_integral hz hT ht.1.le (by linarith [ht.2])]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht.1.le] at hu
  exact hW u ⟨hu.1, hu.2.trans ht.2.le⟩


/-- Testing an `L²(0, T; E)` signal against a scalar `L²` function `φ`: the bounded operator
`F ↦ ∫₀ᵀ φ • F` (Cauchy–Schwarz, `norm_integral_smul_le`). -/
private def testL (T : ℝ) (φ : L2 ℝ T) : L2 E T →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ s in Ioc 0 T, φ s • F s
      map_add' := fun F₁ F₂ => by
        rw [← integral_add (integrable_smul_of_memLp (Lp.memLp F₁) φ)
          (integrable_smul_of_memLp (Lp.memLp F₂) φ)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add F₁ F₂] with s hs
        rw [hs, Pi.add_apply, smul_add]
      map_smul' := fun c F => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c F] with s hs
        rw [hs, Pi.smul_apply, smul_comm] }
    ‖φ‖ fun F => by
      have h := norm_integral_smul_le (Lp.memLp F) φ
      rw [← Lp.norm_def] at h
      simpa [mul_comm] using h

omit [CompleteSpace E] in
private theorem testL_apply (T : ℝ) (φ : L2 ℝ T) (F : L2 E T) :
    testL T φ F = ∫ s in Ioc 0 T, φ s • F s := rfl

omit [CompleteSpace E] in
/-- The derivative of `t ↦ ∫ φ(σ - t) • w σ` (differentiation under the integral sign). -/
private theorem hasDerivAt_integral_comp_sub_smul {φ : ℝ → ℝ} {T : ℝ} (hφ : IsTestFunction T φ)
    {w : ℝ → E} (hw : Integrable w) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ σ, φ (σ - t) • w σ) (-∫ σ, deriv φ (σ - t₀) • w σ) t₀ := by
  obtain ⟨C, hC⟩ := hφ.deriv.continuous.bounded_above_of_compact_support hφ.deriv.hasCompactSupport
  have hd : ∀ σ t, HasDerivAt (fun t => φ (σ - t) • w σ) (-deriv φ (σ - t) • w σ) t := by
    intro σ t
    have h1 : HasDerivAt (fun t => σ - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub σ
    have h2 := ((hφ.differentiable (σ - t)).hasDerivAt.comp t h1).smul_const (w σ)
    simpa [mul_neg, mul_one] using h2
  obtain ⟨C', hC'⟩ := hφ.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  have hc : ∀ t : ℝ, Continuous fun σ : ℝ => σ - t := fun t => continuous_id.sub continuous_const
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t σ => φ (σ - t) • w σ) (F' := fun t σ => -deriv φ (σ - t) • w σ) (x₀ := t₀)
    (bound := fun σ => C * ‖w σ‖) (s := univ) univ_mem
    (Eventually.of_forall fun t =>
      (hφ.continuous.comp (hc t)).aestronglyMeasurable.smul hw.aestronglyMeasurable)
    (hw.bdd_smul C' (hφ.continuous.comp (hc t₀)).aestronglyMeasurable
      (ae_of_all _ fun σ => hC' _))
    ((hφ.deriv.continuous.comp (hc t₀)).neg.aestronglyMeasurable.smul hw.aestronglyMeasurable)
    (ae_of_all _ fun σ t _ => ?_) (hw.norm.const_mul C) (ae_of_all _ fun σ t _ => hd σ t)
  · simpa only [neg_smul, integral_neg] using key.2
  · rw [norm_smul, norm_neg]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

set_option linter.unusedVariables false in
/-- **Weak derivative from `L²` difference quotients**: if `z ∈ L²(0, T + δ; E)` and the
difference quotients `t⁻¹ (z (t + ·) - z)` converge in `L²(0, T; E)` to `G` as `t → 0⁺`, then
`z = c + ∫₀^· G` a.e. on `(0, T]` (so `z` has an `H¹` representative with derivative `G`; the
hard inclusion of the generator domain of the delay semigroup, `ex:intro-delay`). -/
theorem exists_ae_eq_of_tendsto_diffQuot_window {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    {z : ℝ → E} (hz : MemLp z 2 (μI (T + δ))) {G : L2 E T}
    (hG : Tendsto (fun t : ℝ => t⁻¹ • (window T z t - window T z 0)) (𝓝[>] 0) (𝓝 G)) :
    ∃ c : E, ∀ᵐ σ ∂(μI T), z σ = c + ∫ s in (0 : ℝ)..σ, G s := by
  have hzT : MemLp z 2 (μI T) := memLp_μI_of_le hz (by linarith)
  refine exists_ae_eq_of_integral_deriv_smul (hzT.integrable one_le_two)
    ((Lp.memLp G).integrable one_le_two) fun φ hφ => ?_
  set w : ℝ → E := (Ioc 0 (T + δ)).indicator z with hw_def
  have hw : Integrable w :=
    (integrable_indicator_iff measurableSet_Ioc).2 (hz.integrable one_le_two)
  have hφL : MemLp φ 2 (μI T) := hφ.continuous.memLp_of_hasCompactSupport hφ.hasCompactSupport
  set φL : L2 ℝ T := hφL.toLp φ
  set M : ℝ → E := fun t => ∫ σ, φ (σ - t) • w σ with hM_def
  have hM : ∀ t ∈ Icc 0 δ, testL T φL (window T z t) = M t := by
    intro t ht
    rw [testL_apply]
    calc ∫ s in Ioc 0 T, φL s • (window T z t) s = ∫ s in Ioc 0 T, φ s • z (t + s) := by
          refine integral_congr_ae ?_
          filter_upwards [hφL.coeFn_toLp, coeFn_window_of_memLp hz ht.1 (by linarith [ht.2])]
            with s h1 h2
          rw [h1, h2]
      _ = ∫ s, φ s • z (t + s) := (hφ.integral_smul_eq_setIntegral (fun s => z (t + s))).symm
      _ = ∫ σ, φ ((σ + t) - t) • w (σ + t) := by
          refine integral_congr_ae (ae_of_all _ fun σ => ?_)
          simp only [add_sub_cancel_right]
          by_cases hσ : σ ∈ Ioo 0 T
          · rw [hw_def, indicator_of_mem (show σ + t ∈ Ioc 0 (T + δ) from
              ⟨by linarith [hσ.1, ht.1], by linarith [hσ.2, ht.2]⟩), add_comm]
          · rw [hφ.apply_eq_zero hσ, zero_smul, zero_smul]
      _ = M t := integral_add_right_eq_self (fun σ => φ (σ - t) • w σ) t
  have hderiv := (hasDerivAt_integral_comp_sub_smul hφ hw 0).tendsto_slope_zero_right
  have hlim := ((testL T φL).continuous.tendsto G).comp hG
  have hev : (fun t : ℝ => t⁻¹ • (M (0 + t) - M 0)) =ᶠ[𝓝[>] 0]
      (testL T φL) ∘ (fun t : ℝ => t⁻¹ • (window T z t - window T z 0)) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
    simp only [Function.comp_apply, map_smul, map_sub, zero_add]
    rw [hM t ⟨ht.1.le, ht.2.le⟩, hM 0 ⟨le_rfl, hδ.le⟩]
  have heq := tendsto_nhds_unique (hderiv.congr' hev) hlim
  rw [testL_apply] at heq
  have e1 : ∫ σ, deriv φ (σ - 0) • w σ = ∫ t, deriv φ t • z t := by
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [sub_zero]
    by_cases hσ : σ ∈ Ioo 0 T
    · rw [hw_def, indicator_of_mem (show σ ∈ Ioc 0 (T + δ) from ⟨hσ.1, by linarith [hσ.2]⟩)]
    · rw [hφ.deriv.apply_eq_zero hσ, zero_smul, zero_smul]
  have e2 : ∫ s in Ioc 0 T, φL s • G s = ∫ t, φ t • G t := by
    rw [hφ.integral_smul_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hφL.coeFn_toLp] with s hs
    rw [hs]
  rw [e1, e2] at heq
  rw [← heq, neg_neg]


end Delay

end DataDrivenControl
