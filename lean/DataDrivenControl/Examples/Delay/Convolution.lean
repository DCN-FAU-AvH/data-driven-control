module

public import DataDrivenControl.Examples.Delay.Trajectory

/-!
# Delay measures along trajectories

The delay functionals of `ex:intro-delay` are bounded maps on continuous histories, i.e. finite
(matrix) measures on the delay interval.  Along a trajectory `z` in shifted time
(`Delay/Trajectory`, `x(t - δ) = z(H - δ + t)`) a finite measure `ν` on `[0, H]` acts at time `s` by

`mconv ν H z s = ∫ z(H - δ + s) dν(δ)`,  the paper's `∫ x(s - δ) dν(δ)`.

## Main results

For a finite measure `ν` with `ν (Icc 0 H)ᶜ = 0`:

* `ae_ae_comp`: an a.e. statement on `(0, H + τ]` holds, for a.e. `s ∈ (0, τ]`, at `H - δ + s`
  for `ν`-a.e. `δ` (Tonelli).  Hence `mconv_congr_ae` (`mconv` only sees classes) and
  `ae_integrable_comp` (along an `L²` trajectory the integral exists for a.e. `s`).
* `eLpNorm_mconv_le`: `‖mconv ν H z‖_{L²(0, τ)} ≤ ν(ℝ) ‖z‖_{L²(0, H + τ)}` (Cauchy–Schwarz in `δ`,
  `enorm_integral_rpow_le`, and Tonelli); `memLp_mconv`.
* `continuousOn_mconv` (dominated convergence) and `hasWeakDeriv_mconv` (Fubini): `mconv` commutes
  with the weak derivative of an `H¹` trajectory.
* `mconv_dirac`: a point delay is a Dirac measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Auxiliary `L²` facts -/

/-- Translating into a longer window does not increase the `Lᵖ` seminorm. -/
theorem eLpNorm_comp_add_le {q : ℝ≥0∞} {T₁ T s : ℝ} {f : ℝ → E}
    (hf : AEStronglyMeasurable f (μI T₁)) (hs : 0 ≤ s) (hsT : s + T ≤ T₁) :
    eLpNorm (fun t => f (s + t)) q (μI T) ≤ eLpNorm f q (μI T₁) := by
  have hmono : volume.restrict (Ioc s (s + T)) ≤ μI T₁ :=
    Measure.restrict_mono (Ioc_subset_Ioc hs hsT) le_rfl
  calc eLpNorm (fun t => f (s + t)) q (μI T)
      = eLpNorm f q (volume.restrict (Ioc s (s + T))) :=
        eLpNorm_comp_measurePreserving (hf.mono_measure hmono) (measurePreserving_add_μI s T)
    _ ≤ eLpNorm f q (μI T₁) := eLpNorm_mono_measure _ hmono

/-- `‖f‖²_{L²} = ∫ ‖f‖²`. -/
theorem eLpNorm_two_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ← ENNReal.rpow_mul]
  norm_num

/-- **Cauchy–Schwarz** for a finite measure: `‖∫ g dν‖² ≤ ν(univ) ∫ ‖g‖² dν`. -/
theorem enorm_integral_rpow_le {α : Type*} [MeasurableSpace α] (ν : Measure α) {g : α → E}
    (hg : AEStronglyMeasurable g ν) :
    ‖∫ a, g a ∂ν‖ₑ ^ (2 : ℝ) ≤ ν univ * ∫⁻ a, ‖g a‖ₑ ^ (2 : ℝ) ∂ν := by
  have h1 : ‖∫ a, g a ∂ν‖ₑ ≤ eLpNorm g 2 ν * ν univ ^ (1 / (2 : ℝ)) := by
    refine (enorm_integral_le_lintegral_enorm g).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm hg]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two hg
    rwa [show (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num] at this
  calc ‖∫ a, g a ∂ν‖ₑ ^ (2 : ℝ) ≤ (eLpNorm g 2 ν * ν univ ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ν univ * ∫⁻ a, ‖g a‖ₑ ^ (2 : ℝ) ∂ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), eLpNorm_two_rpow hg,
          ← ENNReal.rpow_mul]
        norm_num
        ring

/-! ### Measures on the delay interval -/

variable {ν : Measure ℝ} {H : ℝ}

/-- `ν`-almost every delay lies in `[0, H]`. -/
theorem ae_mem_Icc_of_compl (hν : ν (Icc 0 H)ᶜ = 0) : ∀ᵐ δ ∂ν, δ ∈ Icc 0 H :=
  mem_ae_iff.2 hν

/-- A function continuous on `[0, H]` is integrable for a finite measure on `[0, H]`. -/
theorem integrable_of_continuousOn [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0)
    {f : ℝ → E} (hf : ContinuousOn f (Icc 0 H)) : Integrable f ν := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have : Integrable f (ν.restrict (Icc 0 H)) :=
    Integrable.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
      (ae_restrict_of_forall_mem measurableSet_Icc hC)
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_Icc_of_compl hν)] at this

/-- **Translating an a.e. statement into the delays** (Tonelli): if `p` holds a.e. on
`(0, H + τ]`, then for a.e. `s ∈ (0, τ]`, `p (H - δ + s)` holds for `ν`-a.e. `δ`. -/
theorem ae_ae_comp [SFinite ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {p : ℝ → Prop}
    (hp : ∀ᵐ σ ∂(μI (H + τ)), p σ) : ∀ᵐ s ∂(μI τ), ∀ᵐ δ ∂ν, p (H - δ + s) := by
  rw [ae_restrict_iff' measurableSet_Ioc] at hp
  obtain ⟨S, hsub, hSm, hS0⟩ := exists_measurable_superset_of_null (ae_iff.1 hp)
  have h1 : ∀ᵐ δ ∂ν, ∀ᵐ s ∂volume, H - δ + s ∉ S := ae_of_all _ fun δ =>
    measure_eq_zero_iff_ae_notMem (s := (fun s => H - δ + s) ⁻¹' S).1
      (by rw [measure_preimage_add]; exact hS0)
  have h2 : ∀ᵐ s ∂volume, ∀ᵐ δ ∂ν, H - δ + s ∉ S :=
    (Measure.ae_ae_comm (p := fun s δ => H - δ + s ∉ S)
      (hSm.preimage (by fun_prop : Measurable fun x : ℝ × ℝ => H - x.2 + x.1)).compl).2 h1
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h2] with s hs hsI
  filter_upwards [hs, ae_mem_Icc_of_compl hν] with δ hδS hδ
  by_contra hn
  exact hδS (hsub fun hp' => hn (hp' ⟨by linarith [hδ.2, hsI.1], by linarith [hδ.1, hsI.2]⟩))

/-! ### The measure delay along a trajectory -/

/-- **A measure delay along a trajectory** in shifted time: `∫ z(H - δ + s) dν(δ)`, i.e. the
paper's `∫ x(s - δ) dν(δ)`. -/
def mconv (ν : Measure ℝ) (H : ℝ) (z : ℝ → E) (s : ℝ) : E := ∫ δ, z (H - δ + s) ∂ν

/-- A point delay: `∫ z(H - δ + s) d𝛿_a(δ) = z(H - a + s)`. -/
@[simp] theorem mconv_dirac (a H : ℝ) (z : ℝ → E) (s : ℝ) :
    mconv (Measure.dirac a) H z s = z (H - a + s) := integral_dirac _ a

/-- `mconv` only sees the trajectory on `[s, H + s]`. -/
theorem mconv_congr (hν : ν (Icc 0 H)ᶜ = 0) {z₁ z₂ : ℝ → E} {s : ℝ}
    (hz : ∀ δ ∈ Icc 0 H, z₁ (H - δ + s) = z₂ (H - δ + s)) : mconv ν H z₁ s = mconv ν H z₂ s :=
  integral_congr_ae ((ae_mem_Icc_of_compl hν).mono hz)

/-- Trajectories that agree a.e. on `(0, H + τ]` have measure delays that agree a.e. on
`(0, τ]`. -/
theorem mconv_congr_ae [SFinite ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z₁ z₂ : ℝ → E}
    (hz : z₁ =ᵐ[μI (H + τ)] z₂) : mconv ν H z₁ =ᵐ[μI τ] mconv ν H z₂ := by
  filter_upwards [ae_ae_comp hν hz] with s hs
  exact integral_congr_ae hs

/-- `mconv` is homogeneous. -/
theorem mconv_smul (c : ℝ) (z : ℝ → E) (s : ℝ) : mconv ν H (c • z) s = c • mconv ν H z s :=
  integral_smul c _

/-- `mconv` is additive where the integrals exist. -/
theorem mconv_add {z₁ z₂ : ℝ → E} {s : ℝ} (h₁ : Integrable (fun δ => z₁ (H - δ + s)) ν)
    (h₂ : Integrable (fun δ => z₂ (H - δ + s)) ν) :
    mconv ν H (z₁ + z₂) s = mconv ν H z₁ s + mconv ν H z₂ s :=
  integral_add h₁ h₂

/-- Translating the trajectory translates `mconv`. -/
theorem mconv_shift (z : ℝ → E) (s σ : ℝ) :
    mconv ν H (fun ρ => z (s + ρ)) σ = mconv ν H z (s + σ) := by
  unfold mconv
  congr 1 with δ
  ring_nf

/-- Along a trajectory continuous on `[0, H + τ]`, the integrand of `mconv` at `s ∈ [0, τ]` is
integrable. -/
theorem integrable_comp_of_continuousOn [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0)
    {τ s : ℝ} {z : ℝ → E} (hz : ContinuousOn z (Icc 0 (H + τ))) (hs : s ∈ Icc 0 τ) :
    Integrable (fun δ => z (H - δ + s)) ν :=
  integrable_of_continuousOn hν (hz.comp (f := fun δ => H - δ + s) (by fun_prop)
    fun δ hδ => ⟨by linarith [hδ.2, hs.1], by linarith [hδ.1, hs.2]⟩)

/-- **Continuity**: along a trajectory continuous on `[0, H + τ]`, `mconv` is continuous on
`[0, τ]` (dominated convergence). -/
theorem continuousOn_mconv [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : ContinuousOn z (Icc 0 (H + τ))) : ContinuousOn (mconv ν H z) (Icc 0 τ) := by
  unfold mconv
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun s hs => (integrable_comp_of_continuousOn hν hz hs).aestronglyMeasurable) ?_
    (integrable_const C) ?_
  · intro s hs
    filter_upwards [ae_mem_Icc_of_compl hν] with δ hδ
    exact hC _ ⟨by linarith [hδ.2, hs.1], by linarith [hδ.1, hs.2]⟩
  · filter_upwards [ae_mem_Icc_of_compl hν] with δ hδ
    exact hz.comp (f := fun s => H - δ + s) (by fun_prop)
      fun s hs => ⟨by linarith [hδ.2, hs.1], by linarith [hδ.1, hs.2]⟩

/-- `mconv` of a strongly measurable trajectory is strongly measurable. -/
theorem stronglyMeasurable_mconv [SFinite ν] {z : ℝ → E} (hz : StronglyMeasurable z) :
    StronglyMeasurable (mconv ν H z) :=
  StronglyMeasurable.integral_prod_right (f := fun s δ => z (H - δ + s))
    (hz.comp_measurable (by fun_prop))

/-- `mconv` of an a.e. strongly measurable trajectory is a.e. strongly measurable. -/
theorem aestronglyMeasurable_mconv [SFinite ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : AEStronglyMeasurable z (μI (H + τ))) : AEStronglyMeasurable (mconv ν H z) (μI τ) :=
  (stronglyMeasurable_mconv hz.stronglyMeasurable_mk).aestronglyMeasurable.congr
    (mconv_congr_ae hν hz.ae_eq_mk).symm

/-- Tonelli: `∫₀^τ ∫ ‖z(H - δ + s)‖² dν ds ≤ ν(ℝ) ‖z‖²_{L²(0, H + τ)}`. -/
private theorem lintegral_lintegral_le [SFinite ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : StronglyMeasurable z) :
    ∫⁻ s in Ioc 0 τ, ∫⁻ δ, ‖z (H - δ + s)‖ₑ ^ (2 : ℝ) ∂ν ≤
      ν univ * eLpNorm z 2 (μI (H + τ)) ^ (2 : ℝ) := by
  have hm : Measurable (Function.uncurry fun s δ => ‖z (H - δ + s)‖ₑ ^ (2 : ℝ)) :=
    ((hz.comp_measurable (by fun_prop : Measurable fun x : ℝ × ℝ => H - x.2 + x.1)).enorm).pow_const _
  rw [lintegral_lintegral_swap hm.aemeasurable, mul_comm, ← lintegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_mem_Icc_of_compl hν] with δ hδ
  rw [← eLpNorm_two_rpow (f := fun s => z (H - δ + s)) (μ := μI τ)
    (hz.comp_measurable (by fun_prop)).aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow (eLpNorm_comp_add_le hz.aestronglyMeasurable (by linarith [hδ.2])
    (by linarith [hδ.1])) (by norm_num)

/-- **`L²` bound of a measure delay**: `‖∫ z(H - δ + ·) dν(δ)‖_{L²(0, τ)} ≤ ν(ℝ) ‖z‖_{L²(0, H + τ)}`
(Cauchy–Schwarz in `δ` and Tonelli). -/
theorem eLpNorm_mconv_le [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : AEStronglyMeasurable z (μI (H + τ))) :
    eLpNorm (mconv ν H z) 2 (μI τ) ≤ ν univ * eLpNorm z 2 (μI (H + τ)) := by
  rw [eLpNorm_congr_ae (mconv_congr_ae hν hz.ae_eq_mk), eLpNorm_congr_ae hz.ae_eq_mk]
  set z₀ := hz.mk z
  have hz₀ : StronglyMeasurable z₀ := hz.stronglyMeasurable_mk
  have key : ∫⁻ s in Ioc 0 τ, ‖mconv ν H z₀ s‖ₑ ^ (2 : ℝ) ≤
      ν univ * (ν univ * eLpNorm z₀ 2 (μI (H + τ)) ^ (2 : ℝ)) :=
    calc ∫⁻ s in Ioc 0 τ, ‖mconv ν H z₀ s‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ s in Ioc 0 τ, ν univ * ∫⁻ δ, ‖z₀ (H - δ + s)‖ₑ ^ (2 : ℝ) ∂ν :=
          lintegral_mono fun s =>
            enorm_integral_rpow_le ν (hz₀.comp_measurable (by fun_prop)).aestronglyMeasurable
      _ = ν univ * ∫⁻ s in Ioc 0 τ, ∫⁻ δ, ‖z₀ (H - δ + s)‖ₑ ^ (2 : ℝ) ∂ν :=
          lintegral_const_mul _ (Measurable.lintegral_prod_right ((hz₀.comp_measurable
            (by fun_prop : Measurable fun x : ℝ × ℝ => H - x.2 + x.1)).enorm.pow_const _))
      _ ≤ ν univ * (ν univ * eLpNorm z₀ 2 (μI (H + τ)) ^ (2 : ℝ)) :=
          mul_le_mul_right (lintegral_lintegral_le hν hz₀) _
  rw [← ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num),
    eLpNorm_two_rpow (stronglyMeasurable_mconv hz₀).aestronglyMeasurable,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two (ν univ), pow_two, mul_assoc]
  exact key

/-- Along an `L²` trajectory, `mconv` is square integrable. -/
theorem memLp_mconv [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : MemLp z 2 (μI (H + τ))) : MemLp (mconv ν H z) 2 (μI τ) :=
  memLp_iff.2 ((eLpNorm_mconv_le hν hz.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (measure_lt_top _ _) hz.eLpNorm_lt_top))

/-- Along an `L²` trajectory, the integrand of `mconv` at `s` is integrable for a.e. `s`. -/
theorem ae_integrable_comp [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z : ℝ → E}
    (hz : MemLp z 2 (μI (H + τ))) : ∀ᵐ s ∂(μI τ), Integrable (fun δ => z (H - δ + s)) ν := by
  set z₀ := hz.aestronglyMeasurable.mk z
  have hz₀ : StronglyMeasurable z₀ := hz.aestronglyMeasurable.stronglyMeasurable_mk
  have hfin : ∫⁻ s in Ioc 0 τ, ∫⁻ δ, ‖z₀ (H - δ + s)‖ₑ ^ (2 : ℝ) ∂ν ≠ ∞ :=
    ((lintegral_lintegral_le hν hz₀).trans_lt (ENNReal.mul_lt_top (measure_lt_top _ _)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (by rw [← eLpNorm_congr_ae hz.aestronglyMeasurable.ae_eq_mk]; exact hz.eLpNorm_ne_top)))).ne
  have hm : Measurable fun s => ∫⁻ δ, ‖z₀ (H - δ + s)‖ₑ ^ (2 : ℝ) ∂ν :=
    Measurable.lintegral_prod_right
      ((hz₀.comp_measurable (by fun_prop : Measurable fun x : ℝ × ℝ => H - x.2 + x.1)).enorm.pow_const _)
  filter_upwards [ae_ae_comp hν hz.aestronglyMeasurable.ae_eq_mk, ae_lt_top hm hfin] with s hs hfs
  have hg : AEStronglyMeasurable (fun δ => z₀ (H - δ + s)) ν :=
    (hz₀.comp_measurable (by fun_prop)).aestronglyMeasurable
  have hL : MemLp (fun δ => z₀ (H - δ + s)) 2 ν :=
    memLp_iff.2 ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 2)).1
      (by rw [eLpNorm_two_rpow hg]; exact hfs))
  exact (hL.integrable one_le_two).congr (hs.mono fun δ h => h.symm)

/-- **`mconv` commutes with the weak derivative**: for an `H¹` trajectory `z` on `[0, H + τ]` with
derivative `z'`, `s ↦ ∫ z(H - δ + s) dν(δ)` is `H¹` on `[0, τ]` with derivative
`s ↦ ∫ z'(H - δ + s) dν(δ)` (Fubini). -/
theorem hasWeakDeriv_mconv [IsFiniteMeasure ν] (hν : ν (Icc 0 H)ᶜ = 0) {τ : ℝ} {z z' : ℝ → E}
    (hz : HasWeakDeriv (H + τ) z z') : HasWeakDeriv τ (mconv ν H z) (mconv ν H z') := by
  refine ⟨memLp_mconv hν hz.memLp_deriv, fun t ht => ?_⟩
  have hm := hz.memLp_deriv.aestronglyMeasurable
  set g : ℝ → E := (Ioc 0 (H + τ)).indicator (hm.mk z') with hg_def
  have hgz : z' =ᵐ[μI (H + τ)] g :=
    hm.ae_eq_mk.trans (indicator_ae_eq_restrict measurableSet_Ioc.nullMeasurableSet).symm
  have hgm : StronglyMeasurable g := hm.stronglyMeasurable_mk.indicator measurableSet_Ioc
  have hgi : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioc).2 (hz.integrable_deriv.congr hm.ae_eq_mk)
  have hzg : HasWeakDeriv (H + τ) z g := hz.congr (fun _ _ => rfl) hgz
  -- Fubini for `(δ, u) ↦ g(H - δ + u)` on `ν × (0, t]`.
  have hmeas : StronglyMeasurable (Function.uncurry fun δ u => g (H - δ + u)) :=
    hgm.comp_measurable (by fun_prop)
  have hF : Integrable (Function.uncurry fun δ u => g (H - δ + u))
      (ν.prod (volume.restrict (Ioc 0 t))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun δ => (hgi.comp_add_left (H - δ)).restrict, ?_⟩
    refine Integrable.of_bound hmeas.aestronglyMeasurable.norm.integral_prod_right'
      (∫ x, ‖g x‖) (ae_of_all _ fun δ => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ u in Ioc 0 t, ‖g (H - δ + u)‖ ≤ ∫ u, ‖g (H - δ + u)‖ :=
          setIntegral_le_integral (hgi.comp_add_left (H - δ)).norm
            (ae_of_all _ fun _ => norm_nonneg _)
      _ = ∫ x, ‖g x‖ := integral_add_left_eq_self (fun x => ‖g x‖) (H - δ)
  have hpt : ∀ δ ∈ Icc 0 H, z (H - δ + t) =
      z (H - δ + 0) + ∫ u in Ioc 0 t, g (H - δ + u) := fun δ hδ => by
    rw [← intervalIntegral.integral_of_le ht.1]
    exact (hasWeakDeriv_comp_add hzg (by linarith [hδ.2]) (by linarith [hδ.1])).eq_add_integral
      t ht
  have i0 : Integrable (fun δ => z (H - δ + 0)) ν :=
    integrable_comp_of_continuousOn hν hz.continuousOn ⟨le_rfl, ht.1.trans ht.2⟩
  have hcongr : ∫ u in Ioc 0 t, mconv ν H z' u = ∫ u in Ioc 0 t, mconv ν H g u :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2)
      (mconv_congr_ae hν hgz))
  show mconv ν H z t = mconv ν H z 0 + ∫ u in (0 : ℝ)..t, mconv ν H z' u
  rw [intervalIntegral.integral_of_le ht.1, hcongr]
  unfold mconv
  have i1 : Integrable (fun δ => ∫ u in Ioc 0 t, g (H - δ + u)) ν := hF.integral_prod_left
  rw [← integral_integral_swap hF, ← integral_add i0 i1]
  exact integral_congr_ae ((ae_mem_Icc_of_compl hν).mono fun δ hδ => hpt δ hδ)

end Delay

end DataDrivenControl
