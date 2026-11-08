module

public import DataDrivenControl.Examples.Delay.Operator

/-!
# Weighted `L²` norms and the neutral Volterra operators

Solutions of the neutral delay equation of `ex:intro-delay` are only square integrable, and the
neutral term `M x_t` is not an integral, so existence is proved by a contraction argument in the
weighted norm

`‖x‖_γ² = ∫₀^τ e^{-2γt} ‖x(t)‖² dt`  (`wnorm γ τ x`),

which is equivalent to the `L²(0, τ)` norm (`wnorm_le`, `eLpNorm_le_wnorm`).

## Main results

* `wnorm_mconv_le`: a finite delay measure `ν` on `[0, H]` with zero history has weighted norm
  `≤ ∫ e^{-γδ} dν(δ)` (the `L²` bound of `mconv` for the measure `e^{-γδ} ν`), and
  `tendsto_integral_exp`: this tends to `0` as `γ → ∞` when `ν({0}) = 0`.  This is where the
  condition "`M` has no mass at `0`" enters.
* `wnorm_window_le`: a distributed delay `x ↦ D x_t`, `D` bounded on `L²(0, H; E)`, has weighted
  norm `≤ ‖D‖ / √(2γ)` (Tonelli: `∫₀^τ e^{-2γt} ‖x_t‖² dt ≤ (2γ)⁻¹ ‖x‖_γ²`).
* `wnorm_primL_le`: the primitive `x ↦ ∫₀^· x` has weighted norm `≤ √τ / √(2γ)` (it is the
  distributed delay `∫_{(0, τ]}` over a window of length `τ`, `primitive_eq_segOp`).
* `DelayOp.wnorm_opL_le`: the weighted bound `DelayOp.wconst p γ` of a delay functional with zero
  history, `DelayOp.tendsto_wconst` (it tends to `0` when no measure has an atom at `0`).
* `isUnit_one_sub_of_wnorm_le`: an operator `K` on `L²(0, τ; E)` with `‖K x‖_γ ≤ q ‖x‖_γ`,
  `q < 1`, has `‖Kⁿ‖ ≤ e^{γτ} qⁿ < 1` for large `n`, so `1 - K` is invertible (Neumann series for
  `Kⁿ` and the geometric sum `(1 - K) ∑_{i<n} Kⁱ = 1 - Kⁿ`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ### The weighted norm -/

/-- The **weighted `L²` norm** `(∫₀^τ e^{-2γt} ‖x(t)‖² dt)^{1/2}`, as an extended real. -/
def wnorm (γ τ : ℝ) (x : ℝ → F) : ℝ≥0∞ := eLpNorm (fun t => Real.exp (-(γ * t)) • x t) 2 (μI τ)

/-- The weighted norm only depends on the class in `L²(0, τ)`. -/
theorem wnorm_congr_ae {γ τ : ℝ} {x₁ x₂ : ℝ → F} (hx : x₁ =ᵐ[μI τ] x₂) :
    wnorm γ τ x₁ = wnorm γ τ x₂ :=
  eLpNorm_congr_ae (hx.mono fun t ht => by simp only [ht])

/-- The weighted function is measurable. -/
theorem aestronglyMeasurable_weight {γ τ : ℝ} {x : ℝ → F} (hx : AEStronglyMeasurable x (μI τ)) :
    AEStronglyMeasurable (fun t => Real.exp (-(γ * t)) • x t) (μI τ) :=
  (by fun_prop : Continuous fun t : ℝ => Real.exp (-(γ * t))).aestronglyMeasurable.smul hx

/-- A pointwise bound `‖x‖ ≤ c ‖y‖` gives `‖x‖_γ ≤ c ‖y‖_γ`. -/
theorem wnorm_le_of_ae {γ τ c : ℝ} (hc : 0 ≤ c) {x : ℝ → E} {y : ℝ → F}
    (hx : AEStronglyMeasurable x (μI τ)) (h : ∀ᵐ t ∂(μI τ), ‖x t‖ ≤ c * ‖y t‖) :
    wnorm γ τ x ≤ ENNReal.ofReal c * wnorm γ τ y := by
  rw [wnorm, wnorm, ← Real.enorm_of_nonneg hc, ← eLpNorm_const_smul]
  refine eLpNorm_mono_ae (aestronglyMeasurable_weight hx) ?_
  filter_upwards [h] with t ht
  rw [Pi.smul_apply, norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hc, mul_left_comm]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

/-- `‖x‖_γ ≤ ‖x‖_{L²(0, τ)}` for `γ ≥ 0`. -/
theorem wnorm_le {γ τ : ℝ} (hγ : 0 ≤ γ) {x : ℝ → F} (hx : AEStronglyMeasurable x (μI τ)) :
    wnorm γ τ x ≤ eLpNorm x 2 (μI τ) := by
  refine eLpNorm_mono_ae (aestronglyMeasurable_weight hx) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
  nlinarith [ht.1]

/-- `‖x‖_{L²(0, τ)} ≤ e^{γτ} ‖x‖_γ` for `γ ≥ 0`. -/
theorem eLpNorm_le_wnorm {γ τ : ℝ} (hγ : 0 ≤ γ) {x : ℝ → F} (hx : AEStronglyMeasurable x (μI τ)) :
    eLpNorm x 2 (μI τ) ≤ ENNReal.ofReal (Real.exp (γ * τ)) * wnorm γ τ x := by
  rw [wnorm, ← Real.enorm_of_nonneg (Real.exp_pos _).le, ← eLpNorm_const_smul]
  refine eLpNorm_mono_ae hx ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Pi.smul_apply, norm_smul, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add]
  refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.2 ?_)
  nlinarith [ht.2]

/-- Triangle inequality for the weighted norm. -/
theorem wnorm_add_le {γ τ : ℝ} (x y : ℝ → F) :
    wnorm γ τ (fun t => x t + y t) ≤ wnorm γ τ x + wnorm γ τ y := by
  have e : (fun t => Real.exp (-(γ * t)) • (x t + y t)) =
      (fun t => Real.exp (-(γ * t)) • x t) + fun t => Real.exp (-(γ * t)) • y t := by
    funext t
    simp only [smul_add, Pi.add_apply]
  rw [wnorm, e]
  exact eLpNorm_add_le one_le_two

/-- Weighted bounds add up. -/
theorem wnorm_add_le_of_le {γ τ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : ℝ → F} {W : ℝ≥0∞}
    (hx : wnorm γ τ x ≤ ENNReal.ofReal a * W) (hy : wnorm γ τ y ≤ ENNReal.ofReal b * W) :
    wnorm γ τ (fun t => x t + y t) ≤ ENNReal.ofReal (a + b) * W := by
  rw [ENNReal.ofReal_add ha hb, add_mul]
  exact (wnorm_add_le _ _).trans (add_le_add hx hy)

/-- Weighted bounds of finite sums. -/
theorem wnorm_sum_le_of_le {ι : Type*} (s : Finset ι) {γ τ : ℝ} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) {x : ι → ℝ → F} {W : ℝ≥0∞}
    (hx : ∀ i ∈ s, wnorm γ τ (x i) ≤ ENNReal.ofReal (a i) * W) :
    wnorm γ τ (fun t => ∑ i ∈ s, x i t) ≤ ENNReal.ofReal (∑ i ∈ s, a i) * W := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact wnorm_add_le_of_le (ha i) (Finset.sum_nonneg fun j _ => ha j)
      (hx i (Finset.mem_insert_self i s)) (ih fun j hj => hx j (Finset.mem_insert_of_mem hj))

/-- Bounded operators act on weighted norms with their norm. -/
theorem wnorm_clm_le {γ τ : ℝ} (P : E →L[ℝ] F) {x : ℝ → E} (hx : AEStronglyMeasurable x (μI τ)) :
    wnorm γ τ (fun t => P (x t)) ≤ ENNReal.ofReal ‖P‖ * wnorm γ τ x :=
  wnorm_le_of_ae (norm_nonneg _) (P.continuous.comp_aestronglyMeasurable hx)
    (ae_of_all _ fun t => P.le_opNorm (x t))

/-! ### Translations and windows -/

/-- The weighted function of an `L²` signal is square integrable (`γ ≥ 0`). -/
theorem memLp_weight {γ τ : ℝ} (hγ : 0 ≤ γ) {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    MemLp (fun t => Real.exp (-(γ * t)) • x t) 2 (μI τ) := by
  refine hx.of_le (aestronglyMeasurable_weight hx.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
  nlinarith [ht.1]

/-- The weighted zero-history trajectory: `e^{-γ(ρ - H)} z(ρ) = traj H 0 (e^{-γ·} x) ρ`. -/
theorem traj_weight (H γ : ℝ) (x : ℝ → E) (ρ : ℝ) :
    traj H 0 (fun u => Real.exp (-(γ * u)) • x u) ρ =
      Real.exp (-(γ * (ρ - H))) • traj H 0 x ρ := by
  unfold traj
  split_ifs <;> simp

/-- **A measure delay is a weighted contraction**: with zero history,
`‖∫ x(· - δ) dν(δ)‖_γ ≤ (∫ e^{-γδ} dν(δ)) ‖x‖_γ` (the `L²` bound `eLpNorm_mconv_le` for the
measure `e^{-γδ} ν`, since `e^{-γs} x(s - δ) = e^{-γδ} (e^{-γ·} x)(s - δ)`). -/
theorem wnorm_mconv_le {ν : Measure ℝ} [IsFiniteMeasure ν] {H τ γ : ℝ}
    (hν : ν (Icc 0 H)ᶜ = 0) (hH : 0 ≤ H) (hτ : 0 ≤ τ) (hγ : 0 ≤ γ) {x : ℝ → E}
    (hx : MemLp x 2 (μI τ)) :
    wnorm γ τ (mconv ν H (traj H 0 x)) ≤
      ENNReal.ofReal (∫ δ, Real.exp (-(γ * δ)) ∂ν) * wnorm γ τ x := by
  have hw := memLp_weight hγ hx
  set Y : ℝ → E := traj H 0 (fun u => Real.exp (-(γ * u)) • x u) with hY
  have hYL : MemLp Y 2 (μI (H + τ)) := memLp_traj_of_memLp hH hτ MemLp.zero hw
  set w : ℝ → ℝ≥0 := fun δ => Real.toNNReal (Real.exp (-(γ * δ))) with hwdef
  have hwm : Measurable w :=
    (by fun_prop : Measurable fun δ : ℝ => Real.exp (-(γ * δ))).real_toNNReal
  have hei : Integrable (fun δ => Real.exp (-(γ * δ))) ν :=
    integrable_of_continuousOn hν (by fun_prop)
  set ν' := ν.withDensity fun δ => (w δ : ℝ≥0∞) with hν'def
  have hν'u : ν' univ = ENNReal.ofReal (∫ δ, Real.exp (-(γ * δ)) ∂ν) := by
    rw [hν'def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ofReal_integral_eq_lintegral_ofReal hei (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    rfl
  have : IsFiniteMeasure ν' := ⟨by rw [hν'u]; exact ENNReal.ofReal_lt_top⟩
  have hν' : ν' (Icc 0 H)ᶜ = 0 := withDensity_absolutelyContinuous ν _ hν
  have e : (fun s => Real.exp (-(γ * s)) • mconv ν H (traj H 0 x) s) = mconv ν' H Y := by
    funext s
    rw [mconv, mconv, hν'def, integral_withDensity_eq_integral_smul hwm, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun δ => ?_)
    simp only [hY, traj_weight, hwdef, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le,
      smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [wnorm, e, ← hν'u, wnorm, ← eLpNorm_traj_zero_left hH hw]
  exact eLpNorm_mconv_le hν' hYL.aestronglyMeasurable

/-- `∫ e^{-γδ} dν(δ) → 0` as `γ → ∞` for a finite measure `ν` on `[0, H]` without atom at `0`
(dominated convergence). -/
theorem tendsto_integral_exp {ν : Measure ℝ} [IsFiniteMeasure ν] {H : ℝ}
    (hν : ν (Icc 0 H)ᶜ = 0) (h0 : ν {0} = 0) :
    Tendsto (fun γ : ℝ => ∫ δ, Real.exp (-(γ * δ)) ∂ν) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
    (F := fun γ δ => Real.exp (-(γ * δ))) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun γ =>
      (by fun_prop : Continuous fun δ : ℝ => Real.exp (-(γ * δ))).aestronglyMeasurable)
    ((eventually_ge_atTop 0).mono fun γ hγ => by
      filter_upwards [ae_mem_Icc_of_compl hν] with δ hδ
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      nlinarith [hδ.1])
    (integrable_const 1)
    (by
      filter_upwards [ae_mem_Icc_of_compl hν, measure_eq_zero_iff_ae_notMem.1 h0] with δ hδ hδ0
      have hpos : 0 < δ := lt_of_le_of_ne hδ.1 (Ne.symm (by simpa using hδ0))
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hpos))
  simpa using hlim

/-- `∫ e^{-γδ} dν(δ) ≤ ν(ℝ)` for `γ ≥ 0` and `ν` on `[0, H]`. -/
theorem integral_exp_le {ν : Measure ℝ} [IsFiniteMeasure ν] {H γ : ℝ}
    (hν : ν (Icc 0 H)ᶜ = 0) (hγ : 0 ≤ γ) : ∫ δ, Real.exp (-(γ * δ)) ∂ν ≤ ν.real univ := by
  calc ∫ δ, Real.exp (-(γ * δ)) ∂ν ≤ ∫ _, (1 : ℝ) ∂ν :=
        integral_mono_ae (integrable_of_continuousOn hν (by fun_prop)) (integrable_const 1) (by
          filter_upwards [ae_mem_Icc_of_compl hν] with δ hδ
          exact Real.exp_le_one_iff.2 (by nlinarith [hδ.1]))
    _ = ν.real univ := by simp

/-- `∫₀^H e^{-2γ(H - σ)} dσ ≤ (2γ)⁻¹`. -/
theorem lintegral_exp_le {H γ : ℝ} (hH : 0 ≤ H) (hγ : 0 < γ) :
    ∫⁻ σ in Ioc 0 H, ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) ≤
      ENNReal.ofReal (1 / (2 * γ)) := by
  have hc : Continuous fun σ : ℝ => Real.exp (-(2 * γ * (H - σ))) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ fun σ => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : ∀ σ ∈ uIcc 0 H, HasDerivAt (fun σ => Real.exp (-(2 * γ * (H - σ))) / (2 * γ))
      (Real.exp (-(2 * γ * (H - σ)))) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => -(2 * γ * (H - σ))) (2 * γ) σ := by
      have := ((hasDerivAt_id σ).const_mul (2 * γ)).sub_const (2 * γ * H)
      convert this using 1
      · funext u
        simp only [id]
        ring
      · ring
    convert (h1.exp.div_const (2 * γ)) using 1
    field_simp
  rw [← intervalIntegral.integral_of_le hH, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable 0 H)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]
  have : 0 < Real.exp (-(2 * γ * H)) / (2 * γ) := by positivity
  linarith

/-- The weighted distributed delay, for a strongly measurable representative. -/
private theorem wnorm_window_le_aux {H τ γ : ℝ} (hH : 0 ≤ H) (hτ : 0 ≤ τ) (hγ : 0 < γ)
    (D : L2 E H →L[ℝ] F) {x : ℝ → E} (hx : MemLp x 2 (μI τ)) (hxm : StronglyMeasurable x) :
    wnorm γ τ (fun t => D (window H (traj H 0 x) t)) ≤
      ENNReal.ofReal (‖D‖ / √(2 * γ)) * wnorm γ τ x := by
  have hw := memLp_weight hγ.le hx
  have hwm : StronglyMeasurable fun u => Real.exp (-(γ * u)) • x u :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(γ * u))).stronglyMeasurable.smul hxm
  set Y : ℝ → E := traj H 0 (fun u => Real.exp (-(γ * u)) • x u) with hY
  have hYm : StronglyMeasurable Y := by
    have e : Y = (Iic H)ᶜ.indicator fun ρ => Real.exp (-(γ * (ρ - H))) • x (ρ - H) := by
      funext ρ
      simp only [hY, traj, indicator, mem_compl_iff, mem_Iic, Pi.zero_apply]
      split_ifs <;> rfl
    rw [e]
    exact (hwm.comp_measurable (measurable_sub_const H)).indicator measurableSet_Iic.compl
  have hYL : MemLp Y 2 (μI (H + τ)) := memLp_traj_of_memLp hH hτ MemLp.zero hw
  have hYn : eLpNorm Y 2 (μI (H + τ)) = wnorm γ τ x := eLpNorm_traj_zero_left hH hw
  have hz : MemLp (traj H 0 x) 2 (μI (H + τ)) := memLp_traj_of_memLp hH hτ MemLp.zero hx
  have key : ∀ t σ : ℝ, Real.exp (-(γ * t)) • traj H 0 x (t + σ) =
      Real.exp (-(γ * (H - σ))) • Y (t + σ) := by
    intro t σ
    rw [hY, traj_weight, smul_smul, ← Real.exp_add]
    congr 2
    ring
  set N : ℝ → ℝ≥0∞ := fun t =>
    eLpNorm (fun σ => Real.exp (-(γ * (H - σ))) • Y (t + σ)) 2 (μI H) with hN
  have hpt : ∀ t ∈ Ioc 0 τ, ‖Real.exp (-(γ * t)) • D (window H (traj H 0 x) t)‖ₑ ≤
      ‖D‖ₑ * N t := by
    intro t ht
    have hm : MemLp (fun σ => traj H 0 x (t + σ)) 2 (μI H) :=
      memLp_comp_add hz ht.1.le (by linarith [ht.2])
    have e1 : Real.exp (-(γ * t)) • window H (traj H 0 x) t =
        (hm.const_smul (Real.exp (-(γ * t)))).toLp _ := by
      rw [window_eq_toLp hm, MemLp.toLp_const_smul]
    rw [← map_smul, e1]
    refine (D.le_opENorm _).trans (mul_le_mul_right (le_of_eq ?_) _)
    rw [Lp.enorm_toLp, hN]
    congr 1
    funext σ
    exact key t σ
  have hLm : AEStronglyMeasurable (fun t => Real.exp (-(γ * t)) • D (window H (traj H 0 x) t))
      (μI τ) :=
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(γ * t))).continuousOn.smul
      (D.continuous.comp_continuousOn (continuousOn_window (T := H) (T' := τ) hz))).mono
      Ioc_subset_Icc_self |>.aestronglyMeasurable measurableSet_Ioc
  have hNsq : ∀ t, N t ^ (2 : ℝ) = ∫⁻ σ in Ioc 0 H,
      ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) * ‖Y (t + σ)‖ₑ ^ (2 : ℝ) := by
    intro t
    have hm : AEStronglyMeasurable (fun σ => Real.exp (-(γ * (H - σ))) • Y (t + σ)) (μI H) :=
      ((by fun_prop : Continuous fun σ : ℝ => Real.exp (-(γ * (H - σ)))).stronglyMeasurable.smul
        (hYm.comp_measurable (measurable_const_add t))).aestronglyMeasurable
    simp only [hN]
    rw [eLpNorm_two_rpow hm]
    refine lintegral_congr fun σ => ?_
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      Real.enorm_of_nonneg (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    congr 3
    ring
  have hG : Measurable (Function.uncurry fun t σ : ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) * ‖Y (t + σ)‖ₑ ^ (2 : ℝ)) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
        Real.exp (-(2 * γ * (H - p.2)))).measurable
    · exact ((hYm.comp_measurable (measurable_fst.add measurable_snd)).enorm).pow_const _
  have hinner : ∀ σ ∈ Ioc 0 H, ∫⁻ t in Ioc 0 τ, ‖Y (t + σ)‖ₑ ^ (2 : ℝ) ≤
      wnorm γ τ x ^ (2 : ℝ) := by
    intro σ hσ
    have e : (fun t => ‖Y (t + σ)‖ₑ ^ (2 : ℝ)) = fun t => ‖Y (σ + t)‖ₑ ^ (2 : ℝ) := by
      funext t
      rw [add_comm]
    have hm : AEStronglyMeasurable (fun t => Y (σ + t)) (μI τ) :=
      (hYm.comp_measurable (measurable_const_add σ)).aestronglyMeasurable
    rw [e, ← eLpNorm_two_rpow hm, ← hYn]
    exact ENNReal.rpow_le_rpow
      (eLpNorm_comp_add_le hYL.aestronglyMeasurable hσ.1.le (by linarith [hσ.2]))
      (by norm_num)
  have step2 : ∫⁻ t in Ioc 0 τ, N t ^ (2 : ℝ) ≤
      ENNReal.ofReal (1 / (2 * γ)) * wnorm γ τ x ^ (2 : ℝ) := by
    simp_rw [hNsq]
    rw [lintegral_lintegral_swap hG.aemeasurable]
    calc ∫⁻ σ in Ioc 0 H, ∫⁻ t in Ioc 0 τ,
          ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) * ‖Y (t + σ)‖ₑ ^ (2 : ℝ)
        = ∫⁻ σ in Ioc 0 H, ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) *
            ∫⁻ t in Ioc 0 τ, ‖Y (t + σ)‖ₑ ^ (2 : ℝ) :=
          lintegral_congr fun σ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ σ in Ioc 0 H, ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ)))) *
            wnorm γ τ x ^ (2 : ℝ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
          exact mul_le_mul_right (hinner σ hσ) _
      _ = (∫⁻ σ in Ioc 0 H, ENNReal.ofReal (Real.exp (-(2 * γ * (H - σ))))) *
            wnorm γ τ x ^ (2 : ℝ) := lintegral_mul_const' _ _ (by
          rw [← hYn]
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hYL.eLpNorm_ne_top)
      _ ≤ ENNReal.ofReal (1 / (2 * γ)) * wnorm γ τ x ^ (2 : ℝ) :=
          mul_le_mul_left (lintegral_exp_le hH hγ) _
  have step1 : wnorm γ τ (fun t => D (window H (traj H 0 x) t)) ^ (2 : ℝ) ≤
      ‖D‖ₑ ^ (2 : ℝ) * ∫⁻ t in Ioc 0 τ, N t ^ (2 : ℝ) := by
    rw [wnorm, eLpNorm_two_rpow hLm, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    exact ENNReal.rpow_le_rpow (hpt t ht) (by norm_num)
  have hc : ‖D‖ₑ ^ (2 : ℝ) * ENNReal.ofReal (1 / (2 * γ)) =
      ENNReal.ofReal (‖D‖ / √(2 * γ)) ^ (2 : ℝ) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← ENNReal.ofReal_mul
        (by positivity)]
    congr 1
    rw [Real.rpow_two, Real.rpow_two, div_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [← ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num), ENNReal.mul_rpow_of_nonneg _ _
    (by norm_num), ← hc, mul_assoc]
  exact step1.trans (mul_le_mul_right step2 _)

/-- **A distributed delay is a weighted contraction** for `γ` large: with zero history,
`‖t ↦ D x_t‖_γ ≤ ‖D‖ / √(2γ) ‖x‖_γ` (Tonelli). -/
theorem wnorm_window_le {H τ γ : ℝ} (hH : 0 ≤ H) (hτ : 0 ≤ τ) (hγ : 0 < γ)
    (D : L2 E H →L[ℝ] F) {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    wnorm γ τ (fun t => D (window H (traj H 0 x) t)) ≤
      ENNReal.ofReal (‖D‖ / √(2 * γ)) * wnorm γ τ x := by
  set x₀ := hx.aestronglyMeasurable.mk x
  have hx₀ : x =ᵐ[μI τ] x₀ := hx.aestronglyMeasurable.ae_eq_mk
  have e1 : (fun t => D (window H (traj H 0 x) t)) =ᵐ[μI τ]
      fun t => D (window H (traj H 0 x₀) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [window_congr_ae (traj_ae_congr_right 0 hx₀) ht.1.le (by linarith [ht.2])]
  rw [wnorm_congr_ae e1, wnorm_congr_ae hx₀]
  exact wnorm_window_le_aux hH hτ hγ D (hx.ae_eq hx₀) hx.aestronglyMeasurable.stronglyMeasurable_mk

/-! ### The primitive as a distributed delay -/

/-- `‖∫_{(a, H]} w‖ ≤ √H ‖w‖_{L²(0, H)}` for `a ≥ 0`. -/
theorem norm_segOp_le {H a : ℝ} (hH : 0 ≤ H) (ha : 0 ≤ a) :
    ‖(segOp H a : L2 E H →L[ℝ] E)‖ ≤ √H := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun w => ?_
  rw [segOp_apply ha, Lp.norm_def]
  refine (norm_integral_le_integral_norm _).trans ((setIntegral_mono_set
    ((Lp.memLp w).integrable one_le_two).norm (ae_of_all _ fun _ => norm_nonneg _)
    (Ioc_subset_Ioc_left ha).eventuallyLE).trans ?_)
  exact integral_norm_le_sqrt_mul hH (Lp.memLp w)

/-- **The primitive is a distributed delay** over a window of length `τ`:
`∫₀ᵗ x = ∫_{(0, τ]} (traj τ 0 x)(t + ·)` for `t ∈ [0, τ]`. -/
theorem primitive_eq_segOp {τ t : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) (ht : t ∈ Icc 0 τ) :
    ∫ s in (0 : ℝ)..t, x s = segOp τ 0 (window τ (traj τ 0 x) t) := by
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have hz : MemLp (traj τ 0 x) 2 (μI (τ + τ)) := memLp_traj_of_memLp hτ hτ MemLp.zero hx
  have hzi : IntegrableOn (traj τ 0 x) (Ioc 0 (τ + τ)) := hz.integrable one_le_two
  rw [segOp_apply le_rfl]
  rw [integral_congr_ae (coeFn_window_of_memLp hz ht.1 (by linarith [ht.2])),
    setIntegral_comp_add (traj τ 0 x) t τ, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := τ)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).2
        (hzi.mono_set (Ioc_subset_Ioc ht.1 (by linarith))))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [ht.1])).2
        (hzi.mono_set (Ioc_subset_Ioc hτ (by linarith [ht.2]))))]
  have e1 : ∫ ρ in t..τ, traj τ 0 x ρ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : E)) fun ρ hρ => ?_]
    · simp
    · rw [uIcc_of_le ht.2] at hρ
      rw [traj_of_le _ _ hρ.2]
      rfl
  have e2 : ∫ ρ in τ..t + τ, traj τ 0 x ρ = ∫ ρ in τ..t + τ, x (ρ - τ) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun ρ hρ => ?_)
    rw [uIoc_of_le (by linarith [ht.1])] at hρ
    rw [traj_of_lt _ _ hρ.1]
  rw [e1, e2, zero_add, intervalIntegral.integral_comp_sub_right x τ, sub_self,
    add_sub_cancel_right]

/-- **The primitive is a weighted contraction** for `γ` large:
`‖∫₀^· x‖_γ ≤ √τ / √(2γ) ‖x‖_γ`. -/
theorem wnorm_primL_le {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : L2 E τ) :
    wnorm γ τ (primL τ x) ≤ ENNReal.ofReal (√τ / √(2 * γ)) * wnorm γ τ x := by
  have e : ⇑(primL τ x) =ᵐ[μI τ] fun t => segOp τ 0 (window τ (traj τ 0 ⇑x) t) := by
    filter_upwards [coeFn_primL τ x, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    rw [h1, primitive_eq_segOp (Lp.memLp x) (Ioc_subset_Icc_self h2)]
  rw [wnorm_congr_ae e]
  refine (wnorm_window_le hτ hτ hγ _ (Lp.memLp x)).trans (mul_le_mul_left ?_ _)
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_segOp_le hτ le_rfl)
    (Real.sqrt_nonneg _))

/-! ### Delay functionals with zero history -/

namespace DelayOp

variable {h : ℝ} (p : DelayOp h E F)

/-- The weighted bound `∑ₖ ‖Pₖ‖ ∫ e^{-γδ} dμₖ(δ) + ‖D‖ / √(2γ)` of a delay functional with zero
history. -/
def wconst (γ : ℝ) : ℝ := ∑ k, ‖p.P k‖ * ∫ δ, Real.exp (-(γ * δ)) ∂(p.μ k) + ‖p.D‖ / √(2 * γ)

/-- The weighted bound is nonnegative. -/
theorem wconst_nonneg (γ : ℝ) : 0 ≤ p.wconst γ :=
  add_nonneg (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le))
    (div_nonneg (norm_nonneg p.D) (Real.sqrt_nonneg _))

/-- **Weighted bound of a delay functional with zero history**:
`‖p x‖_γ ≤ (∑ₖ ‖Pₖ‖ ∫ e^{-γδ} dμₖ(δ) + ‖D‖ / √(2γ)) ‖x‖_γ`. -/
theorem wnorm_opL_le {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : L2 E τ) :
    wnorm γ τ (p.opL τ x) ≤ ENNReal.ofReal (p.wconst γ) * wnorm γ τ x := by
  rw [wnorm_congr_ae (p.coeFn_opL τ x)]
  have hx := Lp.memLp x
  have hc : ∀ k, 0 ≤ ‖p.P k‖ * ∫ δ, Real.exp (-(γ * δ)) ∂(p.μ k) := fun k =>
    mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => (Real.exp_pos _).le)
  refine wnorm_add_le_of_le (Finset.sum_nonneg fun k _ => hc k) (by positivity)
    (wnorm_sum_le_of_le Finset.univ hc fun k _ => ?_)
    (wnorm_window_le p.h_pos.le hτ hγ p.D hx)
  refine (wnorm_clm_le (p.P k) (aestronglyMeasurable_mconv (p.μ_compl k)
    (memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero hx).aestronglyMeasurable)).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
  exact mul_le_mul_right (wnorm_mconv_le (p.μ_compl k) p.h_pos.le hτ hγ.le hx) _

/-- The weighted bound tends to `0` when no delay measure has an atom at `0`. -/
theorem tendsto_wconst (h0 : ∀ k, p.μ k {0} = 0) : Tendsto p.wconst atTop (𝓝 0) := by
  have h1 : ∀ k, Tendsto (fun γ : ℝ => ‖p.P k‖ * ∫ δ, Real.exp (-(γ * δ)) ∂(p.μ k)) atTop
      (𝓝 0) := fun k => by
    simpa using (tendsto_integral_exp (p.μ_compl k) (h0 k)).const_mul ‖p.P k‖
  have h2 : Tendsto (fun γ : ℝ => ‖p.D‖ / √(2 * γ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_id.const_mul_atTop two_pos))
  have := (tendsto_finsetSum Finset.univ fun k _ => h1 k).add h2
  rw [Finset.sum_const_zero, add_zero] at this
  exact this

/-- For `γ ≥ 1/2` the weighted bound is at most `∑ₖ ‖Pₖ‖ μₖ([0, h]) + ‖D‖`. -/
theorem wconst_le {γ : ℝ} (hγ : 1 / 2 ≤ γ) : p.wconst γ ≤ p.mass + ‖p.D‖ := by
  refine add_le_add (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
    (integral_exp_le (p.μ_compl k) (by linarith)) (norm_nonneg _)) ?_
  refine div_le_self (norm_nonneg p.D) ?_
  rw [Real.one_le_sqrt]
  linarith

end DelayOp

/-- `√τ / √(2γ) → 0` as `γ → ∞`. -/
theorem tendsto_sqrt_div_sqrt (τ : ℝ) : Tendsto (fun γ : ℝ => √τ / √(2 * γ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop two_pos))

/-! ### Invertibility from a weighted contraction -/

/-- **Invertibility from a weighted contraction**: if `‖K x‖_γ ≤ q ‖x‖_γ` with `q < 1`, then
`‖Kⁿ‖ ≤ e^{γτ} qⁿ`, so `‖Kⁿ‖ < 1` for some `n`; `1 - Kⁿ` is a unit (Neumann series) and
`1 - Kⁿ = (1 - K) ∑_{i<n} Kⁱ` with commuting factors, so `1 - K` is a unit. -/
theorem isUnit_one_sub_of_wnorm_le {τ γ q : ℝ} (hγ : 0 ≤ γ) (hq0 : 0 ≤ q) (hq : q < 1)
    (K : L2 E τ →L[ℝ] L2 E τ)
    (hK : ∀ x : L2 E τ, wnorm γ τ (K x) ≤ ENNReal.ofReal q * wnorm γ τ x) : IsUnit (1 - K) := by
  have hpow : ∀ (n : ℕ) (x : L2 E τ),
      wnorm γ τ ((K ^ n) x) ≤ ENNReal.ofReal (q ^ n) * wnorm γ τ x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have e : (K ^ (n + 1)) x = K ((K ^ n) x) := by rw [pow_succ']; rfl
      rw [e, pow_succ', ENNReal.ofReal_mul hq0, mul_assoc]
      exact (hK _).trans (mul_le_mul_right (ih x) _)
  have hnorm : ∀ (n : ℕ) (x : L2 E τ), ‖(K ^ n) x‖ ≤ (Real.exp (γ * τ) * q ^ n) * ‖x‖ := by
    intro n x
    rw [Lp.norm_def, Lp.norm_def]
    have h1 := eLpNorm_le_wnorm (τ := τ) hγ (Lp.aestronglyMeasurable ((K ^ n) x))
    have h2 := wnorm_le (γ := γ) hγ (Lp.aestronglyMeasurable x)
    have h3 : eLpNorm ((K ^ n) x) 2 (μI τ) ≤
        ENNReal.ofReal (Real.exp (γ * τ) * q ^ n) * eLpNorm x 2 (μI τ) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      exact h1.trans (mul_le_mul_right ((hpow n x).trans (mul_le_mul_right h2 _)) _)
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Lp.eLpNorm_ne_top x)) h3).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (Real.exp_pos (-(γ * τ))) hq
  have hlt : ‖K ^ n‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hnorm n)) ?_
    calc Real.exp (γ * τ) * q ^ n < Real.exp (γ * τ) * Real.exp (-(γ * τ)) :=
          mul_lt_mul_of_pos_left hn (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hu : IsUnit (1 - K ^ n) := (Units.oneSub (K ^ n) hlt).isUnit
  rw [← mul_neg_geom_sum] at hu
  have hc : Commute (1 - K) (∑ i ∈ Finset.range n, K ^ i) :=
    Commute.sum_right _ _ _ fun i _ =>
      (Commute.one_left (K ^ i)).sub_left ((Commute.refl K).pow_right i)
  exact (hc.isUnit_mul_iff.1 hu).1

end Delay

end DataDrivenControl
