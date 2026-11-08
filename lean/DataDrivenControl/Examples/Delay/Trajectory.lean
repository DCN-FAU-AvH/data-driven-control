module

public import DataDrivenControl.Signal.Shift
public import DataDrivenControl.Signal.WeakDerivative

/-!
# Trajectories of delay equations in shifted time

Conventions and auxiliary facts for the delay system of `ex:intro-delay`.

* **Shifted time.**  The history lives on `(0, h]`: `ψ(s) = φ(s - h)` for the paper's history
  `φ` on `[-h, 0]`, so that the signal library's `L2`, `window` and `HasWeakDeriv` apply.  The
  trajectory `traj h ψ x σ` is `ψ σ` for `σ ≤ h` and `x (σ - h)` for `σ > h`; the history at time
  `t` is `x_t = window h (traj h ψ x) t`, and `x(t - δ) = traj h ψ x (h - δ + t)`.
* `traj` is linear (`traj_add`, `traj_smul`), only sees classes (`traj_ae_congr`,
  `traj_ae_congr_right`), restarts by translation (`traj_shift`), is square integrable
  (`memLp_traj_of_memLp`, `eLpNorm_traj_le`), and glues `H¹` functions (`hasWeakDeriv_traj_of`).
* `kernelOp h A_d`: the paper's distributed delay `∫_{-h}^0 A_d(θ) x(t + θ) dθ` with an `L²`
  kernel, as a bounded operator on the history (`kernelOp_apply`); `segOp h a w = ∫_{(a, h]} w`.
* Auxiliary facts on `L²(0, T)`: Cauchy–Schwarz (`integral_norm_le_sqrt_mul`,
  `norm_L2_le_of_ae_bound`), primitives (`continuousOn_primitive_Ioc`, `hasWeakDeriv_primitive`),
  translates of `H¹` signals (`hasWeakDeriv_comp_add`), windows at `0` (`window_zero_eq_toLp`).
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

/-! ### Auxiliary facts on `L²(0, T)` -/

/-- The window measure of a nonpositive horizon vanishes. -/
theorem μI_eq_zero {τ : ℝ} (hτ : τ ≤ 0) : μI τ = 0 := by
  simp [μI, Ioc_eq_empty (not_lt.2 hτ)]

/-- The total mass of the window `(0, T]`. -/
theorem measureUnivNNReal_μI {T : ℝ} (hT : 0 ≤ T) : (measureUnivNNReal (μI T) : ℝ) = T := by
  simp only [measureUnivNNReal, μI, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hT]

/-- `‖f‖_{L²(0, T)} ≤ √T c` when `‖f‖ ≤ c` a.e. -/
theorem norm_L2_le_of_ae_bound {G : Type*} [NormedAddCommGroup G] {T : ℝ} (hT : 0 ≤ T)
    (f : L2 G T) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ t ∂(μI T), ‖f t‖ ≤ c) : ‖f‖ ≤ √T * c := by
  refine (Lp.norm_le_of_ae_bound hc hf).trans_eq ?_
  rw [measureUnivNNReal_μI hT, Real.sqrt_eq_rpow]
  norm_num

/-- Cauchy–Schwarz on the window: `∫₀ᵗ ‖g‖ ≤ √t ‖g‖_{L²(0, t)}`. -/
theorem integral_norm_le_sqrt_mul {G : Type*} [NormedAddCommGroup G] {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → G} (hg : MemLp g 2 (μI t)) :
    ∫ s in Ioc 0 t, ‖g s‖ ≤ √t * (eLpNorm g 2 (μI t)).toReal := by
  have hint : Integrable g (μI t) := hg.integrable one_le_two
  rw [integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two
    hg.aestronglyMeasurable
  have hu : (μI t) univ = ENNReal.ofReal t := by simp [μI]
  have hexp : (1 / ENNReal.toReal 1 - 1 / ENNReal.toReal 2 : ℝ) = 1 / 2 := by norm_num
  rw [hu, hexp] at h1
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hg.eLpNorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)) h1).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal ht, ← Real.sqrt_eq_rpow,
    mul_comm]

/-- The representative of a finite sum in `L²`. -/
theorem coeFn_sum_L2 {G : Type*} [NormedAddCommGroup G] {T : ℝ} {ι : Type*} (s : Finset ι)
    (f : ι → L2 G T) : ⇑(∑ i ∈ s, f i) =ᵐ[μI T] fun t => ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero G 2 (μI T)] with t ht
    rw [Finset.sum_empty, Finset.sum_empty, ht]
    rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with t h1 h2
    rw [h1, Pi.add_apply, h2]

/-- Continuity of the primitive `t ↦ ∫₀ᵗ g` on `[0, τ]`. -/
theorem continuousOn_primitive_Ioc {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℝ → G} {τ : ℝ} (hg : IntegrableOn g (Ioc 0 τ)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · rw [Icc_eq_empty (not_le.2 hτ)]
    exact continuousOn_empty _
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := τ)
    (f := g) (by rw [uIcc_of_le hτ, integrableOn_Icc_iff_integrableOn_Ioc]; exact hg)
  rwa [uIcc_of_le hτ] at this

/-- Interval integrability on `[0, t] ⊆ [0, τ]` from integrability on `(0, τ]`. -/
theorem intervalIntegrable_of_integrableOn {G : Type*} [NormedAddCommGroup G]
    {g : ℝ → G} {τ t : ℝ} (hg : IntegrableOn g (Ioc 0 τ)) (ht : t ∈ Icc 0 τ) :
    IntervalIntegrable g volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hg.mono_set (Ioc_subset_Ioc_right ht.2))

/-- Interval integrability is preserved by bounded operators. -/
theorem intervalIntegrable_clm_comp (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) : IntervalIntegrable (fun t => L (f t)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

/-- Interval integrals over `[0, t] ⊆ [0, τ]` only see the class in `L²(0, τ)`. -/
theorem intervalIntegral_congr_μI {τ t : ℝ} {x₁ x₂ : ℝ → E} (hx : x₁ =ᵐ[μI τ] x₂)
    (ht : t ∈ Icc 0 τ) : ∫ s in (0 : ℝ)..t, x₁ s = ∫ s in (0 : ℝ)..t, x₂ s := by
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  exact setIntegral_congr_ae measurableSet_Ioc (by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hx
    filter_upwards [hx] with s hs hsI
    exact hs (Ioc_subset_Ioc_right ht.2 hsI))

/-- The primitive of a square-integrable signal is `H¹` with this signal as weak derivative. -/
theorem hasWeakDeriv_primitive {τ : ℝ} {y : ℝ → E} (hy : MemLp y 2 (μI τ)) :
    HasWeakDeriv τ (fun t => ∫ s in (0 : ℝ)..t, y s) y :=
  ⟨hy, fun t _ => by simp⟩

/-- Translates of `H¹` signals are `H¹`. -/
theorem hasWeakDeriv_comp_add {T₁ T t : ℝ} {z z' : ℝ → E} (hz : HasWeakDeriv T₁ z z')
    (ht : 0 ≤ t) (htT : t + T ≤ T₁) :
    HasWeakDeriv T (fun σ => z (t + σ)) (fun σ => z' (t + σ)) := by
  refine ⟨memLp_comp_add hz.memLp_deriv ht htT, fun σ hσ => ?_⟩
  have hi : IntegrableOn z' (Ioc 0 T₁) := hz.memLp_deriv.integrable one_le_two
  have h1 : t + σ ∈ Icc 0 T₁ := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have h2 : t ∈ Icc 0 T₁ := ⟨ht, by linarith [hσ.1, hσ.2]⟩
  show z (t + σ) = z (t + 0) + ∫ s in (0 : ℝ)..σ, z' (t + s)
  rw [add_zero, hz.eq_add_integral _ h1, hz.eq_add_integral _ h2, add_assoc,
    ← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (intervalIntegrable_of_integrableOn hi h2)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hσ.1])).2
        (hi.mono_set (Ioc_subset_Ioc ht h1.2))),
    intervalIntegral.integral_comp_add_left (fun s => z' s) t, add_zero]

/-- The integral form of `H¹` on an end segment: `g(h) - ∫_{(a, h]} g' = g(a)`. -/
theorem sub_integral_Ioc_of_hasWeakDeriv {h a : ℝ} {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (ha : a ∈ Icc 0 h) : g h - ∫ s in Ioc a h, g' s = g a := by
  have hi : IntegrableOn g' (Ioc 0 h) := hg.memLp_deriv.integrable one_le_two
  have hh : h ∈ Icc 0 h := ⟨ha.1.trans ha.2, le_rfl⟩
  rw [← intervalIntegral.integral_of_le ha.2, hg.eq_add_integral h hh, hg.eq_add_integral a ha,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (intervalIntegrable_of_integrableOn hi ha)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.2).2
        (hi.mono_set (Ioc_subset_Ioc ha.1 le_rfl)))]
  abel

/-- Continuous functions on `[0, a]` that agree a.e. on `(0, a]` agree on `[0, a]`. -/
theorem eqOn_Icc_of_ae {G : Type*} [NormedAddCommGroup G] {u w : ℝ → G} {a : ℝ} (ha : 0 < a)
    (hu : ContinuousOn u (Icc 0 a)) (hw : ContinuousOn w (Icc 0 a))
    (h : ∀ᵐ σ ∂(μI a), u σ = w σ) : EqOn u w (Icc 0 a) := by
  have h' : u =ᵐ[volume.restrict (Icc 0 a)] w := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    exact h
  exact Measure.eqOn_of_ae_eq h' hu hw (by simp [interior_Icc, closure_Ioo ha.ne])

/-- Averages of a continuous function converge: `t⁻¹ ∫₀ᵗ G → G 0` as `t → 0⁺`. -/
theorem tendsto_inv_smul_intervalIntegral {G : ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (hG : ContinuousOn G (Icc 0 δ)) :
    Tendsto (fun t => t⁻¹ • ∫ s in (0 : ℝ)..t, G s) (𝓝[>] 0) (𝓝 (G 0)) := by
  have hd : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, G s) (G 0) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (by simp)
      ⟨Ioc 0 δ, mem_of_superset (Ioo_mem_nhdsGT hδ) Ioo_subset_Ioc_self,
        (hG.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc⟩
      ((hG 0 ⟨le_rfl, hδ.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT hδ) Ioo_subset_Icc_self))
  have e : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, e] at hd
  refine hd.congr fun t => ?_
  rw [slope_def_module, intervalIntegral.integral_same, sub_zero, sub_zero]

/-! ### Windows -/

/-- The window at `0` of a square-integrable signal is its class. -/
theorem window_zero_eq_toLp {T : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T)) :
    window T f 0 = hf.toLp f := by
  have hm : MemLp (fun σ => f (0 + σ)) 2 (μI T) := by simpa only [zero_add] using hf
  rw [window_eq_toLp hm]
  exact MemLp.toLp_congr hm hf (ae_of_all _ fun σ => by simp only [zero_add])

/-- The window at `0` of an `L²` class is the class itself. -/
theorem window_coeFn_zero {T : ℝ} (w : L2 E T) : window T (⇑w) 0 = w := by
  rw [window_zero_eq_toLp (Lp.memLp w)]
  exact Lp.toLp_coeFn w (Lp.memLp w)

/-- Windows of a translate are translated windows. -/
theorem window_comp_add {T : ℝ} (f : ℝ → E) (s t : ℝ) :
    window T (fun σ => f (s + σ)) t = window T f (s + t) :=
  window_eq_of_ae (ae_of_all _ fun σ => by simp only [add_assoc])

/-! ### The paper's kernel form of the distributed delay -/

/-- For an `L²` kernel `A_d` and `w ∈ L²`, `s ↦ A_d(s) w(s)` is integrable (Hölder). -/
theorem memLp_kernel {h : ℝ} {Ad : ℝ → E →L[ℝ] E} (hA : MemLp Ad 2 (μI h)) (w : L2 E h) :
    MemLp (fun s => Ad s (w s)) 1 (μI h) :=
  MemLp.of_bilin (fun A v => A v) 1 hA (Lp.memLp w) (continuous_fst.clm_apply continuous_snd)
    (ae_of_all _ fun s => by simpa using (Ad s).le_opNNNorm (w s))

/-- The linear map `w ↦ ∫₀ʰ A_d(s) w(s) ds` of an `L²` kernel. -/
def kernelOpₗ {h : ℝ} {Ad : ℝ → E →L[ℝ] E} (hA : MemLp Ad 2 (μI h)) : L2 E h →ₗ[ℝ] E where
  toFun w := ∫ s in Ioc 0 h, Ad s (w s)
  map_add' w ψ := by
    rw [← integral_add (memLp_one_iff_integrable.1 (memLp_kernel hA w))
      (memLp_one_iff_integrable.1 (memLp_kernel hA ψ))]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add w ψ] with s hs
    rw [hs, Pi.add_apply, map_add]
  map_smul' c w := by
    rw [RingHom.id_apply, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c w] with s hs
    rw [hs, Pi.smul_apply, map_smul]

open scoped Classical in
/-- **The paper's distributed delay** `∫_{-h}^0 A_d(θ) x(t + θ) dθ` with a square-integrable
kernel, as a bounded operator on the history `L²(0, h; E)`: with `ψ(s) = x(t + s - h)` it is
`ψ ↦ ∫₀ʰ A_d(s - h) ψ(s) ds`, i.e. `kernelOp h (fun s => A_d (s - h))`.  (Junk value `0` when the
kernel is not square integrable.) -/
def kernelOp (h : ℝ) (Ad : ℝ → E →L[ℝ] E) : L2 E h →L[ℝ] E :=
  if hA : MemLp Ad 2 (μI h) then
    (kernelOpₗ hA).mkContinuous (eLpNorm Ad 2 (μI h)).toReal fun w => by
      have hm := memLp_kernel hA w
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable,
        ← eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable]
      have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
        (fun (A : E →L[ℝ] E) (v : E) => A v) 1 (continuous_fst.clm_apply continuous_snd)
        hA.aestronglyMeasurable (Lp.aestronglyMeasurable w)
        (ae_of_all _ fun s => by simpa using (Ad s).le_opNorm (w s))
      refine (ENNReal.toReal_mono (by
        simpa using ENNReal.mul_ne_top hA.eLpNorm_ne_top (Lp.eLpNorm_ne_top w)) this).trans_eq ?_
      rw [ENNReal.coe_one, one_mul, ENNReal.toReal_mul, Lp.norm_def]
  else 0

/-- `kernelOp h A_d w = ∫₀ʰ A_d(s) w(s) ds` for a square-integrable kernel (`ex:intro-delay`). -/
theorem kernelOp_apply {h : ℝ} {Ad : ℝ → E →L[ℝ] E} (hA : MemLp Ad 2 (μI h)) (w : L2 E h) :
    kernelOp h Ad w = ∫ s in Ioc 0 h, Ad s (w s) := by
  simp only [kernelOp, hA, dite_true, LinearMap.mkContinuous_apply]
  rfl

/-- The integral over the end segment `(a, h]` of the history, a bounded operator on `L²`. -/
def segOp (h a : ℝ) : L2 E h →L[ℝ] E :=
  kernelOp h ((Ioc a h).indicator fun _ => ContinuousLinearMap.id ℝ E)

/-- `segOp h a w = ∫_{(a, h]} w` for `0 ≤ a`. -/
theorem segOp_apply {h a : ℝ} (ha : 0 ≤ a) (w : L2 E h) : segOp h a w = ∫ s in Ioc a h, w s := by
  have hA : MemLp ((Ioc a h).indicator fun _ : ℝ => ContinuousLinearMap.id ℝ E) 2 (μI h) :=
    (memLp_const _).indicator measurableSet_Ioc.nullMeasurableSet
  rw [segOp, kernelOp_apply hA]
  have e : (fun s => ((Ioc a h).indicator (fun _ : ℝ => ContinuousLinearMap.id ℝ E) s) (w s)) =
      (Ioc a h).indicator (fun s => w s) := by
    funext s
    by_cases hs : s ∈ Ioc a h <;> simp [hs]
  rw [e, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (Ioc_subset_Ioc_left ha)]

/-! ### The trajectory in shifted time -/

/-- The **trajectory in shifted time** `σ = t + h`: the history `ψ` on `σ ≤ h` (that is, on
`(-h, 0]` in the paper's time) followed by the solution, `x (σ - h)` for `σ > h`.  The history
at time `t` is its window `(t, t + h]`, `window h (traj h ψ x) t` (`ψ(s) = φ(s - h)` in the
paper's notation `x_t(θ) = x(t + θ)`, `θ ∈ [-h, 0]`). -/
def traj (h : ℝ) (ψ x : ℝ → E) (σ : ℝ) : E := if σ ≤ h then ψ σ else x (σ - h)

/-- On the history, `σ ≤ h`, the trajectory is the history. -/
theorem traj_of_le {h σ : ℝ} (ψ x : ℝ → E) (hσ : σ ≤ h) : traj h ψ x σ = ψ σ := by simp [traj, hσ]

/-- After the history, `σ > h`, the trajectory is the solution, `x (σ - h)`. -/
theorem traj_of_lt {h σ : ℝ} (ψ x : ℝ → E) (hσ : h < σ) : traj h ψ x σ = x (σ - h) :=
  by simp [traj, not_le.2 hσ]

/-- The trajectory is additive in the history and the solution. -/
theorem traj_add (h : ℝ) (ψ₁ ψ₂ x₁ x₂ : ℝ → E) :
    traj h (ψ₁ + ψ₂) (x₁ + x₂) = traj h ψ₁ x₁ + traj h ψ₂ x₂ := by
  funext σ
  simp only [traj, Pi.add_apply]
  split_ifs <;> rfl

/-- The trajectory is homogeneous. -/
theorem traj_smul (h c : ℝ) (ψ x : ℝ → E) : traj h (c • ψ) (c • x) = c • traj h ψ x := by
  funext σ
  simp only [traj, Pi.smul_apply]
  split_ifs <;> rfl

/-- Restarting the trajectory at time `s ≥ 0`. -/
theorem traj_shift {h s : ℝ} (hs : 0 ≤ s) (ψ x : ℝ → E) :
    traj h (fun σ => traj h ψ x (s + σ)) (fun σ => x (s + σ)) = fun σ => traj h ψ x (s + σ) := by
  funext σ
  by_cases h1 : σ ≤ h
  · simp only [traj, h1, ite_true]
  · have h2 : ¬ s + σ ≤ h := fun h2 => h1 (by linarith)
    simp only [traj, h1, h2, ite_false]
    congr 1
    ring

/-- Changing the history on a null set changes the trajectory on a null set. -/
theorem traj_ae_congr {h : ℝ} {ψ₁ ψ₂ : ℝ → E} (hψ : ψ₁ =ᵐ[μI h] ψ₂) (x : ℝ → E) (T : ℝ) :
    traj h ψ₁ x =ᵐ[μI T] traj h ψ₂ x := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hψ ⊢
  filter_upwards [hψ] with σ hσ hσI
  unfold traj
  split_ifs with h1
  · exact hσ ⟨hσI.1, h1⟩
  · rfl

/-- The translation `σ ↦ σ - h` maps `(h, h + τ]` onto `(0, τ]`. -/
theorem measurePreserving_sub_Ioc (h τ : ℝ) :
    MeasurePreserving (fun σ => σ - h) (volume.restrict (Ioc h (h + τ))) (μI τ) := by
  have := (measurePreserving_sub_right volume h).restrict_preimage (s := Ioc 0 τ)
    measurableSet_Ioc
  rwa [preimage_sub_const_Ioc, zero_add, add_comm τ h] at this

/-- Changing the solution on a null set changes the trajectory on a null set. -/
theorem traj_ae_congr_right {h τ : ℝ} (ψ : ℝ → E) {x₁ x₂ : ℝ → E} (hx : x₁ =ᵐ[μI τ] x₂) :
    traj h ψ x₁ =ᵐ[μI (h + τ)] traj h ψ x₂ := by
  have hx' := (measurePreserving_sub_Ioc h τ).quasiMeasurePreserving.ae_eq_comp hx
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hx' ⊢
  filter_upwards [hx'] with σ hσ hσI
  unfold traj
  split_ifs with h1
  · rfl
  · exact hσ ⟨not_le.1 h1, hσI.2⟩

/-- `(0, h + τ] ∩ (-∞, h] = (0, h]`, as measures. -/
theorem restrict_Iic_μI {h τ : ℝ} (hτ : 0 ≤ τ) : (μI (h + τ)).restrict (Iic h) = μI h := by
  rw [Measure.restrict_restrict measurableSet_Iic]
  congr 1
  ext σ
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1, by linarith⟩

/-- `(0, h + τ] ∩ (h, ∞) = (h, h + τ]`, as measures. -/
theorem restrict_Ioi_μI {h τ : ℝ} (hh : 0 ≤ h) : (μI (h + τ)).restrict (Iic h)ᶜ =
    volume.restrict (Ioc h (h + τ)) := by
  rw [Measure.restrict_restrict measurableSet_Iic.compl]
  congr 1
  ext σ
  simp only [mem_inter_iff, mem_compl_iff, mem_Iic, not_le, mem_Ioc]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, h2⟩

/-- The trajectory of an `L²` history and an `L²` solution is square integrable on
`(0, h + τ]`. -/
theorem memLp_traj_of_memLp {h τ : ℝ} (hh : 0 ≤ h) (hτ : 0 ≤ τ) {ψ x : ℝ → E}
    (hψ : MemLp ψ 2 (μI h)) (hx : MemLp x 2 (μI τ)) : MemLp (traj h ψ x) 2 (μI (h + τ)) := by
  have e : traj h ψ x = (Iic h).piecewise ψ (fun σ => x (σ - h)) := by
    funext σ
    simp only [traj, Set.piecewise, mem_Iic]
  rw [e]
  refine MemLp.piecewise measurableSet_Iic.nullMeasurableSet ?_ ?_
  · rwa [restrict_Iic_μI hτ]
  · rw [restrict_Ioi_μI hh]
    exact hx.comp_measurePreserving (measurePreserving_sub_Ioc h τ)

/-- The trajectory of the history alone has the `L²` norm of the history. -/
theorem eLpNorm_traj_zero_right {h τ : ℝ} (hτ : 0 ≤ τ) (ψ : ℝ → E) :
    eLpNorm (traj h ψ 0) 2 (μI (h + τ)) = eLpNorm ψ 2 (μI h) := by
  have e : traj h ψ 0 = (Iic h).indicator ψ := by
    funext σ
    simp only [traj, Set.indicator, mem_Iic, Pi.zero_apply]
  rw [e, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.nullMeasurableSet,
    restrict_Iic_μI hτ]

/-- The trajectory of a solution with zero history has the `L²` norm of the solution. -/
theorem eLpNorm_traj_zero_left {h τ : ℝ} (hh : 0 ≤ h) {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    eLpNorm (traj h 0 x) 2 (μI (h + τ)) = eLpNorm x 2 (μI τ) := by
  have e : traj h 0 x = (Iic h)ᶜ.indicator (fun σ => x (σ - h)) := by
    funext σ
    simp only [traj, indicator, mem_compl_iff, mem_Iic, Pi.zero_apply]
    split_ifs <;> rfl
  rw [e, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.compl.nullMeasurableSet,
    restrict_Ioi_μI hh]
  exact eLpNorm_comp_measurePreserving hx.aestronglyMeasurable (measurePreserving_sub_Ioc h τ)

/-- The `L²` norm of a trajectory is at most the sum of those of the history and the solution. -/
theorem eLpNorm_traj_le {h τ : ℝ} (hh : 0 ≤ h) (hτ : 0 ≤ τ) {ψ x : ℝ → E}
    (hψ : MemLp ψ 2 (μI h)) (hx : MemLp x 2 (μI τ)) :
    (eLpNorm (traj h ψ x) 2 (μI (h + τ))).toReal ≤
      (eLpNorm ψ 2 (μI h)).toReal + (eLpNorm x 2 (μI τ)).toReal := by
  have e : traj h ψ x = traj h ψ 0 + traj h 0 x := by rw [← traj_add, add_zero, zero_add]
  have h1 := memLp_traj_of_memLp hh hτ hψ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI τ))
  have h2 := memLp_traj_of_memLp hh hτ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI h)) hx
  rw [e, ← eLpNorm_traj_zero_right hτ ψ, ← eLpNorm_traj_zero_left hh hx]
  rw [← ENNReal.toReal_add h1.eLpNorm_ne_top h2.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1.eLpNorm_ne_top, h2.eLpNorm_ne_top⟩)
    (eLpNorm_add_le one_le_two)

/-- **Gluing `H¹` functions**: an `H¹` history `g` followed by an `H¹` solution `X` with
`X 0 = g h` gives an `H¹` trajectory on `[0, h + τ]`, with derivative `g'` on the history and `y`
afterwards. -/
theorem hasWeakDeriv_traj_of {h τ : ℝ} (hh : 0 ≤ h) (hτ : 0 ≤ τ) {g g' X y : ℝ → E}
    (hg : HasWeakDeriv h g g') (hX : HasWeakDeriv τ X y) (h0 : X 0 = g h) :
    HasWeakDeriv (h + τ) (traj h g X) (traj h g' y) := by
  have hd : MemLp (traj h g' y) 2 (μI (h + τ)) :=
    memLp_traj_of_memLp hh hτ hg.memLp_deriv hX.memLp_deriv
  refine ⟨hd, fun σ hσ => ?_⟩
  have hdi : IntegrableOn (traj h g' y) (Ioc 0 (h + τ)) := hd.integrable one_le_two
  rw [traj_of_le g X hh]
  by_cases h1 : σ ≤ h
  · rw [traj_of_le _ _ h1, hg.eq_add_integral σ ⟨hσ.1, h1⟩]
    congr 1
    refine intervalIntegral.integral_congr fun ρ hρ => ?_
    rw [uIcc_of_le hσ.1] at hρ
    rw [traj_of_le _ _ (hρ.2.trans h1)]
  · have h1' : h < σ := not_le.1 h1
    have hhm : h ∈ Icc 0 (h + τ) := ⟨hh, by linarith⟩
    rw [traj_of_lt _ _ h1', hX.eq_add_integral (σ - h) ⟨by linarith, by linarith [hσ.2]⟩, h0,
      hg.eq_add_integral h ⟨hh, le_rfl⟩,
      ← intervalIntegral.integral_add_adjacent_intervals (b := h)
        (intervalIntegrable_of_integrableOn hdi hhm)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1'.le).2
          (hdi.mono_set (Ioc_subset_Ioc hh hσ.2))), add_assoc]
    congr 2
    · refine intervalIntegral.integral_congr fun ρ hρ => ?_
      rw [uIcc_of_le hh] at hρ
      rw [traj_of_le _ _ hρ.2]
    · have e2 : ∫ ρ in h..σ, traj h g' y ρ = ∫ ρ in h..σ, y (ρ - h) := by
        refine intervalIntegral.integral_congr_ae (ae_of_all _ fun ρ hρ => ?_)
        rw [uIoc_of_le h1'.le] at hρ
        rw [traj_of_lt _ _ hρ.1]
      rw [e2, intervalIntegral.integral_comp_sub_right y h, sub_self]

end Delay

end DataDrivenControl
