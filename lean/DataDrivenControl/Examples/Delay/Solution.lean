module

public import DataDrivenControl.Semigroup.Perturbation
public import DataDrivenControl.Signal.WeakDerivative

/-!
# The delay equation of `ex:intro-delay`: existence and uniqueness

The retarded equation with `M = 0`,

`ẋ(t) = ∑ₖ Aₖ x(t - hₖ) + L_d x_t + f(t)`,  `x(0) = r`,  `x_0 = φ`,

with finitely many point delays `hₖ ∈ [0, h]`, a distributed part `L_d` bounded on the `L²`
history, square-integrable history and locally integrable forcing.

## Conventions

* **Shifted time.**  The history lives on `(0, h]`: `ψ(s) = φ(s - h)`, so that the signal library's `L2`,
  `window` and `HasWeakDeriv` apply.  The *trajectory* `traj h ψ x σ` is `ψ σ` for `σ ≤ h` and
  `x (σ - h)` for `σ > h`; the history at time `t` is `x_t = window h (traj h ψ x) t`, and
  `x(t - hₖ) = traj h ψ x (h - hₖ + t)`.
* `Delay.Equation h E` packages `h`, the `Aₖ`, the `hₖ` and `L_d : L²(0, h; E) →L E`.  The
  paper's kernel form `∫_{-h}^0 A_d(θ) x(t + θ) dθ` with `A_d ∈ L²` is `Delay.kernelOp`
  (`kernelOp_apply`).
* `d.rhs z s = ∑ₖ Aₖ z(h - hₖ + s) + L_d (window h z s)` is the right-hand side `L x_s` evaluated
  on a trajectory `z`.
* `d.IsSolOn τ r ψ f x`: `x` continuous on `[0, τ]` and
  `x t = r + ∫₀ᵗ (L x_s + f s) ds` there (integral form).

## Main results

* `Equation.sol r ψ f`: the solution, `∑ₙ (xₙ₊₁ - xₙ)` for the Picard iterates `Equation.picard`
  (Volterra iteration with `Kⁿ tⁿ / n!` bounds, `norm_picard_sub_le`, as for
  `C0Semigroup.dysonPhillips`); **existence** `isSolOn_sol` and **uniqueness** `IsSolOn.eqOn`,
  `eqOn_sol` (`IsSolOn.eq_zero`, the analogue of `C0Semigroup.eq_zero_of_volterra`).
* Linearity: `IsSolOn.add`, `IsSolOn.smul`, `IsSolOn.sub`, `sol_add`, `sol_smul`; dependence on
  classes only: `IsSolOn.congr_hist`, `IsSolOn.congr_forcing`, `sol_congr_hist`,
  `sol_congr_forcing`; causality `IsSolOn.congr`, `traj_eqOn`.
* Time shift: `IsSolOn.shift`, `sol_add_time` (`x(s + t) = x(t; x(s), x_s, f(s + ·))`).
* Grönwall-type bound `norm_sol_le`:
  `‖x(t)‖ ≤ (‖r‖ + Kψ(τ) ‖ψ‖ + ∫₀^τ ‖f‖) e^{K τ}` with `K = ∑ₖ ‖Aₖ‖ + ‖L_d‖ √h`.
* The history lies in `L²`: `memLp_traj`, `memLp_traj_window`, `norm_window_traj_le`
  (`‖x_t‖ ≤ ‖ψ‖ + √h sup ‖x‖`), and is continuous in `t` (`continuousOn_window`).
* Regularity `hasWeakDeriv_traj`: for an `H¹` history `g` with `g h = r` and `L²` forcing, the
  trajectory is `H¹` on `[0, h + τ]` with derivative `traj h g' (L x_· + f)`.
-/
@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace Nat

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Auxiliary lemmas on windows and `L²` norms -/

/-- The exponential series `∑ xⁿ / n! = eˣ`. -/
theorem hasSum_pow_div_factorial_exp (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / n !) (Real.exp x) :=
  Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp x

/-- The total mass of the window `(0, T]`. -/
theorem measureUnivNNReal_μI {T : ℝ} (hT : 0 ≤ T) : (measureUnivNNReal (μI T) : ℝ) = T := by
  simp only [measureUnivNNReal, μI, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hT]

/-- `‖window T f s‖ ≤ √T c` when `‖f‖ ≤ c` on the window `(s, s + T]`.  No measurability is
needed: the window is `0` when the translate is not square integrable. -/
theorem norm_window_le_of_forall {T s c : ℝ} {f : ℝ → E} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hf : ∀ σ ∈ Ioc 0 T, ‖f (s + σ)‖ ≤ c) : ‖window T f s‖ ≤ √T * c := by
  by_cases hm : MemLp (fun σ => f (s + σ)) 2 (μI T)
  · rw [window_eq_toLp hm]
    have hb : ∀ᵐ σ ∂(μI T), ‖(hm.toLp _ : L2 E T) σ‖ ≤ c := by
      filter_upwards [hm.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with σ h1 h2
      rw [h1]
      exact hf σ h2
    refine (Lp.norm_le_of_ae_bound hc hb).trans_eq ?_
    rw [measureUnivNNReal_μI hT, Real.sqrt_eq_rpow]
    norm_num
  · simp only [window, hm, dite_false, norm_zero]
    positivity

/-- A function continuous on `[a, b]` is in every `Lᵖ` of `(a, b]`. -/
theorem memLp_Ioc_of_continuousOn {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {a b : ℝ}
    {p : ℝ≥0∞} (hf : ContinuousOn f (Icc a b)) : MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hC t (Ioc_subset_Icc_self ht))

/-- Continuity of the primitive `t ↦ ∫₀ᵗ g` on `[0, τ]`. -/
theorem continuousOn_primitive_Ioc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} {τ : ℝ} (hg : IntegrableOn g (Ioc 0 τ)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · rw [Icc_eq_empty (not_le.2 hτ)]
    exact continuousOn_empty _
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := τ)
    (f := g) (by rw [uIcc_of_le hτ, integrableOn_Icc_iff_integrableOn_Ioc]; exact hg)
  rwa [uIcc_of_le hτ] at this

/-- Interval integrability on `[0, t] ⊆ [0, τ]` from integrability on `(0, τ]`. -/
theorem intervalIntegrable_of_integrableOn {F : Type*} [NormedAddCommGroup F]
    {g : ℝ → F} {τ t : ℝ} (hg : IntegrableOn g (Ioc 0 τ)) (ht : t ∈ Icc 0 τ) :
    IntervalIntegrable g volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hg.mono_set (Ioc_subset_Ioc_right ht.2))

/-- Cauchy–Schwarz on the window: `∫₀ᵗ ‖g‖ ≤ √t ‖g‖_{L²(0, t)}`. -/
theorem integral_norm_le_sqrt_mul {F : Type*} [NormedAddCommGroup F] {t : ℝ} (ht : 0 ≤ t)
    {g : ℝ → F} (hg : MemLp g 2 (μI t)) :
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

/-- The trajectory of a difference. -/
theorem traj_sub (h : ℝ) (ψ₁ ψ₂ x₁ x₂ : ℝ → E) :
    traj h (ψ₁ - ψ₂) (x₁ - x₂) = traj h ψ₁ x₁ - traj h ψ₂ x₂ := by
  funext σ
  simp only [traj, Pi.sub_apply]
  split_ifs <;> rfl

/-- The trajectory is homogeneous. -/
theorem traj_smul (h c : ℝ) (ψ x : ℝ → E) : traj h (c • ψ) (c • x) = c • traj h ψ x := by
  funext σ
  simp only [traj, Pi.smul_apply]
  split_ifs <;> rfl

/-- The trajectory of zero data vanishes. -/
theorem traj_zero (h : ℝ) : traj h (0 : ℝ → E) 0 = 0 := by
  funext σ
  simp only [traj, Pi.zero_apply]
  split_ifs <;> rfl

/-- The trajectory only sees `x` on `[0, ∞)`. -/
theorem traj_congr_right {h : ℝ} (ψ : ℝ → E) {x y : ℝ → E} (hxy : ∀ t, 0 ≤ t → x t = y t) :
    traj h ψ x = traj h ψ y := by
  funext σ
  unfold traj
  split_ifs with h1
  · rfl
  · exact hxy _ (by linarith [not_le.1 h1])

/-- The trajectory up to `h + τ` only sees `x` on `[0, τ]`. -/
theorem traj_eqOn {h τ : ℝ} (ψ : ℝ → E) {x y : ℝ → E} (hxy : EqOn x y (Icc 0 τ)) :
    EqOn (traj h ψ x) (traj h ψ y) (Iic (h + τ)) := by
  intro σ hσ
  unfold traj
  split_ifs with h1
  · rfl
  · exact hxy ⟨by linarith [not_le.1 h1], by linarith [mem_Iic.1 hσ]⟩

/-- Changing the history on a null set changes the trajectory on a null set. -/
theorem traj_ae_congr {h : ℝ} {ψ₁ ψ₂ : ℝ → E} (hψ : ψ₁ =ᵐ[μI h] ψ₂) (x : ℝ → E) (T : ℝ) :
    traj h ψ₁ x =ᵐ[μI T] traj h ψ₂ x := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hψ ⊢
  filter_upwards [hψ] with σ hσ hσI
  unfold traj
  split_ifs with h1
  · exact hσ ⟨hσI.1, h1⟩
  · rfl

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

/-- The trajectory of an `L²` history and a solution continuous on `[0, τ]` is square integrable
on `(0, h + τ]`. -/
theorem memLp_traj {h τ : ℝ} (hh : 0 ≤ h) (hτ : 0 ≤ τ) {ψ x : ℝ → E} (hψ : MemLp ψ 2 (μI h))
    (hx : ContinuousOn x (Icc 0 τ)) : MemLp (traj h ψ x) 2 (μI (h + τ)) := by
  have e : traj h ψ x = (Iic h).piecewise ψ (fun σ => x (σ - h)) := by
    funext σ
    simp only [traj, Set.piecewise, mem_Iic]
  rw [e]
  refine MemLp.piecewise measurableSet_Iic.nullMeasurableSet ?_ ?_
  · rwa [restrict_Iic_μI hτ]
  · rw [restrict_Ioi_μI hh]
    exact memLp_Ioc_of_continuousOn (hx.comp (f := fun σ => σ - h) (by fun_prop)
      fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)

/-- `‖traj h 0 y σ‖ ≤ c` up to `σ ≤ h + s` when `‖y‖ ≤ c` on `[0, s]`. -/
theorem norm_traj_zero_le {h : ℝ} {y : ℝ → E} {s c σ : ℝ} (hc : 0 ≤ c)
    (hy : ∀ ρ ∈ Icc 0 s, ‖y ρ‖ ≤ c) (hσ : σ ≤ h + s) : ‖traj h 0 y σ‖ ≤ c := by
  by_cases h1 : σ ≤ h
  · rw [traj_of_le _ _ h1]
    simpa using hc
  · rw [traj_of_lt _ _ (not_le.1 h1)]
    exact hy _ ⟨by linarith [not_le.1 h1], by linarith⟩

/-- The windows `(s, s + h]` of a trajectory are square integrable. -/
theorem memLp_traj_window {h τ s : ℝ} (hh : 0 ≤ h) {ψ x : ℝ → E} (hψ : MemLp ψ 2 (μI h))
    (hx : ContinuousOn x (Icc 0 τ)) (hs : s ∈ Icc 0 τ) :
    MemLp (fun σ => traj h ψ x (s + σ)) 2 (μI h) :=
  memLp_comp_add (memLp_traj hh (hs.1.trans hs.2) hψ hx) hs.1 (by linarith [hs.2])

/-! ### The equation -/

/-- **Data of a retarded delay equation** (`ex:intro-delay` with `M = 0`):
`ẋ(t) = ∑ₖ Aₖ x(t - hₖ) + L_d x_t + f(t)`, with finitely many point delays `hₖ ∈ [0, h]` and a
distributed part `L_d`, a bounded operator on the `L²` history.  The paper's kernel form
`∫_{-h}^0 A_d(θ) x(t + θ) dθ` with `A_d ∈ L²` is `kernelOp`. -/
structure Equation (h : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The maximal delay is positive. -/
  h_pos : 0 < h
  /-- The number of point delays. -/
  N : ℕ
  /-- The coefficients `Aₖ` of the point delays. -/
  A : Fin N → E →L[ℝ] E
  /-- The point delays `hₖ`. -/
  τ : Fin N → ℝ
  /-- The point delays lie in `[0, h]`. -/
  τ_mem : ∀ k, τ k ∈ Icc 0 h
  /-- The distributed part `L_d`, acting on the history in `L²(0, h; E)`. -/
  Ad : L2 E h →L[ℝ] E

namespace Equation

variable {h : ℝ} (d : Equation h E)

/-- The right-hand side `L x_s = ∑ₖ Aₖ x(s - hₖ) + L_d x_s` at time `s`, evaluated on a trajectory
`z` in shifted time (`z = traj h ψ x`, so `x(s - hₖ) = z(h - hₖ + s)` and `x_s = z(s + ·)`). -/
def rhs (z : ℝ → E) (s : ℝ) : E := ∑ k, d.A k (z (h - d.τ k + s)) + d.Ad (window h z s)

/-- The Lipschitz constant of the right-hand side in the sup norm, `∑ₖ ‖Aₖ‖ + ‖L_d‖ √h`. -/
def K : ℝ := ∑ k, ‖d.A k‖ + ‖d.Ad‖ * √h

/-- The Lipschitz constant `K` is nonnegative. -/
theorem K_nonneg : 0 ≤ d.K := by
  unfold K
  positivity

/-- `h - hₖ ≥ 0`. -/
theorem sub_τ_nonneg (k : Fin d.N) : 0 ≤ h - d.τ k := by linarith [(d.τ_mem k).2]

/-- `h - hₖ ≤ h`. -/
theorem sub_τ_le (k : Fin d.N) : h - d.τ k ≤ h := by linarith [(d.τ_mem k).1]

/-- The right-hand side is additive on square-integrable windows. -/
theorem rhs_add {z₁ z₂ : ℝ → E} {s : ℝ} (h₁ : MemLp (fun σ => z₁ (s + σ)) 2 (μI h))
    (h₂ : MemLp (fun σ => z₂ (s + σ)) 2 (μI h)) :
    d.rhs (z₁ + z₂) s = d.rhs z₁ s + d.rhs z₂ s := by
  simp only [rhs, window_add_of_memLp h₁ h₂, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

/-- The right-hand side of a difference. -/
theorem rhs_sub {z₁ z₂ : ℝ → E} {s : ℝ} (h₁ : MemLp (fun σ => z₁ (s + σ)) 2 (μI h))
    (h₂ : MemLp (fun σ => z₂ (s + σ)) 2 (μI h)) :
    d.rhs (z₁ - z₂) s = d.rhs z₁ s - d.rhs z₂ s := by
  simp only [rhs, window_sub_of_memLp h₁ h₂, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
  abel

/-- The right-hand side is homogeneous. -/
theorem rhs_smul (c : ℝ) (z : ℝ → E) (s : ℝ) : d.rhs (c • z) s = c • d.rhs z s := by
  simp only [rhs, window_smul, Pi.smul_apply, map_smul, Finset.smul_sum, smul_add]

/-- The right-hand side of the zero trajectory vanishes. -/
@[simp] theorem rhs_zero (s : ℝ) : d.rhs 0 s = 0 := by simp [rhs]

/-- Translating the trajectory translates the right-hand side. -/
theorem rhs_shift (z : ℝ → E) (s σ : ℝ) : d.rhs (fun ρ => z (s + ρ)) σ = d.rhs z (s + σ) := by
  have hw : window h (fun ρ => z (s + ρ)) σ = window h z (s + σ) :=
    window_eq_of_ae (ae_of_all _ fun ρ => by simp only [add_assoc])
  simp only [rhs, hw]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring

/-- The sup-norm bound `‖L (traj h 0 y)_s‖ ≤ K sup_{[0, s]} ‖y‖`. -/
theorem norm_rhs_traj_zero_le {y : ℝ → E} {s c : ℝ} (hc : 0 ≤ c)
    (hy : ∀ ρ ∈ Icc 0 s, ‖y ρ‖ ≤ c) : ‖d.rhs (traj h 0 y) s‖ ≤ d.K * c := by
  have h1 : ∀ k, ‖d.A k (traj h 0 y (h - d.τ k + s))‖ ≤ ‖d.A k‖ * c := fun k =>
    (d.A k).le_opNorm_of_le (norm_traj_zero_le hc hy (by linarith [d.sub_τ_le k]))
  have h2 : ‖d.Ad (window h (traj h 0 y) s)‖ ≤ ‖d.Ad‖ * (√h * c) :=
    d.Ad.le_opNorm_of_le (norm_window_le_of_forall d.h_pos.le hc fun σ hσ =>
      norm_traj_zero_le hc hy (by linarith [hσ.2]))
  calc ‖d.rhs (traj h 0 y) s‖
      ≤ ∑ k, ‖d.A k (traj h 0 y (h - d.τ k + s))‖ + ‖d.Ad (window h (traj h 0 y) s)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sum_le _ _) _)
    _ ≤ ∑ k, ‖d.A k‖ * c + ‖d.Ad‖ * (√h * c) :=
        add_le_add (Finset.sum_le_sum fun k _ => h1 k) h2
    _ = d.K * c := by
        simp only [K, add_mul, Finset.sum_mul]
        ring

/-- The right-hand side of an `L²` trajectory is integrable. -/
theorem integrableOn_rhs {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    IntegrableOn (d.rhs z) (Ioc 0 τ) := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d.N)),
      Integrable (fun s => d.A k (z (h - d.τ k + s))) (μI τ) :=
    fun k _ => (d.A k).integrable_comp
      ((memLp_comp_add hz (d.sub_τ_nonneg k) (by linarith [d.sub_τ_le k])).integrable one_le_two)
  have h2 : IntegrableOn (fun s => d.Ad (window h z s)) (Ioc 0 τ) :=
    ((d.Ad.continuous.comp_continuousOn (continuousOn_window hz)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  exact (integrable_finsetSum _ h1).add h2

/-- The right-hand side of a continuous trajectory is continuous. -/
theorem continuousOn_rhs {z : ℝ → E} {τ : ℝ} (hz : ContinuousOn z (Icc 0 (h + τ))) :
    ContinuousOn (d.rhs z) (Icc 0 τ) := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d.N)),
      ContinuousOn (fun s => d.A k (z (h - d.τ k + s))) (Icc 0 τ) := fun k _ =>
    (d.A k).continuous.comp_continuousOn (hz.comp (f := fun s => h - d.τ k + s) (by fun_prop)
      fun s hs => ⟨by linarith [hs.1, d.sub_τ_nonneg k], by linarith [hs.2, d.sub_τ_le k]⟩)
  have h2 := d.Ad.continuous.comp_continuousOn
    (continuousOn_window (T := h) (T' := τ) (memLp_μI_of_continuousOn hz))
  exact (continuousOn_finsetSum _ h1).add h2

/-- Trajectories that agree a.e. on `(0, h + τ]` have right-hand sides that agree a.e. on
`(0, τ]`. -/
theorem ae_rhs_eq {z₁ z₂ : ℝ → E} {τ : ℝ} (hz : z₁ =ᵐ[μI (h + τ)] z₂) :
    ∀ᵐ s ∂(μI τ), d.rhs z₁ s = d.rhs z₂ s := by
  have hk : ∀ᵐ s ∂(μI τ), ∀ k, z₁ (h - d.τ k + s) = z₂ (h - d.τ k + s) :=
    ae_all_iff.2 fun k => ae_comp_add hz (d.sub_τ_nonneg k) (by linarith [d.sub_τ_le k])
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  simp only [rhs, hs, window_congr_ae (T := h) hz hsI.1.le (by linarith [hsI.2])]

/-! ### Solutions -/

/-- `x` solves the delay equation on `[0, τ]` with initial value `r`, history `ψ` and forcing `f`
(integral form): `x` is continuous on `[0, τ]` and `x t = r + ∫₀ᵗ (L x_s + f s) ds`. -/
def IsSolOn (τ : ℝ) (r : E) (ψ f x : ℝ → E) : Prop :=
  ContinuousOn x (Icc 0 τ) ∧
    ∀ t ∈ Icc 0 τ, x t = r + ∫ s in (0 : ℝ)..t, (d.rhs (traj h ψ x) s + f s)

variable {d}

/-- A solution on `[0, τ]` is a solution on every `[0, τ']`, `τ' ≤ τ`. -/
theorem IsSolOn.mono {τ τ' : ℝ} {r : E} {ψ f x : ℝ → E} (hx : d.IsSolOn τ r ψ f x)
    (hτ : τ' ≤ τ) : d.IsSolOn τ' r ψ f x :=
  ⟨hx.1.mono (Icc_subset_Icc_right hτ), fun t ht => hx.2 t ⟨ht.1, ht.2.trans hτ⟩⟩

variable (d)


/-- Additivity of `L` along trajectories of `L²` histories and continuous solutions. -/
theorem rhs_traj_add {τ s : ℝ} {ψ₁ ψ₂ x₁ x₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h))
    (hψ₂ : MemLp ψ₂ 2 (μI h)) (hx₁ : ContinuousOn x₁ (Icc 0 τ))
    (hx₂ : ContinuousOn x₂ (Icc 0 τ)) (hs : s ∈ Icc 0 τ) :
    d.rhs (traj h ψ₁ x₁) s + d.rhs (traj h ψ₂ x₂) s = d.rhs (traj h (ψ₁ + ψ₂) (x₁ + x₂)) s := by
  rw [traj_add, d.rhs_add (memLp_traj_window d.h_pos.le hψ₁ hx₁ hs)
    (memLp_traj_window d.h_pos.le hψ₂ hx₂ hs)]

/-- `L` of a difference of trajectories. -/
theorem rhs_traj_sub {τ s : ℝ} {ψ₁ ψ₂ x₁ x₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h))
    (hψ₂ : MemLp ψ₂ 2 (μI h)) (hx₁ : ContinuousOn x₁ (Icc 0 τ))
    (hx₂ : ContinuousOn x₂ (Icc 0 τ)) (hs : s ∈ Icc 0 τ) :
    d.rhs (traj h ψ₁ x₁) s - d.rhs (traj h ψ₂ x₂) s = d.rhs (traj h (ψ₁ - ψ₂) (x₁ - x₂)) s := by
  rw [traj_sub, d.rhs_sub (memLp_traj_window d.h_pos.le hψ₁ hx₁ hs)
    (memLp_traj_window d.h_pos.le hψ₂ hx₂ hs)]

/-- The integrand `L x_s + f s` of a continuous `x` is integrable on `(0, τ]`. -/
theorem integrableOn_integrand {τ : ℝ} (hτ : 0 ≤ τ) {ψ f x : ℝ → E} (hψ : MemLp ψ 2 (μI h))
    (hf : IntegrableOn f (Ioc 0 τ)) (hx : ContinuousOn x (Icc 0 τ)) :
    IntegrableOn (fun s => d.rhs (traj h ψ x) s + f s) (Ioc 0 τ) :=
  (d.integrableOn_rhs (memLp_traj d.h_pos.le hτ hψ hx)).add hf

variable {d}

/-- Superposition. -/
theorem IsSolOn.add {τ : ℝ} {r₁ r₂ : E} {ψ₁ ψ₂ f₁ f₂ x₁ x₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h))
    (hψ₂ : MemLp ψ₂ 2 (μI h)) (hf₁ : IntegrableOn f₁ (Ioc 0 τ)) (hf₂ : IntegrableOn f₂ (Ioc 0 τ))
    (hx₁ : d.IsSolOn τ r₁ ψ₁ f₁ x₁) (hx₂ : d.IsSolOn τ r₂ ψ₂ f₂ x₂) :
    d.IsSolOn τ (r₁ + r₂) (ψ₁ + ψ₂) (f₁ + f₂) (x₁ + x₂) := by
  refine ⟨hx₁.1.add hx₂.1, fun t ht => ?_⟩
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have i₁ := intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ₁ hf₁ hx₁.1) ht
  have i₂ := intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ₂ hf₂ hx₂.1) ht
  rw [Pi.add_apply, hx₁.2 t ht, hx₂.2 t ht, add_add_add_comm,
    ← intervalIntegral.integral_add i₁ i₂]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  have hs' : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [Pi.add_apply]
  rw [← d.rhs_traj_add hψ₁ hψ₂ hx₁.1 hx₂.1 hs']
  abel

/-- Homogeneity. -/
theorem IsSolOn.smul {τ : ℝ} {r : E} {ψ f x : ℝ → E} (hx : d.IsSolOn τ r ψ f x) (c : ℝ) :
    d.IsSolOn τ (c • r) (c • ψ) (c • f) (c • x) := by
  refine ⟨hx.1.const_smul c, fun t ht => ?_⟩
  rw [Pi.smul_apply, hx.2 t ht, smul_add, ← intervalIntegral.integral_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [traj_smul, d.rhs_smul, Pi.smul_apply, smul_add]

/-- Differences of solutions. -/
theorem IsSolOn.sub {τ : ℝ} {r₁ r₂ : E} {ψ₁ ψ₂ f₁ f₂ x₁ x₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h))
    (hψ₂ : MemLp ψ₂ 2 (μI h)) (hf₁ : IntegrableOn f₁ (Ioc 0 τ)) (hf₂ : IntegrableOn f₂ (Ioc 0 τ))
    (hx₁ : d.IsSolOn τ r₁ ψ₁ f₁ x₁) (hx₂ : d.IsSolOn τ r₂ ψ₂ f₂ x₂) :
    d.IsSolOn τ (r₁ - r₂) (ψ₁ - ψ₂) (f₁ - f₂) (x₁ - x₂) := by
  have := hx₁.add hψ₁ (hψ₂.const_smul (-1)) hf₁ (hf₂.smul (-1)) (hx₂.smul (-1))
  simpa only [neg_one_smul, ← sub_eq_add_neg] using this

/-- **Volterra uniqueness**: a solution with zero data vanishes. -/
theorem IsSolOn.eq_zero {τ : ℝ} {x : ℝ → E} (hx : d.IsSolOn τ 0 0 0 x) :
    ∀ t ∈ Icc 0 τ, x t = 0 := by
  obtain ⟨c, hc⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.1
  have key : ∀ k : ℕ, ∀ t ∈ Icc 0 τ, ‖x t‖ ≤ c * ((d.K * t) ^ k / k !) := by
    intro k
    induction k with
    | zero => intro t ht; simpa using hc t ht
    | succ k ih =>
      intro t ht
      have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc t ht)
      rw [hx.2 t ht, zero_add, intervalIntegral.integral_of_le ht.1]
      refine C0Semigroup.norm_integral_le_pow_div_factorial ht.1 k fun s hs => ?_
      simp only [Pi.zero_apply, add_zero]
      exact d.norm_rhs_traj_zero_le (mul_nonneg hc0 (div_nonneg
        (pow_nonneg (mul_nonneg d.K_nonneg hs.1.le) _) (by positivity))) fun ρ hρ =>
        (ih ρ ⟨hρ.1, hρ.2.trans (hs.2.trans ht.2)⟩).trans
          (C0Semigroup.mul_pow_div_factorial_mono d.K_nonneg hρ.1 hρ.2 hc0 k)
  intro t ht
  have hlim : Tendsto (fun k : ℕ => c * ((d.K * t) ^ k / k !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (d.K * t)).const_mul c
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim fun k => key k t ht)

/-- **Uniqueness** of solutions on `[0, τ]`. -/
theorem IsSolOn.eqOn {τ : ℝ} {r : E} {ψ f x y : ℝ → E} (hψ : MemLp ψ 2 (μI h))
    (hf : IntegrableOn f (Ioc 0 τ)) (hx : d.IsSolOn τ r ψ f x) (hy : d.IsSolOn τ r ψ f y) :
    EqOn x y (Icc 0 τ) := by
  have := hx.sub hψ hψ hf hf hy
  rw [sub_self, sub_self, sub_self] at this
  intro t ht
  exact sub_eq_zero.1 (this.eq_zero t ht)

/-! ### Existence: Picard iteration -/

variable (d)

/-- The **Picard iterates** `x₀ = 0`, `xₙ₊₁ t = r + ∫₀ᵗ (L (xₙ)_s + f s) ds`. -/
def picard (r : E) (ψ f : ℝ → E) : ℕ → ℝ → E
  | 0 => 0
  | n + 1 => fun t => r + ∫ s in (0 : ℝ)..t, (d.rhs (traj h ψ (picard r ψ f n)) s + f s)

/-- The zeroth Picard iterate is `0`. -/
theorem picard_zero (r : E) (ψ f : ℝ → E) : d.picard r ψ f 0 = 0 := rfl

/-- The Picard recursion, as an identity of functions. -/
theorem picard_succ' (r : E) (ψ f : ℝ → E) (n : ℕ) :
    d.picard r ψ f (n + 1) =
      fun t => r + ∫ s in (0 : ℝ)..t, (d.rhs (traj h ψ (d.picard r ψ f n)) s + f s) := rfl

/-- The Picard recursion `xₙ₊₁ t = r + ∫₀ᵗ (L (xₙ)_s + f s) ds`. -/
theorem picard_succ (r : E) (ψ f : ℝ → E) (n : ℕ) (t : ℝ) :
    d.picard r ψ f (n + 1) t =
      r + ∫ s in (0 : ℝ)..t, (d.rhs (traj h ψ (d.picard r ψ f n)) s + f s) := rfl

/-- The **solution** `x = ∑ₙ (xₙ₊₁ - xₙ)` of the delay equation (Volterra/Picard iteration with
`Kⁿ tⁿ / n!` bounds, as for `C0Semigroup.dysonPhillips`). -/
def sol (r : E) (ψ f : ℝ → E) (t : ℝ) : E :=
  ∑' n, (d.picard r ψ f (n + 1) t - d.picard r ψ f n t)

variable {r : E} {ψ f : ℝ → E}

/-- The Picard iterates are continuous on `[0, τ]`. -/
theorem continuousOn_picard (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ))
    (n : ℕ) : ContinuousOn (d.picard r ψ f n) (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · rw [Icc_eq_empty (not_le.2 hτ)]
    exact continuousOn_empty _
  induction n with
  | zero => exact continuous_zero.continuousOn
  | succ n ih =>
    rw [picard_succ']
    exact continuousOn_const.add (continuousOn_primitive_Ioc (d.integrableOn_integrand hτ hψ hf ih))

/-- Telescoping: `∑_{i < n} (xᵢ₊₁ - xᵢ) = xₙ`. -/
theorem sum_range_picard (n : ℕ) (t : ℝ) :
    ∑ i ∈ Finset.range n, (d.picard r ψ f (i + 1) t - d.picard r ψ f i t) = d.picard r ψ f n t :=
  (Finset.sum_range_sub (fun i => d.picard r ψ f i t) n).trans (by simp [picard_zero])

/-- The Volterra form of consecutive differences: `xₙ₊₂ - xₙ₊₁ = ∫₀ᵗ L (xₙ₊₁ - xₙ)_s ds`. -/
theorem picard_succ_sub (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ)) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    d.picard r ψ f (n + 1 + 1) t - d.picard r ψ f (n + 1) t =
      ∫ s in (0 : ℝ)..t, d.rhs (traj h 0 (d.picard r ψ f (n + 1) - d.picard r ψ f n)) s := by
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have c₁ := d.continuousOn_picard (r := r) hψ hf (n + 1)
  have c₀ := d.continuousOn_picard (r := r) hψ hf n
  rw [picard_succ, picard_succ, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
    (intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ hf c₁) ht)
    (intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ hf c₀) ht)]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  simp only [add_sub_add_right_eq_sub]
  rw [d.rhs_traj_sub hψ hψ c₁ c₀ ⟨hs.1, hs.2.trans ht.2⟩, sub_self]

/-- `‖xₙ₊₁ t - xₙ t‖ ≤ c (K t)ⁿ / n!` on `[0, τ]`, where `c` bounds `x₁` there. -/
theorem norm_picard_sub_le (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ))
    {c : ℝ} (hc : ∀ t ∈ Icc 0 τ, ‖d.picard r ψ f 1 t‖ ≤ c) (n : ℕ) :
    ∀ t ∈ Icc 0 τ, ‖d.picard r ψ f (n + 1) t - d.picard r ψ f n t‖ ≤ c * ((d.K * t) ^ n / n !) := by
  induction n with
  | zero => intro t ht; simpa [picard_zero] using hc t ht
  | succ n ih =>
    intro t ht
    have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc t ht)
    rw [d.picard_succ_sub hψ hf n ht, intervalIntegral.integral_of_le ht.1]
    refine C0Semigroup.norm_integral_le_pow_div_factorial ht.1 n fun s hs => ?_
    exact d.norm_rhs_traj_zero_le (mul_nonneg hc0 (div_nonneg
      (pow_nonneg (mul_nonneg d.K_nonneg hs.1.le) _) (by positivity))) fun ρ hρ =>
      (ih ρ ⟨hρ.1, hρ.2.trans (hs.2.trans ht.2)⟩).trans
        (C0Semigroup.mul_pow_div_factorial_mono d.K_nonneg hρ.1 hρ.2 hc0 n)

/-- The first Picard iterate is bounded on `[0, τ]`. -/
theorem exists_bound_picard_one (hψ : MemLp ψ 2 (μI h)) {τ : ℝ}
    (hf : IntegrableOn f (Ioc 0 τ)) : ∃ c, ∀ t ∈ Icc 0 τ, ‖d.picard r ψ f 1 t‖ ≤ c :=
  isCompact_Icc.exists_bound_of_continuousOn (d.continuousOn_picard hψ hf 1)

/-- The Picard series converges to `sol` at every `t ≥ 0`. -/
theorem hasSum_sol (hψ : MemLp ψ 2 (μI h)) {t : ℝ} (hf : IntegrableOn f (Ioc 0 t)) (ht : 0 ≤ t) :
    HasSum (fun n => d.picard r ψ f (n + 1) t - d.picard r ψ f n t) (d.sol r ψ f t) := by
  obtain ⟨c, hc⟩ := d.exists_bound_picard_one (r := r) hψ hf
  exact (((Real.summable_pow_div_factorial (d.K * t)).mul_left c).of_norm_bounded
    fun n => d.norm_picard_sub_le hψ hf hc n t ⟨ht, le_rfl⟩).hasSum

/-- The Picard iterates converge to `sol` pointwise on `[0, ∞)`. -/
theorem tendsto_picard (hψ : MemLp ψ 2 (μI h)) {t : ℝ} (hf : IntegrableOn f (Ioc 0 t))
    (ht : 0 ≤ t) : Tendsto (fun n => d.picard r ψ f n t) atTop (𝓝 (d.sol r ψ f t)) :=
  (d.hasSum_sol hψ hf ht).tendsto_sum_nat.congr fun n => d.sum_range_picard n t

/-- Uniform tail bound on `[0, τ]`. -/
theorem norm_sol_sub_picard_le (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ))
    {c : ℝ} (hc : ∀ t ∈ Icc 0 τ, ‖d.picard r ψ f 1 t‖ ≤ c) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖d.sol r ψ f t - d.picard r ψ f n t‖ ≤ ∑' k, c * ((d.K * τ) ^ (k + n) / (k + n)!) := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc t ht)
  have hs := (d.hasSum_sol (r := r) hψ (hf.mono_set (Ioc_subset_Ioc_right ht.2)) ht.1).summable
  have e := hs.sum_add_tsum_nat_add n
  rw [d.sum_range_picard] at e
  rw [sol, ← e, add_sub_cancel_left]
  have hb : Summable fun k => c * ((d.K * τ) ^ (k + n) / (k + n)!) :=
    (summable_nat_add_iff n).2 ((Real.summable_pow_div_factorial (d.K * τ)).mul_left c)
  refine tsum_of_norm_bounded hb.hasSum fun k => ?_
  exact (d.norm_picard_sub_le hψ hf hc (k + n) t ht).trans
    (C0Semigroup.mul_pow_div_factorial_mono d.K_nonneg ht.1 ht.2 hc0 _)

/-- The solution is continuous on `[0, τ]` (uniform convergence of the Picard series). -/
theorem continuousOn_sol (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ)) :
    ContinuousOn (d.sol r ψ f) (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · rw [Icc_eq_empty (not_le.2 hτ)]
    exact continuousOn_empty _
  obtain ⟨c, hc⟩ := d.exists_bound_picard_one (r := r) hψ hf
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 ⟨le_rfl, hτ⟩)
  refine continuousOn_tsum (fun n => (d.continuousOn_picard hψ hf (n + 1)).sub
    (d.continuousOn_picard hψ hf n)) ((Real.summable_pow_div_factorial (d.K * τ)).mul_left c)
    fun n t ht => ?_
  exact (d.norm_picard_sub_le hψ hf hc n t ht).trans
    (C0Semigroup.mul_pow_div_factorial_mono d.K_nonneg ht.1 ht.2 hc0 n)

/-- `x(0) = r`. -/
@[simp] theorem sol_zero_time (r : E) (ψ f : ℝ → E) : d.sol r ψ f 0 = r := by
  rw [sol, tsum_eq_single 0 fun n hn => ?_]
  · simp [picard_succ, picard_zero]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp [picard_succ]

/-- **Existence**: the Picard series solves the delay equation on every `[0, τ]`. -/
theorem isSolOn_sol (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ)) :
    d.IsSolOn τ r ψ f (d.sol r ψ f) := by
  refine ⟨d.continuousOn_sol hψ hf, fun t ht => ?_⟩
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  obtain ⟨c, hc⟩ := d.exists_bound_picard_one (r := r) hψ hf
  set ε : ℕ → ℝ := fun n => ∑' k, c * ((d.K * τ) ^ (k + n) / (k + n)!) with hε
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_sum_nat_add fun k => c * ((d.K * τ) ^ k / k !)
  have hft : IntegrableOn f (Ioc 0 t) := hf.mono_set (Ioc_subset_Ioc_right ht.2)
  have h1 : Tendsto (fun n => d.picard r ψ f (n + 1) t) atTop (𝓝 (d.sol r ψ f t)) :=
    (d.tendsto_picard hψ hft ht.1).comp (tendsto_add_atTop_nat 1)
  have hsc := d.continuousOn_sol (r := r) hψ hf
  have h2 : Tendsto (fun n => d.picard r ψ f (n + 1) t) atTop
      (𝓝 (r + ∫ s in (0 : ℝ)..t, (d.rhs (traj h ψ (d.sol r ψ f)) s + f s))) := by
    simp only [picard_succ]
    refine tendsto_const_nhds.add (f := fun _ => r) ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n => d.K * ε n * |t - 0|) atTop (𝓝 0) := by
      simpa using (hεlim.const_mul d.K).mul_const |t - 0|
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have cn := d.continuousOn_picard (r := r) hψ hf n
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ hf cn) ht)
      (intervalIntegrable_of_integrableOn (d.integrableOn_integrand hτ hψ hf hsc) ht)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le ht.1] at hs
    have hs' : s ∈ Icc 0 τ := ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [add_sub_add_right_eq_sub, d.rhs_traj_sub hψ hψ cn hsc hs', sub_self]
    refine d.norm_rhs_traj_zero_le (tsum_nonneg fun k => ?_) fun ρ hρ => ?_
    · have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc t ht)
      exact mul_nonneg hc0 (div_nonneg (pow_nonneg (mul_nonneg d.K_nonneg hτ) _) (by positivity))
    · rw [Pi.sub_apply, norm_sub_rev]
      exact d.norm_sol_sub_picard_le hψ hf hc n ⟨hρ.1, hρ.2.trans hs'.2⟩
  exact tendsto_nhds_unique h1 h2

/-- Every solution on `[0, τ]` is the Picard solution there. -/
theorem eqOn_sol (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ)) {x : ℝ → E}
    (hx : d.IsSolOn τ r ψ f x) : EqOn x (d.sol r ψ f) (Icc 0 τ) :=
  hx.eqOn hψ hf (d.isSolOn_sol hψ hf)

/-! ### Congruences, time shift, linearity -/

variable {d}

/-- Changing the history on a null set does not change the solutions. -/
theorem IsSolOn.congr_hist {τ : ℝ} {ψ₁ ψ₂ x : ℝ → E} (hψ : ψ₁ =ᵐ[μI h] ψ₂)
    (hx : d.IsSolOn τ r ψ₁ f x) : d.IsSolOn τ r ψ₂ f x := by
  refine ⟨hx.1, fun t ht => ?_⟩
  rw [hx.2 t ht]
  congr 1
  have hae := d.ae_rhs_eq (τ := τ) (traj_ae_congr hψ x (h + τ))
  rw [ae_restrict_iff' measurableSet_Ioc] at hae
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  rw [hs ⟨hsI.1, hsI.2.trans ht.2⟩]

/-- Changing the forcing on a null set does not change the solutions. -/
theorem IsSolOn.congr_forcing {τ : ℝ} {f₁ f₂ x : ℝ → E} (hf : ∀ᵐ s ∂(μI τ), f₁ s = f₂ s)
    (hx : d.IsSolOn τ r ψ f₁ x) : d.IsSolOn τ r ψ f₂ x := by
  refine ⟨hx.1, fun t ht => ?_⟩
  rw [hx.2 t ht]
  congr 1
  rw [ae_restrict_iff' measurableSet_Ioc] at hf
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  rw [hs ⟨hsI.1, hsI.2.trans ht.2⟩]

/-- A function equal to a solution on `[0, τ]` is a solution. -/
theorem IsSolOn.congr {τ : ℝ} {x y : ℝ → E} (hx : d.IsSolOn τ r ψ f x)
    (hxy : EqOn x y (Icc 0 τ)) : d.IsSolOn τ r ψ f y := by
  refine ⟨hx.1.congr hxy.symm, fun t ht => ?_⟩
  rw [← hxy ht, hx.2 t ht]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  have he := traj_eqOn (h := h) ψ hxy
  have hw : window h (traj h ψ x) s = window h (traj h ψ y) s :=
    window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      he (show s + σ ≤ h + τ by linarith [hσ.2, hs.2, ht.2]))
  simp only [rhs, hw]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he (show h - d.τ k + s ≤ h + τ by linarith [hs.2, ht.2, (d.τ_mem k).1])]

/-- **Time shift**: restarted at time `s`, a solution solves the equation with initial value
`x s`, history `x_s` and forcing `f (s + ·)`. -/
theorem IsSolOn.shift {s τ : ℝ} {x : ℝ → E} (hs : 0 ≤ s) (hψ : MemLp ψ 2 (μI h))
    (hf : IntegrableOn f (Ioc 0 (s + τ))) (hx : d.IsSolOn (s + τ) r ψ f x) :
    d.IsSolOn τ (x s) (fun σ => traj h ψ x (s + σ)) (fun σ => f (s + σ))
      (fun σ => x (s + σ)) := by
  refine ⟨hx.1.comp (f := fun σ => s + σ) (by fun_prop)
    fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun t ht => ?_⟩
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  have hint := d.integrableOn_integrand (add_nonneg hs hτ) hψ hf hx.1
  have hst : s + t ∈ Icc 0 (s + τ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs' : s ∈ Icc 0 (s + τ) := ⟨hs, by linarith⟩
  have i₂ : IntervalIntegrable (fun σ => d.rhs (traj h ψ x) σ + f σ) volume s (s + t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [ht.1])).2
      (hint.mono_set (Ioc_subset_Ioc hs hst.2))
  show x (s + t) = x s + _
  rw [hx.2 (s + t) hst, hx.2 s hs', add_assoc,
    ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_of_integrableOn hint hs')
      i₂]
  congr 2
  rw [traj_shift hs]
  simp only [d.rhs_shift]
  rw [intervalIntegral.integral_comp_add_left (fun σ => d.rhs (traj h ψ x) σ + f σ) s, add_zero]

/-- Integrability of the translated forcing. -/
theorem integrableOn_comp_add {g : ℝ → E} {s T : ℝ} (hs : 0 ≤ s)
    (hg : IntegrableOn g (Ioc 0 (s + T))) : IntegrableOn (fun σ => g (s + σ)) (Ioc 0 T) :=
  memLp_one_iff_integrable.1 (memLp_comp_add (memLp_one_iff_integrable.2 hg) hs le_rfl)

variable (d)

/-- **Uniqueness**, as an identity: `x(s + t) = x(t; x(s), x_s, f(s + ·))`. -/
theorem sol_add_time (hψ : MemLp ψ 2 (μI h)) (hf : ∀ τ, IntegrableOn f (Ioc 0 τ)) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    d.sol r ψ f (s + t) = d.sol (d.sol r ψ f s) (fun σ => traj h ψ (d.sol r ψ f) (s + σ))
      (fun σ => f (s + σ)) t := by
  have hx := (d.isSolOn_sol (r := r) hψ (hf (s + t))).shift hs hψ (hf _)
  exact d.eqOn_sol (memLp_traj_window d.h_pos.le hψ (d.continuousOn_sol hψ (hf s))
    ⟨hs, le_rfl⟩) (integrableOn_comp_add hs (hf _)) hx ⟨ht, le_rfl⟩

/-- Linearity of the solution map: additivity. -/
theorem sol_add {r₁ r₂ : E} {ψ₁ ψ₂ f₁ f₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h))
    (hψ₂ : MemLp ψ₂ 2 (μI h)) (hf₁ : ∀ τ, IntegrableOn f₁ (Ioc 0 τ))
    (hf₂ : ∀ τ, IntegrableOn f₂ (Ioc 0 τ)) {t : ℝ} (ht : 0 ≤ t) :
    d.sol (r₁ + r₂) (ψ₁ + ψ₂) (f₁ + f₂) t = d.sol r₁ ψ₁ f₁ t + d.sol r₂ ψ₂ f₂ t :=
  (d.eqOn_sol (hψ₁.add hψ₂) ((hf₁ t).add (hf₂ t)) ((d.isSolOn_sol hψ₁ (hf₁ t)).add hψ₁ hψ₂
    (hf₁ t) (hf₂ t) (d.isSolOn_sol hψ₂ (hf₂ t))) ⟨ht, le_rfl⟩).symm

/-- Linearity of the solution map: homogeneity. -/
theorem sol_smul (hψ : MemLp ψ 2 (μI h)) (hf : ∀ τ, IntegrableOn f (Ioc 0 τ)) (c : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : d.sol (c • r) (c • ψ) (c • f) t = c • d.sol r ψ f t :=
  (d.eqOn_sol (hψ.const_smul c) ((hf t).smul c) ((d.isSolOn_sol hψ (hf t)).smul c)
    ⟨ht, le_rfl⟩).symm

/-- The solution only depends on the class of the history in `L²`. -/
theorem sol_congr_hist {ψ₁ ψ₂ : ℝ → E} (hψ₁ : MemLp ψ₁ 2 (μI h)) (hψ : ψ₁ =ᵐ[μI h] ψ₂)
    (hf : ∀ τ, IntegrableOn f (Ioc 0 τ)) {t : ℝ} (ht : 0 ≤ t) :
    d.sol r ψ₁ f t = d.sol r ψ₂ f t :=
  d.eqOn_sol (hψ₁.ae_eq hψ) (hf t) ((d.isSolOn_sol hψ₁ (hf t)).congr_hist hψ) ⟨ht, le_rfl⟩

/-- The solution on `[0, t]` only depends on the forcing on `(0, t]`. -/
theorem sol_congr_forcing {f₁ f₂ : ℝ → E} (hψ : MemLp ψ 2 (μI h))
    (hf₁ : ∀ τ, IntegrableOn f₁ (Ioc 0 τ)) {t : ℝ} (hf : ∀ᵐ s ∂(μI t), f₁ s = f₂ s)
    (hf₂ : IntegrableOn f₂ (Ioc 0 t)) (ht : 0 ≤ t) :
    d.sol r ψ f₁ t = d.sol r ψ f₂ t :=
  d.eqOn_sol hψ hf₂ ((d.isSolOn_sol hψ (hf₁ t)).congr_forcing hf) ⟨ht, le_rfl⟩

/-! ### Regularity: `H¹` histories give `H¹` trajectories -/

/-- The right-hand side of an `L²` trajectory is square integrable. -/
theorem memLp_rhs {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    MemLp (d.rhs z) 2 (μI τ) := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin d.N)),
      MemLp (fun s => d.A k (z (h - d.τ k + s))) 2 (μI τ) :=
    fun k _ => (d.A k).comp_memLp'
      (memLp_comp_add hz (d.sub_τ_nonneg k) (by linarith [d.sub_τ_le k]))
  have h2 : MemLp (fun s => d.Ad (window h z s)) 2 (μI τ) :=
    memLp_μI_of_continuousOn (d.Ad.continuous.comp_continuousOn (continuousOn_window hz))
  exact (memLp_finsetSum _ h1).add h2

/-- **Regularity**: for an `H¹` history `g` with `g h = r` and an `L²` forcing, the trajectory
`traj h g x` is `H¹` on `[0, h + τ]`, with derivative `g'` on the history and `L x_s + f s`
afterwards. -/
theorem hasWeakDeriv_traj {τ : ℝ} (hτ : 0 ≤ τ) {g g' x : ℝ → E} (hg : HasWeakDeriv h g g')
    (hf : MemLp f 2 (μI τ)) (hx : d.IsSolOn τ (g h) g f x) :
    HasWeakDeriv (h + τ) (traj h g x) (traj h g' fun s => d.rhs (traj h g x) s + f s) := by
  have hgL : MemLp g 2 (μI h) := hg.memLp
  have hFm : MemLp (fun s => d.rhs (traj h g x) s + f s) 2 (μI τ) :=
    (d.memLp_rhs (memLp_traj d.h_pos.le hτ hgL hx.1)).add hf
  have hmp : MeasurePreserving (fun σ => σ - h) (volume.restrict (Ioc h (h + τ))) (μI τ) := by
    have := (measurePreserving_sub_right volume h).restrict_preimage (s := Ioc 0 τ)
      measurableSet_Ioc
    rwa [preimage_sub_const_Ioc, zero_add, add_comm τ h] at this
  have hd : MemLp (traj h g' fun s => d.rhs (traj h g x) s + f s) 2 (μI (h + τ)) := by
    have e : (traj h g' fun s => d.rhs (traj h g x) s + f s) =
        (Iic h).piecewise g' (fun σ => d.rhs (traj h g x) (σ - h) + f (σ - h)) := by
      funext σ
      simp only [traj, Set.piecewise, mem_Iic]
    rw [e]
    refine MemLp.piecewise measurableSet_Iic.nullMeasurableSet ?_ ?_
    · rw [restrict_Iic_μI hτ]
      exact hg.memLp_deriv
    · rw [restrict_Ioi_μI d.h_pos.le]
      exact hFm.comp_measurePreserving hmp
  refine ⟨hd, fun σ hσ => ?_⟩
  have hdi : IntegrableOn (traj h g' fun s => d.rhs (traj h g x) s + f s) (Ioc 0 (h + τ)) :=
    hd.integrable one_le_two
  rw [traj_of_le g x d.h_pos.le]
  by_cases h1 : σ ≤ h
  · rw [traj_of_le _ _ h1, hg.eq_add_integral σ ⟨hσ.1, h1⟩]
    congr 1
    refine intervalIntegral.integral_congr fun ρ hρ => ?_
    rw [uIcc_of_le hσ.1] at hρ
    rw [traj_of_le _ _ (hρ.2.trans h1)]
  · have h1' : h < σ := not_le.1 h1
    have hh : h ∈ Icc 0 (h + τ) := ⟨d.h_pos.le, by linarith⟩
    rw [traj_of_lt _ _ h1', hx.2 (σ - h) ⟨by linarith, by linarith [hσ.2]⟩,
      hg.eq_add_integral h ⟨d.h_pos.le, le_rfl⟩,
      ← intervalIntegral.integral_add_adjacent_intervals (b := h)
        (intervalIntegrable_of_integrableOn hdi hh)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le h1'.le).2
          (hdi.mono_set (Ioc_subset_Ioc d.h_pos.le hσ.2))), add_assoc]
    congr 2
    · refine intervalIntegral.integral_congr fun ρ hρ => ?_
      rw [uIcc_of_le d.h_pos.le] at hρ
      rw [traj_of_le _ _ hρ.2]
    · have e2 : ∫ ρ in h..σ, traj h g' (fun s => d.rhs (traj h g x) s + f s) ρ =
          ∫ ρ in h..σ, (d.rhs (traj h g x) (ρ - h) + f (ρ - h)) := by
        refine intervalIntegral.integral_congr_ae (ae_of_all _ fun ρ hρ => ?_)
        rw [uIoc_of_le h1'.le] at hρ
        rw [traj_of_lt _ _ hρ.1]
      rw [e2, intervalIntegral.integral_comp_sub_right
        (fun s => d.rhs (traj h g x) s + f s) h, sub_self]

/-! ### Bounds -/

/-- The constant `√τ ∑ₖ ‖Aₖ‖ + τ ‖L_d‖` of the history in the Grönwall bound. -/
def Kψ (τ : ℝ) : ℝ := √τ * ∑ k, ‖d.A k‖ + τ * ‖d.Ad‖

/-- The trajectory of the history alone has the `L²` norm of the history. -/
theorem eLpNorm_traj_zero {τ : ℝ} (hτ : 0 ≤ τ) (ψ : ℝ → E) :
    eLpNorm (traj h ψ 0) 2 (μI (h + τ)) = eLpNorm ψ 2 (μI h) := by
  have e : traj h ψ 0 = (Iic h).indicator ψ := by
    funext σ
    simp only [traj, Set.indicator, mem_Iic, Pi.zero_apply]
  rw [e, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.nullMeasurableSet,
    restrict_Iic_μI hτ]

/-- The first Picard iterate is bounded by the data. -/
theorem norm_picard_one_le (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ))
    {t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖d.picard r ψ f 1 t‖ ≤
      ‖r‖ + d.Kψ τ * (eLpNorm ψ 2 (μI h)).toReal + ∫ s in Ioc 0 τ, ‖f s‖ := by
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  set Ψ := (eLpNorm ψ 2 (μI h)).toReal with hΨ
  have hΨ0 : 0 ≤ Ψ := ENNReal.toReal_nonneg
  have hzt : MemLp (traj h ψ 0) 2 (μI (h + t)) :=
    memLp_traj d.h_pos.le ht.1 hψ continuous_zero.continuousOn
  have hzΨ : (eLpNorm (traj h ψ 0) 2 (μI (h + t))).toReal = Ψ := by
    rw [eLpNorm_traj_zero ht.1]
  have i1 : IntegrableOn (d.rhs (traj h ψ 0)) (Ioc 0 t) := d.integrableOn_rhs hzt
  have i2 : IntegrableOn f (Ioc 0 t) := hf.mono_set (Ioc_subset_Ioc_right ht.2)
  rw [picard_succ, picard_zero, intervalIntegral.integral_add
    (intervalIntegrable_of_integrableOn i1 ⟨ht.1, le_rfl⟩)
    (intervalIntegrable_of_integrableOn i2 ⟨ht.1, le_rfl⟩)]
  have b2 : ‖∫ s in (0 : ℝ)..t, f s‖ ≤ ∫ s in Ioc 0 τ, ‖f s‖ := by
    rw [intervalIntegral.integral_of_le ht.1]
    exact (norm_integral_le_integral_norm _).trans (setIntegral_mono_set hf.norm
      (ae_of_all _ fun _ => norm_nonneg _) (Ioc_subset_Ioc_right ht.2).eventuallyLE)
  have hk : ∀ k, MemLp (fun s => traj h ψ 0 (h - d.τ k + s)) 2 (μI t) := fun k =>
    memLp_comp_add hzt (d.sub_τ_nonneg k) (by linarith [d.sub_τ_le k])
  have hkb : ∀ k, ∫ s in Ioc 0 t, ‖traj h ψ 0 (h - d.τ k + s)‖ ≤ √t * Ψ := by
    intro k
    refine (integral_norm_le_sqrt_mul ht.1 (hk k)).trans
      (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    have := norm_window_le (T := t) hzt (d.sub_τ_nonneg k) (by linarith [d.sub_τ_le k])
    rwa [window_eq_toLp (hk k), Lp.norm_toLp, hzΨ] at this
  have hpt : ∀ s ∈ Ioc 0 t, ‖d.rhs (traj h ψ 0) s‖ ≤
      ∑ k, ‖d.A k‖ * ‖traj h ψ 0 (h - d.τ k + s)‖ + ‖d.Ad‖ * Ψ := by
    intro s hs
    refine (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun k _ => (d.A k).le_opNorm _)) ?_)
    refine (d.Ad.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [← hzΨ]
    exact norm_window_le hzt hs.1.le (by linarith [hs.2])
  have hint_k : ∀ k ∈ (Finset.univ : Finset (Fin d.N)),
      Integrable (fun s => ‖d.A k‖ * ‖traj h ψ 0 (h - d.τ k + s)‖) (μI t) :=
    fun k _ => ((hk k).integrable one_le_two).norm.const_mul _
  have b1 : ‖∫ s in (0 : ℝ)..t, d.rhs (traj h ψ 0) s‖ ≤ d.Kψ τ * Ψ := by
    rw [intervalIntegral.integral_of_le ht.1]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_on (g := fun s =>
      ∑ k, ‖d.A k‖ * ‖traj h ψ 0 (h - d.τ k + s)‖ + ‖d.Ad‖ * Ψ) i1.norm
      ((integrable_finsetSum _ hint_k).add (integrable_const _)) measurableSet_Ioc hpt).trans ?_
    rw [integral_add (integrable_finsetSum _ hint_k) (integrable_const _),
      integral_finsetSum _ hint_k, setIntegral_const, Real.volume_real_Ioc_of_le ht.1, sub_zero,
      smul_eq_mul]
    simp only [integral_const_mul]
    calc ∑ k, ‖d.A k‖ * (∫ s in Ioc 0 t, ‖traj h ψ 0 (h - d.τ k + s)‖) + t * (‖d.Ad‖ * Ψ)
        ≤ ∑ k, ‖d.A k‖ * (√t * Ψ) + t * (‖d.Ad‖ * Ψ) :=
          add_le_add_left (Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hkb k) (norm_nonneg _)) _
      _ ≤ ∑ k, ‖d.A k‖ * (√τ * Ψ) + τ * (‖d.Ad‖ * Ψ) := by
          gcongr
          · exact ht.2
          · exact ht.2
      _ = d.Kψ τ * Ψ := by
          simp only [Kψ, add_mul, Finset.mul_sum, Finset.sum_mul]
          congr 1
          · exact Finset.sum_congr rfl fun k _ => by ring
          · ring
  calc ‖r + ((∫ s in (0 : ℝ)..t, d.rhs (traj h ψ 0) s) + ∫ s in (0 : ℝ)..t, f s)‖
      ≤ ‖r‖ + (‖∫ s in (0 : ℝ)..t, d.rhs (traj h ψ 0) s‖ + ‖∫ s in (0 : ℝ)..t, f s‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := by linarith

/-- **Grönwall-type bound**: `‖x(t)‖ ≤ (‖r‖ + Kψ(τ) ‖ψ‖ + ∫₀^τ ‖f‖) e^{K τ}` on `[0, τ]`. -/
theorem norm_sol_le (hψ : MemLp ψ 2 (μI h)) {τ : ℝ} (hf : IntegrableOn f (Ioc 0 τ)) {t : ℝ}
    (ht : t ∈ Icc 0 τ) :
    ‖d.sol r ψ f t‖ ≤ (‖r‖ + d.Kψ τ * (eLpNorm ψ 2 (μI h)).toReal + ∫ s in Ioc 0 τ, ‖f s‖) *
      Real.exp (d.K * τ) := by
  have hc : ∀ t ∈ Icc 0 τ, ‖d.picard r ψ f 1 t‖ ≤
      ‖r‖ + d.Kψ τ * (eLpNorm ψ 2 (μI h)).toReal + ∫ s in Ioc 0 τ, ‖f s‖ :=
    fun t ht => d.norm_picard_one_le hψ hf ht
  have hc0 := (norm_nonneg _).trans (hc t ht)
  rw [← (d.hasSum_sol (r := r) hψ (hf.mono_set (Ioc_subset_Ioc_right ht.2)) ht.1).tsum_eq]
  refine (tsum_of_norm_bounded ((hasSum_pow_div_factorial_exp (d.K * t)).mul_left _)
    fun n => d.norm_picard_sub_le hψ hf hc n t ht).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left ht.2 d.K_nonneg)) hc0

end Equation

/-- **The history lies in `L²`**, with `‖x_t‖ ≤ ‖ψ‖ + √h sup_{[0, t]} ‖x‖`. -/
theorem norm_window_traj_le {h : ℝ} (hh : 0 ≤ h) {ψ x : ℝ → E} (hψ : MemLp ψ 2 (μI h)) {t M : ℝ}
    (ht : 0 ≤ t) (hx : ContinuousOn x (Icc 0 t)) (hM0 : 0 ≤ M)
    (hM : ∀ ρ ∈ Icc 0 t, ‖x ρ‖ ≤ M) :
    ‖window h (traj h ψ x) t‖ ≤ (eLpNorm ψ 2 (μI h)).toReal + √h * M := by
  have e : traj h ψ x = traj h ψ 0 + traj h 0 x := by rw [← traj_add, add_zero, zero_add]
  rw [e, window_add_of_memLp
    (memLp_traj_window hh hψ continuous_zero.continuousOn ⟨ht, le_rfl⟩)
    (memLp_traj_window hh MemLp.zero hx ⟨ht, le_rfl⟩)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_window_le (memLp_traj hh ht hψ continuous_zero.continuousOn) ht
      (by linarith)).trans_eq ?_
    rw [Equation.eLpNorm_traj_zero ht]
  · exact norm_window_le_of_forall hh hM0 fun σ hσ => norm_traj_zero_le hM0 hM (by linarith [hσ.2])

end Delay

end DataDrivenControl
