module

public import DataDrivenControl.Examples.Delay.Convolution
public import DataDrivenControl.Examples.Delay.Translation
public import DataDrivenControl.System.Mild

/-!
# Delay functionals

The paper's `L`, `M` and `C` of `ex:intro-delay` are bounded maps on continuous histories, i.e.
matrices of finite measures on the delay interval.  A matrix of signed measures is a finite sum
of positive measures times matrices (Jordan decomposition, matrix units), so they have the shape

`φ ↦ ∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ) + D φ`,  `μₖ` finite positive measures on `[0, h]`,

where a part `D` bounded on the `L²` history is also allowed (e.g. an `L²` kernel, `kernelOp`).

## Main declarations

* `DelayOp h E F` packages `Pₖ`, `μₖ` and `D : L²(0, h; E) →L F`;
  `DelayOp.eval p z s = ∑ₖ Pₖ ∫ z(h - δ + s) dμₖ(δ) + D (window h z s)` evaluates it at time `s`
  along a trajectory `z` in shifted time (`x(s - δ) = z(h - δ + s)`, `x_s = window h z s`,
  `Delay/Trajectory`; the measure part is `mconv`, `Delay/Convolution`).  `DelayOp.ofPoints`:
  finitely many point delays (Dirac measures), `eval_ofPoints`.
* Algebra and measure theory of `eval`: `eval_smul`, `eval_shift`, `ae_eval_add`,
  `eval_add_of_continuousOn`, `ae_eval_eq` (dependence on classes only), `eval_traj_zero` and
  `eval_zero_congr` (at time `0` only the history is seen), `continuousOn_eval`, `memLp_eval`,
  the `L²` bound `eLpNorm_eval_le`
  (`‖p z‖_{L²(0, τ)} ≤ (∑ₖ ‖Pₖ‖ μₖ([0, h]) + √τ ‖D‖) ‖z‖_{L²(0, h + τ)}`), and
  `hasWeakDeriv_eval` (`p` commutes with the weak derivative of an `H¹` trajectory).
* `L2op`: a bounded operator on `L²(0, τ; E)` from a map on representatives that is linear up to
  null sets; `DelayOp.opL p τ` is `x ↦ (s ↦ p (x_s))` with zero history, and `primL τ` is the
  primitive `x ↦ ∫₀^· x`.
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

/-- Finite sums of `H¹` signals are `H¹`. -/
theorem hasWeakDeriv_finsetSum {ι : Type*} (s : Finset ι) {T : ℝ} {x g : ι → ℝ → E}
    (h : ∀ i ∈ s, HasWeakDeriv T (x i) (g i)) :
    HasWeakDeriv T (fun t => ∑ i ∈ s, x i t) (fun t => ∑ i ∈ s, g i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, fun t _ => by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### Delay functionals -/

/-- A **delay functional** `φ ↦ ∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ) + D φ` on histories `φ ∈ L²(-h, 0; E)`, with
finitely many finite measures `μₖ` on `[0, h]` and a part `D` bounded on the `L²` history.  The
paper's `L`, `M` and `C` of `ex:intro-delay` (matrices of finite measures) are of this form. -/
structure DelayOp (h : ℝ) (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  /-- The maximal delay is positive. -/
  h_pos : 0 < h
  /-- The number of measures. -/
  N : ℕ
  /-- The coefficients `Pₖ`. -/
  P : Fin N → E →L[ℝ] F
  /-- The delay measures `μₖ`. -/
  μ : Fin N → Measure ℝ
  /-- The delay measures are finite. -/
  isFiniteMeasure_μ : ∀ k, IsFiniteMeasure (μ k)
  /-- The delay measures live on `[0, h]`. -/
  μ_compl : ∀ k, μ k (Icc 0 h)ᶜ = 0
  /-- The part bounded on the `L²` history. -/
  D : L2 E h →L[ℝ] F

attribute [instance] DelayOp.isFiniteMeasure_μ

namespace DelayOp

variable {h : ℝ} (p : DelayOp h E F)

/-- The delay functional at time `s` along a trajectory `z` in shifted time:
`∑ₖ Pₖ ∫ z(h - δ + s) dμₖ(δ) + D (window h z s)`, i.e. `∑ₖ Pₖ ∫ x(s - δ) dμₖ(δ) + D x_s`. -/
def eval (z : ℝ → E) (s : ℝ) : F := ∑ k, p.P k (mconv (p.μ k) h z s) + p.D (window h z s)

/-- **Point delays** `φ ↦ ∑ₖ Pₖ φ(-δₖ) + D φ`, `δₖ ∈ [0, h]`: Dirac measures. -/
def ofPoints (h_pos : 0 < h) {N : ℕ} (P : Fin N → E →L[ℝ] F) (δ : Fin N → ℝ)
    (hδ : ∀ k, δ k ∈ Icc 0 h) (D : L2 E h →L[ℝ] F) : DelayOp h E F where
  h_pos := h_pos
  N := N
  P := P
  μ k := Measure.dirac (δ k)
  isFiniteMeasure_μ := fun _ => inferInstance
  μ_compl k := by
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, indicator_of_notMem (by simpa using hδ k)]
  D := D

/-- Point delays act by point evaluation: `∑ₖ Pₖ z(h - δₖ + s) + D (window h z s)`. -/
theorem eval_ofPoints (h_pos : 0 < h) {N : ℕ} (P : Fin N → E →L[ℝ] F) (δ : Fin N → ℝ)
    (hδ : ∀ k, δ k ∈ Icc 0 h) (D : L2 E h →L[ℝ] F) (z : ℝ → E) (s : ℝ) :
    (ofPoints h_pos P δ hδ D).eval z s = ∑ k, P k (z (h - δ k + s)) + D (window h z s) := by
  simp only [eval, ofPoints, mconv_dirac]
  rfl

/-- The total mass `∑ₖ ‖Pₖ‖ μₖ([0, h])` of the measure part. -/
def mass : ℝ := ∑ k, ‖p.P k‖ * (p.μ k).real univ

/-- The total mass is nonnegative. -/
theorem mass_nonneg : 0 ≤ p.mass :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) measureReal_nonneg

/-- The constant `∑ₖ ‖Pₖ‖ μₖ([0, h]) + √τ ‖D‖` of the `L²` bound on `(0, τ]`. -/
def bound (τ : ℝ) : ℝ := p.mass + √τ * ‖p.D‖

/-- The constant of the `L²` bound is nonnegative. -/
theorem bound_nonneg (τ : ℝ) : 0 ≤ p.bound τ :=
  add_nonneg p.mass_nonneg (by positivity)

/-- The delay functional is homogeneous. -/
theorem eval_smul (c : ℝ) (z : ℝ → E) (s : ℝ) : p.eval (c • z) s = c • p.eval z s := by
  simp only [eval, mconv_smul, window_smul, map_smul, Finset.smul_sum, smul_add]

/-- The delay functional of the zero trajectory vanishes. -/
@[simp] theorem eval_zero (s : ℝ) : p.eval 0 s = 0 := by
  simpa using p.eval_smul 0 0 s

/-- Translating the trajectory translates the delay functional. -/
theorem eval_shift (z : ℝ → E) (s σ : ℝ) : p.eval (fun ρ => z (s + ρ)) σ = p.eval z (s + σ) := by
  have hw : window h (fun ρ => z (s + ρ)) σ = window h z (s + σ) :=
    window_eq_of_ae (ae_of_all _ fun ρ => by simp only [add_assoc])
  simp only [eval, hw, mconv_shift]

/-- Trajectories that agree a.e. on `(0, h + τ]` have delay functionals that agree a.e. on
`(0, τ]`. -/
theorem ae_eval_eq {z₁ z₂ : ℝ → E} {τ : ℝ} (hz : z₁ =ᵐ[μI (h + τ)] z₂) :
    ∀ᵐ s ∂(μI τ), p.eval z₁ s = p.eval z₂ s := by
  have hk : ∀ᵐ s ∂(μI τ), ∀ k, mconv (p.μ k) h z₁ s = mconv (p.μ k) h z₂ s :=
    ae_all_iff.2 fun k => mconv_congr_ae (p.μ_compl k) hz
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  simp only [eval, hs, window_congr_ae (T := h) hz hsI.1.le (by linarith [hsI.2])]

/-- The delay functional is additive along `L²` trajectories, a.e. in time. -/
theorem ae_eval_add {z₁ z₂ : ℝ → E} {τ : ℝ} (h₁ : MemLp z₁ 2 (μI (h + τ)))
    (h₂ : MemLp z₂ 2 (μI (h + τ))) :
    ∀ᵐ s ∂(μI τ), p.eval (z₁ + z₂) s = p.eval z₁ s + p.eval z₂ s := by
  have hk : ∀ᵐ s ∂(μI τ), ∀ k, mconv (p.μ k) h (z₁ + z₂) s =
      mconv (p.μ k) h z₁ s + mconv (p.μ k) h z₂ s :=
    ae_all_iff.2 fun k => by
      filter_upwards [ae_integrable_comp (p.μ_compl k) h₁, ae_integrable_comp (p.μ_compl k) h₂]
        with s e₁ e₂
      exact mconv_add e₁ e₂
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  simp only [eval, hs, map_add, Finset.sum_add_distrib,
    window_add_of_memLp (memLp_comp_add (T := h) h₁ hsI.1.le (by linarith [hsI.2]))
      (memLp_comp_add (T := h) h₂ hsI.1.le (by linarith [hsI.2]))]
  abel

/-- The delay functional is additive along trajectories continuous on `[0, h + τ]`. -/
theorem eval_add_of_continuousOn {z₁ z₂ : ℝ → E} {τ s : ℝ}
    (h₁ : ContinuousOn z₁ (Icc 0 (h + τ))) (h₂ : ContinuousOn z₂ (Icc 0 (h + τ)))
    (hs : s ∈ Icc 0 τ) : p.eval (z₁ + z₂) s = p.eval z₁ s + p.eval z₂ s := by
  have hm : ∀ {z : ℝ → E}, ContinuousOn z (Icc 0 (h + τ)) → MemLp (fun σ => z (s + σ)) 2 (μI h) :=
    fun hz => memLp_comp_add (memLp_μI_of_continuousOn hz) hs.1 (by linarith [hs.2])
  simp only [eval, mconv_add (integrable_comp_of_continuousOn (p.μ_compl _) h₁ hs)
    (integrable_comp_of_continuousOn (p.μ_compl _) h₂ hs), map_add, Finset.sum_add_distrib,
    window_add_of_memLp (hm h₁) (hm h₂)]
  abel

/-- At time `0` the delay functional only sees the history on `[0, h]`. -/
theorem eval_zero_congr {g₁ g₂ : ℝ → E} (hg : EqOn g₁ g₂ (Icc 0 h)) : p.eval g₁ 0 = p.eval g₂ 0 := by
  have hw : window h g₁ 0 = window h g₂ 0 :=
    window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      hg ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
  simp only [eval, hw]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [mconv_congr (p.μ_compl k) fun δ hδ => hg ⟨by linarith [hδ.2], by linarith [hδ.1]⟩]

/-- At time `0` the delay functional only sees the history: `p (traj h g x)_0 = p g`. -/
theorem eval_traj_zero (g x : ℝ → E) : p.eval (traj h g x) 0 = p.eval g 0 :=
  p.eval_zero_congr fun _ hσ => traj_of_le _ _ hσ.2

/-- The delay functional of a continuous trajectory is continuous. -/
theorem continuousOn_eval {z : ℝ → E} {τ : ℝ} (hz : ContinuousOn z (Icc 0 (h + τ))) :
    ContinuousOn (p.eval z) (Icc 0 τ) :=
  (continuousOn_finsetSum _ fun k _ => (p.P k).continuous.comp_continuousOn
    (continuousOn_mconv (p.μ_compl k) hz)).add
    (p.D.continuous.comp_continuousOn
      (continuousOn_window (T := h) (T' := τ) (memLp_μI_of_continuousOn hz)))

/-- The distributed part along an `L²` trajectory is continuous in time. -/
theorem continuousOn_D {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    ContinuousOn (fun s => p.D (window h z s)) (Icc 0 τ) :=
  p.D.continuous.comp_continuousOn (continuousOn_window hz)

/-- The delay functional of an `L²` trajectory is square integrable. -/
theorem memLp_eval {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    MemLp (p.eval z) 2 (μI τ) :=
  (memLp_finsetSum _ fun k _ => (p.P k).comp_memLp' (memLp_mconv (p.μ_compl k) hz)).add
    (memLp_μI_of_continuousOn (p.continuousOn_D hz))

/-- The delay functional of an `L²` trajectory is integrable. -/
theorem integrableOn_eval {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    IntegrableOn (p.eval z) (Ioc 0 τ) :=
  (p.memLp_eval hz).integrable one_le_two

/-- **`L²` bound**: `‖p z‖_{L²(0, τ)} ≤ (∑ₖ ‖Pₖ‖ μₖ([0, h]) + √τ ‖D‖) ‖z‖_{L²(0, h + τ)}`. -/
theorem eLpNorm_eval_le {z : ℝ → E} {τ : ℝ} (hτ : 0 ≤ τ) (hz : MemLp z 2 (μI (h + τ))) :
    (eLpNorm (p.eval z) 2 (μI τ)).toReal ≤ p.bound τ * (eLpNorm z 2 (μI (h + τ))).toReal := by
  set Z := (eLpNorm z 2 (μI (h + τ))).toReal with hZ
  have hm : ∀ k, MemLp (mconv (p.μ k) h z) 2 (μI τ) := fun k => memLp_mconv (p.μ_compl k) hz
  have hQ : MemLp (fun t => p.D (window h z t)) 2 (μI τ) :=
    memLp_μI_of_continuousOn (p.continuousOn_D hz)
  set Yw : L2 F τ := ∑ k, (p.P k).compLp ((hm k).toLp _) + hQ.toLp _ with hYw
  have hYe : ⇑Yw =ᵐ[μI τ] p.eval z := by
    have hc : ∀ᵐ t ∂(μI τ), ∀ k,
        ((p.P k).compLp ((hm k).toLp _)) t = p.P k (mconv (p.μ k) h z t) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [(p.P k).coeFn_compLp' ((hm k).toLp _), (hm k).coeFn_toLp] with t e1 e2
      rw [e1, e2]
    filter_upwards [Lp.coeFn_add (∑ k, (p.P k).compLp ((hm k).toLp _)) (hQ.toLp _),
      coeFn_sum_L2 Finset.univ fun k => (p.P k).compLp ((hm k).toLp _),
      hQ.coeFn_toLp, hc] with t e1 e2 e3 e4
    rw [hYw, e1, Pi.add_apply, e2, e3]
    simp only [e4, eval]
  have hYn : ‖Yw‖ ≤ p.bound τ * Z := by
    have b1 : ‖∑ k, (p.P k).compLp ((hm k).toLp _)‖ ≤ ∑ k, ‖p.P k‖ * ((p.μ k).real univ * Z) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
        ((p.P k).norm_compLp_le _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
      rw [Lp.norm_toLp, hZ, measureReal_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) hz.eLpNorm_ne_top)
        (eLpNorm_mconv_le (p.μ_compl k) hz.aestronglyMeasurable)
    have b2 : ‖hQ.toLp (fun t => p.D (window h z t))‖ ≤ √τ * (‖p.D‖ * Z) := by
      refine norm_L2_le_of_ae_bound hτ _ (by positivity) ?_
      filter_upwards [hQ.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t e1 e2
      rw [e1]
      exact p.D.le_opNorm_of_le (norm_window_le hz e2.1.le (by linarith [e2.2]))
    refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans_eq ?_)
    rw [bound, mass, add_mul, Finset.sum_mul]
    simp only [mul_assoc]
  rw [← eLpNorm_congr_ae hYe, ← Lp.norm_def]
  exact hYn

/-- **The delay functional commutes with the weak derivative**: for an `H¹` trajectory `z` on
`[0, h + τ]` with derivative `z'`, `s ↦ p z_s` is `H¹` on `[0, τ]` with derivative `s ↦ p z'_s`
(`hasWeakDeriv_mconv`; for the distributed part: `window_sub_window_eq_integral`). -/
theorem hasWeakDeriv_eval {τ : ℝ} {z z' : ℝ → E}
    (hz : HasWeakDeriv (h + τ) z z') : HasWeakDeriv τ (p.eval z) (p.eval z') := by
  have hD : HasWeakDeriv τ (fun s => p.D (window h z s)) (fun s => p.D (window h z' s)) := by
    refine ⟨memLp_μI_of_continuousOn (p.continuousOn_D hz.memLp_deriv), fun t ht => ?_⟩
    have hwi : IntervalIntegrable (window h z') volume 0 t :=
      ((continuousOn_window (T := h) (T' := τ) hz.memLp_deriv).mono
        (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    rw [eq_add_of_sub_eq' (window_sub_window_eq_integral hz p.h_pos.le ht.1 (by linarith [ht.2])),
      map_add, p.D.intervalIntegral_comp_comm hwi]
  exact (hasWeakDeriv_finsetSum Finset.univ fun k _ =>
    (hasWeakDeriv_mconv (p.μ_compl k) hz).map (p.P k)).add hD

/-- Zero-history evaluation of an `L²` solution is square integrable. -/
theorem memLp_eval_traj_zero {τ : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    MemLp (p.eval (traj h 0 x)) 2 (μI τ) := by
  rcases le_or_gt 0 τ with hτ | hτ
  · exact p.memLp_eval (memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero hx)
  · rw [μI_eq_zero hτ.le]
    exact memLp_measure_zero

/-- Zero-history evaluation only depends on the class of the solution. -/
theorem ae_eval_traj_zero_congr {τ : ℝ} {x₁ x₂ : ℝ → E} (hx : x₁ =ᵐ[μI τ] x₂) :
    p.eval (traj h 0 x₁) =ᵐ[μI τ] p.eval (traj h 0 x₂) :=
  p.ae_eval_eq (traj_ae_congr_right 0 hx)

/-- Zero-history evaluation is additive on `L²` solutions. -/
theorem eval_traj_zero_add {τ : ℝ} {x₁ x₂ : ℝ → E} (h₁ : MemLp x₁ 2 (μI τ))
    (h₂ : MemLp x₂ 2 (μI τ)) :
    p.eval (traj h 0 (x₁ + x₂)) =ᵐ[μI τ] p.eval (traj h 0 x₁) + p.eval (traj h 0 x₂) := by
  rcases le_or_gt 0 τ with hτ | hτ
  · rw [← add_zero (0 : ℝ → E), traj_add, add_zero]
    exact p.ae_eval_add (memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero h₁)
      (memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero h₂)
  · rw [μI_eq_zero hτ.le, EventuallyEq, ae_zero]
    exact Filter.eventually_bot

/-- Zero-history evaluation is homogeneous. -/
theorem eval_traj_zero_smul (c : ℝ) (x : ℝ → E) :
    p.eval (traj h 0 (c • x)) = c • p.eval (traj h 0 x) := by
  funext s
  rw [← smul_zero c, traj_smul, smul_zero, p.eval_smul, Pi.smul_apply]

/-- The `L²` bound of zero-history evaluation. -/
theorem eLpNorm_eval_traj_zero_le {τ : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    (eLpNorm (p.eval (traj h 0 x)) 2 (μI τ)).toReal ≤
      p.bound τ * (eLpNorm x 2 (μI τ)).toReal := by
  rcases le_or_gt 0 τ with hτ | hτ
  · refine (p.eLpNorm_eval_le hτ (memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero hx)).trans_eq ?_
    rw [eLpNorm_traj_zero_left p.h_pos.le hx]
  · rw [μI_eq_zero hτ.le, eLpNorm_measure_zero, ENNReal.toReal_zero]
    exact mul_nonneg (p.bound_nonneg τ) ENNReal.toReal_nonneg

end DelayOp

/-! ### Bounded operators on `L²(0, τ; E)` from maps on representatives -/

/-- A bounded operator `L²(0, τ; E) → L²(0, τ; F)` from a map `Φ` on representatives that is square
integrable, linear up to null sets and bounded. -/
def L2op (τ : ℝ) (Φ : (ℝ → E) → ℝ → F) (hmem : ∀ x : L2 E τ, MemLp (Φ x) 2 (μI τ))
    (hadd : ∀ x y : L2 E τ, Φ ⇑(x + y) =ᵐ[μI τ] Φ x + Φ y)
    (hsmul : ∀ (c : ℝ) (x : L2 E τ), Φ ⇑(c • x) =ᵐ[μI τ] c • Φ x) (C : ℝ)
    (hC : ∀ x : L2 E τ, (eLpNorm (Φ x) 2 (μI τ)).toReal ≤ C * ‖x‖) : L2 E τ →L[ℝ] L2 F τ :=
  LinearMap.mkContinuous
    { toFun := fun x => (hmem x).toLp _
      map_add' := fun x y => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd x y)
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c x) }
    C fun x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      exact hC x

/-- The operator `L2op` acts by `Φ` on representatives. -/
theorem coeFn_L2op {τ : ℝ} {Φ : (ℝ → E) → ℝ → F} {hmem : ∀ x : L2 E τ, MemLp (Φ x) 2 (μI τ)}
    {hadd : ∀ x y : L2 E τ, Φ ⇑(x + y) =ᵐ[μI τ] Φ x + Φ y}
    {hsmul : ∀ (c : ℝ) (x : L2 E τ), Φ ⇑(c • x) =ᵐ[μI τ] c • Φ x} {C : ℝ}
    {hC : ∀ x : L2 E τ, (eLpNorm (Φ x) 2 (μI τ)).toReal ≤ C * ‖x‖} (x : L2 E τ) :
    ⇑(L2op τ Φ hmem hadd hsmul C hC x) =ᵐ[μI τ] Φ x :=
  (hmem x).coeFn_toLp

namespace DelayOp

variable {h : ℝ} (p : DelayOp h E F)

/-- **The delay functional with zero history** as a bounded operator on `L²(0, τ)`:
`x ↦ (s ↦ ∑ₖ Pₖ x(s - δₖ) + D x_s)`, with `x = 0` on the history. -/
def opL (τ : ℝ) : L2 E τ →L[ℝ] L2 F τ :=
  L2op τ (fun x => p.eval (traj h 0 x)) (fun x => p.memLp_eval_traj_zero (Lp.memLp x))
    (fun x y => (p.ae_eval_traj_zero_congr (Lp.coeFn_add x y)).trans
      (p.eval_traj_zero_add (Lp.memLp x) (Lp.memLp y)))
    (fun c x => (p.ae_eval_traj_zero_congr (Lp.coeFn_smul c x)).trans
      (EventuallyEq.of_eq (p.eval_traj_zero_smul c _)))
    (p.bound τ) fun x => by
      rw [Lp.norm_def]
      exact p.eLpNorm_eval_traj_zero_le (Lp.memLp x)

/-- `opL` acts by the delay functional along the zero-history trajectory. -/
theorem coeFn_opL (τ : ℝ) (x : L2 E τ) : ⇑(p.opL τ x) =ᵐ[μI τ] p.eval (traj h 0 ⇑x) :=
  coeFn_L2op x

end DelayOp

/-! ### The primitive -/

/-- The primitive of a square-integrable signal is square integrable. -/
theorem memLp_primitive {τ : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    MemLp (fun t => ∫ s in (0 : ℝ)..t, x s) 2 (μI τ) :=
  memLp_μI_of_continuousOn (continuousOn_primitive_Ioc (hx.integrable one_le_two))

/-- The bound `‖∫₀^· x‖_{L²(0, τ)} ≤ τ ‖x‖_{L²(0, τ)}` (Cauchy–Schwarz). -/
theorem eLpNorm_primitive_le {τ : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    (eLpNorm (fun t => ∫ s in (0 : ℝ)..t, x s) 2 (μI τ)).toReal ≤
      √τ * √τ * (eLpNorm x 2 (μI τ)).toReal := by
  rcases le_or_gt 0 τ with hτ | hτ
  · have hm := memLp_primitive hx
    rw [← Lp.norm_toLp _ hm, mul_assoc]
    refine norm_L2_le_of_ae_bound hτ _ (by positivity) ?_
    filter_upwards [hm.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t e1 e2
    rw [e1, intervalIntegral.integral_of_le e2.1.le]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_set (hx.integrable one_le_two).norm
      (ae_of_all _ fun _ => norm_nonneg _) (Ioc_subset_Ioc_right e2.2).eventuallyLE).trans ?_
    exact integral_norm_le_sqrt_mul hτ hx
  · rw [μI_eq_zero hτ.le, eLpNorm_measure_zero, ENNReal.toReal_zero]
    positivity

/-- **The primitive** `x ↦ ∫₀^· x` as a bounded operator on `L²(0, τ; E)`. -/
def primL (τ : ℝ) : L2 E τ →L[ℝ] L2 E τ :=
  L2op τ (fun x t => ∫ s in (0 : ℝ)..t, x s) (fun x => memLp_primitive (Lp.memLp x))
    (fun x y => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht' : t ∈ Icc 0 τ := Ioc_subset_Icc_self ht
      rw [intervalIntegral_congr_μI (Lp.coeFn_add x y) ht', Pi.add_apply]
      simp only [Pi.add_apply]
      rw [intervalIntegral.integral_add
          (intervalIntegrable_of_integrableOn ((Lp.memLp x).integrable one_le_two) ht')
          (intervalIntegrable_of_integrableOn ((Lp.memLp y).integrable one_le_two) ht')])
    (fun c x => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [intervalIntegral_congr_μI (Lp.coeFn_smul c x) (Ioc_subset_Icc_self ht), Pi.smul_apply]
      simp only [Pi.smul_apply]
      rw [intervalIntegral.integral_smul])
    (√τ * √τ) fun x => by
      rw [Lp.norm_def]
      exact eLpNorm_primitive_le (Lp.memLp x)

/-- `primL` acts by `x ↦ ∫₀^· x` on representatives. -/
theorem coeFn_primL (τ : ℝ) (x : L2 E τ) :
    ⇑(primL τ x) =ᵐ[μI τ] fun t => ∫ s in (0 : ℝ)..t, x s :=
  coeFn_L2op x

end Delay

end DataDrivenControl
