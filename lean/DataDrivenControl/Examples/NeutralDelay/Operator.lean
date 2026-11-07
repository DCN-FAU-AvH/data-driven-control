module

public import DataDrivenControl.Examples.Delay.System

/-!
# Delay functionals for the neutral delay system

Helper file for the neutral delay example (`ex:intro-delay` with `M ≠ 0`).  The paper's `L`, `M`
and `C` have the same shape on the history: finitely many point delays and a part that is bounded
on the `L²` history,

`φ ↦ ∑ₖ Pₖ φ(-δₖ) + D φ`,  `δₖ ∈ [0, h]`.

## Main declarations

* `NeutralDelay.DelayOp h E F` packages `Pₖ`, `δₖ` and `D : L²(0, h; E) →L F`;
  `DelayOp.eval p z s = ∑ₖ Pₖ z(h - δₖ + s) + D (window h z s)` evaluates it at time `s` along a
  trajectory `z` in shifted time (the conventions of `Delay/Solution`: `x(s - δₖ) = z(h - δₖ + s)`
  and `x_s = window h z s`).  The retarded right-hand side `Delay.Equation.rhs` is of this form.
* Algebra and measure theory of `eval`: `eval_add`, `eval_smul`, `eval_shift`, `ae_eval_eq`
  (dependence on classes only), `eval_traj_zero` (at time `0` only the history is seen),
  `continuousOn_eval`, `memLp_eval`, the `L²` bound `eLpNorm_eval_le`
  (`‖p z‖_{L²(0, τ)} ≤ (∑ₖ ‖Pₖ‖ + √τ ‖D‖) ‖z‖_{L²(0, h + τ)}`), and `hasWeakDeriv_eval`
  (`p` commutes with the weak derivative of an `H¹` trajectory).
* `L²` trajectories: `memLp_traj_of_memLp`, `eLpNorm_traj_zero_left`, `traj_ae_congr_right`, and
  the gluing lemma `hasWeakDeriv_traj_of` (an `H¹` history followed by an `H¹` solution starting at
  the endpoint of the history is `H¹`).
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

namespace NeutralDelay

open Delay (traj traj_of_le traj_of_lt traj_add traj_sub traj_smul traj_zero traj_ae_congr
  restrict_Iic_μI restrict_Ioi_μI intervalIntegrable_of_integrableOn continuousOn_primitive_Ioc
  integral_norm_le_sqrt_mul norm_L2_le_of_ae_bound coeFn_sum_L2 hasWeakDeriv_comp_add)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ### Square-integrable trajectories -/

/-- The window measure of a nonpositive horizon vanishes. -/
theorem μI_eq_zero {τ : ℝ} (hτ : τ ≤ 0) : μI τ = 0 := by
  simp [μI, Ioc_eq_empty (not_lt.2 hτ)]

/-- The translation `σ ↦ σ - h` maps `(h, h + τ]` onto `(0, τ]`. -/
theorem measurePreserving_sub_Ioc (h τ : ℝ) :
    MeasurePreserving (fun σ => σ - h) (volume.restrict (Ioc h (h + τ))) (μI τ) := by
  have := (measurePreserving_sub_right volume h).restrict_preimage (s := Ioc 0 τ)
    measurableSet_Ioc
  rwa [preimage_sub_const_Ioc, zero_add, add_comm τ h] at this

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
  rw [e, ← Delay.Equation.eLpNorm_traj_zero hτ ψ, ← eLpNorm_traj_zero_left hh hx]
  rw [← ENNReal.toReal_add h1.eLpNorm_ne_top h2.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1.eLpNorm_ne_top, h2.eLpNorm_ne_top⟩)
    (eLpNorm_add_le one_le_two)

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

/-- Interval integrability is preserved by bounded operators. -/
theorem intervalIntegrable_clm_comp (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) : IntervalIntegrable (fun t => L (f t)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

/-- The primitive of a square-integrable signal is `H¹` with this signal as weak derivative. -/
theorem hasWeakDeriv_primitive {τ : ℝ} {y : ℝ → E} (hy : MemLp y 2 (μI τ)) :
    HasWeakDeriv τ (fun t => ∫ s in (0 : ℝ)..t, y s) y :=
  ⟨hy, fun t _ => by simp⟩

/-! ### Delay functionals -/

/-- A **delay functional** `φ ↦ ∑ₖ Pₖ φ(-δₖ) + D φ` on histories `φ ∈ L²(-h, 0; E)`, with
finitely many point delays `δₖ ∈ [0, h]` and a part `D` bounded on the `L²` history.  The paper's
`L`, `M` and `C` of `ex:intro-delay` are of this form. -/
structure DelayOp (h : ℝ) (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  /-- The maximal delay is positive. -/
  h_pos : 0 < h
  /-- The number of point delays. -/
  N : ℕ
  /-- The coefficients `Pₖ` of the point delays. -/
  P : Fin N → E →L[ℝ] F
  /-- The point delays `δₖ`. -/
  δ : Fin N → ℝ
  /-- The point delays lie in `[0, h]`. -/
  δ_mem : ∀ k, δ k ∈ Icc 0 h
  /-- The part bounded on the `L²` history. -/
  D : L2 E h →L[ℝ] F

namespace DelayOp

variable {h : ℝ} (p : DelayOp h E F)

/-- The delay functional at time `s` along a trajectory `z` in shifted time:
`∑ₖ Pₖ z(h - δₖ + s) + D (window h z s)`, i.e. `∑ₖ Pₖ x(s - δₖ) + D x_s`. -/
def eval (z : ℝ → E) (s : ℝ) : F := ∑ k, p.P k (z (h - p.δ k + s)) + p.D (window h z s)

/-- The constant `∑ₖ ‖Pₖ‖ + √τ ‖D‖` of the `L²` bound on `(0, τ]`. -/
def bound (τ : ℝ) : ℝ := ∑ k, ‖p.P k‖ + √τ * ‖p.D‖

/-- The constant of the `L²` bound is nonnegative. -/
theorem bound_nonneg (τ : ℝ) : 0 ≤ p.bound τ := by
  unfold bound
  positivity

/-- `h - δₖ ≥ 0`. -/
theorem sub_δ_nonneg (k : Fin p.N) : 0 ≤ h - p.δ k := by linarith [(p.δ_mem k).2]

/-- `h - δₖ ≤ h`. -/
theorem sub_δ_le (k : Fin p.N) : h - p.δ k ≤ h := by linarith [(p.δ_mem k).1]

/-- The delay functional is additive on square-integrable windows. -/
theorem eval_add {z₁ z₂ : ℝ → E} {s : ℝ} (h₁ : MemLp (fun σ => z₁ (s + σ)) 2 (μI h))
    (h₂ : MemLp (fun σ => z₂ (s + σ)) 2 (μI h)) :
    p.eval (z₁ + z₂) s = p.eval z₁ s + p.eval z₂ s := by
  simp only [eval, window_add_of_memLp h₁ h₂, Pi.add_apply, map_add, Finset.sum_add_distrib]
  abel

/-- The delay functional of a difference. -/
theorem eval_sub {z₁ z₂ : ℝ → E} {s : ℝ} (h₁ : MemLp (fun σ => z₁ (s + σ)) 2 (μI h))
    (h₂ : MemLp (fun σ => z₂ (s + σ)) 2 (μI h)) :
    p.eval (z₁ - z₂) s = p.eval z₁ s - p.eval z₂ s := by
  simp only [eval, window_sub_of_memLp h₁ h₂, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
  abel

/-- The delay functional is homogeneous. -/
theorem eval_smul (c : ℝ) (z : ℝ → E) (s : ℝ) : p.eval (c • z) s = c • p.eval z s := by
  simp only [eval, window_smul, Pi.smul_apply, map_smul, Finset.smul_sum, smul_add]

/-- The delay functional of the zero trajectory vanishes. -/
@[simp] theorem eval_zero (s : ℝ) : p.eval 0 s = 0 := by simp [eval]

/-- Translating the trajectory translates the delay functional. -/
theorem eval_shift (z : ℝ → E) (s σ : ℝ) : p.eval (fun ρ => z (s + ρ)) σ = p.eval z (s + σ) := by
  have hw : window h (fun ρ => z (s + ρ)) σ = window h z (s + σ) :=
    window_eq_of_ae (ae_of_all _ fun ρ => by simp only [add_assoc])
  simp only [eval, hw]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  ring

/-- Trajectories that agree a.e. on `(0, h + τ]` have delay functionals that agree a.e. on
`(0, τ]`. -/
theorem ae_eval_eq {z₁ z₂ : ℝ → E} {τ : ℝ} (hz : z₁ =ᵐ[μI (h + τ)] z₂) :
    ∀ᵐ s ∂(μI τ), p.eval z₁ s = p.eval z₂ s := by
  have hk : ∀ᵐ s ∂(μI τ), ∀ k, z₁ (h - p.δ k + s) = z₂ (h - p.δ k + s) :=
    ae_all_iff.2 fun k => ae_comp_add hz (p.sub_δ_nonneg k) (by linarith [p.sub_δ_le k])
  filter_upwards [hk, ae_restrict_mem measurableSet_Ioc] with s hs hsI
  simp only [eval, hs, window_congr_ae (T := h) hz hsI.1.le (by linarith [hsI.2])]

/-- At time `0` the delay functional only sees the history: `p (traj h g x)_0 = p g`. -/
theorem eval_traj_zero (g x : ℝ → E) : p.eval (traj h g x) 0 = p.eval g 0 := by
  have hw : window h (traj h g x) 0 = window h g 0 :=
    window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      traj_of_le _ _ (by linarith [hσ.2]))
  simp only [eval, hw]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [add_zero, traj_of_le _ _ (p.sub_δ_le k)]

/-- The delay functional of a continuous trajectory is continuous. -/
theorem continuousOn_eval {z : ℝ → E} {τ : ℝ} (hz : ContinuousOn z (Icc 0 (h + τ))) :
    ContinuousOn (p.eval z) (Icc 0 τ) := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin p.N)),
      ContinuousOn (fun s => p.P k (z (h - p.δ k + s))) (Icc 0 τ) := fun k _ =>
    (p.P k).continuous.comp_continuousOn (hz.comp (f := fun s => h - p.δ k + s) (by fun_prop)
      fun s hs => ⟨by linarith [hs.1, p.sub_δ_nonneg k], by linarith [hs.2, p.sub_δ_le k]⟩)
  have h2 := p.D.continuous.comp_continuousOn
    (continuousOn_window (T := h) (T' := τ) (memLp_μI_of_continuousOn hz))
  exact (continuousOn_finsetSum _ h1).add h2

/-- The distributed part along an `L²` trajectory is continuous in time. -/
theorem continuousOn_D {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    ContinuousOn (fun s => p.D (window h z s)) (Icc 0 τ) :=
  p.D.continuous.comp_continuousOn (continuousOn_window hz)

/-- The delay functional of an `L²` trajectory is square integrable. -/
theorem memLp_eval {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    MemLp (p.eval z) 2 (μI τ) := by
  have h1 : ∀ k ∈ (Finset.univ : Finset (Fin p.N)),
      MemLp (fun s => p.P k (z (h - p.δ k + s))) 2 (μI τ) :=
    fun k _ => (p.P k).comp_memLp'
      (memLp_comp_add hz (p.sub_δ_nonneg k) (by linarith [p.sub_δ_le k]))
  exact (memLp_finsetSum _ h1).add (memLp_μI_of_continuousOn (p.continuousOn_D hz))

/-- The delay functional of an `L²` trajectory is integrable. -/
theorem integrableOn_eval {z : ℝ → E} {τ : ℝ} (hz : MemLp z 2 (μI (h + τ))) :
    IntegrableOn (p.eval z) (Ioc 0 τ) :=
  (p.memLp_eval hz).integrable one_le_two

/-- **`L²` bound**: `‖p z‖_{L²(0, τ)} ≤ (∑ₖ ‖Pₖ‖ + √τ ‖D‖) ‖z‖_{L²(0, h + τ)}`. -/
theorem eLpNorm_eval_le {z : ℝ → E} {τ : ℝ} (hτ : 0 ≤ τ) (hz : MemLp z 2 (μI (h + τ))) :
    (eLpNorm (p.eval z) 2 (μI τ)).toReal ≤ p.bound τ * (eLpNorm z 2 (μI (h + τ))).toReal := by
  set Z := (eLpNorm z 2 (μI (h + τ))).toReal with hZ
  have hQ : MemLp (fun t => p.D (window h z t)) 2 (μI τ) :=
    memLp_μI_of_continuousOn (p.continuousOn_D hz)
  have hkT : ∀ k, h - p.δ k + τ ≤ h + τ := fun k => by linarith [p.sub_δ_le k]
  set Yw : L2 F τ := ∑ k, (p.P k).compLp (window τ z (h - p.δ k)) + hQ.toLp _ with hYw
  have hYe : ⇑Yw =ᵐ[μI τ] p.eval z := by
    have hc : ∀ᵐ t ∂(μI τ), ∀ k,
        ((p.P k).compLp (window τ z (h - p.δ k))) t = p.P k (z (h - p.δ k + t)) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [(p.P k).coeFn_compLp' (window τ z (h - p.δ k)),
        coeFn_window_of_memLp hz (p.sub_δ_nonneg k) (hkT k)] with t e1 e2
      rw [e1, e2]
    filter_upwards [Lp.coeFn_add (∑ k, (p.P k).compLp (window τ z (h - p.δ k))) (hQ.toLp _),
      coeFn_sum_L2 Finset.univ fun k => (p.P k).compLp (window τ z (h - p.δ k)),
      hQ.coeFn_toLp, hc] with t e1 e2 e3 e4
    rw [hYw, e1, Pi.add_apply, e2, e3]
    simp only [e4, eval]
  have hYn : ‖Yw‖ ≤ p.bound τ * Z := by
    have b1 : ‖∑ k, (p.P k).compLp (window τ z (h - p.δ k))‖ ≤ ∑ k, ‖p.P k‖ * Z :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
        ((p.P k).norm_compLp_le _).trans (mul_le_mul_of_nonneg_left
          (norm_window_le hz (p.sub_δ_nonneg k) (hkT k)) (norm_nonneg _)))
    have b2 : ‖hQ.toLp (fun t => p.D (window h z t))‖ ≤ √τ * (‖p.D‖ * Z) := by
      refine norm_L2_le_of_ae_bound hτ _ (by positivity) ?_
      filter_upwards [hQ.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t e1 e2
      rw [e1]
      exact p.D.le_opNorm_of_le (norm_window_le hz e2.1.le (by linarith [e2.2]))
    refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans_eq ?_)
    rw [bound, add_mul, Finset.sum_mul]
    ring
  rw [← eLpNorm_congr_ae hYe, ← Lp.norm_def]
  exact hYn

/-- **The delay functional commutes with the weak derivative**: for an `H¹` trajectory `z` on
`[0, h + τ]` with derivative `z'`, `s ↦ p z_s` is `H¹` on `[0, τ]` with derivative `s ↦ p z'_s`
(for the distributed part: `window_sub_window_eq_integral`). -/
theorem hasWeakDeriv_eval {τ : ℝ} {z z' : ℝ → E}
    (hz : HasWeakDeriv (h + τ) z z') : HasWeakDeriv τ (p.eval z) (p.eval z') := by
  refine ⟨p.memLp_eval hz.memLp_deriv, fun t ht => ?_⟩
  have hkz : ∀ k, HasWeakDeriv τ (fun s => z (h - p.δ k + s)) (fun s => z' (h - p.δ k + s)) :=
    fun k => hasWeakDeriv_comp_add hz (p.sub_δ_nonneg k) (by linarith [p.sub_δ_le k])
  have hw : window h z t = window h z 0 + ∫ u in (0 : ℝ)..t, window h z' u :=
    eq_add_of_sub_eq' (Delay.window_sub_window_eq_integral hz p.h_pos.le ht.1
      (by linarith [ht.2]))
  have hwi : IntervalIntegrable (window h z') volume 0 t :=
    ((continuousOn_window (T := h) (T' := τ) hz.memLp_deriv).mono
      (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hki : ∀ k, IntervalIntegrable (fun u => p.P k (z' (h - p.δ k + u))) volume 0 t :=
    fun k => intervalIntegrable_clm_comp (p.P k) ((hkz k).intervalIntegrable_deriv ht)
  have e1 : ∀ k, p.P k (z (h - p.δ k + t)) =
      p.P k (z (h - p.δ k + 0)) + ∫ u in (0 : ℝ)..t, p.P k (z' (h - p.δ k + u)) := fun k => by
    rw [(hkz k).eq_add_integral t ht, map_add,
      (p.P k).intervalIntegral_comp_comm ((hkz k).intervalIntegrable_deriv ht)]
  have e2 : p.D (window h z t) = p.D (window h z 0) + ∫ u in (0 : ℝ)..t, p.D (window h z' u) := by
    rw [hw, map_add, p.D.intervalIntegral_comp_comm hwi]
  have hsum : IntervalIntegrable (fun u => ∑ k, p.P k (z' (h - p.δ k + u))) volume 0 t := by
    have := IntervalIntegrable.sum Finset.univ (fun k _ => hki k)
    convert this using 1
    funext u
    simp only [Finset.sum_apply]
  simp only [eval]
  rw [intervalIntegral.integral_add hsum (intervalIntegrable_clm_comp p.D hwi),
    intervalIntegral.integral_finsetSum (fun k _ => hki k)]
  simp only [e1, e2, Finset.sum_add_distrib]
  abel

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
  · have m₁ := memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero h₁
    have m₂ := memLp_traj_of_memLp p.h_pos.le hτ MemLp.zero h₂
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [← add_zero (0 : ℝ → E), traj_add, add_zero, Pi.add_apply,
      p.eval_add (memLp_comp_add m₁ hs.1.le (by linarith [hs.2]))
        (memLp_comp_add m₂ hs.1.le (by linarith [hs.2]))]
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

/-- `opL` on the class of a square-integrable function. -/
theorem coeFn_opL_toLp {τ : ℝ} {x : ℝ → E} (hx : MemLp x 2 (μI τ)) :
    ⇑(p.opL τ (hx.toLp x)) =ᵐ[μI τ] p.eval (traj h 0 x) :=
  (p.coeFn_opL τ _).trans (p.ae_eval_traj_zero_congr hx.coeFn_toLp)

end DelayOp

/-! ### The primitive -/

/-- Interval integrals over `[0, t] ⊆ [0, τ]` only see the class in `L²(0, τ)`. -/
theorem intervalIntegral_congr_μI {τ t : ℝ} {x₁ x₂ : ℝ → E} (hx : x₁ =ᵐ[μI τ] x₂)
    (ht : t ∈ Icc 0 τ) : ∫ s in (0 : ℝ)..t, x₁ s = ∫ s in (0 : ℝ)..t, x₂ s := by
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
  exact setIntegral_congr_ae measurableSet_Ioc (by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hx
    filter_upwards [hx] with s hs hsI
    exact hs (Ioc_subset_Ioc_right ht.2 hsI))

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

end NeutralDelay

end DataDrivenControl
