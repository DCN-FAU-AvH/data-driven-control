module

public import DataDrivenControl.Examples.Delay.System

/-!
# The output operator of the delay system is unbounded on `X`

Paper: `ex:intro-delay` ("a discrete output delay generally makes `C` unbounded on `X`"),
stated as `¬ ∃ K, ∀ w, ‖C w‖ ≤ K ‖ιW w‖`.

* `Model.not_exists_bound_C`: if the output coefficients at some delay `θ ∈ (0, h]` do not cancel,
  `∑_{h'ₖ = θ} Cₖ ≠ 0`, then `C` is not bounded by the `X`-norm on `W = D(A)`.
* `Model.not_exists_bound_C_of_ne_zero`: the case of a single nonzero coefficient `C_{k₀}` at a
  positive delay shared by no other coefficient.

## Proof notes

Pick `e ∈ E` with `(∑_{h'ₖ = θ} Cₖ) e ≠ 0`.  For small `ε > 0` let `φ_ε` be a smooth bump
(`ContDiffBump` centred at `h - θ ∈ [0, h)`, outer radius `ε`, equal to `1` at the centre), with
`ε` below `θ` (so `φ_ε(h) = 0`) and below `|h'ₖ - θ|` for every `h'ₖ ≠ θ`, and `g_ε = φ_ε • e`.
Then `g_ε ∈ H¹` (`HasWeakDeriv.of_hasDerivAt`), `v_ε = (g_ε(h), g_ε) = (0, g_ε) ∈ D(A)`
(`Equation.mem_generator_domain_of_hasWeakDeriv`), `w_ε = toDom v_ε`, and by `Model.Cop_apply`
`C w_ε = (∑_{h'ₖ = θ} Cₖ) e + C_d g_ε`, while `‖ιW w_ε‖ = ‖g_ε‖_{L²} ≤ √(2ε) ‖e‖ → 0`.  A bound
`‖C w‖ ≤ K ‖ιW w‖` would give `‖(∑ Cₖ) e‖ ≤ (K + ‖C_d‖) √(2ε) ‖e‖` for all small `ε`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

namespace Model

variable {E U Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {h : ℝ} (m : Model h E U Y)

/-- **`C` is unbounded on `X`** (`ex:intro-delay`): if the output
coefficients at some delay `θ ∈ (0, h]` do not cancel, `∑_{h'ₖ = θ} Cₖ ≠ 0`, then no `K` gives
`‖C w‖ ≤ K ‖w‖_X` on `W = D(A)`. -/
theorem not_exists_bound_C {θ : ℝ} (hθ : θ ∈ Ioc 0 h)
    (hC : ∑ k ∈ Finset.univ.filter (fun k => m.τC k = θ), m.Cp k ≠ 0) :
    ¬ ∃ K : ℝ, ∀ w : m.S.Dom, ‖m.sys.C w‖ ≤ K * ‖m.sys.ιW w‖ := by
  rintro ⟨K, hK⟩
  set Ch := ∑ k ∈ Finset.univ.filter (fun k => m.τC k = θ), m.Cp k with hCh
  obtain ⟨e, he⟩ : ∃ e, Ch e ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hC (ContinuousLinearMap.ext hne)
  set c := h - θ with hc
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < θ ∧ ∀ k, m.τC k ≠ θ → ε < |m.τC k - θ| := by
    refine eventually_mem_nhdsWithin.and
      (((eventually_lt_nhds hθ.1).filter_mono nhdsWithin_le_nhds).and ?_)
    refine Filter.eventually_all.2 fun k => ?_
    by_cases hk : m.τC k = θ
    · exact Eventually.of_forall fun _ hk' => absurd hk hk'
    · exact ((eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hk))).filter_mono
        nhdsWithin_le_nhds).mono fun ε hε _ => hε
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖Ch e‖ ≤ (|K| + ‖m.Cd‖) * (√(2 * ε) * ‖e‖) := by
    filter_upwards [hev] with ε hε
    obtain ⟨hε0, hεθ, hεk⟩ := hε
    let φ : ContDiffBump c := ⟨ε / 2, ε, by linarith, by linarith⟩
    have hφr : φ.rOut = ε := rfl
    set g : ℝ → E := fun σ => φ σ • e with hgdef
    have hgd : ∀ σ, HasDerivAt g (deriv φ σ • e) σ := fun σ =>
      ((φ.contDiff (n := 1)).differentiable (by norm_num) σ).hasDerivAt.smul_const e
    have hgc : Continuous fun σ => deriv φ σ • e :=
      ((φ.contDiff (n := 2)).continuous_deriv (by norm_num)).smul continuous_const
    have hg : HasWeakDeriv h g (fun σ => deriv φ σ • e) := HasWeakDeriv.of_hasDerivAt hgd hgc
    have hv := m.mem_generator_domain_of_hasWeakDeriv hg
    set w := m.S.toDom ⟨_, hv⟩ with hwdef
    have hzero : ∀ σ, ε ≤ dist σ c → g σ = 0 := fun σ hσ => by
      simp only [hgdef]
      rw [φ.zero_of_le_dist (by rw [hφr]; exact hσ), zero_smul]
    have hgh : g h = 0 := hzero h (by
      rw [Real.dist_eq, hc, sub_sub_cancel, abs_of_pos hθ.1]
      exact hεθ.le)
    have hsum : ∑ k, m.Cp k (g (h - m.τC k)) = Ch e := by
      rw [hCh, FunLike.coe_sum, Finset.sum_apply, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : m.τC k = θ
      · simp only [hk, ↓reduceIte]
        simp only [hgdef]
        rw [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), one_smul]
      · simp only [hk, ↓reduceIte]
        rw [hzero _ (by
          rw [Real.dist_eq, hc, sub_sub_sub_cancel_left, abs_sub_comm]
          exact (hεk k hk).le), map_zero]
    have hCw : m.sys.C w = Ch e + m.Cd (hg.memLp.toLp g) := by
      rw [sys_C, m.Cop_apply w hg rfl hg.memLp.coeFn_toLp, hsum]
    have hgn : ‖hg.memLp.toLp g‖ ≤ √(2 * ε) * ‖e‖ := by
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      have hpt : ∀ σ, ‖g σ‖ ≤ (Metric.ball c ε).indicator (fun _ => ‖e‖) σ := by
        intro σ
        by_cases hσ : σ ∈ Metric.ball c ε
        · rw [indicator_of_mem hσ, hgdef, norm_smul, Real.norm_of_nonneg (φ.nonneg' σ)]
          exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
        · rw [indicator_of_notMem hσ, hzero σ (not_lt.1 hσ), norm_zero]
      calc eLpNorm g 2 (μI h)
          ≤ eLpNorm ((Metric.ball c ε).indicator fun _ => ‖e‖) 2 (μI h) :=
            eLpNorm_mono_real hg.memLp.aestronglyMeasurable hpt
        _ ≤ ‖‖e‖‖ₑ * (μI h) (Metric.ball c ε) ^ (1 / (2 : ℝ≥0∞).toReal) :=
            eLpNorm_indicator_const_le ‖e‖ 2 measurableSet_ball.nullMeasurableSet
        _ ≤ ‖‖e‖‖ₑ * (ENNReal.ofReal (2 * ε)) ^ (1 / (2 : ℝ≥0∞).toReal) := by
            gcongr
            exact (Measure.restrict_apply_le _ _).trans (Real.volume_ball c ε).le
        _ = ENNReal.ofReal (√(2 * ε) * ‖e‖) := by
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm, Real.sqrt_eq_rpow,
              ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
              ← ofReal_norm, norm_norm]
            norm_num
    have hnw : ‖m.sys.ιW w‖ = ‖hg.memLp.toLp g‖ := by
      rw [show m.sys.ιW w = WithLp.toLp 2 (g h, hg.memLp.toLp g) from rfl, hgh,
        WithLp.norm_toLp_snd]
    have hK' : K * ‖m.sys.ιW w‖ ≤ |K| * (√(2 * ε) * ‖e‖) := by
      rw [hnw]
      exact (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hgn (abs_nonneg K))
    calc ‖Ch e‖ = ‖m.sys.C w - m.Cd (hg.memLp.toLp g)‖ := by rw [hCw, add_sub_cancel_right]
      _ ≤ ‖m.sys.C w‖ + ‖m.Cd (hg.memLp.toLp g)‖ := norm_sub_le _ _
      _ ≤ |K| * (√(2 * ε) * ‖e‖) + ‖m.Cd‖ * (√(2 * ε) * ‖e‖) :=
          add_le_add ((hK w).trans hK') (m.Cd.le_opNorm_of_le hgn)
      _ = (|K| + ‖m.Cd‖) * (√(2 * ε) * ‖e‖) := by ring
  have hlim : Tendsto (fun ε : ℝ => (|K| + ‖m.Cd‖) * (√(2 * ε) * ‖e‖)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => √(2 * ε)) (𝓝 0) (𝓝 0) := by
      have := (show Continuous fun ε : ℝ => √(2 * ε) by fun_prop).tendsto 0
      rwa [mul_zero, Real.sqrt_zero] at this
    simpa using ((h0.mono_left nhdsWithin_le_nhds).mul_const ‖e‖).const_mul (|K| + ‖m.Cd‖)
  exact he (norm_le_zero_iff.1 (ge_of_tendsto hlim hbound))

/-- **`C` is unbounded on `X`** as soon as some output coefficient `C_{k₀} ≠ 0` sits at a positive
delay `h'_{k₀} > 0` shared by no other coefficient (`ex:intro-delay`). -/
theorem not_exists_bound_C_of_ne_zero (k₀ : Fin m.NC) (hk₀ : m.Cp k₀ ≠ 0) (hτ : 0 < m.τC k₀)
    (hdist : ∀ k, m.τC k = m.τC k₀ → k = k₀) :
    ¬ ∃ K : ℝ, ∀ w : m.S.Dom, ‖m.sys.C w‖ ≤ K * ‖m.sys.ιW w‖ := by
  refine m.not_exists_bound_C ⟨hτ, (m.τC_mem k₀).2⟩ ?_
  have e : Finset.univ.filter (fun k => m.τC k = m.τC k₀) = {k₀} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hdist k, fun hk => hk ▸ rfl⟩
  rw [e, Finset.sum_singleton]
  exact hk₀

end Model

end Delay

end DataDrivenControl
