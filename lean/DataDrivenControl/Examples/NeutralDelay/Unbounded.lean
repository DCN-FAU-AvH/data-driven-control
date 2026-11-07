module

public import DataDrivenControl.Examples.NeutralDelay.System

/-!
# The output operator of the neutral delay system is unbounded on `X`

Paper: `ex:intro-delay` ("a discrete output delay generally makes `C` unbounded on `X`"), for the
neutral system, stated as `¬ ∃ K, ∀ w, ‖C w‖ ≤ K ‖ιW w‖`.

* `Model.not_exists_bound_C`: if the output coefficients at some delay `θ ∈ (0, h]` do not cancel,
  `∑_{h'ₖ = θ} Cₖ ≠ 0`, and no neutral point delay equals `θ`, then `C` is not bounded by the
  `X`-norm on `W = D(A)`.

## Proof notes

As for the retarded system (`Delay/Unbounded`): a bump `g_ε = φ_ε • e` centred at `h - θ` with
radius `ε` small gives `g_ε(h) = 0`, `C w_ε = (∑_{h'ₖ = θ} Cₖ) e + C_d g_ε` and
`‖g_ε‖_{L²} ≤ √(2ε) ‖e‖`.  Now the state is `(g_ε(h) - M g_ε, g_ε)`; since no neutral delay
equals `θ`, the point delays of `M` miss the bump for `ε` small, so the first component is
`-M_d g_ε` and `‖w_ε‖_X ≤ (1 + ‖M_d‖) ‖g_ε‖_{L²} → 0`.  (If a neutral delay equals `θ`, the first
component does not tend to `0`; the hypothesis is then needed in this form.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace NeutralDelay

open Delay (State norm_toLp_le window_zero_eq_toLp)

namespace Model

variable {E U Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {h : ℝ} (m : Model h E U Y)

/-- **`C` is unbounded on `X`** (`ex:intro-delay`, neutral system): if the output coefficients at
some delay `θ ∈ (0, h]` do not cancel, `∑_{h'ₖ = θ} Cₖ ≠ 0`, and no neutral point delay equals
`θ`, then no `K` gives `‖C w‖ ≤ K ‖w‖_X` on `W = D(A)`. -/
theorem not_exists_bound_C {θ : ℝ} (hθ : θ ∈ Ioc 0 h)
    (hC : ∑ k ∈ Finset.univ.filter (fun k => m.τC k = θ), m.Cp k ≠ 0)
    (hM : ∀ k, m.τM k ≠ θ) :
    ¬ ∃ K : ℝ, ∀ w : m.S.Dom, ‖m.sys.C w‖ ≤ K * ‖m.sys.ιW w‖ := by
  rintro ⟨K, hK⟩
  set Ch := ∑ k ∈ Finset.univ.filter (fun k => m.τC k = θ), m.Cp k with hCh
  obtain ⟨e, he⟩ : ∃ e, Ch e ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hC (ContinuousLinearMap.ext hne)
  set c := h - θ with hc
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < θ ∧ (∀ k, m.τC k ≠ θ → ε < |m.τC k - θ|) ∧
      ∀ k, ε < |m.τM k - θ| := by
    refine eventually_mem_nhdsWithin.and
      (((eventually_lt_nhds hθ.1).filter_mono nhdsWithin_le_nhds).and (Eventually.and ?_ ?_))
    · refine Filter.eventually_all.2 fun k => ?_
      by_cases hk : m.τC k = θ
      · exact Eventually.of_forall fun _ hk' => absurd hk hk'
      · exact ((eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hk))).filter_mono
          nhdsWithin_le_nhds).mono fun ε hε _ => hε
    · exact Filter.eventually_all.2 fun k => (eventually_lt_nhds
        (abs_pos.2 (sub_ne_zero.2 (hM k)))).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖Ch e‖ ≤ (|K| * (1 + ‖m.Md‖) + ‖m.Cd‖) * (√(2 * ε) * ‖e‖) := by
    filter_upwards [hev] with ε hε
    obtain ⟨hε0, hεθ, hεk, hεM⟩ := hε
    let φ : ContDiffBump c := ⟨ε / 2, ε, by linarith, by linarith⟩
    have hφr : φ.rOut = ε := rfl
    set g : ℝ → E := fun σ => φ σ • e with hgdef
    have hgd : ∀ σ, HasDerivAt g (deriv φ σ • e) σ := fun σ =>
      ((φ.contDiff (n := 1)).differentiable (by norm_num) σ).hasDerivAt.smul_const e
    have hgc : Continuous fun σ => deriv φ σ • e :=
      ((φ.contDiff (n := 2)).continuous_deriv (by norm_num)).smul continuous_const
    have hg : HasWeakDeriv h g (fun σ => deriv φ σ • e) := HasWeakDeriv.of_hasDerivAt hgd hgc
    have hv := m.toNeutral.mem_generator_domain_of_hasWeakDeriv hg
    set w := m.S.toDom ⟨_, hv⟩ with hwdef
    have hzero : ∀ σ, ε ≤ dist σ c → g σ = 0 := fun σ hσ => by
      simp only [hgdef]
      rw [φ.zero_of_le_dist (by rw [hφr]; exact hσ), zero_smul]
    have hgh : g h = 0 := hzero h (by
      rw [Real.dist_eq, hc, sub_sub_cancel, abs_of_pos hθ.1]
      exact hεθ.le)
    have hMg : m.M.eval g 0 = m.Md (hg.memLp.toLp g) := by
      rw [DelayOp.eval, window_zero_eq_toLp hg.memLp]
      have : ∑ k, m.M.P k (g (h - m.M.δ k + 0)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hzero _ (by
          rw [add_zero, Real.dist_eq, hc, sub_sub_sub_cancel_left, abs_sub_comm]
          exact (hεM k).le), map_zero]
      rw [this, zero_add]
      rfl
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
      rw [sys_C, m.Cop_apply w hg hg.memLp.coeFn_toLp, hsum]
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
    have hnw : ‖m.sys.ιW w‖ ≤ (1 + ‖m.Md‖) * ‖hg.memLp.toLp g‖ := by
      rw [show m.sys.ιW w = WithLp.toLp 2 (g h - m.M.eval g 0, hg.memLp.toLp g) from rfl, hgh,
        hMg, zero_sub]
      refine (norm_toLp_le _ _).trans ?_
      rw [norm_neg]
      have := m.Md.le_opNorm (hg.memLp.toLp g)
      linarith
    have hK' : K * ‖m.sys.ιW w‖ ≤ |K| * (1 + ‖m.Md‖) * (√(2 * ε) * ‖e‖) := by
      refine (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (hnw.trans ?_) (abs_nonneg K)
      exact mul_le_mul_of_nonneg_left hgn (by positivity)
    calc ‖Ch e‖ = ‖m.sys.C w - m.Cd (hg.memLp.toLp g)‖ := by rw [hCw, add_sub_cancel_right]
      _ ≤ ‖m.sys.C w‖ + ‖m.Cd (hg.memLp.toLp g)‖ := norm_sub_le _ _
      _ ≤ |K| * (1 + ‖m.Md‖) * (√(2 * ε) * ‖e‖) + ‖m.Cd‖ * (√(2 * ε) * ‖e‖) :=
          add_le_add ((hK w).trans hK') (m.Cd.le_opNorm_of_le hgn)
      _ = (|K| * (1 + ‖m.Md‖) + ‖m.Cd‖) * (√(2 * ε) * ‖e‖) := by ring
  have hlim : Tendsto (fun ε : ℝ => (|K| * (1 + ‖m.Md‖) + ‖m.Cd‖) * (√(2 * ε) * ‖e‖))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => √(2 * ε)) (𝓝 0) (𝓝 0) := by
      have := (show Continuous fun ε : ℝ => √(2 * ε) by fun_prop).tendsto 0
      rwa [mul_zero, Real.sqrt_zero] at this
    simpa using ((h0.mono_left nhdsWithin_le_nhds).mul_const ‖e‖).const_mul
      (|K| * (1 + ‖m.Md‖) + ‖m.Cd‖)
  exact he (norm_le_zero_iff.1 (ge_of_tendsto hlim hbound))

end Model

end NeutralDelay

end DataDrivenControl
