module

public import DataDrivenControl.Examples.Delay.System

/-!
# The output operator of the delay system is unbounded on `X`

Paper: `ex:intro-delay` ("a discrete output delay generally makes `C` unbounded on `X`"), stated
as `¬ ∃ K, ∀ w, ‖C w‖ ≤ K ‖ιW w‖`.

* `DelayOp.atom p θ = ∑ₖ μₖ({θ}) Pₖ`: the atom at the delay `θ` of the measure part of a delay
  functional (the paper's `C({θ})` for the matrix measure representing `C`).
* `Model.not_exists_bound_C`: if `θ ∈ (0, h]` and `C({θ}) + C({0}) M({θ}) ≠ 0`, then `C` is not
  bounded by the `X`-norm on `W = D(A)`.  `Model.not_exists_bound_C_of_atom_zero`: if `C` has no
  atom at `0`, every `θ ∈ (0, h]` with `C({θ}) ≠ 0` works, whatever the atoms of `M`.

## Proof notes

Pick `e` with `(C({θ}) + C({0}) M({θ})) e ≠ 0` and put `e' = M({θ}) e`.  Let `g_n = φ_n e + ψ_n e'`
with smooth bumps `φ_n` at `h - θ` and `ψ_n` at `h` (`bump`, radii `1/(2(n+1)) < 1/(n+1)`), equal
to `1` at their centres.  By dominated convergence `∫ φ_n(h - δ) dν(δ) → ν({θ})` and
`∫ ψ_n(h - δ) dν(δ) → ν({0})` for every finite measure `ν` (`tendsto_integral_bump`), and
`‖g_n‖_{L²} → 0` (`tendsto_window_bump`), so `P g_n → P({θ}) e + P({0}) e'` for every delay
functional `P` (`DelayOp.tendsto_eval_bump`).  The state `w_n = (g_n(h) - M g_n, g_n) ∈ D(A)` has
`g_n(h) = e'` for large `n` and `M g_n → M({θ}) e = e'` (`M` has no atom at `0`), so
`‖w_n‖_X → 0`, while `C w_n = C g_n → C({θ}) e + C({0}) e' ≠ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E F U Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-! ### Concentrating bumps -/

/-- A smooth bump at `c`, equal to `1` on `[c - 1/(2(n+1)), c + 1/(2(n+1))]` and vanishing
outside `(c - 1/(n+1), c + 1/(n+1))`. -/
def bump (c : ℝ) (n : ℕ) : ContDiffBump c :=
  ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity,
    one_div_lt_one_div_of_lt (by positivity) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])⟩

/-- **Bumps concentrate**: `∫ φ_n(h - δ) dν(δ) → ν({h - c})` for the bumps `φ_n` at `c`
(dominated convergence). -/
theorem tendsto_integral_bump {ν : Measure ℝ} [IsFiniteMeasure ν] (h c : ℝ) :
    Tendsto (fun n : ℕ => ∫ δ, bump c n (h - δ) ∂ν) atTop (𝓝 (ν.real {h - c})) := by
  rw [← integral_indicator_one (measurableSet_singleton (h - c))]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => ((bump c n).continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ fun δ => ?_) (ae_of_all _ fun δ => ?_)
  · rw [Real.norm_of_nonneg ((bump c n).nonneg' _)]
    exact (bump c n).le_one
  · by_cases hδ : δ = h - c
    · subst hδ
      simp only [indicator_of_mem (mem_singleton _), Pi.one_apply, sub_sub_cancel]
      exact tendsto_const_nhds.congr fun n => ((bump c n).one_of_mem_closedBall
        (Metric.mem_closedBall_self (bump c n).rIn_pos.le)).symm
    · rw [indicator_of_notMem (by simpa using hδ)]
      have hpos : 0 < |h - δ - c| := abs_pos.2 fun h0 => hδ (by linarith)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (eventually_le_nhds hpos)] with n hn
      exact ((bump c n).zero_of_le_dist (by rw [Real.dist_eq]; exact hn)).symm

/-- `‖φ_n e‖_{L²(0, T)} ≤ √(2/(n+1)) ‖e‖`. -/
theorem eLpNorm_bump_smul_le (c : ℝ) (n : ℕ) (e : E) (T : ℝ) :
    eLpNorm (fun σ => bump c n σ • e) 2 (μI T) ≤
      ENNReal.ofReal (√(2 * (1 / ((n : ℝ) + 1))) * ‖e‖) := by
  have hpt : ∀ σ, ‖bump c n σ • e‖ ≤
      (Metric.ball c (1 / ((n : ℝ) + 1))).indicator (fun _ => ‖e‖) σ := by
    intro σ
    by_cases hσ : σ ∈ Metric.ball c (1 / ((n : ℝ) + 1))
    · rw [indicator_of_mem hσ, norm_smul, Real.norm_of_nonneg ((bump c n).nonneg' σ)]
      exact mul_le_of_le_one_left (norm_nonneg _) (bump c n).le_one
    · rw [indicator_of_notMem hσ, (bump c n).zero_of_le_dist (by exact not_lt.1 hσ), zero_smul,
        norm_zero]
  calc eLpNorm (fun σ => bump c n σ • e) 2 (μI T)
      ≤ eLpNorm ((Metric.ball c (1 / ((n : ℝ) + 1))).indicator fun _ => ‖e‖) 2 (μI T) :=
        eLpNorm_mono_real (((bump c n).continuous.smul continuous_const).aestronglyMeasurable) hpt
    _ ≤ ‖‖e‖‖ₑ * (μI T) (Metric.ball c (1 / ((n : ℝ) + 1))) ^ (1 / (2 : ℝ≥0∞).toReal) :=
        eLpNorm_indicator_const_le ‖e‖ 2 measurableSet_ball.nullMeasurableSet
    _ ≤ ‖‖e‖‖ₑ * (ENNReal.ofReal (2 * (1 / ((n : ℝ) + 1)))) ^ (1 / (2 : ℝ≥0∞).toReal) := by
        gcongr
        exact (Measure.restrict_apply_le _ _).trans (Real.volume_ball c _).le
    _ = ENNReal.ofReal (√(2 * (1 / ((n : ℝ) + 1))) * ‖e‖) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm, Real.sqrt_eq_rpow,
          ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ofReal_norm, norm_norm]
        norm_num

/-- The bumps `g_n = φ_n e + ψ_n e'` at `h - θ` and `h` tend to `0` in `L²(0, h)`. -/
theorem tendsto_window_bump (h θ : ℝ) (e e' : E) :
    Tendsto (fun n : ℕ => window h (fun σ => bump (h - θ) n σ • e + bump h n σ • e') 0) atTop
      (𝓝 0) := by
  have hc : ∀ (c : ℝ) (n : ℕ) (v : E), Continuous fun σ => bump c n σ • v := fun c n v =>
    (bump c n).continuous.smul continuous_const
  have hb : ∀ n : ℕ, ‖window h (fun σ => bump (h - θ) n σ • e + bump h n σ • e') 0‖ ≤
      √(2 * (1 / ((n : ℝ) + 1))) * (‖e‖ + ‖e'‖) := fun n => by
    rw [window_zero_eq_toLp (memLp_μI_of_continuousOn
      (f := fun σ => bump (h - θ) n σ • e + bump h n σ • e')
      ((hc (h - θ) n e).add (hc h n e')).continuousOn), Lp.norm_toLp]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((eLpNorm_add_le one_le_two).trans ?_)
    rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (eLpNorm_bump_smul_le _ n e h) (eLpNorm_bump_smul_le _ n e' h)
  have h0 : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine squeeze_zero_norm hb ?_
  simpa using ((Real.continuous_sqrt.tendsto 0).comp h0).mul_const (‖e‖ + ‖e'‖)

/-! ### Atoms of delay functionals -/

namespace DelayOp

variable {h : ℝ} (p : DelayOp h E F)

/-- The **atom** `P({θ}) = ∑ₖ μₖ({θ}) Pₖ` of a delay functional at the delay `θ`. -/
def atom (θ : ℝ) : E →L[ℝ] F := ∑ k, (p.μ k).real {θ} • p.P k

/-- **Delay functionals on concentrating bumps**: for `g_n = φ_n e + ψ_n e'` with bumps `φ_n` at
`h - θ` and `ψ_n` at `h`, `p g_n → P({θ}) e + P({0}) e'`. -/
theorem tendsto_eval_bump (θ : ℝ) (e e' : E) :
    Tendsto (fun n : ℕ => p.eval (fun σ => bump (h - θ) n σ • e + bump h n σ • e') 0) atTop
      (𝓝 (p.atom θ e + p.atom 0 e')) := by
  have hi : ∀ (k : Fin p.N) (c : ℝ) (n : ℕ) (v : E),
      Integrable (fun δ => bump c n (h - δ) • v) (p.μ k) := fun k c n v =>
    Integrable.of_bound (((bump c n).continuous.comp (continuous_const.sub continuous_id)).smul
      continuous_const).aestronglyMeasurable ‖v‖ (ae_of_all _ fun δ => by
        rw [norm_smul, Real.norm_of_nonneg ((bump c n).nonneg' _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (bump c n).le_one)
  have hk : ∀ k, Tendsto (fun n : ℕ =>
      mconv (p.μ k) h (fun σ => bump (h - θ) n σ • e + bump h n σ • e') 0) atTop
      (𝓝 ((p.μ k).real {θ} • e + (p.μ k).real {0} • e')) := fun k => by
    have h1 := (tendsto_integral_bump (ν := p.μ k) h (h - θ)).smul_const e
    have h2 := (tendsto_integral_bump (ν := p.μ k) h h).smul_const e'
    rw [sub_sub_cancel] at h1
    rw [sub_self] at h2
    refine (h1.add h2).congr fun n => ?_
    simp only [mconv, add_zero]
    rw [integral_add (hi k _ n e) (hi k _ n e'), integral_smul_const, integral_smul_const]
  have e1 : p.atom θ e + p.atom 0 e' =
      ∑ k, p.P k ((p.μ k).real {θ} • e + (p.μ k).real {0} • e') + p.D 0 := by
    simp only [atom, sum_apply, smul_apply, map_add,
      map_smul, map_zero, add_zero, Finset.sum_add_distrib]
  rw [e1]
  exact (tendsto_finsetSum Finset.univ fun k _ => ((p.P k).continuous.tendsto _).comp (hk k)).add
    ((p.D.continuous.tendsto 0).comp (tendsto_window_bump h θ e e'))

end DelayOp

/-! ### Unboundedness of the output -/

namespace Model

variable {h : ℝ} (m : Model h E U Y)

/-- **`C` is unbounded on `X`** (`ex:intro-delay`): if at some delay `θ ∈ (0, h]` the atoms do not
cancel, `C({θ}) + C({0}) M({θ}) ≠ 0`, then no `K` gives `‖C w‖ ≤ K ‖w‖_X` on `W = D(A)`. -/
theorem not_exists_bound_C {θ : ℝ} (hθ : θ ∈ Ioc 0 h)
    (hC : m.C.atom θ + m.C.atom 0 ∘L m.M.atom θ ≠ 0) :
    ¬ ∃ K : ℝ, ∀ w : m.S.Dom, ‖m.sys.C w‖ ≤ K * ‖m.sys.ιW w‖ := by
  rintro ⟨K, hK⟩
  obtain ⟨e, he⟩ : ∃ e, (m.C.atom θ + m.C.atom 0 ∘L m.M.atom θ) e ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hC (ContinuousLinearMap.ext hne)
  set e' := m.M.atom θ e with he'
  set g : ℕ → ℝ → E := fun n σ => bump (h - θ) n σ • e + bump h n σ • e' with hgdef
  have hg : ∀ n, HasWeakDeriv h (g n)
      fun σ => deriv (bump (h - θ) n) σ • e + deriv (bump h n) σ • e' := fun n => by
    refine HasWeakDeriv.of_hasDerivAt (fun σ => ?_) ?_
    · exact ((((bump (h - θ) n).contDiff (n := 1)).differentiable (by norm_num) σ).hasDerivAt.smul_const
        e).add ((((bump h n).contDiff (n := 1)).differentiable (by norm_num) σ).hasDerivAt.smul_const e')
    · exact ((((bump (h - θ) n).contDiff (n := 2)).continuous_deriv (by norm_num)).smul
        continuous_const).add ((((bump h n).contDiff (n := 2)).continuous_deriv (by norm_num)).smul
        continuous_const)
  set w : ℕ → m.S.Dom := fun n =>
    m.S.toDom ⟨_, m.toEquation.mem_generator_domain_of_hasWeakDeriv (hg n)⟩
  have hCw : ∀ n, m.sys.C (w n) = m.C.eval (g n) 0 := fun n =>
    m.Cop_apply_eval (w n) (hg n) (hg n).memLp.coeFn_toLp
  have hιW : ∀ n, m.sys.ιW (w n) =
      WithLp.toLp 2 (g n h - m.M.eval (g n) 0, (hg n).memLp.toLp (g n)) := fun _ => rfl
  have hgh : ∀ᶠ n in atTop, g n h = e' := by
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (eventually_le_nhds hθ.1)] with n hn
    simp only [hgdef]
    rw [(bump (h - θ) n).zero_of_le_dist (by
        rw [Real.dist_eq, sub_sub_cancel, abs_of_pos hθ.1]; exact hn), zero_smul, zero_add,
      (bump h n).one_of_mem_closedBall (Metric.mem_closedBall_self (bump h n).rIn_pos.le),
      one_smul]
  have hM : Tendsto (fun n => m.M.eval (g n) 0) atTop (𝓝 e') := by
    have hM0 : m.M.atom 0 = 0 := by simp [DelayOp.atom, measureReal_def, m.M_noAtom]
    simpa [hM0, ← he'] using m.M.tendsto_eval_bump θ e e'
  have hX : Tendsto (fun n => ‖m.sys.ιW (w n)‖) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun n => ‖g n h - m.M.eval (g n) 0‖ + ‖(hg n).memLp.toLp (g n)‖)
      (fun n => norm_nonneg _) (fun n => by rw [hιW n]; exact norm_toLp_le _ _) ?_
    have h1 : Tendsto (fun n => g n h - m.M.eval (g n) 0) atTop (𝓝 0) := by
      have := (tendsto_const_nhds.congr' (hgh.mono fun n hn => hn.symm)).sub hM
      rwa [sub_self] at this
    have h2 : Tendsto (fun n => (hg n).memLp.toLp (g n)) atTop (𝓝 0) :=
      (tendsto_window_bump h θ e e').congr fun n => window_zero_eq_toLp (hg n).memLp
    simpa using h1.norm.add h2.norm
  have hle := le_of_tendsto_of_tendsto' (m.C.tendsto_eval_bump θ e e').norm (hX.const_mul K)
    fun n => by rw [← hCw n]; exact hK (w n)
  rw [mul_zero] at hle
  exact he (by
    rw [add_apply, ContinuousLinearMap.comp_apply]
    exact norm_le_zero_iff.1 hle)

/-- **`C` is unbounded on `X` when `C` has no atom at `0`**: then any nonzero atom
`C({θ}) ≠ 0` at a delay `θ ∈ (0, h]` makes `C` unbounded, whatever the atoms of `M`. -/
theorem not_exists_bound_C_of_atom_zero {θ : ℝ} (hθ : θ ∈ Ioc 0 h) (h0 : m.C.atom 0 = 0)
    (hC : m.C.atom θ ≠ 0) : ¬ ∃ K : ℝ, ∀ w : m.S.Dom, ‖m.sys.C w‖ ≤ K * ‖m.sys.ιW w‖ :=
  m.not_exists_bound_C hθ (by rwa [h0, ContinuousLinearMap.zero_comp, add_zero])

end Model

end Delay

end DataDrivenControl
