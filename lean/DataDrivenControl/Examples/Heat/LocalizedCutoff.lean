module

public import DataDrivenControl.Examples.BoundaryHeat
public import DataDrivenControl.Examples.Heat.LocalizedKernel

/-!
# The cut-off `χ` and analytic tools for the localised heat space

Paper: `ex:boundary-heat-informative` (`informativity.tex`), `app:boundary-heat-informative`
(`appendix_proofs.tex`): the cut-off `χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀` in
`eq:heat-localized-V`, and the tools behind the paper's claims about `V`: continuity of right
translations in `L²` (strong continuity of `S` on `V`), the orthogonality of the derivatives of
the eigenfunctions (`∫₀^∞ e^{-2t} ‖S(t) z‖²_{H¹} dt = ½ ‖z‖²_X`), and eigenfunction series as
bounded continuous functions.

## Main declarations

* `Cutoff`: a `C¹` function `χ` with `tsupport χ ⊆ (0, 1)`; `Cutoff.exists_pos_le` (`d_χ > 0`),
  `Cutoff.eq_zero_of_notMem`, `Cutoff.deriv_eq_zero_of_notMem`, the bounded continuous functions
  `Cutoff.bcf` (`χ`) and `Cutoff.derivBcf` (`χ'`).
* `exists_smooth_cutoff`: **a cut-off exists**: for `ξ₀ ∈ (0, 1)` there is `χ ∈ C_c^∞(0, 1)` with
  `χ = 1` near `ξ₀` (a `ContDiffBump`); `exists_cutoff` packages it as a `Cutoff`.
* `tendsto_eLpNorm_comp_add_sub`: **continuity of translation in `L²(ℝ; E)`**, and
  `tendsto_eLpNorm_comp_add_sub_Ioi`, its right-translation form on `L²(0, ∞; E)`;
  `memLp_comp_add_Ioi`, `eLpNorm_comp_add_Ioi_le`.
* `seriesCLM κ β g`: `a ↦ ∑ₙ (κₙ aₙ) gₙ` from `ℓ²` to `ℝ →ᵇ ℝ` (`hasSum_seriesCLM_apply`).
* `hasSum_sq_of_orthogonal`: `‖∑ₙ cₙ uₙ‖² = ∑ₙ cₙ² rₙ` for `⟪uₙ, uₘ⟫ = [n = m] rₙ`.
* `cosDerivBCF`, `integral_cosDeriv_mul_cosDeriv` (`∫₀¹ eₙ' eₘ' = -λₙ [n = m]`),
  `inner_toL2_cosDerivBCF`.
* `heatModal`: the modal data `λₙ = -(nπ)²` of `Examples/Heat/Spaces`, without an observation
  (`X₋₁`, `S_{X₋₁}`, `X ↪ X₋₁`, `A_{X,-1}` do not depend on it).

## Deviation from the paper

The paper takes `χ ∈ C_c^∞(0, 1)`.  A `Cutoff` only needs `χ ∈ C¹` with compact support in
`(0, 1)`, which every `χ ∈ C_c^∞(0, 1)` satisfies; `exists_smooth_cutoff` provides a smooth one.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BoundedContinuousFunction ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

namespace Localized

open CosineBasis

/-! ### The cut-off -/

/-- **The cut-off `χ`** of `eq:heat-localized-V`: a `C¹` function with compact support in
`(0, 1)`.  The paper takes `χ ∈ C_c^∞(0, 1)`; one derivative suffices here.  The condition
"`χ = 1` near `ξ₀`" is a separate hypothesis where it is needed. -/
structure Cutoff where
  /-- The function `χ`. -/
  toFun : ℝ → ℝ
  /-- `χ ∈ C¹`. -/
  contDiff : ContDiff ℝ 1 toFun
  /-- `supp χ ⊆ (0, 1)`. -/
  tsupport_subset : tsupport toFun ⊆ Ioo 0 1

namespace Cutoff

instance : CoeFun Cutoff fun _ => ℝ → ℝ := ⟨Cutoff.toFun⟩

variable (χ : Cutoff)

/-- `χ` has compact support. -/
theorem hasCompactSupport : HasCompactSupport χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (χ.tsupport_subset.trans Ioo_subset_Icc_self)

/-- `χ` is continuous. -/
theorem continuous : Continuous χ := χ.contDiff.continuous

/-- `χ'` is continuous. -/
theorem continuous_deriv : Continuous (deriv χ) := χ.contDiff.continuous_deriv le_rfl

/-- `χ` is differentiable. -/
theorem differentiable : Differentiable ℝ χ := χ.contDiff.differentiable one_ne_zero

/-- `χ' = deriv χ`. -/
theorem hasDerivAt (ξ : ℝ) : HasDerivAt χ (deriv χ ξ) ξ := (χ.differentiable ξ).hasDerivAt

/-- `χ'` has compact support. -/
theorem hasCompactSupport_deriv : HasCompactSupport (deriv χ) := χ.hasCompactSupport.deriv

/-- `χ` vanishes outside its support. -/
theorem eq_zero_of_notMem {ξ : ℝ} (h : ξ ∉ tsupport χ) : χ ξ = 0 :=
  image_eq_zero_of_notMem_tsupport h

/-- `χ'` vanishes outside the support of `χ`. -/
theorem deriv_eq_zero_of_notMem {ξ : ℝ} (h : ξ ∉ tsupport χ) : deriv χ ξ = 0 :=
  Function.notMem_support.1 fun h' => h (support_deriv_subset h')

/-- `χ(0) = 0`. -/
theorem apply_zero : χ 0 = 0 := χ.eq_zero_of_notMem fun h => lt_irrefl _ (χ.tsupport_subset h).1

/-- `d_χ = dist(supp χ, 0) > 0`: the support lies in `[d, 1)` for some `d > 0`. -/
theorem exists_pos_le : ∃ d > 0, ∀ ξ ∈ tsupport χ, d ≤ ξ := by
  rcases (tsupport χ).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨ξm, hm, hmin⟩ := χ.hasCompactSupport.exists_isMinOn h continuousOn_id
    exact ⟨ξm, (χ.tsupport_subset hm).1, fun ξ hξ => isMinOn_iff.1 hmin ξ hξ⟩

/-- `χ` as a bounded continuous function. -/
def bcf : ℝ →ᵇ ℝ := ofCompactSupport χ χ.continuous χ.hasCompactSupport

/-- `χ'` as a bounded continuous function. -/
def derivBcf : ℝ →ᵇ ℝ := ofCompactSupport (deriv χ) χ.continuous_deriv χ.hasCompactSupport_deriv

/-- `bcf` is `χ`. -/
@[simp] theorem bcf_apply (ξ : ℝ) : χ.bcf ξ = χ ξ := rfl

/-- `derivBcf` is `χ'`. -/
@[simp] theorem derivBcf_apply (ξ : ℝ) : χ.derivBcf ξ = deriv χ ξ := rfl

end Cutoff

/-- **A cut-off exists** (`app:boundary-heat-informative`): for `ξ₀ ∈ (0, 1)` there is
`χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀` (a smooth bump function `ContDiffBump` around `ξ₀`). -/
theorem exists_smooth_cutoff {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Ioo 0 1 ∧ χ =ᶠ[𝓝 ξ₀] 1 := by
  set r := min ξ₀ (1 - ξ₀) with hr
  have hr0 : 0 < r := lt_min hξ₀.1 (by linarith [hξ₀.2])
  have h1 : r ≤ ξ₀ := min_le_left _ _
  have h2 : r ≤ 1 - ξ₀ := min_le_right _ _
  let f : ContDiffBump ξ₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, ?_, ?_⟩
  · rw [f.tsupport_eq]
    intro ξ hξ
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hξ
    have h3 : f.rOut = r / 2 := rfl
    rw [h3] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · filter_upwards [Metric.ball_mem_nhds ξ₀ (by positivity : (0 : ℝ) < r / 4)] with ξ hξ
    exact f.one_of_mem_closedBall (Metric.ball_subset_closedBall hξ)

/-- A `Cutoff` equal to one near `ξ₀ ∈ (0, 1)` exists. -/
theorem exists_cutoff {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) : ∃ χ : Cutoff, ⇑χ =ᶠ[𝓝 ξ₀] 1 := by
  obtain ⟨χ, hχ, hs, h1⟩ := exists_smooth_cutoff hξ₀
  exact ⟨⟨χ, hχ.of_le (by exact_mod_cast le_top), hs⟩, h1⟩

/-! ### Continuity of translation in `L²` -/

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Continuity of translation in `L²(ℝ; E)`**: `‖f(· + s) - f‖_{L²(ℝ)} → 0` as `s → 0`
(approximation by a continuous compactly supported function, which is uniformly continuous). -/
theorem tendsto_eLpNorm_comp_add_sub {f : ℝ → E} (hf : MemLp f 2 volume) :
    Tendsto (fun s => eLpNorm (fun t => f (t + s) - f t) 2 volume) (𝓝 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  set η : ℝ := (min ε 1).toReal / 3 with hη
  have hm1 : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hm0 : 0 < (min ε 1).toReal := ENNReal.toReal_pos (lt_min hε one_pos).ne' hm1
  have hη0 : 0 < η := by positivity
  have h3η : ENNReal.ofReal (3 * η) ≤ ε := by
    rw [hη, mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal hm1]
    exact min_le_left _ _
  obtain ⟨g, hgc, hfg, hg, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη0).ne'
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hgc.isCompact.isBounded
  set ν := volume.restrict (Metric.closedBall (0 : ℝ) (R + 1)) with hν
  have hνt : ν univ ≠ ⊤ := by
    rw [hν, Measure.restrict_apply_univ]; exact measure_closedBall_lt_top.ne
  set M := ν univ ^ (2 : ℝ≥0∞).toReal⁻¹ with hM
  have hMt : M ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hνt
  set K := M.toReal with hK
  have hu := hgc.uniformContinuous_of_continuous hg
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨δ, hδ, hδε⟩ := hu (η / (K + 1)) (by positivity)
  have hg0 : ∀ t, R < |t| → g t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have := hR h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ one_pos)] with s hs
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, lt_min_iff] at hs
  have hgs : eLpNorm (fun t => g (t + s) - g t) 2 volume ≤ ENNReal.ofReal η := by
    have hmeas : AEStronglyMeasurable (fun t => g (t + s) - g t) volume :=
      ((hg.comp (continuous_id.add continuous_const)).sub hg).aestronglyMeasurable
    have hsupp : (fun t => g (t + s) - g t).support ⊆ Metric.closedBall 0 (R + 1) := by
      intro t ht
      by_contra hc
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hc
      apply ht
      have h1 : R < |t + s| := by
        have := abs_add_le (t + s) (-s)
        rw [add_neg_cancel_right, abs_neg] at this
        linarith [hs.2]
      simp only [hg0 t (by linarith), hg0 (t + s) h1, sub_zero]
    rw [← eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
    refine (eLpNorm_le_of_ae_bound hmeas.restrict (C := η / (K + 1))
      (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [← dist_eq_norm]
      refine (hδε ?_).le
      rw [Real.dist_eq, add_sub_cancel_left]
      exact hs.1
    · rw [← hM, ← ENNReal.ofReal_toReal hMt, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hK]
      refine ENNReal.ofReal_le_ofReal ?_
      have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
  have hfgm : AEStronglyMeasurable (f - g) volume :=
    hf.aestronglyMeasurable.sub hgm.aestronglyMeasurable
  have hsplit : (fun t => f (t + s) - f t) =
      ((fun t => (f - g) (t + s)) + fun t => g (t + s) - g t) + fun t => (g - f) t := by
    funext t; simp only [Pi.add_apply, Pi.sub_apply]; abel
  have hshift : eLpNorm (fun t => (f - g) (t + s)) 2 volume = eLpNorm (f - g) 2 volume :=
    eLpNorm_comp_measurePreserving (f := fun t => t + s) hfgm (measurePreserving_add_right _ s)
  have hm1' : AEStronglyMeasurable (fun t => (f - g) (t + s)) volume :=
    hfgm.comp_measurePreserving (measurePreserving_add_right _ s)
  have hm2 : AEStronglyMeasurable (fun t => g (t + s) - g t) volume :=
    ((hg.comp (continuous_id.add continuous_const)).sub hg).aestronglyMeasurable
  rw [hsplit]
  calc eLpNorm (((fun t => (f - g) (t + s)) + fun t => g (t + s) - g t) + fun t => (g - f) t) 2
        volume
      ≤ eLpNorm ((fun t => (f - g) (t + s)) + fun t => g (t + s) - g t) 2 volume +
          eLpNorm (fun t => (g - f) t) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun t => (f - g) (t + s)) 2 volume +
          eLpNorm (fun t => g (t + s) - g t) 2 volume) + eLpNorm (g - f) 2 volume := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal η + ENNReal.ofReal η) + ENNReal.ofReal η := by
        rw [hshift, eLpNorm_sub_comm g f]
        gcongr
    _ = ENNReal.ofReal (3 * η) := by
        rw [← ENNReal.ofReal_add hη0.le hη0.le, ← ENNReal.ofReal_add (by positivity) hη0.le]
        ring_nf
    _ ≤ ε := h3η

/-- Right translation `t ↦ t + s`, `s ≥ 0`, maps `Lᵖ(0, ∞)` into itself. -/
theorem memLp_comp_add_Ioi {f : ℝ → E} {q : ℝ≥0∞} (hf : MemLp f q (volume.restrict (Ioi 0)))
    {s : ℝ} (hs : 0 ≤ s) : MemLp (fun t => f (t + s)) q (volume.restrict (Ioi 0)) := by
  have hmp := (measurePreserving_add_right volume s).restrict_preimage (s := Ioi s)
    measurableSet_Ioi
  rw [preimage_add_const_Ioi, sub_self] at hmp
  exact (hf.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl)).comp_measurePreserving
    hmp

/-- Right translation by `s ≥ 0` does not increase the norm in `Lᵖ(0, ∞)`. -/
theorem eLpNorm_comp_add_Ioi_le {f : ℝ → E} {q : ℝ≥0∞}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) {s : ℝ} (hs : 0 ≤ s) :
    eLpNorm (fun t => f (t + s)) q (volume.restrict (Ioi 0)) ≤
      eLpNorm f q (volume.restrict (Ioi 0)) := by
  have hmp := (measurePreserving_add_right volume s).restrict_preimage (s := Ioi s)
    measurableSet_Ioi
  rw [preimage_add_const_Ioi, sub_self] at hmp
  have hmono : volume.restrict (Ioi s) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl
  calc eLpNorm (fun t => f (t + s)) q (volume.restrict (Ioi 0))
      = eLpNorm f q (volume.restrict (Ioi s)) :=
        eLpNorm_comp_measurePreserving (f := fun t => t + s) (hf.mono_measure hmono) hmp
    _ ≤ eLpNorm f q (volume.restrict (Ioi 0)) := eLpNorm_mono_measure _ hmono

/-- **Continuity of right translation in `L²(0, ∞; E)`**: `‖f(· + s) - f‖ → 0` as `s → 0⁺`. -/
theorem tendsto_eLpNorm_comp_add_sub_Ioi {f : ℝ → E} (hf : MemLp f 2 (volume.restrict (Ioi 0))) :
    Tendsto (fun s => eLpNorm (fun t => f (t + s) - f t) 2 (volume.restrict (Ioi 0)))
      (𝓝[≥] 0) (𝓝 0) := by
  set F := (Ioi (0 : ℝ)).indicator f with hF
  have hFm : MemLp F 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hf
  have h := (tendsto_eLpNorm_comp_add_sub hFm).mono_left (nhdsWithin_le_nhds (s := Ici 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) ≤ s := hs
  calc eLpNorm (fun t => f (t + s) - f t) 2 (volume.restrict (Ioi 0))
      = eLpNorm (fun t => F (t + s) - F t) 2 (volume.restrict (Ioi 0)) := by
        refine eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
        have ht' : (0 : ℝ) < t := ht
        simp only [hF, indicator_of_mem (show t + s ∈ Ioi (0 : ℝ) from
          show (0 : ℝ) < t + s by linarith), indicator_of_mem ht]
    _ ≤ eLpNorm (fun t => F (t + s) - F t) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self

end Translation

/-! ### Eigenfunction series as bounded continuous functions -/

/-- `∑ₙ |aₙ| |bₙ| < ∞` for square-summable `a`, `b`. -/
theorem summable_abs_mul_abs {a b : ℕ → ℝ} (ha : Summable fun n => a n ^ 2)
    (hb : Summable fun n => b n ^ 2) : Summable fun n => |a n| * |b n| :=
  ((ha.add hb).div_const 2).of_nonneg_of_le (fun n => by positivity) fun n => by
    nlinarith [sq_abs (a n), sq_abs (b n), sq_nonneg (|a n| - |b n|)]

/-- Cauchy–Schwarz in `ℓ²`: `∑ₙ |aₙ| |bₙ| ≤ (∑ aₙ²)^{1/2} (∑ bₙ²)^{1/2}`. -/
theorem tsum_abs_mul_abs_le {a b : ℕ → ℝ} (ha : Summable fun n => a n ^ 2)
    (hb : Summable fun n => b n ^ 2) :
    ∑' n, |a n| * |b n| ≤ Real.sqrt (∑' n, a n ^ 2) * Real.sqrt (∑' n, b n ^ 2) := by
  set A := mkL2 (fun n => |a n|) (by simpa only [sq_abs] using ha) with hA
  set B := mkL2 (fun n => |b n|) (by simpa only [sq_abs] using hb) with hB
  have h1 : ⟪A, B⟫_ℝ = ∑' n, |a n| * |b n| := by
    rw [← (lp.hasSum_inner A B).tsum_eq]
    exact tsum_congr fun n => by
      rw [RCLike.inner_apply, conj_trivial, hA, hB, mkL2_apply, mkL2_apply, mul_comm]
  have hn : ∀ (c : ℕ → ℝ) (hc : Summable fun n => |c n| ^ 2),
      ‖mkL2 (fun n => |c n|) hc‖ = Real.sqrt (∑' n, c n ^ 2) := by
    intro c hc
    rw [← Real.sqrt_sq (norm_nonneg _), ← (hasSum_sq (mkL2 (fun n => |c n|) hc)).tsum_eq]
    simp only [mkL2_apply, sq_abs]
  rw [← h1, ← hn a, ← hn b]
  exact real_inner_le_norm A B

section Series

variable (κ β : ℕ → ℝ) (g : ℕ → ℝ →ᵇ ℝ) (hg : ∀ n, ‖g n‖ ≤ β n)
  (h : Summable fun n => (κ n * β n) ^ 2)

include hg h in
/-- The series `∑ₙ (κₙ aₙ) gₙ` converges absolutely in `ℝ →ᵇ ℝ`. -/
theorem summable_norm_series (a : Xm1) : Summable fun n => ‖(κ n * a n) • g n‖ := by
  refine (summable_abs_mul_abs (summable_sq a) h).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul (κ n)]
  have hb : ‖g n‖ ≤ |β n| := (hg n).trans (le_abs_self _)
  calc |κ n| * |a n| * ‖g n‖ ≤ |κ n| * |a n| * |β n| := by gcongr
    _ = |a n| * (|κ n| * |β n|) := by ring

/-- `a ↦ ∑ₙ (κₙ aₙ) gₙ` from `ℓ²` to bounded continuous functions, for `‖gₙ‖ ≤ βₙ` and
`∑ₙ (κₙ βₙ)² < ∞` (`‖·‖ ≤ (∑ (κₙ βₙ)²)^{1/2}`). -/
def seriesCLM : Xm1 →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' n, (κ n * a n) • g n
      map_add' := fun a b => by
        have ha := (summable_norm_series κ β g hg h a).of_norm
        have hb := (summable_norm_series κ β g hg h b).of_norm
        rw [← ha.tsum_add hb]
        exact tsum_congr fun n => by
          rw [lp.coeFn_add, Pi.add_apply, mul_add, add_smul]
      map_smul' := fun c a => by
        have ha := (summable_norm_series κ β g hg h a).of_norm
        rw [RingHom.id_apply, ← (ha.hasSum.const_smul c).tsum_eq]
        exact tsum_congr fun n => by
          rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, smul_smul]
          ring_nf }
    (Real.sqrt (∑' n, (κ n * β n) ^ 2)) fun a => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_tsum_le_tsum_norm (summable_norm_series κ β g hg h a)).trans ?_
      have hle : ∀ n, ‖(κ n * a n) • g n‖ ≤ |a n| * |κ n * β n| := fun n => by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul (κ n)]
        have hb : ‖g n‖ ≤ |β n| := (hg n).trans (le_abs_self _)
        calc |κ n| * |a n| * ‖g n‖ ≤ |κ n| * |a n| * |β n| := by gcongr
          _ = |a n| * (|κ n| * |β n|) := by ring
      refine (Summable.tsum_le_tsum hle (summable_norm_series κ β g hg h a)
        (summable_abs_mul_abs (summable_sq a) h)).trans ?_
      refine (tsum_abs_mul_abs_le (summable_sq a) h).trans (le_of_eq ?_)
      rw [(hasSum_sq a).tsum_eq, Real.sqrt_sq (norm_nonneg a), mul_comm]

/-- `seriesCLM κ β g a = ∑ₙ (κₙ aₙ) gₙ`. -/
theorem seriesCLM_apply (a : Xm1) : seriesCLM κ β g hg h a = ∑' n, (κ n * a n) • g n := rfl

/-- The series `∑ₙ (κₙ aₙ) gₙ` converges in `ℝ →ᵇ ℝ`. -/
theorem hasSum_seriesCLM (a : Xm1) :
    HasSum (fun n => (κ n * a n) • g n) (seriesCLM κ β g hg h a) :=
  (summable_norm_series κ β g hg h a).of_norm.hasSum

/-- Pointwise: `(∑ₙ (κₙ aₙ) gₙ)(ξ) = ∑ₙ κₙ aₙ gₙ(ξ)`. -/
theorem hasSum_seriesCLM_apply (a : Xm1) (ξ : ℝ) :
    HasSum (fun n => κ n * a n * g n ξ) (seriesCLM κ β g hg h a ξ) := by
  simpa using (hasSum_seriesCLM κ β g hg h a).mapL (BoundedContinuousFunction.evalCLM ℝ ξ)

end Series

/-! ### Orthogonal series -/

/-- **The norm of an orthogonal series**: if `∑ₙ cₙ uₙ = y` and `⟪uₙ, uₘ⟫ = [n = m] rₙ`, then
`‖y‖² = ∑ₙ cₙ² rₙ`. -/
theorem hasSum_sq_of_orthogonal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : ℕ → H} {r c : ℕ → ℝ} (hu : ∀ n m, ⟪u n, u m⟫_ℝ = if n = m then r n else 0) {y : H}
    (hy : HasSum (fun n => c n • u n) y) : HasSum (fun n => c n ^ 2 * r n) (‖y‖ ^ 2) := by
  have h1 : ∀ n, ⟪u n, y⟫_ℝ = c n * r n := by
    intro n
    have := hy.mapL (innerSL ℝ (u n))
    simp only [innerSL_apply_apply, inner_smul_right, hu] at this
    have e : (fun m => c m * (if n = m then r n else 0)) =
        fun m => if m = n then c n * r n else 0 := by
      funext m
      by_cases hm : m = n
      · subst hm; simp
      · simp [hm, Ne.symm hm]
    rw [e] at this
    exact this.unique (hasSum_ite_eq n _)
  have h2 := hy.mapL (innerSL ℝ y)
  simp only [innerSL_apply_apply, inner_smul_right] at h2
  rw [← real_inner_self_eq_norm_sq]
  convert h2 using 1
  funext n
  rw [real_inner_comm, h1]
  ring

/-! ### The derivatives of the eigenfunctions -/

/-- `eₙ'` as a bounded continuous function (`‖eₙ'‖_∞ ≤ √2 π n`). -/
def cosDerivBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cosDeriv n) (continuous_cosDeriv n)
    (Real.sqrt 2 * Real.pi * n) fun ξ => by rw [Real.norm_eq_abs]; exact abs_cosDeriv_le n ξ

/-- `cosDerivBCF n` is `eₙ'`. -/
@[simp] theorem cosDerivBCF_apply (n : ℕ) (ξ : ℝ) : cosDerivBCF n ξ = cosDeriv n ξ := rfl

/-- `‖eₙ'‖_∞ ≤ √2 π n`. -/
theorem norm_cosDerivBCF_le (n : ℕ) : ‖cosDerivBCF n‖ ≤ Real.sqrt 2 * Real.pi * n :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- **Orthogonality of the derivatives**: `∫₀¹ eₙ' eₘ' = -λₙ [n = m]` (integration by parts,
`eₙ'(0) = eₙ'(1) = 0`, `eₙ'' = λₙ eₙ`). -/
theorem integral_cosDeriv_mul_cosDeriv (n m : ℕ) :
    ∫ ξ in (0 : ℝ)..1, cosDeriv n ξ * cosDeriv m ξ = if n = m then -cosEig n else 0 := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := cosDeriv n) (u' := fun ξ => cosEig n * cosFun n ξ) (v := cosFun m) (v' := cosDeriv m)
    (fun ξ _ => hasDerivAt_cosDeriv n ξ) (fun ξ _ => hasDerivAt_cosFun m ξ)
    (((continuous_cosFun n).const_mul _).intervalIntegrable _ _)
    ((continuous_cosDeriv m).intervalIntegrable _ _)
  rw [h, cosDeriv_one, cosDeriv_zero]
  have e : ∫ ξ in (0 : ℝ)..1, cosEig n * cosFun n ξ * cosFun m ξ =
      cosEig n * ∫ ξ in (0 : ℝ)..1, cosFun n ξ * cosFun m ξ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun ξ _ => by ring
  rw [e, integral_cosFun_mul_cosFun]
  split_ifs <;> ring

/-- `⟪[eₙ'], [eₘ']⟫_{L²(0,1)} = -λₙ [n = m]`. -/
theorem inner_toL2_cosDerivBCF (n m : ℕ) :
    ⟪toL2 (cosDerivBCF n), toL2 (cosDerivBCF m)⟫_ℝ = if n = m then -cosEig n else 0 := by
  rw [inner_toL2]
  exact integral_cosDeriv_mul_cosDeriv n m

/-- `⟪[eₙ], [eₘ]⟫_{L²(0,1)} = [n = m]`. -/
theorem inner_toL2_cosBCF (n m : ℕ) :
    ⟪toL2 (cosBCF n), toL2 (cosBCF m)⟫_ℝ = if n = m then 1 else 0 := by
  rw [inner_toL2]
  exact integral_cosFun_mul_cosFun n m

/-- `‖[f]‖²_{L²(0,1)} = ∫₀¹ f²` for a bounded continuous `f`. -/
theorem norm_toL2_sq (f : ℝ →ᵇ ℝ) : ‖toL2 f‖ ^ 2 = ∫ ξ in Ioc 0 1, f ξ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toL2, intervalIntegral.integral_of_le zero_le_one]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only [sq])

/-! ### The modal data -/

/-- The modal data of the Neumann heat equation without an observation: `λₙ = -(nπ)²`.  The
extrapolation space `X₋₁`, `S_{X₋₁}`, `X ↪ X₋₁`, `A_{X,-1}` and the smoothing `S(t) : X₋₁ → X` of
`Examples/Heat/Spaces` depend only on the eigenvalues. -/
def heatModal : ModalData where
  lam := eig
  c := fun _ => 0
  lam_nonpos := eig_nonpos
  summable_inv_wt := summable_inv_one_sub_eig
  exists_abs_c_le := ⟨0, fun _ => by simp⟩

/-- The weights `wₙ = 1 - λₙ`. -/
theorem heatModal_wt (n : ℕ) : heatModal.wt n = 1 - eig n := rfl

/-- The eigenvalues `λₙ`. -/
theorem heatModal_lam : heatModal.lam = eig := rfl

end Localized

end BoundaryHeat

end DataDrivenControl
