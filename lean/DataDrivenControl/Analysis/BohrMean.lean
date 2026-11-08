module

public import Mathlib

/-!
# Bohr means of almost periodic series

Paper: `def:harmonic-signal` and the remark after it (the
coefficients of a harmonic signal are recovered by the Bohr mean `ĥ(ωₗ) = vₗ`),
`app:harmonic-pe`, `lem:harmonic-pe-implies-pe` and `lem:bohr-annihilator`.

## Main definitions

* `HasMeanValue g v`: `S⁻¹ ∫₀^S g t dt → v` as `S → ∞`; `meanValue g` is the limit (`0` if
  there is none);
* `HasBohrMean h ω v`: the Bohr mean `ĥ(ω) = lim_{S→∞} S⁻¹ ∫₀^S e^{-iωt} h t dt` exists and
  equals `v`; `bohrMean h ω` is its value;
* `bohrSeries ω v t = ∑' l, e^{i ωₗ t} vₗ`: the almost periodic series of
  `def:harmonic-signal`.

## Main results

* the mean is linear, insensitive to changes on null sets, and commutes with bounded linear
  maps (`HasMeanValue.map`, `HasBohrMean.map`);
* `hasMeanValue_zero_of_bounded_integral`: a function with bounded primitive has mean `0`
  (the free-response step of `lem:bohr-annihilator`: `e^{-sₗ t}⟨ζ, S t c⟩` is the derivative of
  the bounded `e^{-sₗ t}⟨ζ, S t d⟩`);
* `hasMeanValue_tsum`: termwise averaging of a uniformly dominated series;
* `hasMeanValue_of_tendsto` (continuous Cesàro): functions that are `o(1)` have mean `0`, and so
  have Bohr mean `0` at every frequency;
* `hasBohrMean_bohrSeries`: `ĥ(ωₗ) = vₗ` for an absolutely convergent series with pairwise
  distinct frequencies, and `hasBohrMean_bohrSeries_of_ne`: `ĥ(ω) = 0` at other frequencies;
* uniqueness of the coefficients: `eq_zero_of_bohrSeries_ae_eq_zero`, and the form used by `lem:bohr-annihilator`, `eq_zero_of_add_bohrSeries_ae_eq_zero`
  (`g t + ∑ dₗ e^{i ωₗ t} = 0` with `g` of Bohr mean `0` at every `ωₗ` forces `d = 0`).

Everything is stated for functions on `ℝ`; only their values for `t > 0` matter.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Complex Real

noncomputable section

namespace DataDrivenControl

/-! ### Mean values -/

section Mean

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `g` has **mean value** `v`: `S⁻¹ ∫₀^S g t dt → v` as `S → ∞`. -/
def HasMeanValue (g : ℝ → E) (v : E) : Prop :=
  Tendsto (fun S : ℝ ↦ S⁻¹ • ∫ t in (0 : ℝ)..S, g t) atTop (𝓝 v)

open scoped Classical in
/-- The mean value `lim_{S→∞} S⁻¹ ∫₀^S g`, or `0` if the limit does not exist. -/
def meanValue (g : ℝ → E) : E :=
  if h : ∃ v, HasMeanValue g v then h.choose else 0

/-- Mean values are unique. -/
theorem HasMeanValue.unique {g : ℝ → E} {v w : E} (hv : HasMeanValue g v)
    (hw : HasMeanValue g w) : v = w :=
  tendsto_nhds_unique hv hw

/-- `meanValue` returns the mean value when there is one. -/
theorem HasMeanValue.meanValue_eq {g : ℝ → E} {v : E} (h : HasMeanValue g v) :
    meanValue g = v := by
  unfold meanValue
  split_ifs with hex
  · exact hex.choose_spec.unique h
  · exact absurd ⟨v, h⟩ hex

/-- A constant is its own mean. -/
theorem hasMeanValue_const [CompleteSpace E] (c : E) : HasMeanValue (fun _ ↦ c) c := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with S hS
  rw [intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ hS.ne', one_smul]

/-- The mean only depends on `g` a.e. on `(0, ∞)`. -/
theorem HasMeanValue.congr_ae {f g : ℝ → E} {v : E} (hf : HasMeanValue f v)
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) : HasMeanValue g v := by
  refine hf.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with S hS
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le hS]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hfg] with t ht hts
  exact ht hts.1

/-- The mean is additive (for locally integrable functions). -/
theorem HasMeanValue.add {f g : ℝ → E} {v w : E} (hf : HasMeanValue f v)
    (hg : HasMeanValue g w) (hfi : ∀ S : ℝ, IntervalIntegrable f volume 0 S)
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) :
    HasMeanValue (fun t ↦ f t + g t) (v + w) := by
  refine (Filter.Tendsto.add hf hg).congr' (Eventually.of_forall fun S ↦ ?_)
  simp only
  rw [intervalIntegral.integral_add (hfi S) (hgi S), smul_add]

/-- The mean commutes with negation. -/
theorem HasMeanValue.neg {f : ℝ → E} {v : E} (hf : HasMeanValue f v) :
    HasMeanValue (fun t ↦ -f t) (-v) := by
  refine (Filter.Tendsto.neg hf).congr' (Eventually.of_forall fun S ↦ ?_)
  simp only
  rw [intervalIntegral.integral_neg, smul_neg]

/-- The mean is subtractive (for locally integrable functions). -/
theorem HasMeanValue.sub {f g : ℝ → E} {v w : E} (hf : HasMeanValue f v)
    (hg : HasMeanValue g w) (hfi : ∀ S : ℝ, IntervalIntegrable f volume 0 S)
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) :
    HasMeanValue (fun t ↦ f t - g t) (v - w) := by
  refine (Filter.Tendsto.sub hf hg).congr' (Eventually.of_forall fun S ↦ ?_)
  simp only
  rw [intervalIntegral.integral_sub (hfi S) (hgi S), smul_sub]

/-- The mean commutes with scalar multiplication. -/
theorem HasMeanValue.const_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] {f : ℝ → E} {v : E} (hf : HasMeanValue f v) (c : 𝕜) :
    HasMeanValue (fun t ↦ c • f t) (c • v) := by
  refine (Filter.Tendsto.const_smul hf c).congr' (Eventually.of_forall fun S ↦ ?_)
  simp only
  rw [intervalIntegral.integral_smul]
  exact (smul_comm _ _ _).symm

/-- The mean commutes with bounded linear maps. -/
theorem HasMeanValue.map [CompleteSpace E] [CompleteSpace F] {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (L : E →L[𝕜] F) {f : ℝ → E} {v : E} (hf : HasMeanValue f v)
    (hfi : ∀ S : ℝ, IntervalIntegrable f volume 0 S) :
    HasMeanValue (fun t ↦ L (f t)) (L v) := by
  refine ((L.continuous.tendsto v).comp hf).congr' (Eventually.of_forall fun S ↦ ?_)
  simp only [Function.comp_apply]
  rw [L.intervalIntegral_comp_comm (hfi S), map_real_smul L L.continuous]

/-- A function whose primitive `∫₀^S g` stays bounded has mean `0`. -/
theorem hasMeanValue_zero_of_bounded_integral {g : ℝ → E} {C : ℝ}
    (h : ∀ᶠ S in atTop, ‖∫ t in (0 : ℝ)..S, g t‖ ≤ C) : HasMeanValue g 0 := by
  have hC : Tendsto (fun S : ℝ ↦ S⁻¹ * C) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const C
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [h, eventually_gt_atTop 0] with S hS hS0
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS0.le)]
  exact mul_le_mul_of_nonneg_left hS (inv_nonneg.2 hS0.le)

private theorem hasMeanValue_zero_of_tendsto_zero {g : ℝ → E} (hg : Tendsto g atTop (𝓝 0))
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) : HasMeanValue g 0 := by
  rw [HasMeanValue, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hg) (ε / 2) (half_pos hε))
  set T := max T₀ 0
  set C := ‖∫ t in (0 : ℝ)..T, g t‖
  have hC : Tendsto (fun S : ℝ ↦ S⁻¹ * C) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const C
  filter_upwards [(Metric.tendsto_nhds.1 hC) (ε / 2) (half_pos hε), eventually_gt_atTop T,
    eventually_gt_atTop 0] with S hSC hST hS0
  rw [dist_zero_right]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hSC
  have hsplit : ∫ t in (0 : ℝ)..S, g t = (∫ t in (0 : ℝ)..T, g t) + ∫ t in T..S, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hgi T)
      (((hgi S).mono_set (by
        rw [Set.uIcc_of_le hS0.le, Set.uIcc_of_le hST.le]
        exact Set.Icc_subset_Icc (le_max_right _ _) le_rfl)))).symm
  have htail : ‖∫ t in T..S, g t‖ ≤ ε / 2 * |S - T| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [Set.uIoc_of_le hST.le] at ht
    have := hT₀ t ((le_max_left _ _).trans ht.1.le)
    rw [dist_zero_right] at this
    exact this.le
  rw [abs_of_nonneg (by linarith)] at htail
  calc ‖S⁻¹ • ∫ t in (0 : ℝ)..S, g t‖
      ≤ S⁻¹ * (C + ε / 2 * (S - T)) := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS0.le), hsplit]
        exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith))
          (inv_nonneg.2 hS0.le)
    _ = S⁻¹ * C + ε / 2 * ((S - T) / S) := by field_simp
    _ ≤ S⁻¹ * C + ε / 2 * 1 := by
        gcongr
        rw [div_le_one hS0]
        have : 0 ≤ T := le_max_right _ _
        linarith
    _ < ε := by linarith

/-- **Continuous Cesàro**: a locally integrable function with a limit at `∞` has that limit as
its mean.  In particular every `o(1)` function has mean `0`. -/
theorem hasMeanValue_of_tendsto [CompleteSpace E] {g : ℝ → E} {v : E} (hg : Tendsto g atTop (𝓝 v))
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) : HasMeanValue g v := by
  have h0 : HasMeanValue (fun t ↦ g t - v) 0 :=
    hasMeanValue_zero_of_tendsto_zero (by simpa using hg.sub_const v)
      fun S ↦ (hgi S).sub intervalIntegrable_const
  simpa using h0.add (hasMeanValue_const v) (fun S ↦ (hgi S).sub intervalIntegrable_const)
    fun _ ↦ intervalIntegrable_const

/-- **Termwise averaging**: if `‖F l t‖ ≤ b l` with `b` summable and each `F l` has mean
`m l`, then `∑' l, F l` has mean `∑' l, m l`. -/
theorem hasMeanValue_tsum [CompleteSpace E] {ι : Type*} [Countable ι] {F : ι → ℝ → E}
    {m : ι → E} {b : ι → ℝ} (hF : ∀ l, AEStronglyMeasurable (F l)) (hb : Summable b)
    (hFb : ∀ l t, ‖F l t‖ ≤ b l) (hm : ∀ l, HasMeanValue (F l) (m l)) :
    HasMeanValue (fun t ↦ ∑' l, F l t) (∑' l, m l) := by
  have hsum : ∀ S : ℝ, HasSum (fun l ↦ ∫ t in (0 : ℝ)..S, F l t)
      (∫ t in (0 : ℝ)..S, ∑' l, F l t) := fun S ↦
    intervalIntegral.hasSum_integral_of_dominated_convergence (fun l _ ↦ b l)
      (fun l ↦ (hF l).restrict) (fun l ↦ ae_of_all _ fun t _ ↦ hFb l t)
      (ae_of_all _ fun _ _ ↦ hb) intervalIntegrable_const
      (ae_of_all _ fun t _ ↦ (Summable.of_norm_bounded hb fun l ↦ hFb l t).hasSum)
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (S : ℝ) l ↦ S⁻¹ • ∫ t in (0 : ℝ)..S, F l t) hb hm ?_
  · refine key.congr' (Eventually.of_forall fun S ↦ ?_)
    exact ((hsum S).const_smul S⁻¹).tsum_eq
  · filter_upwards [eventually_gt_atTop 0] with S hS l
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS.le)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S)
      (fun t _ ↦ hFb l t)
    rw [sub_zero, abs_of_pos hS] at this
    calc S⁻¹ * ‖∫ t in (0 : ℝ)..S, F l t‖ ≤ S⁻¹ * (b l * S) := by gcongr
      _ = b l := by field_simp

end Mean

/-! ### Bohr means -/

section Bohr

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `h` has **Bohr mean** `v` at the frequency `ω`:
`ĥ(ω) = lim_{S→∞} S⁻¹ ∫₀^S e^{-iωt} h t dt = v` (`app:harmonic-pe`). -/
def HasBohrMean (h : ℝ → E) (ω : ℝ) (v : E) : Prop :=
  HasMeanValue (fun t : ℝ ↦ cexp (-(ω * t * Complex.I)) • h t) v

/-- The **Bohr mean** (Bohr coefficient) `ĥ(ω)` of `h` at the frequency `ω`, or `0` if the
limit does not exist. -/
def bohrMean (h : ℝ → E) (ω : ℝ) : E :=
  meanValue (fun t : ℝ ↦ cexp (-(ω * t * Complex.I)) • h t)

/-- Bohr means are unique. -/
theorem HasBohrMean.unique {h : ℝ → E} {ω : ℝ} {v w : E} (hv : HasBohrMean h ω v)
    (hw : HasBohrMean h ω w) : v = w :=
  HasMeanValue.unique hv hw

/-- `bohrMean` returns the Bohr mean when there is one. -/
theorem HasBohrMean.bohrMean_eq {h : ℝ → E} {ω : ℝ} {v : E} (hh : HasBohrMean h ω v) :
    bohrMean h ω = v :=
  HasMeanValue.meanValue_eq hh

/-- The Bohr mean only depends on `h` a.e. on `(0, ∞)`. -/
theorem HasBohrMean.congr_ae {h g : ℝ → E} {ω : ℝ} {v : E} (hh : HasBohrMean h ω v)
    (hhg : h =ᵐ[volume.restrict (Ioi 0)] g) : HasBohrMean g ω v :=
  HasMeanValue.congr_ae hh (hhg.mono fun t ht ↦ by simp only [ht])

private theorem norm_cexp_neg_mul_I (ω t : ℝ) : ‖cexp (-(ω * t * Complex.I))‖ = 1 := by
  rw [show -((ω : ℂ) * t * Complex.I) = ((-(ω * t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Bohr kernel is continuous, hence preserves interval integrability. -/
private theorem intervalIntegrable_cexp_smul {h : ℝ → E} {ω : ℝ}
    (hhi : ∀ S : ℝ, IntervalIntegrable h volume 0 S) (S : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ cexp (-(ω * t * Complex.I)) • h t) volume 0 S :=
  (hhi S).continuousOn_smul (by fun_prop)

/-- The Bohr mean is additive (for locally integrable functions). -/
theorem HasBohrMean.add {h g : ℝ → E} {ω : ℝ} {v w : E} (hh : HasBohrMean h ω v)
    (hg : HasBohrMean g ω w) (hhi : ∀ S : ℝ, IntervalIntegrable h volume 0 S)
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) :
    HasBohrMean (fun t ↦ h t + g t) ω (v + w) := by
  have := HasMeanValue.add hh hg (intervalIntegrable_cexp_smul hhi)
    (intervalIntegrable_cexp_smul hgi)
  simpa only [HasBohrMean, smul_add] using this

/-- The Bohr mean commutes with negation. -/
theorem HasBohrMean.neg {h : ℝ → E} {ω : ℝ} {v : E} (hh : HasBohrMean h ω v) :
    HasBohrMean (fun t ↦ -h t) ω (-v) := by
  simpa only [HasBohrMean, smul_neg] using HasMeanValue.neg hh

/-- The Bohr mean is subtractive (for locally integrable functions). -/
theorem HasBohrMean.sub {h g : ℝ → E} {ω : ℝ} {v w : E} (hh : HasBohrMean h ω v)
    (hg : HasBohrMean g ω w) (hhi : ∀ S : ℝ, IntervalIntegrable h volume 0 S)
    (hgi : ∀ S : ℝ, IntervalIntegrable g volume 0 S) :
    HasBohrMean (fun t ↦ h t - g t) ω (v - w) := by
  have := HasMeanValue.sub hh hg (intervalIntegrable_cexp_smul hhi)
    (intervalIntegrable_cexp_smul hgi)
  simpa only [HasBohrMean, smul_sub] using this

/-- The Bohr mean commutes with complex scalar multiplication. -/
theorem HasBohrMean.const_smul {h : ℝ → E} {ω : ℝ} {v : E} (hh : HasBohrMean h ω v) (c : ℂ) :
    HasBohrMean (fun t ↦ c • h t) ω (c • v) := by
  have := HasMeanValue.const_smul hh c
  simpa only [HasBohrMean, smul_comm c] using this

/-- The Bohr mean commutes with bounded linear maps. -/
theorem HasBohrMean.map [CompleteSpace E] [CompleteSpace F] (L : E →L[ℂ] F) {h : ℝ → E}
    {ω : ℝ} {v : E} (hh : HasBohrMean h ω v)
    (hhi : ∀ S : ℝ, IntervalIntegrable h volume 0 S) :
    HasBohrMean (fun t ↦ L (h t)) ω (L v) := by
  have := HasMeanValue.map L hh (intervalIntegrable_cexp_smul hhi)
  simpa only [HasBohrMean, map_smul] using this

/-- A function `h` with `∫₀^S e^{-iωt} h t dt` bounded in `S` has Bohr mean `0` at `ω`
(`lem:bohr-annihilator`, the free response). -/
theorem hasBohrMean_zero_of_bounded_integral {h : ℝ → E} {ω C : ℝ}
    (hC : ∀ᶠ S in atTop, ‖∫ t in (0 : ℝ)..S, cexp (-(ω * t * Complex.I)) • h t‖ ≤ C) :
    HasBohrMean h ω 0 :=
  hasMeanValue_zero_of_bounded_integral hC

/-- An `o(1)` locally integrable function has Bohr mean `0` at every frequency. -/
theorem hasBohrMean_zero_of_tendsto_zero [CompleteSpace E] {h : ℝ → E}
    (hh : Tendsto h atTop (𝓝 0))
    (hhi : ∀ S : ℝ, IntervalIntegrable h volume 0 S) (ω : ℝ) : HasBohrMean h ω 0 := by
  refine hasMeanValue_of_tendsto ?_ (intervalIntegrable_cexp_smul hhi)
  refine squeeze_zero_norm (fun t ↦ (norm_smul _ _).trans_le ?_) (tendsto_norm_zero.comp hh)
  rw [norm_cexp_neg_mul_I, one_mul]
  rfl

/-- The Bohr mean of a single exponential `e^{iαt} v`: `v` at `ω = α`, `0` elsewhere. -/
theorem hasBohrMean_cexp [CompleteSpace E] (α ω : ℝ) (v : E) :
    HasBohrMean (fun t : ℝ ↦ cexp (α * t * Complex.I) • v) ω (if α = ω then v else 0) := by
  have hk : ∀ t : ℝ, cexp (-(ω * t * Complex.I)) • cexp (α * t * Complex.I) • v
      = cexp ((α - ω : ℝ) * Complex.I * t) • v := by
    intro t
    rw [smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold HasBohrMean
  simp_rw [hk]
  split_ifs with hαω
  · subst hαω
    simpa using hasMeanValue_const v
  · have hc : ((α - ω : ℝ) : ℂ) * Complex.I ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast sub_ne_zero.2 hαω
    refine hasMeanValue_zero_of_bounded_integral (C := 2 / ‖((α - ω : ℝ) : ℂ) * Complex.I‖ * ‖v‖)
      (Eventually.of_forall fun S ↦ ?_)
    rw [intervalIntegral.integral_smul_const, integral_exp_mul_complex hc, norm_smul]
    gcongr
    rw [norm_div]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    have h1 : ∀ x : ℝ, ‖cexp (((α - ω : ℝ) : ℂ) * Complex.I * x)‖ = 1 := by
      intro x
      rw [mul_assoc, mul_comm Complex.I, ← mul_assoc, ← Complex.ofReal_mul,
        Complex.norm_exp_ofReal_mul_I]
    rw [h1, h1]
    norm_num

/-! ### Almost periodic series -/

private theorem norm_cexp_mul_I (a t : ℝ) : ‖cexp (a * t * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The almost periodic series `t ↦ ∑' l, e^{i ωₗ t} vₗ` of `def:harmonic-signal`. -/
def bohrSeries {ι : Type*} (ω : ι → ℝ) (v : ι → E) (t : ℝ) : E :=
  ∑' l, cexp (ω l * t * Complex.I) • v l

/-- Unfolding `bohrSeries`. -/
theorem bohrSeries_apply {ι : Type*} (ω : ι → ℝ) (v : ι → E) (t : ℝ) :
    bohrSeries ω v t = ∑' l, cexp (ω l * t * Complex.I) • v l :=
  rfl

private theorem norm_cexp_smul {ι : Type*} (ω : ι → ℝ) (v : ι → E) (t : ℝ) (l : ι) :
    ‖cexp (ω l * t * Complex.I) • v l‖ = ‖v l‖ := by
  rw [norm_smul, norm_cexp_mul_I, one_mul]

/-- An absolutely convergent almost periodic series is bounded by `∑ ‖vₗ‖`. -/
theorem norm_bohrSeries_le {ι : Type*} {ω : ι → ℝ} {v : ι → E}
    (hv : Summable fun l ↦ ‖v l‖) (t : ℝ) : ‖bohrSeries ω v t‖ ≤ ∑' l, ‖v l‖ := by
  rw [bohrSeries_apply]
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · simpa only [norm_cexp_smul] using hv
  · simp only [norm_cexp_smul]

/-- An absolutely convergent almost periodic series is continuous. -/
theorem continuous_bohrSeries [CompleteSpace E] {ι : Type*} {ω : ι → ℝ} {v : ι → E}
    (hv : Summable fun l ↦ ‖v l‖) : Continuous (bohrSeries ω v) :=
  continuous_tsum (fun l ↦ by fun_prop) hv fun l t ↦ (norm_cexp_smul ω v t l).le

private theorem hasBohrMean_bohrSeries_aux [CompleteSpace E] {ι : Type*} [Countable ι]
    {ω : ι → ℝ} {v : ι → E} (hv : Summable fun l ↦ ‖v l‖) (ω₀ : ℝ) :
    HasBohrMean (bohrSeries ω v) ω₀ (∑' l, if ω l = ω₀ then v l else 0) := by
  have key := hasMeanValue_tsum
    (F := fun l t ↦ cexp (-(ω₀ * t * Complex.I)) • cexp (ω l * t * Complex.I) • v l)
    (b := fun l ↦ ‖v l‖) (fun l ↦ (by fun_prop : Continuous _).aestronglyMeasurable) hv
    (fun l t ↦ by rw [norm_smul, norm_cexp_neg_mul_I, one_mul, norm_cexp_smul])
    (fun l ↦ hasBohrMean_cexp (ω l) ω₀ (v l))
  refine HasMeanValue.congr_ae key (Eventually.of_forall fun t ↦ ?_)
  simp only [bohrSeries]
  exact Summable.tsum_const_smul (cexp (-(ω₀ * t * Complex.I)))
    (Summable.of_norm (f := fun l ↦ cexp (ω l * t * Complex.I) • v l)
      (by simpa only [norm_cexp_smul] using hv))

/-- **Bohr coefficients**: for an absolutely convergent series with pairwise distinct
frequencies, `ĥ(ωₗ) = vₗ` (`app:harmonic-pe`). -/
theorem hasBohrMean_bohrSeries [CompleteSpace E] {ι : Type*} [Countable ι] {ω : ι → ℝ}
    {v : ι → E} (hv : Summable fun l ↦ ‖v l‖) (hω : Function.Injective ω) (l : ι) :
    HasBohrMean (bohrSeries ω v) (ω l) (v l) := by
  convert hasBohrMean_bohrSeries_aux (ω := ω) hv (ω l) using 1
  rw [tsum_eq_single l fun l' hl' ↦ by simp [hω.ne hl']]
  simp

/-- The Bohr mean of an absolutely convergent series vanishes away from its frequencies. -/
theorem hasBohrMean_bohrSeries_of_ne [CompleteSpace E] {ι : Type*} [Countable ι] {ω : ι → ℝ}
    {v : ι → E} (hv : Summable fun l ↦ ‖v l‖) {ω₀ : ℝ} (hω₀ : ∀ l, ω l ≠ ω₀) :
    HasBohrMean (bohrSeries ω v) ω₀ 0 := by
  simpa [hω₀] using hasBohrMean_bohrSeries_aux (ω := ω) hv ω₀

/-- **Vanishing of the coefficients** (`lem:bohr-annihilator`): if
`g t + ∑ dₗ e^{i ωₗ t} = 0` for a.e. `t > 0`, the series converges absolutely with pairwise
distinct frequencies, and `g` has Bohr mean `0` at every `ωₗ`, then every `dₗ` vanishes. -/
theorem eq_zero_of_add_bohrSeries_ae_eq_zero [CompleteSpace E] {ι : Type*} [Countable ι]
    {ω : ι → ℝ} {d : ι → E} {g : ℝ → E} (hd : Summable fun l ↦ ‖d l‖)
    (hω : Function.Injective ω) (hg : ∀ l, HasBohrMean g (ω l) 0)
    (h : ∀ᵐ t ∂(volume.restrict (Ioi 0)), g t + bohrSeries ω d t = 0) : d = 0 := by
  funext l
  have h1 := (hasBohrMean_bohrSeries hd hω l).neg
  have h2 : HasBohrMean (fun t ↦ -bohrSeries ω d t) (ω l) 0 :=
    (hg l).congr_ae (h.mono fun t ht ↦ eq_neg_of_add_eq_zero_left ht)
  simpa using h1.unique h2

/-- **Uniqueness of the Bohr coefficients**: an absolutely convergent series with pairwise
distinct frequencies that vanishes a.e. on `(0, ∞)` has zero coefficients. -/
theorem eq_zero_of_bohrSeries_ae_eq_zero [CompleteSpace E] {ι : Type*} [Countable ι]
    {ω : ι → ℝ} {d : ι → E} (hd : Summable fun l ↦ ‖d l‖) (hω : Function.Injective ω)
    (h : ∀ᵐ t ∂(volume.restrict (Ioi 0)), bohrSeries ω d t = 0) : d = 0 := by
  refine eq_zero_of_add_bohrSeries_ae_eq_zero (g := fun _ ↦ 0) hd hω (fun l ↦ ?_)
    (h.mono fun t ht ↦ by simpa using ht)
  simpa [HasBohrMean] using hasMeanValue_const (0 : E)

end Bohr

end DataDrivenControl
