module

public import Mathlib

/-!
# C₀-semigroups

Mathlib has no C₀-semigroups.

## Main declarations

* `C0Semigroup 𝕜 E`: `S : ℝ≥0 → E →L[𝕜] E` with `S 0 = 1`, `S (s + t) = S s ∘L S t` and
  strong continuity (`t ↦ S t x` continuous on `ℝ≥0` for every `x`).  `FunLike` instance,
  so `S t x` typechecks; `C0Semigroup.ext`.
* `C0Semigroup.ofTendsto`: constructor from strong continuity at `0` only.
* `C0Semigroup.real S t := S t.toNNReal`: the real-argument accessor used in convolutions
  `S (t - r)`; `S.real t = 1` for `t ≤ 0` (simp lemmas `real_coe`, `real_of_nonpos`, `real_add`).
* `exists_norm_le_exp`: `‖S t‖ ≤ M e^{ω t}` (Banach–Steinhaus); `exists_norm_real_le`.
* `continuous_apply₂`, `continuous_real_apply₂`: joint continuity of `(t, x) ↦ S t x`.
* `aestronglyMeasurable_conv`, `integrableOn_conv`: measurability and integrability of
  `r ↦ S (t - r) (f r)`.
* `C0Semigroup.Consistent ι S' S`: `ι ∘ S' t = S t ∘ ι` along `ι : F →L[𝕜] E`
  (used for `W ↪ X ↪ V`).

`continuous_of_tendsto`, `ofTendsto`, `exists_norm_le_exp`, `exists_norm_real_le`,
`continuous_apply₂`, `continuous_real_apply₂` and `integrableOn_conv` assume `[CompleteSpace E]`:
on incomplete spaces uniform boundedness fails and they are false (on the algebraic direct sum
`⊕ₙ ℝ²`, the blockwise `S t = e^{-nt} (1 + n² t N)`, `N = [[0, 1], [0, 0]]`, has
`‖S (1/n)‖ ≥ n/e`).
`aestronglyMeasurable_conv` needs no completeness.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace DataDrivenControl

/-- A **C₀-semigroup** (strongly continuous semigroup) of bounded operators on `E`, indexed by
`ℝ≥0`.  Strong continuity is stated on all of `ℝ≥0`; `C0Semigroup.ofTendsto` builds one from
continuity at `0`. -/
structure C0Semigroup (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] where
  /-- The operators `S t`, `t ≥ 0`. -/
  toFun : ℝ≥0 → E →L[𝕜] E
  map_zero' : toFun 0 = 1
  map_add' : ∀ s t, toFun (s + t) = (toFun s).comp (toFun t)
  continuous_apply' : ∀ x, Continuous fun t => toFun t x

namespace C0Semigroup

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

instance instFunLike : FunLike (C0Semigroup 𝕜 E) ℝ≥0 (E →L[𝕜] E) where
  coe S := S.toFun
  coe_injective S S' h := by cases S; cases S'; congr

variable (S : C0Semigroup 𝕜 E)

@[simp] theorem toFun_eq_coe : S.toFun = ⇑S := rfl

@[ext] theorem ext {S S' : C0Semigroup 𝕜 E} (h : ∀ t, S t = S' t) : S = S' :=
  DFunLike.ext _ _ h

/-- `S 0 = 1`. -/
@[simp] protected theorem map_zero : S 0 = 1 := S.map_zero'

/-- The semigroup law `S (s + t) = S s ∘ S t`. -/
protected theorem map_add (s t : ℝ≥0) : S (s + t) = (S s).comp (S t) := S.map_add' s t

@[simp] theorem zero_apply (x : E) : S 0 x = x := by simp

theorem add_apply (s t : ℝ≥0) (x : E) : S (s + t) x = S s (S t x) := by
  rw [S.map_add]; rfl

theorem comm_apply (s t : ℝ≥0) (x : E) : S s (S t x) = S t (S s x) := by
  rw [← add_apply, ← add_apply, add_comm]

/-- Strong continuity. -/
theorem continuous_apply (x : E) : Continuous fun t => S t x := S.continuous_apply' x

/-! ### Construction from continuity at `0` -/

section Generic

variable {f : ℝ≥0 → E →L[𝕜] E}

/-- `‖f (n δ)‖ ≤ C ^ n` for a semigroup law `f`. -/
private theorem norm_natCast_mul_le (h0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = (f s).comp (f t))
    {δ : ℝ≥0} {C : ℝ} (hC : ‖f δ‖ ≤ C) (n : ℕ) : ‖f (n * δ)‖ ≤ C ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, h0, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, add_comm, hadd, pow_succ']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hC ih (norm_nonneg _) ((norm_nonneg _).trans hC))

/-- A bound on `[0, δ]` propagates to an exponential bound on `ℝ≥0`. -/
private theorem exists_norm_le_exp_of_le (h0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = (f s).comp (f t)) {δ : ℝ≥0} (hδ : 0 < δ) {C : ℝ} (hC1 : 1 ≤ C)
    (hC : ∀ t ≤ δ, ‖f t‖ ≤ C) :
    ∃ M ω : ℝ, 1 ≤ M ∧ ∀ t : ℝ≥0, ‖f t‖ ≤ M * Real.exp (ω * t) := by
  refine ⟨C, Real.log C / δ, hC1, fun t => ?_⟩
  set n := ⌊t / δ⌋₊ with hn
  have hn1 : (n : ℝ≥0) ≤ t / δ := Nat.floor_le zero_le
  have h1 : (n : ℝ≥0) * δ ≤ t := (le_div_iff₀ hδ).1 hn1
  have h2 : t - n * δ ≤ δ := by
    have := Nat.lt_floor_add_one (t / δ)
    rw [div_lt_iff₀ hδ, add_mul, one_mul] at this
    exact tsub_le_iff_left.2 this.le
  have hnr : (n : ℝ) ≤ (t : ℝ) / δ := by exact_mod_cast hn1
  have hC0 : 0 < C := by linarith
  calc ‖f t‖ = ‖(f (t - n * δ)).comp (f (n * δ))‖ := by rw [← hadd, tsub_add_cancel_of_le h1]
    _ ≤ ‖f (t - n * δ)‖ * ‖f (n * δ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * C ^ n :=
        mul_le_mul (hC _ h2) (norm_natCast_mul_le h0 hadd (hC δ le_rfl) n) (norm_nonneg _)
          hC0.le
    _ ≤ C * Real.exp (Real.log C / δ * t) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0.le
        calc C ^ n = Real.exp (n * Real.log C) := by rw [Real.exp_nat_mul, Real.exp_log hC0]
          _ ≤ Real.exp (Real.log C / δ * t) := by
              refine Real.exp_le_exp.2 ?_
              calc (n : ℝ) * Real.log C ≤ ((t : ℝ) / δ) * Real.log C :=
                    mul_le_mul_of_nonneg_right hnr (Real.log_nonneg hC1)
                _ = Real.log C / δ * t := by ring

/-- Uniform boundedness near `0` (Banach–Steinhaus along a sequence `tₙ → 0`). -/
private theorem exists_le_of_tendsto [CompleteSpace E]
    (hcont : ∀ x, Tendsto (fun t => f t x) (𝓝 0) (𝓝 x)) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ t ≤ δ, ‖f t‖ ≤ C := by
  by_contra! H
  have : ∀ n : ℕ, ∃ t : ℝ≥0, t ≤ ((n : ℝ≥0) + 1)⁻¹ ∧ (n : ℝ) + 1 < ‖f t‖ := fun n =>
    H _ (by positivity) _ (by linarith [n.cast_nonneg (α := ℝ)])
  choose τ hτ hτC using this
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)
  have hτ0 : Tendsto τ atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun n => zero_le) hτ
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖f (τ n)‖ ≤ C := banach_steinhaus fun x => by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
      (Metric.isBounded_range_of_tendsto _ ((hcont x).comp hτ0))
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  linarith [hC n, hτC n]

/-- Strong continuity at `0` plus a continuous bound on `‖f t‖` give strong continuity. -/
private theorem continuous_of_le (h0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = (f s).comp (f t))
    (hcont : ∀ x, Tendsto (fun t => f t x) (𝓝 0) (𝓝 x)) {b : ℝ≥0 → ℝ} (hb : Continuous b)
    (hfb : ∀ t, ‖f t‖ ≤ b t) (x : E) : Continuous fun t => f t x := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ s, ‖f s x - f t x‖ ≤ b s * ‖f (t - s) x - x‖ + b t * ‖f (s - t) x - x‖ := by
    intro s
    rcases le_total s t with hst | hts
    · have e : f t x = f s (f (t - s) x) := by
        calc f t x = f (s + (t - s)) x := by rw [add_tsub_cancel_of_le hst]
          _ = f s (f (t - s) x) := by rw [hadd]; rfl
      rw [e, tsub_eq_zero_of_le hst, h0, one_apply_eq_self, sub_self, norm_zero,
        mul_zero, add_zero]
      calc ‖f s x - f s (f (t - s) x)‖ = ‖f s (f (t - s) x - x)‖ := by
            rw [map_sub, norm_sub_rev]
        _ ≤ ‖f s‖ * ‖f (t - s) x - x‖ := (f s).le_opNorm _
        _ ≤ b s * ‖f (t - s) x - x‖ := mul_le_mul_of_nonneg_right (hfb s) (norm_nonneg _)
    · have e : f s x = f t (f (s - t) x) := by
        calc f s x = f (t + (s - t)) x := by rw [add_tsub_cancel_of_le hts]
          _ = f t (f (s - t) x) := by rw [hadd]; rfl
      rw [e, tsub_eq_zero_of_le hts, h0, one_apply_eq_self, sub_self, norm_zero,
        mul_zero, zero_add]
      calc ‖f t (f (s - t) x) - f t x‖ = ‖f t (f (s - t) x - x)‖ := by rw [map_sub]
        _ ≤ ‖f t‖ * ‖f (s - t) x - x‖ := (f t).le_opNorm _
        _ ≤ b t * ‖f (s - t) x - x‖ := mul_le_mul_of_nonneg_right (hfb t) (norm_nonneg _)
  have h1 : Tendsto (fun s => ‖f (t - s) x - x‖) (𝓝 t) (𝓝 0) := by
    have : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := t)).sub (tendsto_id (x := 𝓝 t))
    simpa using (((hcont x).comp this).sub (tendsto_const_nhds (x := x))).norm
  have h2 : Tendsto (fun s => ‖f (s - t) x - x‖) (𝓝 t) (𝓝 0) := by
    have : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 t)).sub (tendsto_const_nhds (x := t))
    simpa using (((hcont x).comp this).sub (tendsto_const_nhds (x := x))).norm
  refine squeeze_zero (fun _ => norm_nonneg _) key ?_
  simpa using ((hb.tendsto t).mul h1).add ((tendsto_const_nhds (x := b t)).mul h2)

end Generic

/-- Strong continuity at `0` implies strong continuity everywhere on a Banach space
(Banach–Steinhaus gives local boundedness, then the semigroup law). -/
theorem continuous_of_tendsto [CompleteSpace E] (f : ℝ≥0 → E →L[𝕜] E) (h0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = (f s).comp (f t))
    (hcont : ∀ x, Tendsto (fun t => f t x) (𝓝 0) (𝓝 x)) (x : E) :
    Continuous fun t => f t x := by
  obtain ⟨δ, hδ, C, hC1, hC⟩ := exists_le_of_tendsto hcont
  obtain ⟨M, ω, -, hM⟩ := exists_norm_le_exp_of_le h0 hadd hδ hC1 hC
  exact continuous_of_le h0 hadd hcont (b := fun t => M * Real.exp (ω * t))
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)))
    hM x

/-- A C₀-semigroup on a Banach space from the algebraic laws and strong continuity at `0`. -/
def ofTendsto [CompleteSpace E] (f : ℝ≥0 → E →L[𝕜] E) (h0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = (f s).comp (f t))
    (hcont : ∀ x, Tendsto (fun t => f t x) (𝓝 0) (𝓝 x)) : C0Semigroup 𝕜 E where
  toFun := f
  map_zero' := h0
  map_add' := hadd
  continuous_apply' := continuous_of_tendsto f h0 hadd hcont

@[simp] theorem ofTendsto_apply [CompleteSpace E] (f : ℝ≥0 → E →L[𝕜] E) (h0) (hadd) (hcont)
    (t : ℝ≥0) : ofTendsto f h0 hadd hcont t = f t := rfl

/-! ### Real-argument accessor -/

/-- `S` at a real time: `S.real t = S (max t 0)`.  Used in convolutions `S (t - r)`; it is the
identity for `t ≤ 0`. -/
def real (t : ℝ) : E →L[𝕜] E := S t.toNNReal

@[simp] theorem real_coe (t : ℝ≥0) : S.real t = S t := by simp [real]

theorem real_of_nonneg {t : ℝ} (ht : 0 ≤ t) : S.real t = S ⟨t, ht⟩ := by
  simp only [real, Real.toNNReal_of_nonneg ht]; rfl

theorem real_of_nonpos {t : ℝ} (ht : t ≤ 0) : S.real t = 1 := by
  simp [real, Real.toNNReal_of_nonpos ht]

@[simp] theorem real_zero : S.real 0 = 1 := S.real_of_nonpos le_rfl

theorem real_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.real (s + t) = (S.real s).comp (S.real t) := by
  simp [real, Real.toNNReal_add hs ht, S.map_add]

theorem real_add_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : E) :
    S.real (s + t) x = S.real s (S.real t x) := by
  rw [S.real_add hs ht]; rfl

theorem real_comm_apply (s t : ℝ) (x : E) : S.real s (S.real t x) = S.real t (S.real s x) :=
  S.comm_apply _ _ x

theorem continuous_real_apply (x : E) : Continuous fun t : ℝ => S.real t x :=
  (S.continuous_apply x).comp continuous_real_toNNReal

/-! ### Exponential bound, joint continuity, measurability -/

/-- **Exponential bound** `‖S t‖ ≤ M e^{ω t}` on a Banach space (uniform boundedness
principle). -/
theorem exists_norm_le_exp [CompleteSpace E] :
    ∃ M ω : ℝ, 1 ≤ M ∧ ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t) := by
  have hcont : ∀ x, Tendsto (fun t => S t x) (𝓝 0) (𝓝 x) := fun x => by
    simpa using (S.continuous_apply x).tendsto 0
  obtain ⟨δ, hδ, C, hC1, hC⟩ := exists_le_of_tendsto (f := ⇑S) hcont
  exact exists_norm_le_exp_of_le S.map_zero S.map_add hδ hC1 hC

/-- Local boundedness: `‖S.real t‖ ≤ M` for `t ≤ τ` (Banach space). -/
theorem exists_norm_real_le [CompleteSpace E] (τ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, t ≤ τ → ‖S.real t‖ ≤ M := by
  obtain ⟨M, ω, hM, h⟩ := S.exists_norm_le_exp
  refine ⟨M * Real.exp (|ω| * max τ 0), by positivity, fun t ht => (h _).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
  calc ω * (t.toNNReal : ℝ) ≤ |ω| * t.toNNReal :=
        mul_le_mul_of_nonneg_right (le_abs_self ω) (NNReal.coe_nonneg _)
    _ ≤ |ω| * max τ 0 := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ω)
        rw [Real.coe_toNNReal']; exact max_le_max ht le_rfl

/-- Joint continuity of `(t, x) ↦ S t x` (Banach space). -/
theorem continuous_apply₂ [CompleteSpace E] : Continuous fun p : ℝ≥0 × E => S p.1 p.2 := by
  obtain ⟨M, ω, -, hM⟩ := S.exists_norm_le_exp
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ p : ℝ≥0 × E, ‖S p.1 p.2 - S t x‖ ≤
      M * Real.exp (ω * p.1) * ‖p.2 - x‖ + ‖S p.1 x - S t x‖ := by
    intro p
    calc ‖S p.1 p.2 - S t x‖ = ‖S p.1 (p.2 - x) + (S p.1 x - S t x)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖S p.1 (p.2 - x)‖ + ‖S p.1 x - S t x‖ := norm_add_le _ _
      _ ≤ M * Real.exp (ω * p.1) * ‖p.2 - x‖ + ‖S p.1 x - S t x‖ := by
          gcongr
          exact ((S p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  refine squeeze_zero (fun _ => norm_nonneg _) key ?_
  have h1 : Continuous fun p : ℝ≥0 × E =>
      M * Real.exp (ω * p.1) * ‖p.2 - x‖ + ‖S p.1 x - S t x‖ :=
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (NNReal.continuous_coe.comp continuous_fst)))).mul
      (continuous_snd.sub continuous_const).norm).add
      (((S.continuous_apply x).comp continuous_fst).sub continuous_const).norm
  simpa using h1.tendsto (t, x)

/-- Joint continuity of `(t, x) ↦ S.real t x` (Banach space). -/
theorem continuous_real_apply₂ [CompleteSpace E] :
    Continuous fun p : ℝ × E => S.real p.1 p.2 :=
  S.continuous_apply₂.comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

/-- `r ↦ Φ r (g r)` is strongly measurable for a simple function `g` if every `Φ · y` is. -/
private theorem stronglyMeasurable_simpleFunc_apply {α : Type*} [MeasurableSpace α]
    {Φ : α → E → E} (hΦ : ∀ y, StronglyMeasurable fun a => Φ a y) (g : SimpleFunc α E) :
    StronglyMeasurable fun a => Φ a (g a) := by
  have e : (fun a => Φ a (g a)) =
      fun a => ∑ y ∈ g.range, (g ⁻¹' {y}).indicator (fun a => Φ a y) a := by
    ext a
    rw [Finset.sum_eq_single (g a)]
    · simp
    · intro y _ hy
      exact Set.indicator_of_notMem (fun h => hy (by simpa using h.symm)) _
    · intro h; exact absurd (g.mem_range_self a) h
  rw [e]
  exact Finset.stronglyMeasurable_fun_sum _ fun y _ => (hΦ y).indicator (g.measurableSet_fiber y)

/-- Measurability of the convolution integrand `r ↦ S (t - r) (f r)`.  (No completeness is
needed: approximate `f` by simple functions.) -/
theorem aestronglyMeasurable_conv {f : ℝ → E} {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ)
    (t : ℝ) : AEStronglyMeasurable (fun r => S.real (t - r) (f r)) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun r => S.real (t - r) (g r), ?_, hfg.mono fun r hr => by simp only [hr]⟩
  refine stronglyMeasurable_of_tendsto atTop (fun n => stronglyMeasurable_simpleFunc_apply
    (Φ := fun r y => S.real (t - r) y) (fun y => ?_) (hg.approx n)) ?_
  · exact ((S.continuous_real_apply y).comp (continuous_const.sub continuous_id)).stronglyMeasurable
  · rw [tendsto_pi_nhds]
    intro r
    exact ((S.real (t - r)).continuous.tendsto _).comp (hg.tendsto_approx r)

/-- Integrability of the convolution integrand `r ↦ S (t - r) (f r)` on `(a, t]` (Banach
space). -/
theorem integrableOn_conv [CompleteSpace E] {f : ℝ → E} {a t : ℝ}
    (hf : IntegrableOn f (Ioc a t)) :
    IntegrableOn (fun r => S.real (t - r) (f r)) (Ioc a t) := by
  obtain ⟨M, -, hM⟩ := S.exists_norm_real_le (t - a)
  refine Integrable.mono' (hf.norm.const_mul M)
    (S.aestronglyMeasurable_conv hf.aestronglyMeasurable t) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
  calc ‖S.real (t - r) (f r)‖ ≤ ‖S.real (t - r)‖ * ‖f r‖ := (S.real (t - r)).le_opNorm _
    _ ≤ M * ‖f r‖ := mul_le_mul_of_nonneg_right (hM _ (by linarith [hr.1])) (norm_nonneg _)

/-! ### Consistency along embeddings -/

/-- Two semigroups are **consistent** along `ι : F →L[𝕜] E` if `ι (S' t x) = S t (ι x)`; this is
how the semigroups on `W ↪ X ↪ V` are related (`eq:intro-WXV`). -/
def Consistent (ι : F →L[𝕜] E) (S' : C0Semigroup 𝕜 F) (S : C0Semigroup 𝕜 E) : Prop :=
  ∀ (t : ℝ≥0) (x : F), ι (S' t x) = S t (ι x)

theorem Consistent.real {ι : F →L[𝕜] E} {S' : C0Semigroup 𝕜 F} {S : C0Semigroup 𝕜 E}
    (h : Consistent ι S' S) (t : ℝ) (x : F) : ι (S'.real t x) = S.real t (ι x) :=
  h _ x

theorem Consistent.comp {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ι : F →L[𝕜] E} {κ : G →L[𝕜] F} {S'' : C0Semigroup 𝕜 G} {S' : C0Semigroup 𝕜 F}
    {S : C0Semigroup 𝕜 E} (h : Consistent ι S' S) (h' : Consistent κ S'' S') :
    Consistent (ι.comp κ) S'' S := by
  intro t x
  simp only [ContinuousLinearMap.comp_apply, h' t x, h t]

theorem consistent_id : Consistent (ContinuousLinearMap.id 𝕜 E) S S := fun _ _ => rfl

end C0Semigroup

end DataDrivenControl
