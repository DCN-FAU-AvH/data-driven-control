module

public import DataDrivenControl.System.Setting
public import DataDrivenControl.Signal.Shift

/-!
# Mild solutions and the finite-horizon operators

Paper: `eq:hilbert-mild`, `lem:finite-horizon-output`, `app:finite-horizon-output`.

## Design

Signals are functions `ℝ → E`, square integrable on the window (`MemLp u 2 (μI τ)`); the
operators `𝓕 τ`, `𝓞 τ`, `Lop τ` act on `L2 E τ`.  Hypotheses enter only lemmas, never
definitions: the `W`-valued control convolution `L t u` is *defined* as the preimage under the
injective `ιWV : W → V` of the `V`-valued integral (junk `0` when there is none), and the
operators `Lop`, `𝓕`, `𝓞` are defined by choice from existence theorems (junk `0` when
`hyp:H1`/`hyp:H2` fails at that horizon).  Lemmas take the paper's hypotheses
`(hH1 : sys.H1 T) (hT : 0 < T)` (resp. `hH2`), which give H1/H2 at every horizon
(`H1.of_pos`, `H2.of_pos`).  Use the API lemmas (`ιWV_L`, `Lop_apply`, `𝓕_ae_eq`, `𝓞_ae_eq`),
not the definitions.

## Main declarations

* `H1.of_pos`, `H2.of_pos`: H1/H2 at one horizon `T > 0` give them at every horizon
  (`app:finite-horizon-output`); `bounded_H1`, `bounded_H2` for `System.bounded`.
* `liftV v`: the preimage of `v ∈ V` under the injective `ιWV : W → V` (`ιWV_liftV`,
  `liftV_eq`);
* `convV t u = ∫₀ᵗ S_V(t - r) B u(r) dr ∈ V` (`convV_add_time`: interval splitting,
  `convV_shift`: translation to the end of a longer interval); `L t u ∈ W` (`L_t u`,
  `eq:hilbert-mild-state`) with `ιWV_L : ιWV (L t u) = convV t u` under H1; `L_congr_ae`
  (causality), `L_add`, `L_smul`, `L_add_time` (splitting), `L_shift`, `L_eq_Lop_windowL`
  (`L_t u = L_τ u_t`), `exists_norm_L_le` (`sup_{t ≤ τ} ‖L_t u‖_W ≤ b_τ ‖u‖`),
  `continuousOn_L` (`L_· u ∈ C([0, τ]; W)`).
* `Lop t : L2 U t →L[ℝ] W` (`Lop_apply : Lop t u = L t u`).
* `mild x₀ u t = S(t) x₀ + L_t u ∈ X`, `mildW w₀ u t ∈ W` (for `x₀ ∈ W`), `outputW w₀ u t = C x(t)`;
  `mild_zero_time`, `mild_zero_left`, `ιW_mildW`,
  `mild_add_time` (`x(s + t; x₀, u) = x(t; x(s), u(s + ·))`), `mild_congr_ae`, `mild_add`,
  `mild_smul`, `continuousOn_mild`, `continuousOn_mildW`, `memLp_mild`, `memLp_mildW`.
* `𝓕 τ : L2 U τ →L[ℝ] L2 Y τ` (`𝓕_ae_eq : 𝓕 τ u = C L_(·) u`), `𝓞 τ : X →L[ℝ] L2 Y τ`
  (`𝓞_ae_eq : 𝓞 τ (ιW w) = C S(·) w`; `eq_𝓞`, `eq_𝓕` uniqueness), `𝓞_restrict`, `𝓕_causal`,
  `𝓞_shift` (`(𝓞_τ x)(s + ·) = 𝓞_ρ S(s) x`) (`lem:finite-horizon-output`).
* `output τ x₀ u : ℝ → Y`, the output record `y = 𝓞_τ x₀ + 𝓕_τ u` as a function
  (`output_ae_eq`, `memLp_output`, `output_ιW`), and the shift identity `output_shift`:
  `y(s + ·) = 𝓞_ρ x(s) + 𝓕_ρ u(s + ·)` in `L²(0, ρ; Y)`.

## Proof notes (`app:finite-horizon-output`)

* H1 at `T` gives H1 at `τ ≤ T` by translating the input to the end of `(0, T)`
  (`convV_shift`), and at `s + t` from `s` and `t` by splitting (`convV_add_time`) and the
  semigroup on `W`; induction covers every horizon.  H2 likewise (restriction and splitting,
  with `ιWV ∘ S_W = S_V ∘ ιWV`).
* `L_t u = L_τ u_t` where `u_t = windowL τ τ (t - τ) u` (the translate, zero-extended);
  continuity of translation in `L²` (`continuous_windowL`) and boundedness of `Lop τ` give the
  uniform bound and continuity of `t ↦ L_t u`.
* `𝓞_τ` is extended from `W` to `X` with `LinearMap.extendOfNorm` (H2 bounds it by the
  `V`-norm, hence by the `X`-norm).  The shift identity for the free response is checked on
  `W` and extended by density (`𝓞_shift`); the forced part splits with `L_add_time`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

/-- `L²` norms are subadditive in the measure. -/
private theorem eLpNorm_two_add_measure_le {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {f : α → F} {μ ν : Measure α} (hμ : AEStronglyMeasurable f μ)
    (hν : AEStronglyMeasurable f ν) :
    eLpNorm f 2 (μ + ν) ≤ eLpNorm f 2 μ + eLpNorm f 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hμ.add_measure hν),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hμ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hν,
    lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

/-- An a.e. bound gives an `L²` bound on a finite measure. -/
private theorem eLpNorm_two_le_ofReal_of_bound {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} [IsFiniteMeasure μ] {f : α → F} {K : ℝ}
    (hf : AEStronglyMeasurable f μ) (hK : ∀ᵐ x ∂μ, ‖f x‖ ≤ K) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal ((μ univ).toReal ^ (1 / 2 : ℝ) * K) := by
  refine (eLpNorm_le_of_ae_bound hf hK).trans_eq ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ univ),
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  norm_num

/-- A signal continuous on `[0, τ]` is square integrable on the window `(0, τ]`. -/
theorem memLp_μI_of_continuousOn {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {τ : ℝ}
    (hf : ContinuousOn f (Icc 0 τ)) : MemLp f 2 (μI τ) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) K ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hK t (Ioc_subset_Icc_self ht)

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-! ### The control convolution in `V` -/

/-- The control convolution in `V`: `∫₀ᵗ S_V(t - r) B u(r) dr` (over `(0, t]`; `0` for
`t ≤ 0`). -/
def convV (t : ℝ) (u : ℝ → U) : V := ∫ r in Ioc 0 t, sys.SV.real (t - r) (sys.B (u r))

open scoped Classical in
/-- The preimage of `v ∈ V` under the injective embedding `ιWV : W → V` (junk `0` if `v` is
not in the image). -/
def liftV (v : V) : W := if h : ∃ w : W, sys.ιWV w = v then h.choose else 0

/-- The control convolution `L_t u ∈ W` (`eq:hilbert-mild-state`): the preimage of `convV t u`
under the injective `ιWV : W → V`, which exists under `hyp:H1` (`ιWV_L`); junk `0` otherwise. -/
def L (t : ℝ) (u : ℝ → U) : W := sys.liftV (sys.convV t u)

variable {sys}

theorem ιWV_liftV {v : V} (h : ∃ w : W, sys.ιWV w = v) : sys.ιWV (sys.liftV v) = v := by
  rw [liftV, dite_eq_left h]; exact h.choose_spec

theorem liftV_eq {v : V} {w : W} (h : sys.ιWV w = v) : sys.liftV v = w :=
  sys.ιWV_injective ((ιWV_liftV ⟨w, h⟩).trans h.symm)

@[simp] theorem liftV_ιWV (w : W) : sys.liftV (sys.ιWV w) = w := liftV_eq rfl

theorem ιWV_L_of_exists {t : ℝ} {u : ℝ → U} (h : ∃ w : W, sys.ιWV w = sys.convV t u) :
    sys.ιWV (sys.L t u) = sys.convV t u :=
  ιWV_liftV h

theorem L_eq_of_ιWV {t : ℝ} {u : ℝ → U} {w : W} (h : sys.ιWV w = sys.convV t u) :
    sys.L t u = w :=
  liftV_eq h

/-- Causality of the control convolution: `convV t u` depends only on `u` on `(0, t]`. -/
theorem convV_congr_ae {t : ℝ} {u v : ℝ → U} (h : u =ᵐ[μI t] v) :
    sys.convV t u = sys.convV t v :=
  integral_congr_ae (h.mono fun r hr => by simp only [hr])

/-- Causality: `L_t u` depends only on `u` on `(0, t]`. -/
theorem L_congr_ae {t : ℝ} {u v : ℝ → U} (h : u =ᵐ[μI t] v) : sys.L t u = sys.L t v := by
  rw [L, L, convV_congr_ae h]

theorem convV_of_nonpos {t : ℝ} (ht : t ≤ 0) (u : ℝ → U) : sys.convV t u = 0 := by
  simp [convV, Ioc_eq_empty (not_lt.2 ht)]

theorem L_of_nonpos {t : ℝ} (ht : t ≤ 0) (u : ℝ → U) : sys.L t u = 0 :=
  L_eq_of_ιWV (by simp [convV_of_nonpos ht])

@[simp] theorem L_zero_left (u : ℝ → U) : sys.L 0 u = 0 := L_of_nonpos le_rfl u

theorem integrableOn_convV {t : ℝ} {u : ℝ → U} (hu : MemLp u 2 (μI t)) :
    IntegrableOn (fun r => sys.SV.real (t - r) (sys.B (u r))) (Ioc 0 t) :=
  sys.SV.integrableOn_conv (f := fun r => sys.B (u r))
    (sys.B.integrable_comp (hu.integrable one_le_two))

theorem convV_add {t : ℝ} {u v : ℝ → U} (hu : MemLp u 2 (μI t)) (hv : MemLp v 2 (μI t)) :
    sys.convV t (u + v) = sys.convV t u + sys.convV t v := by
  simp only [convV, Pi.add_apply, map_add]
  exact integral_add (integrableOn_convV hu) (integrableOn_convV hv)

theorem convV_smul (t c : ℝ) (u : ℝ → U) : sys.convV t (c • u) = c • sys.convV t u := by
  simp only [convV, Pi.smul_apply, map_smul]
  exact integral_smul c _

/-- Interval splitting of the `V`-valued convolution:
`∫₀^{s+t} S(s + t - r) B u(r) dr = S(t) ∫₀ˢ S(s - r) B u(r) dr + ∫₀ᵗ S(t - r) B u(s + r) dr`. -/
theorem convV_add_time {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {u : ℝ → U}
    (hu : MemLp u 2 (μI (s + t))) :
    sys.convV (s + t) u = sys.SV.real t (sys.convV s u) + sys.convV t (fun r => u (s + r)) := by
  have hint := integrableOn_convV (sys := sys) hu
  have hst : s ≤ s + t := le_add_of_nonneg_right ht
  simp only [convV]
  rw [← Ioc_union_Ioc_eq_Ioc hs hst, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
    measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hst))
    (hint.mono_set (Ioc_subset_Ioc_left hs))]
  congr 1
  · rw [← ContinuousLinearMap.integral_comp_comm _ (integrableOn_convV (memLp_μI_of_le hu hst))]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [← sys.SV.real_add_apply ht (by linarith [hr.2])]
    congr 2
    ring
  · rw [← setIntegral_comp_add (fun r => sys.SV.real (s + t - r) (sys.B (u r))) s t]
    refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    congr 2
    ring

/-- Translation of an input to the end of a longer interval (`app:finite-horizon-output`):
with `u` extended by zero outside `(0, τ]`, `∫₀ᵀ S(T - r) B u(t - T + r) dr = ∫₀ᵗ S(t - r) B u(r) dr`
for `t ≤ T` and `t ≤ τ`. -/
theorem convV_shift {τ T t : ℝ} (htT : t ≤ T) (htτ : t ≤ τ) (u : ℝ → U) :
    sys.convV T (fun r => (Ioc 0 τ).indicator u (t - T + r)) = sys.convV t u := by
  simp only [convV]
  have h := setIntegral_comp_add
    ((Ioc 0 τ).indicator (fun r => sys.SV.real (t - r) (sys.B (u r)))) (t - T) T
  rw [show t - T + T = t by ring, setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc,
    max_eq_right (by linarith), min_eq_left htτ] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : t - T + r ∈ Ioc 0 τ
  · simp only [indicator_of_mem hr]
    congr 2
    ring
  · simp [indicator_of_notMem hr]

/-- Translation of an input to the end of a longer interval: `L_t u = L_T ũ` with
`ũ = u(t - T + ·)` (`u` extended by zero outside `(0, τ]`), for `t ≤ T` and `t ≤ τ`. -/
theorem L_shift {τ T t : ℝ} (htT : t ≤ T) (htτ : t ≤ τ) (u : ℝ → U) :
    sys.L T (fun r => (Ioc 0 τ).indicator u (t - T + r)) = sys.L t u := by
  rw [L, L, convV_shift htT htτ]

/-! ### H1 and H2 at every horizon -/

variable (sys) in
/-- `hyp:H1` at horizon `τ` with the constant `b`, for raw signals (auxiliary). -/
def H1f (τ b : ℝ) : Prop :=
  ∀ u : ℝ → U, MemLp u 2 (μI τ) →
    ∃ w : W, sys.ιWV w = sys.convV τ u ∧ ‖w‖ ≤ b * (eLpNorm u 2 (μI τ)).toReal

theorem exists_H1f_of_H1 {τ : ℝ} (h : sys.H1 τ) : ∃ b, 0 ≤ b ∧ sys.H1f τ b := by
  obtain ⟨b, hb⟩ := h
  refine ⟨max b 0, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨w, hw, hwb⟩ := hb (hu.toLp u)
  refine ⟨w, hw.trans (convV_congr_ae hu.coeFn_toLp), hwb.trans ?_⟩
  rw [Lp.norm_toLp]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg

theorem H1_of_H1f {τ b : ℝ} (h : sys.H1f τ b) : sys.H1 τ := by
  refine ⟨b, fun u => ?_⟩
  obtain ⟨w, hw, hwb⟩ := h u (Lp.memLp u)
  exact ⟨w, hw, by rwa [Lp.norm_def]⟩

/-- H1 passes to shorter horizons, with the same constant (translate the input to the end of
the longer interval). -/
theorem H1f.mono {T τ b : ℝ} (h : sys.H1f T b) (hb : 0 ≤ b) (hτT : τ ≤ T) : sys.H1f τ b := by
  intro u hu
  have hg : MemLp ((Ioc 0 τ).indicator u) 2 volume := memLp_indicator_Ioc hu
  have hv : MemLp (fun r => (Ioc 0 τ).indicator u (τ - T + r)) 2 (μI T) :=
    memLp_comp_add_of_volume hg _ T
  obtain ⟨w, hw, hwb⟩ := h _ hv
  refine ⟨w, hw.trans (convV_shift hτT le_rfl u), hwb.trans (mul_le_mul_of_nonneg_left ?_ hb)⟩
  refine ENNReal.toReal_mono hu.eLpNorm_ne_top ?_
  calc eLpNorm (fun r => (Ioc 0 τ).indicator u (τ - T + r)) 2 (μI T)
      ≤ eLpNorm (fun r => (Ioc 0 τ).indicator u (τ - T + r)) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm ((Ioc 0 τ).indicator u) 2 volume :=
        eLpNorm_comp_measurePreserving hg.aestronglyMeasurable (measurePreserving_add_left _ _)
    _ = eLpNorm u 2 (μI τ) :=
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet

/-- H1 at `s` and at `t` gives H1 at `s + t` (interval splitting and the semigroup on `W`). -/
theorem H1f.add {s t b₁ b₂ : ℝ} (h₁ : sys.H1f s b₁) (h₂ : sys.H1f t b₂) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) :
    sys.H1f (s + t) (‖sys.SW.real t‖ * b₁ + b₂) := by
  intro u hu
  have hst : s ≤ s + t := le_add_of_nonneg_right ht
  have hu₂ : MemLp (fun r => u (s + r)) 2 (μI t) := memLp_comp_add hu hs le_rfl
  obtain ⟨w₁, hw₁, hwb₁⟩ := h₁ u (memLp_μI_of_le hu hst)
  obtain ⟨w₂, hw₂, hwb₂⟩ := h₂ _ hu₂
  refine ⟨sys.SW.real t w₁ + w₂, ?_, ?_⟩
  · rw [map_add, ιWV_SW, hw₁, hw₂, convV_add_time hs ht hu]
  · set e := (eLpNorm u 2 (μI (s + t))).toReal
    have he₁ : (eLpNorm u 2 (μI s)).toReal ≤ e :=
      ENNReal.toReal_mono hu.eLpNorm_ne_top
        (eLpNorm_mono_measure _ (Measure.restrict_mono (Ioc_subset_Ioc_right hst) le_rfl))
    have he₂ : (eLpNorm (fun r => u (s + r)) 2 (μI t)).toReal ≤ e := by
      have := norm_window_le hu hs le_rfl (T := t)
      rwa [window_eq_toLp hu₂, Lp.norm_toLp] at this
    calc ‖sys.SW.real t w₁ + w₂‖ ≤ ‖sys.SW.real t w₁‖ + ‖w₂‖ := norm_add_le _ _
      _ ≤ ‖sys.SW.real t‖ * ‖w₁‖ + ‖w₂‖ := by gcongr; exact (sys.SW.real t).le_opNorm w₁
      _ ≤ ‖sys.SW.real t‖ * (b₁ * e) + b₂ * e := by
          gcongr
          · exact hwb₁.trans (mul_le_mul_of_nonneg_left he₁ hb₁)
          · exact hwb₂.trans (mul_le_mul_of_nonneg_left he₂ hb₂)
      _ = (‖sys.SW.real t‖ * b₁ + b₂) * e := by ring

variable (sys) in
/-- `hyp:H1` at one horizon `T > 0` gives it at every horizon (`app:finite-horizon-output`:
translation for `τ ≤ T`, interval splitting and the semigroup on `W` for `τ > T`). -/
theorem H1.of_pos {T : ℝ} (h : sys.H1 T) (hT : 0 < T) (τ : ℝ) : sys.H1 τ := by
  obtain ⟨b, hb, hbT⟩ := exists_H1f_of_H1 h
  have key : ∀ n : ℕ, ∃ b', 0 ≤ b' ∧ sys.H1f (n * T) b' := by
    intro n
    induction n with
    | zero => exact ⟨b, hb, hbT.mono hb (by simp [hT.le])⟩
    | succ n ih =>
      obtain ⟨b', hb', h'⟩ := ih
      refine ⟨‖sys.SW.real T‖ * b' + b, by positivity, ?_⟩
      have := h'.add hbT (by positivity) hT.le hb' hb
      rwa [show ((n + 1 : ℕ) : ℝ) * T = n * T + T by push_cast; ring]
  obtain ⟨n, hn⟩ := exists_nat_ge (τ / T)
  obtain ⟨b', hb', h'⟩ := key n
  exact H1_of_H1f (h'.mono hb' (by rwa [div_le_iff₀ hT] at hn))

/-- `hyp:H2` with a nonnegative constant. -/
theorem H2.exists_nonneg {τ : ℝ} (h : sys.H2 τ) : ∃ c, 0 ≤ c ∧ ∀ w : W,
    eLpNorm (fun t => sys.C (sys.SW.real t w)) 2 (μI τ) ≤ ENNReal.ofReal (c * ‖sys.ιWV w‖) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨max c 0, le_max_right _ _, fun w => (hc w).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

/-- H2 passes to shorter horizons. -/
theorem H2.mono {T τ : ℝ} (h : sys.H2 T) (hτT : τ ≤ T) : sys.H2 τ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun w => (eLpNorm_mono_measure _
    (Measure.restrict_mono (Ioc_subset_Ioc_right hτT) le_rfl)).trans (hc w)⟩

/-- H2 at `s` and at `t` gives H2 at `s + t` (interval splitting, `ιWV ∘ S_W = S_V ∘ ιWV`). -/
theorem H2.add {s t : ℝ} (h₁ : sys.H2 s) (h₂ : sys.H2 t) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    sys.H2 (s + t) := by
  obtain ⟨c₁, hc₁, h₁⟩ := h₁.exists_nonneg
  obtain ⟨c₂, hc₂, h₂⟩ := h₂.exists_nonneg
  refine ⟨c₁ + c₂ * ‖sys.SV.real s‖, fun w => ?_⟩
  set f := fun r => sys.C (sys.SW.real r w) with hf
  have hfm : ∀ μ : Measure ℝ, AEStronglyMeasurable f μ := fun μ =>
    (sys.C.continuous.comp (sys.SW.continuous_real_apply w)).aestronglyMeasurable
  have hsplit : μI (s + t) = μI s + volume.restrict (Ioc s (s + t)) := by
    rw [μI, ← Ioc_union_Ioc_eq_Ioc hs (le_add_of_nonneg_right ht),
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  have h2 : eLpNorm f 2 (volume.restrict (Ioc s (s + t))) ≤
      ENNReal.ofReal (c₂ * ‖sys.SV.real s‖ * ‖sys.ιWV w‖) := by
    rw [← eLpNorm_comp_measurePreserving (hfm _) (measurePreserving_add_μI s t)]
    have hae : (f ∘ fun r => s + r) =ᵐ[μI t]
        fun r => sys.C (sys.SW.real r (sys.SW.real s w)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simp only [Function.comp, hf]
      rw [add_comm, sys.SW.real_add_apply hr.1.le hs]
    rw [eLpNorm_congr_ae hae]
    refine (h₂ _).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ιWV_SW, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((sys.SV.real s).le_opNorm _) hc₂
  calc eLpNorm f 2 (μI (s + t))
      ≤ eLpNorm f 2 (μI s) + eLpNorm f 2 (volume.restrict (Ioc s (s + t))) := by
        rw [hsplit]; exact eLpNorm_two_add_measure_le (hfm _) (hfm _)
    _ ≤ ENNReal.ofReal (c₁ * ‖sys.ιWV w‖) +
          ENNReal.ofReal (c₂ * ‖sys.SV.real s‖ * ‖sys.ιWV w‖) := add_le_add (h₁ w) h2
    _ = ENNReal.ofReal ((c₁ + c₂ * ‖sys.SV.real s‖) * ‖sys.ιWV w‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

variable (sys) in
/-- `hyp:H2` at one horizon `T > 0` gives it at every horizon (`app:finite-horizon-output`). -/
theorem H2.of_pos {T : ℝ} (h : sys.H2 T) (hT : 0 < T) (τ : ℝ) : sys.H2 τ := by
  have key : ∀ n : ℕ, sys.H2 (n * T) := by
    intro n
    induction n with
    | zero => exact h.mono (by simp [hT.le])
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ) * T = n * T + T by push_cast; ring]
      exact ih.add h (by positivity) hT.le
  obtain ⟨n, hn⟩ := exists_nat_ge (τ / T)
  exact (key n).mono (by rwa [div_le_iff₀ hT] at hn)

/-- Bounded `B` satisfies `hyp:H1` with `W = X = V`. -/
theorem bounded_H1 (S : C0Semigroup ℝ X) (B : U →L[ℝ] X) (C : X →L[ℝ] Y) (T : ℝ) :
    (bounded S B C).H1 T := by
  obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le T
  set m := ((μI T) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal
  refine ⟨M * ‖B‖ * m, fun u => ⟨∫ r in Ioc 0 T, S.real (T - r) (B (u r)), rfl, ?_⟩⟩
  have hF : ∀ᵐ r ∂μI T, ‖S.real (T - r) (B (u r))‖ ≤ (M * ‖B‖) * ‖u r‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    calc _ ≤ ‖S.real (T - r)‖ * ‖B (u r)‖ := (S.real (T - r)).le_opNorm _
      _ ≤ M * (‖B‖ * ‖u r‖) :=
          mul_le_mul (hM _ (by linarith [hr.1])) (B.le_opNorm _) (norm_nonneg _) hM0
      _ = _ := by ring
  have hFm : AEStronglyMeasurable (fun r => S.real (T - r) (B (u r))) (μI T) :=
    S.aestronglyMeasurable_conv (B.continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)) T
  have hfin : (μI T) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  calc ‖∫ r in Ioc 0 T, S.real (T - r) (B (u r))‖
      ≤ (eLpNorm (fun r => S.real (T - r) (B (u r))) 1 (μI T)).toReal := by
        refine (norm_integral_le_lintegral_norm _).trans_eq ?_
        rw [eLpNorm_one_eq_lintegral_enorm hFm]
        simp_rw [ofReal_norm]
    _ ≤ (eLpNorm (fun r => S.real (T - r) (B (u r))) 2 (μI T) *
          (μI T) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal := by
        refine ENNReal.toReal_mono ?_ (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hFm)
        refine ENNReal.mul_ne_top ?_ hfin
        exact ((eLpNorm_le_mul_eLpNorm_of_ae_le_mul hFm hF 2).trans_lt
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top u))).ne
    _ ≤ (ENNReal.ofReal (M * ‖B‖) * eLpNorm u 2 (μI T) *
          (μI T) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal := by
        refine ENNReal.toReal_mono ?_ ?_
        · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (Lp.eLpNorm_ne_top u)) hfin
        · gcongr
          exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hFm hF 2
    _ = M * ‖B‖ * m * ‖u‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ← Lp.norm_def]
        ring

/-- Bounded `C` satisfies `hyp:H2` with `W = X = V`. -/
theorem bounded_H2 (S : C0Semigroup ℝ X) (B : U →L[ℝ] X) (C : X →L[ℝ] Y) (T : ℝ) :
    (bounded S B C).H2 T := by
  obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le T
  refine ⟨((μI T) univ).toReal ^ (1 / 2 : ℝ) * (‖C‖ * M), fun w => ?_⟩
  refine (eLpNorm_two_le_ofReal_of_bound (K := ‖C‖ * M * ‖w‖)
    (C.continuous.comp (S.continuous_real_apply w)).aestronglyMeasurable ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    calc ‖C (S.real r w)‖ ≤ ‖C‖ * ‖S.real r w‖ := C.le_opNorm _
      _ ≤ ‖C‖ * (M * ‖w‖) := by
          gcongr; exact ((S.real r).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (hM r hr.2) (norm_nonneg w))
      _ = _ := by ring
  · simp only [bounded_ιV, bounded_ιW, ιWV, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_apply]
    ring_nf

/-! ### The control-to-state map `L_t` -/

/-- Under `hyp:H1` at the horizon `t` itself, `L_t u` is the `V`-valued convolution. -/
theorem ιWV_L_of_H1 {t : ℝ} (h : sys.H1 t) {u : ℝ → U} (hu : MemLp u 2 (μI t)) :
    sys.ιWV (sys.L t u) = sys.convV t u := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨w, hw, -⟩ := hb (hu.toLp u)
  exact ιWV_L_of_exists ⟨w, hw.trans (convV_congr_ae hu.coeFn_toLp)⟩

/-- Under `hyp:H1`, `L_t u ∈ W` is the `V`-valued convolution `∫₀ᵗ S_V(t - r) B u(r) dr`. -/
theorem ιWV_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) : sys.ιWV (sys.L t u) = sys.convV t u :=
  ιWV_L_of_H1 (hH1.of_pos sys hT t) hu

theorem L_add_of_H1 {t : ℝ} (h : sys.H1 t) {u v : ℝ → U} (hu : MemLp u 2 (μI t))
    (hv : MemLp v 2 (μI t)) : sys.L t (u + v) = sys.L t u + sys.L t v :=
  L_eq_of_ιWV (by rw [map_add, ιWV_L_of_H1 h hu, ιWV_L_of_H1 h hv, convV_add hu hv])

theorem L_smul_of_H1 {t : ℝ} (h : sys.H1 t) {u : ℝ → U} (hu : MemLp u 2 (μI t)) (c : ℝ) :
    sys.L t (c • u) = c • sys.L t u :=
  L_eq_of_ιWV (by rw [map_smul, ιWV_L_of_H1 h hu, convV_smul])

theorem L_add {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u v : ℝ → U}
    (hu : MemLp u 2 (μI t)) (hv : MemLp v 2 (μI t)) : sys.L t (u + v) = sys.L t u + sys.L t v :=
  L_add_of_H1 (hH1.of_pos sys hT t) hu hv

theorem L_smul {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) (c : ℝ) : sys.L t (c • u) = c • sys.L t u :=
  L_smul_of_H1 (hH1.of_pos sys hT t) hu c

/-- Interval splitting: `L_{s+t} u = S_W(t) L_s u + L_t u(s + ·)`. -/
theorem L_add_time {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {u : ℝ → U} (hu : MemLp u 2 (μI (s + t))) :
    sys.L (s + t) u = sys.SW.real t (sys.L s u) + sys.L t (fun r => u (s + r)) := by
  refine L_eq_of_ιWV ?_
  rw [map_add, ιWV_SW, ιWV_L hH1 hT (memLp_μI_of_le hu (le_add_of_nonneg_right ht)),
    ιWV_L hH1 hT (memLp_comp_add hu hs le_rfl), convV_add_time hs ht hu]

variable (sys)

theorem exists_Lop {t : ℝ} (h : sys.H1 t) : ∃ L : L2 U t →L[ℝ] W, ∀ u, L u = sys.L t u := by
  obtain ⟨b, hb⟩ := h
  let f : L2 U t →ₗ[ℝ] W :=
    { toFun := fun u => sys.L t u
      map_add' := fun u v => by
        rw [L_congr_ae (Lp.coeFn_add u v)]
        exact L_add_of_H1 ⟨b, hb⟩ (Lp.memLp u) (Lp.memLp v)
      map_smul' := fun c u => by
        rw [RingHom.id_apply, L_congr_ae (Lp.coeFn_smul c u)]
        exact L_smul_of_H1 ⟨b, hb⟩ (Lp.memLp u) c }
  refine ⟨f.mkContinuous b fun u => ?_, fun u => rfl⟩
  obtain ⟨w, hw, hwb⟩ := hb u
  have : sys.L t u = w := L_eq_of_ιWV hw
  simpa [f, this] using hwb

open scoped Classical in
/-- The control-to-state map `L_t : L²(0, t; U) → W` as a bounded operator (junk `0` if
`hyp:H1` fails at `t`).  `ℛ_t(0) = im (ιW ∘L Lop t)`. -/
def Lop (t : ℝ) : L2 U t →L[ℝ] W := if h : sys.H1 t then (sys.exists_Lop h).choose else 0

variable {sys}

theorem Lop_apply {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} (u : L2 U t) :
    sys.Lop t u = sys.L t u := by
  have h := hH1.of_pos sys hT t
  rw [Lop, dite_eq_left h]
  exact (sys.exists_Lop h).choose_spec u

/-- `L_t u = L_τ u_t` (`app:finite-horizon-output`), where `u_t = windowL τ τ (t - τ) u` is `u`
translated to the end of `(0, τ)` (zero on `(0, τ - t)`). -/
theorem L_eq_Lop_windowL {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ t : ℝ} (ht : t ≤ τ)
    (u : L2 U τ) : sys.L t u = sys.Lop τ (windowL τ τ (t - τ) u) := by
  rw [Lop_apply hH1 hT, L_congr_ae (coeFn_windowL u), L_shift ht ht]

/-- `sup_{t ≤ τ} ‖L_t u‖_W ≤ b_τ ‖u‖_{L²(0, τ; U)}` (`app:finite-horizon-output`). -/
theorem exists_norm_L_le {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (τ : ℝ) :
    ∃ b : ℝ, ∀ u : L2 U τ, ∀ t ∈ Icc 0 τ, ‖sys.L t u‖ ≤ b * ‖u‖ := by
  refine ⟨‖sys.Lop τ‖, fun u t ht => ?_⟩
  rw [L_eq_Lop_windowL hH1 hT ht.2 u]
  have h1 : ‖windowL τ τ (t - τ) u‖ ≤ ‖u‖ := by
    have h2 := (windowL (E := U) τ τ (t - τ)).le_opNorm u
    have h3 := norm_windowL_le (E := U) τ τ (t - τ)
    calc ‖windowL τ τ (t - τ) u‖ ≤ ‖windowL (E := U) τ τ (t - τ)‖ * ‖u‖ := h2
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  exact ((sys.Lop τ).le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))

/-- `t ↦ L_t u` is continuous into `W` (`L_· u ∈ C([0, τ]; W)`, `app:finite-horizon-output`). -/
theorem continuousOn_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) : ContinuousOn (fun t => sys.L t u) (Icc 0 τ) := by
  refine ((sys.Lop τ).continuous.comp ((continuous_windowL τ τ (hu.toLp u)).comp
    (continuous_sub_right τ))).continuousOn.congr fun t ht => ?_
  simp only [Function.comp_apply]
  rw [← L_eq_Lop_windowL hH1 hT ht.2]
  exact L_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2)
    hu.coeFn_toLp.symm)

/-! ### Mild solutions -/

variable (sys)

/-- The mild solution `x(t; x₀, u) = S(t) x₀ + L_t u ∈ X` (`eq:hilbert-mild-state`). -/
def mild (x₀ : X) (u : ℝ → U) (t : ℝ) : X := sys.SX.real t x₀ + sys.ιW (sys.L t u)

/-- The mild solution for `x₀ ∈ W`, as a `W`-valued function (`x ∈ C(I; W)`). -/
def mildW (w₀ : W) (u : ℝ → U) (t : ℝ) : W := sys.SW.real t w₀ + sys.L t u

/-- The output `y(t) = C x(t)` for `x₀ ∈ W` (`eq:hilbert-mild-output`). -/
def outputW (w₀ : W) (u : ℝ → U) (t : ℝ) : Y := sys.C (sys.mildW w₀ u t)

variable {sys}

theorem ιW_mildW (w₀ : W) (u : ℝ → U) (t : ℝ) :
    sys.ιW (sys.mildW w₀ u t) = sys.mild (sys.ιW w₀) u t := by
  simp [mildW, mild, ιW_SW]

@[simp] theorem mild_zero_time (x₀ : X) (u : ℝ → U) : sys.mild x₀ u 0 = x₀ := by
  simp [mild]

@[simp] theorem mildW_zero_time (w₀ : W) (u : ℝ → U) : sys.mildW w₀ u 0 = w₀ := by
  simp [mildW]

theorem mild_zero_left (u : ℝ → U) (t : ℝ) : sys.mild 0 u t = sys.ιW (sys.L t u) := by
  simp [mild]

/-- Causality: `x(t; x₀, u)` depends only on `u` on `(0, t]`. -/
theorem mild_congr_ae {t : ℝ} {u v : ℝ → U} (h : u =ᵐ[μI t] v) (x₀ : X) :
    sys.mild x₀ u t = sys.mild x₀ v t := by
  simp only [mild, L_congr_ae h]

theorem mildW_congr_ae {t : ℝ} {u v : ℝ → U} (h : u =ᵐ[μI t] v) (w₀ : W) :
    sys.mildW w₀ u t = sys.mildW w₀ v t := by
  simp only [mildW, L_congr_ae h]

theorem mild_add {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u v : ℝ → U}
    (hu : MemLp u 2 (μI t)) (hv : MemLp v 2 (μI t)) (x₀ x₁ : X) :
    sys.mild (x₀ + x₁) (u + v) t = sys.mild x₀ u t + sys.mild x₁ v t := by
  simp only [mild, map_add, L_add hH1 hT hu hv]; abel

theorem mild_smul {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) (c : ℝ) (x₀ : X) :
    sys.mild (c • x₀) (c • u) t = c • sys.mild x₀ u t := by
  simp only [mild, map_smul, L_smul hH1 hT hu, smul_add]

/-- The flow property `x(s + t; x₀, u) = x(t; x(s; x₀, u), u(s + ·))`. -/
theorem mild_add_time {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {u : ℝ → U} (hu : MemLp u 2 (μI (s + t))) (x₀ : X) :
    sys.mild x₀ u (s + t) = sys.mild (sys.mild x₀ u s) (fun r => u (s + r)) t := by
  simp only [mild, L_add_time hH1 hT hs ht hu, map_add, ιW_SW]
  rw [show s + t = t + s from add_comm s t, sys.SX.real_add_apply ht hs]
  abel

/-- The flow property in `W`. -/
theorem mildW_add_time {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {u : ℝ → U} (hu : MemLp u 2 (μI (s + t))) (w₀ : W) :
    sys.mildW w₀ u (s + t) = sys.mildW (sys.mildW w₀ u s) (fun r => u (s + r)) t := by
  simp only [mildW, L_add_time hH1 hT hs ht hu, map_add]
  rw [show s + t = t + s from add_comm s t, sys.SW.real_add_apply ht hs]
  abel

theorem continuousOn_mildW {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (w₀ : W) : ContinuousOn (sys.mildW w₀ u) (Icc 0 τ) :=
  (sys.SW.continuous_real_apply w₀).continuousOn.add (continuousOn_L hH1 hT hu)

theorem continuousOn_mild {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) : ContinuousOn (sys.mild x₀ u) (Icc 0 τ) :=
  (sys.SX.continuous_real_apply x₀).continuousOn.add
    (sys.ιW.continuous.comp_continuousOn (continuousOn_L hH1 hT hu))

theorem memLp_mild {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) : MemLp (sys.mild x₀ u) 2 (μI τ) :=
  memLp_μI_of_continuousOn (continuousOn_mild hH1 hT hu x₀)

theorem memLp_mildW {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (w₀ : W) : MemLp (sys.mildW w₀ u) 2 (μI τ) :=
  memLp_μI_of_continuousOn (continuousOn_mildW hH1 hT hu w₀)

/-! ### The input–output map `𝓕_τ` and the observability operator `𝓞_τ` -/

variable (sys)

/-- Existence of `𝓕_τ` (`lem:finite-horizon-output`). -/
theorem exists_𝓕 {τ : ℝ} (h : sys.H1 τ) :
    ∃ F : L2 U τ →L[ℝ] L2 Y τ, ∀ u, ⇑(F u) =ᵐ[μI τ] fun t => sys.C (sys.L t u) := by
  rcases le_or_gt τ 0 with hτ | hτ
  · refine ⟨0, fun u => ?_⟩
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      absurd (ht.1.trans_le ht.2) (not_lt.2 hτ)
  obtain ⟨b, hb⟩ := exists_norm_L_le h hτ τ
  set b' := max b 0
  have hb' : ∀ u : L2 U τ, ∀ t ∈ Icc 0 τ, ‖sys.L t u‖ ≤ b' * ‖u‖ := fun u t ht =>
    (hb u t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hmem : ∀ u : L2 U τ, MemLp (fun t => sys.C (sys.L t u)) 2 (μI τ) := fun u =>
    memLp_μI_of_continuousOn
      (sys.C.continuous.comp_continuousOn (continuousOn_L h hτ (Lp.memLp u)))
  have hsub : ∀ t ∈ Ioc 0 τ, ∀ {f g : ℝ → U}, f =ᵐ[μI τ] g → f =ᵐ[μI t] g :=
    fun t ht _ _ hfg => ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) hfg
  let F : L2 U τ →ₗ[ℝ] L2 Y τ :=
    { toFun := fun u => (hmem u).toLp _
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Pi.add_apply]
        rw [L_congr_ae (hsub t ht (Lp.coeFn_add u v)),
          L_add h hτ (memLp_μI_of_le (Lp.memLp u) ht.2) (memLp_μI_of_le (Lp.memLp v) ht.2),
          map_add]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Pi.smul_apply]
        rw [L_congr_ae (hsub t ht (Lp.coeFn_smul c u)),
          L_smul h hτ (memLp_μI_of_le (Lp.memLp u) ht.2), map_smul] }
  refine ⟨F.mkContinuous ((measureUnivNNReal (μI τ) : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ *
    (‖sys.C‖ * b')) fun u => ?_, fun u => (hmem u).coeFn_toLp⟩
  have := Lp.norm_le_of_ae_bound (f := (hmem u).toLp _) (C := ‖sys.C‖ * (b' * ‖u‖))
    (by positivity) ?_
  · change ‖(hmem u).toLp _‖ ≤ _
    refine this.trans_eq ?_
    ring
  · filter_upwards [(hmem u).coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t h1 h2
    rw [h1]
    exact (sys.C.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (hb' u t (Ioc_subset_Icc_self h2)) (norm_nonneg _))

/-- Existence of `𝓞_τ`: `x₀ ↦ C S(·) x₀`, extended from `W` to `X` by density and `hyp:H2`
(`lem:finite-horizon-output`). -/
theorem exists_𝓞 {τ : ℝ} (h : sys.H2 τ) :
    ∃ O : X →L[ℝ] L2 Y τ, ∀ w : W, ⇑(O (sys.ιW w)) =ᵐ[μI τ] fun t => sys.C (sys.SW.real t w) := by
  obtain ⟨c, hc⟩ := h
  have hmem : ∀ w : W, MemLp (fun t => sys.C (sys.SW.real t w)) 2 (μI τ) := fun w =>
    memLp_iff.2 (lt_of_le_of_lt (hc w) ENNReal.ofReal_lt_top)
  let O₀ : W →ₗ[ℝ] L2 Y τ :=
    { toFun := fun w => (hmem w).toLp _
      map_add' := fun w w' => by
        rw [← MemLp.toLp_add]
        congr 1
        funext t
        simp only [Pi.add_apply, map_add]
      map_smul' := fun a w => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        funext t
        simp only [Pi.smul_apply, map_smul] }
  have hbound : ∀ w : W, ‖O₀ w‖ ≤ (max c 0 * ‖sys.ιV‖) * ‖(sys.ιW : W →ₗ[ℝ] X) w‖ := by
    intro w
    change ‖(hmem w).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((hc w).trans (ENNReal.ofReal_le_ofReal ?_))
    calc c * ‖sys.ιWV w‖ ≤ max c 0 * ‖sys.ιWV w‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max c 0 * (‖sys.ιV‖ * ‖sys.ιW w‖) :=
          mul_le_mul_of_nonneg_left (sys.ιV.le_opNorm _) (le_max_right _ _)
      _ = _ := by simp only [ContinuousLinearMap.coe_coe]; ring
  refine ⟨O₀.extendOfNorm (sys.ιW : W →ₗ[ℝ] X), fun w => ?_⟩
  have hd : DenseRange (sys.ιW : W →ₗ[ℝ] X) := sys.ιW_denseRange
  have := LinearMap.extendOfNorm_eq hd ⟨_, hbound⟩ w
  rw [ContinuousLinearMap.coe_coe] at this
  rw [this]
  exact (hmem w).coeFn_toLp

open scoped Classical in
/-- The **input–output map** `𝓕_τ : L²(0, τ; U) → L²(0, τ; Y)`, `u ↦ C L_(·) u`
(`lem:finite-horizon-output`; junk `0` if `hyp:H1` fails at `τ`). -/
def 𝓕 (τ : ℝ) : L2 U τ →L[ℝ] L2 Y τ := if h : sys.H1 τ then (sys.exists_𝓕 h).choose else 0

open scoped Classical in
/-- The **observability operator** `𝓞_τ : X → L²(0, τ; Y)`, `x₀ ↦ C S(·) x₀`
(`lem:finite-horizon-output`; junk `0` if `hyp:H2` fails at `τ`). -/
def 𝓞 (τ : ℝ) : X →L[ℝ] L2 Y τ := if h : sys.H2 τ then (sys.exists_𝓞 h).choose else 0

variable {sys}

/-- `𝓕_τ u = C L_(·) u` in `L²(0, τ; Y)`. -/
theorem 𝓕_ae_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} (u : L2 U τ) :
    ⇑(sys.𝓕 τ u) =ᵐ[μI τ] fun t => sys.C (sys.L t u) := by
  have h := hH1.of_pos sys hT τ
  rw [𝓕, dite_eq_left h]
  exact (sys.exists_𝓕 h).choose_spec u

/-- `𝓞_τ x₀ = C S(·) x₀` in `L²(0, τ; Y)` for `x₀ ∈ W`. -/
theorem 𝓞_ae_eq {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {τ : ℝ} (w : W) :
    ⇑(sys.𝓞 τ (sys.ιW w)) =ᵐ[μI τ] fun t => sys.C (sys.SW.real t w) := by
  have h := hH2.of_pos sys hT τ
  rw [𝓞, dite_eq_left h]
  exact (sys.exists_𝓞 h).choose_spec w

/-- `𝓞_τ` is the only bounded operator `X → L²(0, τ; Y)` agreeing with `C S(·)` on `W`. -/
theorem eq_𝓞 {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {τ : ℝ} (O : X →L[ℝ] L2 Y τ)
    (hO : ∀ w : W, ⇑(O (sys.ιW w)) =ᵐ[μI τ] fun t => sys.C (sys.SW.real t w)) :
    O = sys.𝓞 τ := by
  refine ContinuousLinearMap.coe_injective (DFunLike.coe_injective ?_)
  refine sys.ιW_denseRange.equalizer O.continuous (sys.𝓞 τ).continuous (funext fun w => ?_)
  exact Lp.ext ((hO w).trans (𝓞_ae_eq hH2 hT w).symm)

/-- `𝓕_τ` is the only bounded operator `L²(0, τ; U) → L²(0, τ; Y)` given by `C L_(·)`. -/
theorem eq_𝓕 {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} (F : L2 U τ →L[ℝ] L2 Y τ)
    (hF : ∀ u : L2 U τ, ⇑(F u) =ᵐ[μI τ] fun t => sys.C (sys.L t u)) : F = sys.𝓕 τ :=
  ContinuousLinearMap.ext fun u => Lp.ext ((hF u).trans (𝓕_ae_eq hH1 hT u).symm)

/-- Restriction: `(𝓞_τ x)|_(0, ρ) = 𝓞_ρ x` for `ρ ≤ τ`. -/
theorem 𝓞_restrict {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {ρ τ : ℝ} (hρτ : ρ ≤ τ) (x : X) :
    ⇑(sys.𝓞 ρ x) =ᵐ[μI ρ] ⇑(sys.𝓞 τ x) := by
  have h := eq_𝓞 hH2 hT ((restrictL τ ρ).comp (sys.𝓞 τ)) fun w => by
    rw [ContinuousLinearMap.comp_apply]
    filter_upwards [coeFn_restrictL hρτ (sys.𝓞 τ (sys.ιW w)),
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hρτ)
        (𝓞_ae_eq hH2 hT (τ := τ) w)] with t h1 h2
    rw [h1, h2]
  rw [← h]
  exact coeFn_restrictL hρτ _

/-- Causality of `𝓕`: if `u = v` on `(0, ρ)` then `𝓕_τ u = 𝓕_ρ v` on `(0, ρ)`, `ρ ≤ τ`. -/
theorem 𝓕_causal {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {ρ τ : ℝ} (hρτ : ρ ≤ τ)
    (u : L2 U τ) (v : L2 U ρ) (huv : ⇑u =ᵐ[μI ρ] ⇑v) :
    ⇑(sys.𝓕 τ u) =ᵐ[μI ρ] ⇑(sys.𝓕 ρ v) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hρτ)
      (𝓕_ae_eq hH1 hT u), 𝓕_ae_eq hH1 hT v, ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
  rw [h1, h2, L_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) huv)]

/-- The shift identity for the free response (`lem:finite-horizon-output`): for `0 ≤ s` and
`s + ρ ≤ τ`, `(𝓞_τ x)(s + ·) = 𝓞_ρ (S(s) x)` in `L²(0, ρ; Y)`.  Checked on `W`, then extended
by density. -/
theorem 𝓞_shift {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {s ρ τ : ℝ} (hs : 0 ≤ s)
    (hsρ : s + ρ ≤ τ) (x : X) :
    (fun t => sys.𝓞 τ x (s + t)) =ᵐ[μI ρ] ⇑(sys.𝓞 ρ (sys.SX.real s x)) := by
  have key : (windowL τ ρ s).comp (sys.𝓞 τ) = (sys.𝓞 ρ).comp (sys.SX.real s) := by
    refine ContinuousLinearMap.coe_injective (DFunLike.coe_injective ?_)
    refine sys.ιW_denseRange.equalizer ((windowL τ ρ s).comp (sys.𝓞 τ)).continuous
      ((sys.𝓞 ρ).comp (sys.SX.real s)).continuous (funext fun w => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply]
    refine Lp.ext ?_
    rw [← ιW_SW]
    filter_upwards [coeFn_windowL_of_le hs hsρ (sys.𝓞 τ (sys.ιW w)),
      ae_comp_add (𝓞_ae_eq hH2 hT (τ := τ) w) hs hsρ,
      𝓞_ae_eq hH2 hT (τ := ρ) (sys.SW.real s w), ae_restrict_mem measurableSet_Ioc]
      with t h1 h2 h3 ht
    rw [h1, h2, h3, add_comm s t, sys.SW.real_add_apply ht.1.le hs]
  have hx : windowL τ ρ s (sys.𝓞 τ x) = sys.𝓞 ρ (sys.SX.real s x) :=
    DFunLike.congr_fun key x
  rw [← hx]
  exact (coeFn_windowL_of_le hs hsρ _).symm

/-! ### The output record and the shift identity -/

variable (sys)

/-- The output on `[0, τ]` generated by `(x₀, u)`, `y = 𝓞_τ x₀ + 𝓕_τ u`, as a function: a
representative of `𝓞_τ x₀` plus the pointwise forced response `C L_t u`. -/
def output (τ : ℝ) (x₀ : X) (u : ℝ → U) : ℝ → Y := fun t => sys.𝓞 τ x₀ t + sys.C (sys.L t u)

variable {sys}

/-- The output formula `y = 𝓞_τ x₀ + 𝓕_τ u` (`lem:finite-horizon-output`). -/
theorem output_ae_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) :
    sys.output τ x₀ u =ᵐ[μI τ] ⇑(sys.𝓞 τ x₀ + sys.𝓕 τ (hu.toLp u)) := by
  filter_upwards [Lp.coeFn_add (sys.𝓞 τ x₀) (sys.𝓕 τ (hu.toLp u)),
    𝓕_ae_eq hH1 hT (hu.toLp u), ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
  rw [h1, Pi.add_apply, h2, output, L_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right ht.2) hu.coeFn_toLp)]

theorem memLp_output {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) : MemLp (sys.output τ x₀ u) 2 (μI τ) :=
  (Lp.memLp _).ae_eq (output_ae_eq hH1 hT hu x₀).symm

set_option linter.unusedVariables false in
/-- For `x₀ ∈ W` the output is pointwise `y(t) = C x(t)` (`eq:hilbert-mild-output`). -/
theorem output_ιW {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (w₀ : W) :
    sys.output τ (sys.ιW w₀) u =ᵐ[μI τ] sys.outputW w₀ u := by
  filter_upwards [𝓞_ae_eq hH2 hT (τ := τ) w₀] with t ht
  simp only [output, outputW, mildW, ht, map_add]

/-- **Shift identity** (`lem:finite-horizon-output`): for `0 ≤ s` and `s + ρ ≤ τ`,
`y(s + ·) = 𝓞_ρ x(s) + 𝓕_ρ u(s + ·)` in `L²(0, ρ; Y)`. -/
theorem output_shift {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) {s ρ τ : ℝ}
    (hs : 0 ≤ s) (hsρ : s + ρ ≤ τ) {u : ℝ → U} (hu : MemLp u 2 (μI τ)) (x₀ : X) :
    (fun t => sys.output τ x₀ u (s + t)) =ᵐ[μI ρ]
      sys.output ρ (sys.mild x₀ u s) (fun r => u (s + r)) := by
  filter_upwards [𝓞_shift hH2 hT hs hsρ x₀,
    Lp.coeFn_add (sys.𝓞 ρ (sys.SX.real s x₀)) (sys.𝓞 ρ (sys.ιW (sys.L s u))),
    𝓞_ae_eq hH2 hT (τ := ρ) (sys.L s u), ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 ht
  simp only [output, mild]
  rw [(sys.𝓞 ρ).map_add, h2, Pi.add_apply, ← h1, h3,
    L_add_time hH1 hT hs ht.1.le (memLp_μI_of_le hu (by linarith [ht.2])), map_add]
  abel

end System

end DataDrivenControl
