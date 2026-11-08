module

public import Mathlib
public import DataDrivenControl.Signal.Basic

/-!
# Windows, translation and window synthesis operators

Paper: `def:window-informative` (operator `𝒵`), `eq:io-window-synthesis` (operator `𝒴`),
`eq:window-factorization`; the lemmas used in `app:finite-horizon-output` (continuity of
translation in `L²`), `app:window-implies-informative`, `app:window-pe-necessity`,
`app:windowed-io-fundamental-lemma`, `app:io-window-controllability`, `app:lqr-data-io` and
`app:window-strictly-stronger`.

## Contents

* Translation of a.e. statements, of `MemLp` and of integrals from `(0, T₁)` to a window
  `(s, s + T) ⊆ (0, T₁)`: `ae_comp_add`, `memLp_comp_add`, `setIntegral_comp_add`.
* `window T f s ∈ L²(0, T; E)`: the window `f (s + ·)` of a signal `f : ℝ → E`.
  Continuity of translation: `continuous_window` (for `f ∈ L²(ℝ)`) and `continuousOn_window`
  (for `f ∈ L²(0, T + T')`, on `s ∈ [0, T']`).
* Synthesis operators out of `L²(0, T')`:
  - `pointSynth T' g φ = ∫₀^{T'} φ s • g s ds`;
  - `shiftSynth T T' f φ = ∫₀^{T'} φ s • f (s + ·) ds ∈ L²(0, T; E)`;
  - `windowSynth T T' ū x̄`, the paper's `𝒵_{T,T'}^{ū,x̄}`, into `WithLp 2 (L²(0,T;U) × X)`;
  - `ioWindowSynth T T' ū ȳ`, the paper's `𝒴_{T,T'}^{ū,ȳ}`, into
    `WithLp 2 (L²(0,T;U) × L²(0,T;Y))`.
  Their inner products and adjoints, the kernel characterisation
  `(g, ξ) ∈ ker 𝒵†  ↔  ∫₀ᵀ ⟪g t, ū (s + t)⟫ dt + ⟪ξ, x̄ s⟫ = 0` for a.e. `s ∈ (0, T')`
  (`adjoint_windowSynth_eq_zero_iff`, `denseRange_windowSynth_iff`), the same for `𝒴`, and the
  factorisation `𝒴 = 𝓜 𝒵` (`ioWindowSynth_eq_comp_windowSynth`).  Generic:
  `denseRange_iff_adjoint_eq_zero` (`DenseRange A ↔ ker A† = 0`).
* Conventions: windows are taken on `(0, T]` (the paper's `(0, T)` up to a null set); the
  definitions accept arbitrary functions and return `0` on non-square-integrable input, so the
  lemmas carry the `MemLp` hypotheses (`ū, ȳ ∈ L²(0, T + T')`, `x̄ ∈ L²(0, T')`).
* Operators on `L²` (all are instances of `windowL T₁ T r : L²(0,T₁) → L²(0,T)`,
  `f ↦ f (r + ·)` with `f` extended by zero outside `(0, T₁)`):
  `restrictL` (restriction to `(0, T₀)`), `tailL` (the tail `(T₀, T₀ + T)` shifted back),
  `extendL` (zero extension with an offset; the adjoint of `windowL`) and the concatenation
  `concat T₀ T u v ∈ L²(0, T₀ + T)`, with the lemmas used by `thm:lqr-data-io`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

namespace DataDrivenControl

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Translating a window into a longer one -/

/-- An a.e. statement on `(0, T₁)` holds a.e. on every window `(s, s + T) ⊆ (0, T₁)`, written
in the window's own time `t ∈ (0, T)` (the translation step of
`app:window-implies-informative`). -/
theorem ae_comp_add {T₁ T s : ℝ} {p : ℝ → Prop} (h : ∀ᵐ t ∂(μI T₁), p t) (hs : 0 ≤ s)
    (hsT : s + T ≤ T₁) : ∀ᵐ t ∂(μI T), p (s + t) := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h ⊢
  have h' := (measurePreserving_add_left volume s).quasiMeasurePreserving.ae h
  filter_upwards [h'] with t ht htI
  exact ht ⟨by linarith [htI.1], by linarith [htI.2]⟩

/-- A signal in `Lᵖ(0, T₁)` restricts to `Lᵖ(0, T₀)` for `T₀ ≤ T₁`. -/
theorem memLp_μI_of_le {f : ℝ → E} {q : ℝ≥0∞} {T₀ T₁ : ℝ} (hf : MemLp f q (μI T₁))
    (h : T₀ ≤ T₁) : MemLp f q (μI T₀) :=
  hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right h) le_rfl)

/-- Translation `t ↦ s + t` maps the window measure `μI T` onto Lebesgue measure on
`(s, s + T]`. -/
theorem measurePreserving_add_μI (s T : ℝ) :
    MeasurePreserving (fun t => s + t) (μI T) (volume.restrict (Ioc s (s + T))) := by
  have h := (measurePreserving_add_left volume s).restrict_preimage
    (s := Ioc s (s + T)) measurableSet_Ioc
  rwa [preimage_const_add_Ioc, sub_self, add_sub_cancel_left] at h

/-- The windows `f (s + ·)` of a signal `f ∈ Lᵖ(0, T₁)` lie in `Lᵖ(0, T)` when
`(s, s + T) ⊆ (0, T₁)`. -/
theorem memLp_comp_add {f : ℝ → E} {q : ℝ≥0∞} {T₁ T s : ℝ} (hf : MemLp f q (μI T₁))
    (hs : 0 ≤ s) (hsT : s + T ≤ T₁) : MemLp (fun t => f (s + t)) q (μI T) :=
  (hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc hs hsT) le_rfl)).comp_measurePreserving
    (measurePreserving_add_μI s T)

/-- Every window of a signal in `Lᵖ(ℝ)` lies in `Lᵖ(0, T)`. -/
theorem memLp_comp_add_of_volume {f : ℝ → E} {q : ℝ≥0∞} (hf : MemLp f q volume) (s T : ℝ) :
    MemLp (fun t => f (s + t)) q (μI T) :=
  (hf.comp_measurePreserving (measurePreserving_add_left volume s)).restrict _

/-- Extension by zero: a signal in `Lᵖ(0, T)` gives `(Ioc 0 T).indicator f ∈ Lᵖ(ℝ)`. -/
theorem memLp_indicator_Ioc {f : ℝ → E} {q : ℝ≥0∞} {T : ℝ} (hf : MemLp f q (μI T)) :
    MemLp ((Ioc 0 T).indicator f) q volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).2 hf

/-- Change of variables `t ↦ s + t` in an integral over a window. -/
theorem setIntegral_comp_add [NormedSpace ℝ E] (f : ℝ → E) (s T : ℝ) :
    ∫ t in Ioc 0 T, f (s + t) = ∫ t in Ioc s (s + T), f t :=
  (measurePreserving_add_μI s T).integral_comp (measurableEmbedding_addLeft s) f

/-! ### Windows of a signal -/

open scoped Classical in
/-- The window of length `T` of the signal `f` at time `s`: the class of `t ↦ f (s + t)` in
`L²(0, T; E)`, the paper's `f(s + ·)` (by convention `0` when that function is not square
integrable on `(0, T)`). -/
def window (T : ℝ) (f : ℝ → E) (s : ℝ) : L2 E T :=
  if h : MemLp (fun t => f (s + t)) 2 (μI T) then h.toLp _ else 0

/-- The window is the class of the translate. -/
theorem window_eq_toLp {T s : ℝ} {f : ℝ → E} (h : MemLp (fun t => f (s + t)) 2 (μI T)) :
    window T f s = h.toLp _ := by
  simp only [window, h, dite_true]

/-- A representative of the window of a square-integrable translate. -/
theorem coeFn_window {T s : ℝ} {f : ℝ → E} (h : MemLp (fun t => f (s + t)) 2 (μI T)) :
    ⇑(window T f s) =ᵐ[μI T] fun t => f (s + t) := by
  rw [window_eq_toLp h]
  exact h.coeFn_toLp

/-- A representative of the window `(s, s + T) ⊆ (0, T₁)` of a signal in `L²(0, T₁)`. -/
theorem coeFn_window_of_memLp {T₁ T s : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T₁)) (hs : 0 ≤ s)
    (hsT : s + T ≤ T₁) : ⇑(window T f s) =ᵐ[μI T] fun t => f (s + t) :=
  coeFn_window (memLp_comp_add hf hs hsT)

/-- Windows of signals whose translates agree a.e. coincide. -/
theorem window_eq_of_ae {T s s' : ℝ} {f g : ℝ → E} (h : ∀ᵐ t ∂(μI T), f (s + t) = g (s' + t)) :
    window T f s = window T g s' := by
  by_cases hf : MemLp (fun t => f (s + t)) 2 (μI T)
  · have hg : MemLp (fun t => g (s' + t)) 2 (μI T) := hf.ae_eq h
    rw [window_eq_toLp hf, window_eq_toLp hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp (fun t => g (s' + t)) 2 (μI T) := fun hg => hf (hg.ae_eq (h.mono
      fun _ ht => ht.symm))
    simp only [window, hf, hg, dite_false]

/-- The window only depends on the values of the signal on it. -/
theorem window_congr {T s : ℝ} {f g : ℝ → E} (h : ∀ᵐ t ∂(μI T), f (s + t) = g (s + t)) :
    window T f s = window T g s :=
  window_eq_of_ae h

/-- Signals that agree a.e. on `(0, T₁)` have the same windows inside `(0, T₁)`. -/
theorem window_congr_ae {T₁ T s : ℝ} {f g : ℝ → E} (h : f =ᵐ[μI T₁] g) (hs : 0 ≤ s)
    (hsT : s + T ≤ T₁) : window T f s = window T g s :=
  window_congr (ae_comp_add h hs hsT)

/-- Signals that agree a.e. on `ℝ` have the same windows. -/
theorem window_congr_of_volume {f g : ℝ → E} (h : f =ᵐ[volume] g) (T s : ℝ) :
    window T f s = window T g s :=
  window_congr (ae_restrict_of_ae
    ((measurePreserving_add_left volume s).quasiMeasurePreserving.ae_eq_comp h))

/-- The window of a sum, for square-integrable translates. -/
theorem window_add_of_memLp [NormedSpace ℝ E] {T s : ℝ} {f g : ℝ → E}
    (hf : MemLp (fun t => f (s + t)) 2 (μI T)) (hg : MemLp (fun t => g (s + t)) 2 (μI T)) :
    window T (f + g) s = window T f s + window T g s := by
  rw [window_eq_toLp (f := f + g) (hf.add hg), window_eq_toLp hf, window_eq_toLp hg]
  exact MemLp.toLp_add hf hg

/-- The window of a scalar multiple. -/
theorem window_smul [NormedSpace ℝ E] (T : ℝ) (c : ℝ) (f : ℝ → E) (s : ℝ) :
    window T (c • f) s = c • window T f s := by
  by_cases hf : MemLp (fun t => f (s + t)) 2 (μI T)
  · rw [window_eq_toLp (f := c • f) (hf.const_smul c), window_eq_toLp hf]
    exact MemLp.toLp_const_smul c hf
  · rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul, zero_smul, window_eq_toLp (f := 0) (by exact MemLp.zero' (ε := E))]
      exact MemLp.toLp_zero _
    · have hcf : ¬ MemLp (fun t => (c • f) (s + t)) 2 (μI T) := by
        intro h
        apply hf
        have := h.const_smul c⁻¹
        convert this using 1
        funext t
        simp [smul_smul, inv_mul_cancel₀ hc]
      simp only [window, hf, hcf, dite_false, smul_zero]

/-- The window of the zero signal. -/
@[simp] theorem window_zero (T s : ℝ) : window T (0 : ℝ → E) s = 0 := by
  rw [window_eq_toLp (f := 0) (by exact MemLp.zero' (ε := E))]
  exact MemLp.toLp_zero _

/-- The norm of a window is bounded by the norm of the signal on any interval containing it. -/
theorem norm_window_le {T₁ T s : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T₁)) (hs : 0 ≤ s)
    (hsT : s + T ≤ T₁) : ‖window T f s‖ ≤ (eLpNorm f 2 (μI T₁)).toReal := by
  have hf' := memLp_comp_add hf hs hsT
  rw [window_eq_toLp hf', Lp.norm_toLp]
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
  have hmono : volume.restrict (Ioc s (s + T)) ≤ μI T₁ :=
    Measure.restrict_mono (Ioc_subset_Ioc hs hsT) le_rfl
  calc eLpNorm (fun t => f (s + t)) 2 (μI T)
      = eLpNorm f 2 (volume.restrict (Ioc s (s + T))) :=
        eLpNorm_comp_measurePreserving (hf.aestronglyMeasurable.mono_measure hmono)
          (measurePreserving_add_μI s T)
    _ ≤ eLpNorm f 2 (μI T₁) := eLpNorm_mono_measure _ hmono

/-- The norm of a window is bounded by the `L²(ℝ)` norm of the signal. -/
theorem norm_window_le_of_volume {f : ℝ → E} (hf : MemLp f 2 volume) (T s : ℝ) :
    ‖window T f s‖ ≤ (eLpNorm f 2 volume).toReal := by
  have hf' := memLp_comp_add_of_volume hf s T
  rw [window_eq_toLp hf', Lp.norm_toLp]
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
  calc eLpNorm (fun t => f (s + t)) 2 (μI T)
      ≤ eLpNorm (fun t => f (s + t)) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm f 2 volume :=
        eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_add_left _ s)

/-- The inner product with a window. -/
theorem inner_window [InnerProductSpace ℝ E] {T₁ T s : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T₁))
    (hs : 0 ≤ s) (hsT : s + T ≤ T₁) (g : L2 E T) :
    ⟪g, window T f s⟫_ℝ = ∫ t in Ioc 0 T, ⟪g t, f (s + t)⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_window_of_memLp hf hs hsT] with t ht
  rw [ht]

/-- A window of a window is a window. -/
theorem window_window [NormedSpace ℝ E] {T₂ T₁ T r r' : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T₂))
    (hr : 0 ≤ r) (hrT : r + T₁ ≤ T₂) (hr' : 0 ≤ r') (hr'T : r' + T ≤ T₁) :
    window T (⇑(window T₁ f r)) r' = window T f (r + r') := by
  refine window_eq_of_ae ?_
  filter_upwards [ae_comp_add (coeFn_window_of_memLp hf hr hrT) hr' hr'T] with t ht
  rw [ht, add_assoc]

/-! ### Continuity of translation in `L²` -/

/-- The window of a difference, for square-integrable translates. -/
theorem window_sub_of_memLp [NormedSpace ℝ E] {T s : ℝ} {f g : ℝ → E}
    (hf : MemLp (fun t => f (s + t)) 2 (μI T)) (hg : MemLp (fun t => g (s + t)) 2 (μI T)) :
    window T (f - g) s = window T f s - window T g s := by
  rw [window_eq_toLp (f := f - g) (hf.sub hg), window_eq_toLp hf, window_eq_toLp hg]
  exact MemLp.toLp_sub hf hg

/-- Continuity of translation for continuous compactly supported signals (uniform
continuity). -/
private theorem continuous_window_of_hasCompactSupport [NormedSpace ℝ E] {g : ℝ → E}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgm : MemLp g 2 volume) (T : ℝ) :
    Continuous (window T g) := by
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : L2 E T) (C : ℝ), 0 ≤ C →
      (∀ᵐ t ∂(μI T), ‖f t‖ ≤ C) → ‖f‖ ≤ K * C :=
    ⟨_, by positivity, fun f C hC hf => Lp.norm_le_of_ae_bound hC hf⟩
  have hu := hgc.uniformContinuous_of_continuous hg
  rw [Metric.uniformContinuous_iff] at hu
  rw [Metric.continuous_iff]
  intro s₀ ε hε
  obtain ⟨δ, hδ, hδε⟩ := hu (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hgs : ∀ s, MemLp (fun t => g (s + t)) 2 (μI T) := fun s => memLp_comp_add_of_volume hgm s T
  rw [dist_eq_norm, window_eq_toLp (hgs s), window_eq_toLp (hgs s₀)]
  have hb : ∀ᵐ t ∂(μI T),
      ‖((hgs s).toLp _ - (hgs s₀).toLp _ : L2 E T) t‖ ≤ ε / (K + 1) := by
    filter_upwards [Lp.coeFn_sub ((hgs s).toLp _) ((hgs s₀).toLp _), (hgs s).coeFn_toLp,
      (hgs s₀).coeFn_toLp] with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, ← dist_eq_norm]
    refine (hδε ?_).le
    rw [Real.dist_eq] at hs ⊢
    convert hs using 2
    ring
  calc _ ≤ K * (ε / (K + 1)) := hK _ _ (by positivity) hb
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-- **Continuity of translation in `L²`.**  For `f ∈ L²(ℝ; E)` the windows `s ↦ f (s + ·)`
depend continuously on `s` in `L²(0, T; E)` (used in `app:finite-horizon-output`). -/
theorem continuous_window [NormedSpace ℝ E] {f : ℝ → E} (hf : MemLp f 2 volume) (T : ℝ) :
    Continuous (window T f) := by
  rw [Metric.continuous_iff]
  intro s₀ ε hε
  obtain ⟨g, hgc, hfg, hg, hgm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (ε := ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hfg' : (eLpNorm (f - g) 2 volume).toReal ≤ ε / 3 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hfg
  have hd : ∀ s, dist (window T f s) (window T g s) ≤ ε / 3 := by
    intro s
    rw [dist_eq_norm, ← window_sub_of_memLp (memLp_comp_add_of_volume hf s T)
      (memLp_comp_add_of_volume hgm s T)]
    exact (norm_window_le_of_volume (hf.sub hgm) T s).trans hfg'
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1
    (continuous_window_of_hasCompactSupport hg hgc hgm T) s₀ (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have h1 := hd s
  have h2 := hd s₀
  rw [dist_comm] at h2
  have h3 := hδε s hs
  calc dist (window T f s) (window T f s₀)
      ≤ dist (window T f s) (window T g s) + dist (window T g s) (window T g s₀) +
          dist (window T g s₀) (window T f s₀) := dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- **Continuity of translation in `L²`**, on an interval: for `f ∈ L²(0, T + T'; E)` the
windows `s ↦ f (s + ·) ∈ L²(0, T; E)` depend continuously on `s ∈ [0, T']`. -/
theorem continuousOn_window [NormedSpace ℝ E] {T T' : ℝ} {f : ℝ → E}
    (hf : MemLp f 2 (μI (T + T'))) : ContinuousOn (window T f) (Icc 0 T') := by
  refine (continuous_window (memLp_indicator_Ioc hf) T).continuousOn.congr fun s hs => ?_
  refine window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [indicator_of_mem (show s + t ∈ Ioc 0 (T + T') from
    ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩)]

/-- The family of windows of `f ∈ L²(0, T + T')` is square integrable on `(0, T')` as an
`L²(0, T; E)`-valued function. -/
theorem memLp_window [NormedSpace ℝ E] {T T' : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI (T + T'))) :
    MemLp (window T f) 2 (μI T') := by
  have hc := (continuousOn_window hf).mono Ioc_subset_Icc_self
  refine MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Ioc)
    (eLpNorm f 2 (μI (T + T'))).toReal ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  exact norm_window_le hf hs.1.le (by linarith [hs.2])

/-! ### Synthesis out of `L²(0, T')` -/

section Synthesis

variable {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]

section Normed

variable [NormedSpace ℝ G] [NormedSpace ℝ H]

/-- For `g ∈ L²(0, T'; G)` and `φ ∈ L²(0, T')`, `φ • g` is integrable on `(0, T')`. -/
theorem integrable_smul_of_memLp {T' : ℝ} {g : ℝ → G} (hg : MemLp g 2 (μI T')) (φ : L2 ℝ T') :
    Integrable (fun s => φ s • g s) (μI T') :=
  memLp_one_iff_integrable.1 ((Lp.memLp φ).smul hg)

/-- Cauchy–Schwarz bound for the point synthesis. -/
theorem norm_integral_smul_le {T' : ℝ} {g : ℝ → G} (hg : MemLp g 2 (μI T')) (φ : L2 ℝ T') :
    ‖∫ s in Ioc 0 T', φ s • g s‖ ≤ (eLpNorm g 2 (μI T')).toReal * ‖φ‖ := by
  have hint := integrable_smul_of_memLp hg φ
  calc ‖∫ s in Ioc 0 T', φ s • g s‖ ≤ ∫ s in Ioc 0 T', ‖φ s • g s‖ :=
        norm_integral_le_integral_norm _
    _ = (eLpNorm (fun s => φ s • g s) 1 (μI T')).toReal := by
        rw [integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
    _ ≤ (eLpNorm φ 2 (μI T') * eLpNorm g 2 (μI T')).toReal := by
        refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top φ) hg.eLpNorm_ne_top) ?_
        exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable φ) hg.aestronglyMeasurable
    _ = (eLpNorm g 2 (μI T')).toReal * ‖φ‖ := by
        rw [ENNReal.toReal_mul, Lp.norm_def, mul_comm]

/-- The linear map underlying `pointSynth`. -/
def pointSynthₗ (T' : ℝ) (g : ℝ → G) (hg : MemLp g 2 (μI T')) : L2 ℝ T' →ₗ[ℝ] G where
  toFun φ := ∫ s in Ioc 0 T', φ s • g s
  map_add' φ ψ := by
    rw [← integral_add (integrable_smul_of_memLp hg φ) (integrable_smul_of_memLp hg ψ)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add φ ψ] with s hs
    rw [hs, Pi.add_apply, add_smul]
  map_smul' c φ := by
    rw [RingHom.id_apply, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c φ] with s hs
    rw [hs, Pi.smul_apply, smul_eq_mul, mul_smul]

open scoped Classical in
/-- **Point synthesis** `φ ↦ ∫₀^{T'} φ(s) g(s) ds`, a bounded operator `L²(0, T') → G` for
`g ∈ L²(0, T'; G)` (and `0` otherwise).  The state component of `𝒵` in
`def:window-informative`. -/
def pointSynth (T' : ℝ) (g : ℝ → G) : L2 ℝ T' →L[ℝ] G :=
  if hg : MemLp g 2 (μI T') then
    (pointSynthₗ T' g hg).mkContinuous (eLpNorm g 2 (μI T')).toReal
      (norm_integral_smul_le hg)
  else 0

/-- The point synthesis as a Bochner integral. -/
theorem pointSynth_apply {T' : ℝ} {g : ℝ → G} (hg : MemLp g 2 (μI T')) (φ : L2 ℝ T') :
    pointSynth T' g φ = ∫ s in Ioc 0 T', φ s • g s := by
  simp only [pointSynth, hg, dite_true]
  rfl

/-- The point synthesis only depends on the class of `g` in `L²(0, T'; G)`. -/
theorem pointSynth_congr_ae {T' : ℝ} {g g' : ℝ → G} (h : g =ᵐ[μI T'] g') :
    pointSynth T' g = pointSynth T' g' := by
  by_cases hg : MemLp g 2 (μI T')
  · have hg' : MemLp g' 2 (μI T') := hg.ae_eq h
    ext φ
    rw [pointSynth_apply hg, pointSynth_apply hg']
    refine integral_congr_ae ?_
    filter_upwards [h] with s hs
    rw [hs]
  · have hg' : ¬ MemLp g' 2 (μI T') := fun hg' => hg (hg'.ae_eq (h.mono fun _ hs => hs.symm))
    simp only [pointSynth, hg, hg', dite_false]

/-- A bounded operator passes through the point synthesis (the Bochner-integral step of
`eq:window-factorization`). -/
theorem comp_pointSynth [CompleteSpace G] [CompleteSpace H] {T' : ℝ} {g : ℝ → G}
    (hg : MemLp g 2 (μI T')) (L : G →L[ℝ] H) :
    L ∘L pointSynth T' g = pointSynth T' (fun s => L (g s)) := by
  have hLg : MemLp (fun s => L (g s)) 2 (μI T') := L.comp_memLp' hg
  ext φ
  rw [ContinuousLinearMap.comp_apply, pointSynth_apply hg, pointSynth_apply hLg,
    ← L.integral_comp_comm (integrable_smul_of_memLp hg φ)]
  simp only [ContinuousLinearMap.map_smul]

/-- **Shift synthesis** `φ ↦ ∫₀^{T'} φ(s) f(s + ·) ds ∈ L²(0, T; E)`: the input component of `𝒵`
in `def:window-informative` and both components of `𝒴` in `eq:io-window-synthesis`. -/
def shiftSynth [NormedSpace ℝ E] (T T' : ℝ) (f : ℝ → E) : L2 ℝ T' →L[ℝ] L2 E T :=
  pointSynth T' (window T f)

end Normed

/-- An element of `L²` vanishes iff a representative vanishes a.e. -/
private theorem Lp_eq_zero_iff_of_ae {μ : Measure ℝ} {a : Lp ℝ 2 μ} {F : ℝ → ℝ}
    (h : ⇑a =ᵐ[μ] F) : a = 0 ↔ ∀ᵐ s ∂μ, F s = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h0
    filter_upwards [h0, h] with s h1 h2
    simpa [h2] using h1
  · intro h0
    filter_upwards [h0, h] with s h1 h2
    simpa [h2] using h1

/-- A bounded operator between Hilbert spaces has dense range iff its adjoint is injective. -/
theorem denseRange_iff_adjoint_eq_zero {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] (A : V →L[ℝ] W) : DenseRange A ↔ ∀ w, (A†) w = 0 → w = 0 := by
  have : DenseRange A ↔ (LinearMap.range (A : V →ₗ[ℝ] W)).topologicalClosure = ⊤ := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range]
    rfl
  rw [this, Submodule.topologicalClosure_eq_top_iff, A.orthogonal_range, Submodule.eq_bot_iff]
  simp [LinearMap.mem_ker]

section Hilbert

variable [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The inner product with a point synthesis. -/
theorem inner_pointSynth {T' : ℝ} {g : ℝ → G} (hg : MemLp g 2 (μI T')) (φ : L2 ℝ T') (ξ : G) :
    ⟪ξ, pointSynth T' g φ⟫_ℝ = ∫ s in Ioc 0 T', φ s * ⟪ξ, g s⟫_ℝ := by
  rw [pointSynth_apply hg, ← integral_inner (integrable_smul_of_memLp hg φ)]
  simp only [real_inner_smul_right]

/-- The adjoint of the point synthesis is `ξ ↦ (s ↦ ⟪ξ, g s⟫)`. -/
theorem coeFn_adjoint_pointSynth {T' : ℝ} {g : ℝ → G} (hg : MemLp g 2 (μI T')) (ξ : G) :
    ⇑(((pointSynth T' g)†) ξ) =ᵐ[μI T'] fun s => ⟪ξ, g s⟫_ℝ := by
  have hm : MemLp (fun s => ⟪ξ, g s⟫_ℝ) 2 (μI T') := hg.const_inner ξ
  have : ((pointSynth T' g)†) ξ = hm.toLp _ := by
    refine ext_inner_left ℝ fun φ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm, inner_pointSynth hg,
      L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with s hs
    rw [hs]
    simp [mul_comm]
  rw [this]
  exact hm.coeFn_toLp

end Hilbert

section HilbertE

variable [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The adjoint of the shift synthesis is `g ↦ (s ↦ ∫₀ᵀ ⟪g t, f (s + t)⟫ dt)`. -/
theorem coeFn_adjoint_shiftSynth {T T' : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI (T + T')))
    (g : L2 E T) :
    ⇑(((shiftSynth T T' f)†) g) =ᵐ[μI T'] fun s => ∫ t in Ioc 0 T, ⟪g t, f (s + t)⟫_ℝ := by
  filter_upwards [coeFn_adjoint_pointSynth (memLp_window hf) g,
    ae_restrict_mem measurableSet_Ioc] with s h1 h2
  rw [shiftSynth, h1, inner_window hf h2.1.le (by linarith [h2.2])]

/-- Kernel of the adjoint of the shift synthesis. -/
theorem adjoint_shiftSynth_eq_zero_iff {T T' : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI (T + T')))
    (g : L2 E T) :
    ((shiftSynth T T' f)†) g = 0 ↔ ∀ᵐ s ∂(μI T'), ∫ t in Ioc 0 T, ⟪g t, f (s + t)⟫_ℝ = 0 :=
  Lp_eq_zero_iff_of_ae (coeFn_adjoint_shiftSynth hf g)

/-- The windows of `f` are total in `L²(0, T; E)` iff no nonzero `g` is orthogonal to almost
every window (`app:window-pe-necessity`). -/
theorem denseRange_shiftSynth_iff {T T' : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI (T + T'))) :
    DenseRange (shiftSynth T T' f) ↔
      ∀ g : L2 E T, (∀ᵐ s ∂(μI T'), ∫ t in Ioc 0 T, ⟪g t, f (s + t)⟫_ℝ = 0) → g = 0 := by
  rw [denseRange_iff_adjoint_eq_zero]
  exact forall_congr' fun g => by rw [adjoint_shiftSynth_eq_zero_iff hf g]

end HilbertE

end Synthesis

/-! ### The window synthesis operators `𝒵` and `𝒴` -/

section WindowSynth

variable {U X Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Window synthesis operator** `𝒵_{T,T'}^{ū,x̄} φ = ∫₀^{T'} φ(s) (ū(s + ·), x̄(s)) ds`
(`def:window-informative`), a bounded operator `L²(0, T') → L²(0, T; U) × X`.  It is meaningful
for `ū ∈ L²(0, T + T'; U)` and `x̄ ∈ L²(0, T'; X)`. -/
def windowSynth (T T' : ℝ) (u : ℝ → U) (x : ℝ → X) : L2 ℝ T' →L[ℝ] WithLp 2 (L2 U T × X) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (L2 U T) X).symm :
      (L2 U T × X) →L[ℝ] WithLp 2 (L2 U T × X)) ∘L
    (shiftSynth T T' u).prod (pointSynth T' x)

/-- **Input–output window synthesis operator**
`𝒴_{T,T'}^{ū,ȳ} φ = ∫₀^{T'} φ(s) (ū(s + ·), ȳ(s + ·)) ds` (`eq:io-window-synthesis`), a bounded
operator `L²(0, T') → L²(0, T; U) × L²(0, T; Y)`.  It is meaningful for `ū ∈ L²(0, T + T'; U)`
and `ȳ ∈ L²(0, T + T'; Y)`. -/
def ioWindowSynth (T T' : ℝ) (u : ℝ → U) (y : ℝ → Y) :
    L2 ℝ T' →L[ℝ] WithLp 2 (L2 U T × L2 Y T) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (L2 U T) (L2 Y T)).symm :
      (L2 U T × L2 Y T) →L[ℝ] WithLp 2 (L2 U T × L2 Y T)) ∘L
    (shiftSynth T T' u).prod (shiftSynth T T' y)

variable {T T' : ℝ} {u : ℝ → U} {x : ℝ → X} {y : ℝ → Y}

/-- A pair of square-integrable families is a square-integrable family in the `L²` product. -/
private theorem memLp_pair {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    {a : ℝ → V} {b : ℝ → W} (ha : MemLp a 2 (μI T')) (hb : MemLp b 2 (μI T')) :
    MemLp (fun s => WithLp.toLp 2 (a s, b s)) 2 (μI T') :=
  MemLp.of_fst_of_snd_prodLp ⟨ha, hb⟩

omit [CompleteSpace U] [CompleteSpace X] in
/-- `𝒵 φ` in components. -/
@[simp] theorem windowSynth_apply (φ : L2 ℝ T') :
    windowSynth T T' u x φ = WithLp.toLp 2 (shiftSynth T T' u φ, pointSynth T' x φ) :=
  rfl

omit [CompleteSpace U] [CompleteSpace X] in
/-- The input component of `𝒵 φ`. -/
@[simp] theorem fst_windowSynth (φ : L2 ℝ T') :
    (windowSynth T T' u x φ).fst = shiftSynth T T' u φ :=
  rfl

omit [CompleteSpace U] [CompleteSpace X] in
/-- The state component of `𝒵 φ`. -/
@[simp] theorem snd_windowSynth (φ : L2 ℝ T') :
    (windowSynth T T' u x φ).snd = pointSynth T' x φ :=
  rfl

omit [CompleteSpace U] [CompleteSpace Y] in
/-- `𝒴 φ` in components. -/
@[simp] theorem ioWindowSynth_apply (φ : L2 ℝ T') :
    ioWindowSynth T T' u y φ = WithLp.toLp 2 (shiftSynth T T' u φ, shiftSynth T T' y φ) :=
  rfl

omit [CompleteSpace U] [CompleteSpace Y] in
/-- The input component of `𝒴 φ`. -/
@[simp] theorem fst_ioWindowSynth (φ : L2 ℝ T') :
    (ioWindowSynth T T' u y φ).fst = shiftSynth T T' u φ :=
  rfl

omit [CompleteSpace U] [CompleteSpace Y] in
/-- The output component of `𝒴 φ`. -/
@[simp] theorem snd_ioWindowSynth (φ : L2 ℝ T') :
    (ioWindowSynth T T' u y φ).snd = shiftSynth T T' y φ :=
  rfl

/-- `𝒵` is the point synthesis of the family of windows `s ↦ (ū(s + ·), x̄(s))`. -/
theorem windowSynth_eq_pointSynth (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T')) :
    windowSynth T T' u x = pointSynth T' (fun s => WithLp.toLp 2 (window T u s, x s)) := by
  have hp := memLp_pair (memLp_window hu) hx
  ext φ : 1
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · change shiftSynth T T' u φ = WithLp.fstL 2 ℝ (L2 U T) X (pointSynth T' _ φ)
    rw [← ContinuousLinearMap.comp_apply, comp_pointSynth hp]
    rfl
  · change pointSynth T' x φ = WithLp.sndL 2 ℝ (L2 U T) X (pointSynth T' _ φ)
    rw [← ContinuousLinearMap.comp_apply, comp_pointSynth hp]
    rfl

/-- `𝒴` is the point synthesis of the family of windows `s ↦ (ū(s + ·), ȳ(s + ·))`. -/
theorem ioWindowSynth_eq_pointSynth (hu : MemLp u 2 (μI (T + T')))
    (hy : MemLp y 2 (μI (T + T'))) :
    ioWindowSynth T T' u y = pointSynth T' (fun s => WithLp.toLp 2 (window T u s, window T y s)) := by
  have hp := memLp_pair (memLp_window hu) (memLp_window hy)
  ext φ : 1
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
  · change shiftSynth T T' u φ = WithLp.fstL 2 ℝ (L2 U T) (L2 Y T) (pointSynth T' _ φ)
    rw [← ContinuousLinearMap.comp_apply, comp_pointSynth hp]
    rfl
  · change shiftSynth T T' y φ = WithLp.sndL 2 ℝ (L2 U T) (L2 Y T) (pointSynth T' _ φ)
    rw [← ContinuousLinearMap.comp_apply, comp_pointSynth hp]
    rfl

/-- `𝒵` as a Bochner integral in `L²(0, T; U) × X`, as written in `def:window-informative`. -/
theorem windowSynth_eq_integral (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T'))
    (φ : L2 ℝ T') :
    windowSynth T T' u x φ = ∫ s in Ioc 0 T', φ s • WithLp.toLp 2 (window T u s, x s) := by
  rw [windowSynth_eq_pointSynth hu hx, pointSynth_apply (memLp_pair (memLp_window hu) hx)]

/-- `𝒴` as a Bochner integral, as written in `eq:io-window-synthesis`. -/
theorem ioWindowSynth_eq_integral (hu : MemLp u 2 (μI (T + T')))
    (hy : MemLp y 2 (μI (T + T'))) (φ : L2 ℝ T') :
    ioWindowSynth T T' u y φ = ∫ s in Ioc 0 T', φ s • WithLp.toLp 2 (window T u s, window T y s) := by
  rw [ioWindowSynth_eq_pointSynth hu hy,
    pointSynth_apply (memLp_pair (memLp_window hu) (memLp_window hy))]

/-- The adjoint `𝒵†`: `(g, ξ) ↦ (s ↦ ∫₀ᵀ ⟪g t, ū (s + t)⟫ dt + ⟪ξ, x̄ s⟫)`. -/
theorem coeFn_adjoint_windowSynth (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T'))
    (p : WithLp 2 (L2 U T × X)) :
    ⇑(((windowSynth T T' u x)†) p) =ᵐ[μI T']
      fun s => (∫ t in Ioc 0 T, ⟪p.fst t, u (s + t)⟫_ℝ) + ⟪p.snd, x s⟫_ℝ := by
  rw [windowSynth_eq_pointSynth hu hx]
  filter_upwards [coeFn_adjoint_pointSynth (memLp_pair (memLp_window hu) hx) p,
    ae_restrict_mem measurableSet_Ioc] with s h1 h2
  rw [h1]
  simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    inner_window hu h2.1.le (by linarith [h2.2] : s + T ≤ T + T')]

/-- **Kernel of `𝒵†`**: `(g, ξ) ∈ ker 𝒵†` iff `∫₀ᵀ ⟪g t, ū (s + t)⟫ dt + ⟪ξ, x̄ s⟫ = 0` for a.e.
`s ∈ (0, T')` (`app:window-implies-informative`, `app:window-strictly-stronger`). -/
theorem adjoint_windowSynth_eq_zero_iff (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T'))
    (p : WithLp 2 (L2 U T × X)) :
    ((windowSynth T T' u x)†) p = 0 ↔
      ∀ᵐ s ∂(μI T'), (∫ t in Ioc 0 T, ⟪p.fst t, u (s + t)⟫_ℝ) + ⟪p.snd, x s⟫_ℝ = 0 :=
  Lp_eq_zero_iff_of_ae (coeFn_adjoint_windowSynth hu hx p)

/-- **Window informativity through the kernel of `𝒵†`**: `𝒵` has dense range iff only
`(g, ξ) = 0` satisfies `∫₀ᵀ ⟪g t, ū (s + t)⟫ dt + ⟪ξ, x̄ s⟫ = 0` for a.e. `s ∈ (0, T')`. -/
theorem denseRange_windowSynth_iff (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T')) :
    DenseRange (windowSynth T T' u x) ↔
      ∀ p : WithLp 2 (L2 U T × X),
        (∀ᵐ s ∂(μI T'), (∫ t in Ioc 0 T, ⟪p.fst t, u (s + t)⟫_ℝ) + ⟪p.snd, x s⟫_ℝ = 0) →
          p = 0 := by
  rw [denseRange_iff_adjoint_eq_zero]
  exact forall_congr' fun p => by rw [adjoint_windowSynth_eq_zero_iff hu hx p]

omit [CompleteSpace U] [CompleteSpace X] in
/-- Projecting onto the input component: if `𝒵` has dense range, the input windows are total in
`L²(0, T; U)` (`app:window-pe-necessity`). -/
theorem denseRange_shiftSynth_of_windowSynth (h : DenseRange (windowSynth T T' u x)) :
    DenseRange (shiftSynth T T' u) := by
  have : ⇑(shiftSynth T T' u) = WithLp.fstL 2 ℝ (L2 U T) X ∘ windowSynth T T' u x := by
    funext φ
    rfl
  rw [this]
  exact (Function.Surjective.denseRange fun a => ⟨WithLp.toLp 2 (a, 0), rfl⟩).comp h
    (WithLp.fstL 2 ℝ (L2 U T) X).continuous

/-- **Factorisation `𝒴 = 𝓜 𝒵`** (`eq:window-factorization`): if a bounded operator `𝓜` maps
almost every state window `(ū(s + ·), x̄(s))` to the input–output window
`(ū(s + ·), ȳ(s + ·))`, then `𝒴 = 𝓜 ∘ 𝒵`. -/
theorem ioWindowSynth_eq_comp_windowSynth
    (M : WithLp 2 (L2 U T × X) →L[ℝ] WithLp 2 (L2 U T × L2 Y T))
    (hu : MemLp u 2 (μI (T + T'))) (hx : MemLp x 2 (μI T')) (hy : MemLp y 2 (μI (T + T')))
    (hM : ∀ᵐ s ∂(μI T'),
      WithLp.toLp 2 (window T u s, window T y s) = M (WithLp.toLp 2 (window T u s, x s))) :
    ioWindowSynth T T' u y = M ∘L windowSynth T T' u x := by
  rw [ioWindowSynth_eq_pointSynth hu hy, windowSynth_eq_pointSynth hu hx,
    comp_pointSynth (memLp_pair (memLp_window hu) hx) M]
  exact pointSynth_congr_ae hM

end WindowSynth

/-! ### Restriction, tail, extension and concatenation on `L²` -/

section Operators

variable [NormedSpace ℝ E]

/-- The linear map underlying `windowL`. -/
def windowₗ (T₁ T r : ℝ) : L2 E T₁ →ₗ[ℝ] L2 E T where
  toFun f := window T ((Ioc 0 T₁).indicator ⇑f) r
  map_add' f g := by
    have h : (Ioc 0 T₁).indicator ⇑(f + g) =ᵐ[volume]
        (Ioc 0 T₁).indicator ⇑f + (Ioc 0 T₁).indicator ⇑g := by
      filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).1
        (Lp.coeFn_add f g)] with t ht
      rw [ht]
      by_cases hm : t ∈ Ioc 0 T₁ <;> simp [hm]
    rw [window_congr_of_volume h T r,
      window_add_of_memLp (memLp_comp_add_of_volume (memLp_indicator_Ioc (Lp.memLp f)) r T)
        (memLp_comp_add_of_volume (memLp_indicator_Ioc (Lp.memLp g)) r T)]
  map_smul' c f := by
    have h : (Ioc 0 T₁).indicator ⇑(c • f) =ᵐ[volume] c • (Ioc 0 T₁).indicator ⇑f := by
      filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).1
        (Lp.coeFn_smul c f)] with t ht
      rw [ht]
      by_cases hm : t ∈ Ioc 0 T₁ <;> simp [hm]
    rw [RingHom.id_apply, window_congr_of_volume h T r, window_smul]

/-- Bound for `windowₗ`. -/
theorem norm_windowₗ_le (T₁ T r : ℝ) (f : L2 E T₁) : ‖windowₗ T₁ T r f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  change ‖window T ((Ioc 0 T₁).indicator ⇑f) r‖ ≤ ‖f‖
  refine (norm_window_le_of_volume (memLp_indicator_Ioc (Lp.memLp f)) T r).trans_eq ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet, Lp.norm_def]

/-- **Sub-window operator** `L²(0, T₁; E) → L²(0, T; E)`, `f ↦ f (r + ·)`, where `f` is extended
by zero outside `(0, T₁)`.  For `0 ≤ r` and `r + T ≤ T₁` it is the window `(r, r + T)` of `f`;
for `r < 0` it is a zero extension (see `extendL`). -/
def windowL (T₁ T r : ℝ) : L2 E T₁ →L[ℝ] L2 E T :=
  (windowₗ T₁ T r).mkContinuous 1 (norm_windowₗ_le T₁ T r)

variable {T₁ T₀ T r : ℝ}

/-- `windowL` is the window of the zero extension. -/
theorem windowL_apply_eq (f : L2 E T₁) :
    windowL T₁ T r f = window T ((Ioc 0 T₁).indicator ⇑f) r :=
  rfl

/-- A representative of `windowL`. -/
theorem coeFn_windowL (f : L2 E T₁) :
    ⇑(windowL T₁ T r f) =ᵐ[μI T] fun t => (Ioc 0 T₁).indicator (⇑f) (r + t) := by
  rw [windowL_apply_eq]
  exact coeFn_window (memLp_comp_add_of_volume (memLp_indicator_Ioc (Lp.memLp f)) r T)

/-- A representative of `windowL` for a window `(r, r + T) ⊆ (0, T₁)`. -/
theorem coeFn_windowL_of_le (hr : 0 ≤ r) (hrT : r + T ≤ T₁) (f : L2 E T₁) :
    ⇑(windowL T₁ T r f) =ᵐ[μI T] fun t => f (r + t) := by
  filter_upwards [coeFn_windowL (T := T) (r := r) f, ae_restrict_mem measurableSet_Ioc]
    with t h1 h2
  rw [h1, indicator_of_mem (show r + t ∈ Ioc 0 T₁ from
    ⟨by linarith [h2.1], by linarith [h2.2]⟩)]

/-- For a window `(r, r + T) ⊆ (0, T₁)`, `windowL` is `window`. -/
theorem windowL_apply (hr : 0 ≤ r) (hrT : r + T ≤ T₁) (f : L2 E T₁) :
    windowL T₁ T r f = window T (⇑f) r := by
  rw [windowL_apply_eq]
  refine window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [indicator_of_mem (show r + t ∈ Ioc 0 T₁ from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]

/-- `windowL` is a contraction. -/
theorem norm_windowL_le (T₁ T r : ℝ) : ‖windowL (E := E) T₁ T r‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The full window is the identity. -/
@[simp] theorem windowL_self (T : ℝ) : windowL (E := E) T T 0 = ContinuousLinearMap.id ℝ _ := by
  ext f : 1
  rw [ContinuousLinearMap.id_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_windowL_of_le le_rfl (zero_add T).le f] with t ht
  rw [ht, zero_add]

/-- Composition of sub-windows. -/
theorem windowL_windowL {T₂ r' : ℝ} (hr' : 0 ≤ r') (hr'T : r' + T ≤ T₁) (f : L2 E T₂) :
    windowL T₁ T r' (windowL T₂ T₁ r f) = windowL T₂ T (r + r') f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_windowL_of_le hr' hr'T (windowL T₂ T₁ r f),
    ae_comp_add (coeFn_windowL (T := T₁) (r := r) f) hr' hr'T,
    coeFn_windowL (T := T) (r := r + r') f] with t h1 h2 h3
  rw [h1, h2, h3, add_assoc]

/-- The windows `r ↦ f (r + ·)` of `f ∈ L²(0, T₁)` depend continuously on `r`. -/
theorem continuous_windowL (T₁ T : ℝ) (f : L2 E T₁) : Continuous fun r => windowL T₁ T r f :=
  (continuous_window (memLp_indicator_Ioc (Lp.memLp f)) T).congr fun _ =>
    (windowL_apply_eq f).symm

/-- Restriction `L²(0, T₁; E) → L²(0, T₀; E)` to the head `(0, T₀)` (zero extension if
`T₁ < T₀`). -/
def restrictL (T₁ T₀ : ℝ) : L2 E T₁ →L[ℝ] L2 E T₀ := windowL T₁ T₀ 0

/-- The tail `(T₀, T₀ + T)` of a signal on `(0, T₀ + T)`, shifted back to `(0, T)`: the paper's
`v (T₀ + ·)` in `app:lqr-data-io`. -/
def tailL (T₀ T : ℝ) : L2 E (T₀ + T) →L[ℝ] L2 E T := windowL (T₀ + T) T T₀

/-- Zero extension `L²(0, T; E) → L²(0, T₁; E)` placing the signal on `(r, r + T)`:
`v ↦ v (· - r)`, zero elsewhere. -/
def extendL (T₁ T r : ℝ) : L2 E T →L[ℝ] L2 E T₁ := windowL T T₁ (-r)

/-- Concatenation of `u ∈ L²(0, T₀)` and `v ∈ L²(0, T)` into `L²(0, T₀ + T)`: `u` on `(0, T₀)`,
`v (· - T₀)` on `(T₀, T₀ + T)` (`app:lqr-data-io`). -/
def concat (T₀ T : ℝ) (u : L2 E T₀) (v : L2 E T) : L2 E (T₀ + T) :=
  extendL (T₀ + T) T₀ 0 u + extendL (T₀ + T) T T₀ v

/-- A representative of the restriction. -/
theorem coeFn_restrictL (h : T₀ ≤ T₁) (f : L2 E T₁) : ⇑(restrictL T₁ T₀ f) =ᵐ[μI T₀] ⇑f := by
  filter_upwards [coeFn_windowL_of_le le_rfl (by rwa [zero_add]) f] with t ht
  exact ht.trans (by rw [zero_add])

/-- A representative of the tail. -/
theorem coeFn_tailL (h₀ : 0 ≤ T₀) (f : L2 E (T₀ + T)) :
    ⇑(tailL T₀ T f) =ᵐ[μI T] fun t => f (T₀ + t) :=
  coeFn_windowL_of_le h₀ le_rfl f

/-- A representative of the zero extension. -/
theorem coeFn_extendL (v : L2 E T) :
    ⇑(extendL T₁ T r v) =ᵐ[μI T₁] fun t => (Ioc 0 T).indicator (⇑v) (t - r) := by
  filter_upwards [coeFn_windowL (T := T₁) (r := -r) v] with t ht
  exact ht.trans (by rw [neg_add_eq_sub])

/-- Windowing undoes the zero extension. -/
theorem windowL_extendL (hr : 0 ≤ r) (hrT : r + T ≤ T₁) (v : L2 E T) :
    windowL T₁ T r (extendL T₁ T r v) = v := by
  change windowL T₁ T r (windowL T T₁ (-r) v) = v
  rw [windowL_windowL hr hrT, neg_add_cancel, windowL_self, ContinuousLinearMap.id_apply]

/-- A sub-window lying outside `(0, T₁)` vanishes. -/
theorem windowL_eq_zero (h : ∀ t ∈ Ioc 0 T, r + t ∉ Ioc 0 T₁) (f : L2 E T₁) :
    windowL T₁ T r f = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_windowL (T := T) (r := r) f, Lp.coeFn_zero E 2 (μI T),
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3
  rw [h1, h2, indicator_of_notMem (h t h3)]
  rfl

/-- A representative of the concatenation. -/
theorem coeFn_concat (u : L2 E T₀) (v : L2 E T) :
    ⇑(concat T₀ T u v) =ᵐ[μI (T₀ + T)] fun t => if t ≤ T₀ then u t else v (t - T₀) := by
  filter_upwards [Lp.coeFn_add (extendL (T₀ + T) T₀ 0 u) (extendL (T₀ + T) T T₀ v),
    coeFn_extendL (T₁ := T₀ + T) (r := 0) u, coeFn_extendL (T₁ := T₀ + T) (r := T₀) v,
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 h4
  rw [concat, h1, Pi.add_apply, h2, h3, sub_zero]
  split_ifs with ht
  · rw [indicator_of_mem (show t ∈ Ioc 0 T₀ from ⟨h4.1, ht⟩),
      indicator_of_notMem (show t - T₀ ∉ Ioc 0 T from fun h => by linarith [h.1]), add_zero]
  · rw [indicator_of_notMem (show t ∉ Ioc 0 T₀ from fun h => ht h.2),
      indicator_of_mem (show t - T₀ ∈ Ioc 0 T from ⟨by linarith, by linarith [h4.2]⟩),
      zero_add]

/-- The head of a concatenation. -/
@[simp] theorem restrictL_concat (h : 0 ≤ T) (u : L2 E T₀) (v : L2 E T) :
    restrictL (T₀ + T) T₀ (concat T₀ T u v) = u := by
  change windowL (T₀ + T) T₀ 0 (extendL (T₀ + T) T₀ 0 u + extendL (T₀ + T) T T₀ v) = u
  have h0 : windowL (T₀ + T) T₀ 0 (extendL (T₀ + T) T T₀ v) = 0 := by
    change windowL (T₀ + T) T₀ 0 (windowL T (T₀ + T) (-T₀) v) = 0
    rw [windowL_windowL le_rfl (by linarith)]
    exact windowL_eq_zero (fun t ht h' => by linarith [h'.1, ht.2]) v
  rw [map_add, windowL_extendL le_rfl (by linarith), h0, add_zero]

/-- The tail of a concatenation. -/
@[simp] theorem tailL_concat (h₀ : 0 ≤ T₀) (u : L2 E T₀) (v : L2 E T) :
    tailL T₀ T (concat T₀ T u v) = v := by
  change windowL (T₀ + T) T T₀ (extendL (T₀ + T) T₀ 0 u + extendL (T₀ + T) T T₀ v) = v
  have h0 : windowL (T₀ + T) T T₀ (extendL (T₀ + T) T₀ 0 u) = 0 := by
    change windowL (T₀ + T) T T₀ (windowL T₀ (T₀ + T) (-0) u) = 0
    rw [windowL_windowL h₀ le_rfl]
    exact windowL_eq_zero (fun t ht h' => by linarith [h'.2, ht.1]) u
  rw [map_add, windowL_extendL h₀ le_rfl, h0, zero_add]

/-- A signal on `(0, T₀ + T)` is the concatenation of its head and its tail. -/
@[simp] theorem concat_restrictL_tailL (h₀ : 0 ≤ T₀) (h : 0 ≤ T) (w : L2 E (T₀ + T)) :
    concat T₀ T (restrictL (T₀ + T) T₀ w) (tailL T₀ T w) = w := by
  refine Lp.ext ?_
  have hr : ∀ᵐ t ∂(μI (T₀ + T)), t ≤ T₀ → restrictL (T₀ + T) T₀ w t = w t := by
    have h1 := coeFn_restrictL (by linarith : T₀ ≤ T₀ + T) w
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h1
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1] with t ht ht' htT
    exact ht ⟨ht'.1, htT⟩
  have htl : ∀ᵐ t ∂(μI (T₀ + T)), T₀ < t → tailL T₀ T w (t - T₀) = w t := by
    have h1 := coeFn_tailL h₀ w
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h1
    have h2 := (measurePreserving_sub_right volume T₀).quasiMeasurePreserving.ae h1
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h2] with t ht ht' htT
    have := ht ⟨by linarith, by linarith [ht'.2]⟩
    rwa [show T₀ + (t - T₀) = t by ring] at this
  filter_upwards [coeFn_concat (restrictL (T₀ + T) T₀ w) (tailL T₀ T w), hr, htl]
    with t h1 h2 h3
  rw [h1]
  split_ifs with ht
  · exact h2 ht
  · exact h3 (not_le.1 ht)

section Hilbert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The adjoint of a sub-window is the zero extension. -/
theorem adjoint_windowL (T₁ T r : ℝ) : ((windowL (E := F) T₁ T r)†) = extendL T₁ T r := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v f
  rw [L2.inner_def, L2.inner_def]
  calc ∫ τ, ⟪(extendL T₁ T r v) τ, f τ⟫_ℝ ∂(μI T₁)
      = ∫ τ in Ioc 0 T₁,
          ⟪(Ioc 0 T).indicator (⇑v) (τ - r), (Ioc 0 T₁).indicator (⇑f) τ⟫_ℝ := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_extendL (T₁ := T₁) (r := r) v, ae_restrict_mem measurableSet_Ioc]
          with τ h1 h2
        rw [h1, indicator_of_mem h2]
    _ = ∫ τ, ⟪(Ioc 0 T).indicator (⇑v) (τ - r), (Ioc 0 T₁).indicator (⇑f) τ⟫_ℝ := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_
        rw [indicator_of_notMem hτ, inner_zero_right]
    _ = ∫ t, ⟪(Ioc 0 T).indicator (⇑v) t, (Ioc 0 T₁).indicator (⇑f) (r + t)⟫_ℝ := by
        conv_lhs => rw [← integral_add_left_eq_self _ r]
        simp only [add_sub_cancel_left]
    _ = ∫ t in Ioc 0 T, ⟪(Ioc 0 T).indicator (⇑v) t, (Ioc 0 T₁).indicator (⇑f) (r + t)⟫_ℝ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
        rw [indicator_of_notMem ht, inner_zero_left]
    _ = ∫ t, ⟪v t, (windowL T₁ T r f) t⟫_ℝ ∂(μI T) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_windowL (T := T) (r := r) f, ae_restrict_mem measurableSet_Ioc]
          with t h1 h2
        rw [h1, indicator_of_mem h2]

end Hilbert

end Operators

end DataDrivenControl
