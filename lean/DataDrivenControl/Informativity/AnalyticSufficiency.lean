module

public import DataDrivenControl.Informativity.Analytic.Bohr
public import DataDrivenControl.Informativity.Harmonic
public import DataDrivenControl.Informativity.Window
public import DataDrivenControl.System.ControlRealization
public import DataDrivenControl.Semigroup.Analytic
public import DataDrivenControl.Analysis.Laplace

/-!
# Universal sufficiency for analytic semigroups

The intermediate results are in `Informativity/Analytic/Transfer`,
`Informativity/Analytic/Expansion` and `Informativity/Analytic/Bohr`.

Paper: `thm:analytic-universal-sufficiency`, `eq:analytic-growth-bound`
(`app:analytic-universal-sufficiency`).

## Setting

`U`, `X` separable real Hilbert spaces; `A` generates an analytic C₀-semigroup on `X`
(`sys.SX.IsAnalytic`, `Semigroup/Analytic`); `hyp:H1` and `hyp:compat` hold.  `h` is a
harmonically persistently exciting signal (`HarmonicSignal.IsHarmonicPE`) with frequencies
`ωₗ = h.freq l`; `T' > 0`, `σ ∈ ℝ` with `σ + i {ωₗ}‾ ⊆ ρ(A)` (`ρ(A)` is
`resolventSet sys.A.complexify`, the resolvent set of the complexified generator) and the growth
bound **`eq:analytic-growth-bound`** `‖S(t)‖_{L(X)} ≤ M e^{σ t}`, `t ≥ 0` (the paper's `M ≥ 1`
is automatic at `t = 0` for `X ≠ 0`, so it is not assumed).  The input is
`ū(t) = e^{σ t} h(t)`, applied on `[0, T + T']`; the state from `x₀ ∈ X` is `sys.mild x₀ ū`,
from `x₀ ∈ W` it is `sys.mildW x₀ ū` (in `W`).

## Main declarations

* `informative_of_approxControllable_harmonic`: (i) ⇒ (ii), the record is informative in
  `U × W` on `I = (0, T)` for every `x₀ ∈ W`;
* `windowInformative_of_approxControllable_harmonic`: (i) ⇒ (iii), the record is window
  informative (`WindowInformative T T'`) for every `x₀ ∈ X`;
* `approxControllable_of_informative_zero`, `approxControllable_of_windowInformative_zero`: the
  "moreover" clause, (ii) or (iii) at the single state `x₀ = 0` ⇒ (i);
* `analytic_universal_sufficiency` (`thm:analytic-universal-sufficiency`): (i), (ii), (iii) are
  equivalent (`List.TFAE`).

## Deviation (strengthening)

The two converse implications are stated for an arbitrary input `u ∈ L²(0, T + T'; U)`
(`L²(0, T; U)` for (ii)), not only the harmonic one; the paper's proof does not use the form of
the input there.  They need neither the harmonic signal, nor the growth bound, nor `σ`.

## Proofs

* (i) ⇒ (ii) (`app:analytic-universal-sufficiency`): an annihilator `(a, b) ∈ U × W` is
  complexified to `(α, η)`; `annihilator_expansion` and `lem:bohr-annihilator` on `W`
  (`bohr_annihilator`, with `analyticOnNhd_SW`, `exists_growth_W`) give `dₗ = 0`.  The functional
  `Φ(s) = ⟨α, ·⟩ + ⟨η, 𝐇(s) ·⟩ ∈ L(U_ℂ, ℂ)` is holomorphic on `Ω_⋆` and `Φ(sₗ) vₗ = dₗ = 0`, so
  `Φ ≡ 0` on `Ω_⋆` by the identity theorem along `σ + i ω_{j,k} → σ + i νⱼ` and totality of
  `(φⱼ)` (`AnalyticSufficiency.eqOn_zero_of_isHarmonicPE`).  The decay `‖𝐇(r)‖ = O(r^{-1/2})`
  gives `⟨α, α⟩ = 0`; then `⟨η, 𝐇(s) ·⟩ = 0` on `Re s > σ`, `lem:transfer-laplace`
  (`psiC_eq_zero_of_inner_transfer_eq_zero`) gives `η ⊥ im L_T`, and `im L_T` is dense in `W`
  (`denseRange_Lop_W`).
* (i) ⇒ (iii): the same with `window_expansion` and `bohr_annihilator` on `X`, for
  `Φ(s) = ∫₀ᵀ e^{s t} ⟨g(t), ·⟩ dt + ⟨ιW† ξ, 𝐇(s) ·⟩` (the first term is the Laplace transform of
  `1_{(0,T]} g` at `-s`, hence entire).  For real `x > σ`, `Φ(x) φⱼ = 0` is the vanishing of
  `∫_{-T}^∞ e^{-x r} pⱼ(r) dr`, `pⱼ(r) = ⟨g(-r), φⱼ⟩` on `(-T, 0]` and `⟨ψ_ξ(r), φⱼ⟩` on
  `(0, ∞)` (`inner_transfer_eq_laplace`); uniqueness of the Laplace transform on `(-T, ∞)`
  (`ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero`) and the reflection `r ↦ -r` give
  `⟨g(t), φⱼ⟩ = 0` a.e. on `(0, T)`, so `g = 0` (`J` is countable).  Then `⟨ξ, 𝐇(s) ·⟩ = 0` on
  `Re s > σ`, and `lem:transfer-laplace` and approximate controllability give `ξ = 0`.
* (ii) at `x₀ = 0` ⇒ (i): if `η ⊥ im L_T` in `X`, then `(0, ιW† η)` annihilates the zero-state
  record on `(0, T]`, because `L_t u = L_T u_t` with `u_t` the input translated to the end of
  `(0, T)` (`L_eq_Lop_windowL`); so `ιW† η = 0`, and `η = 0` since `W` is dense in `X`.  No
  analyticity is used (the paper goes through `ψ_η`).
* (iii) at `x₀ = 0` ⇒ (i): `ψ_η`, `η = ιW† β`, vanishes a.e. on `(0, T)` (test `η ⊥ im L_T` with
  `v(r) = ψ_η(T - r)`, `inner_L_eq_integral_psi`), hence on `(0, ∞)` by analyticity
  (`analyticOnNhd_psi`), so `⟨β, x̄(s)⟩ = ∫₀ˢ ⟨ψ_η(s - r), u(r)⟩ dr = 0` for every `s` and
  `(0, β)` lies in the kernel of `𝒵†`.

## Upstream statements the proofs need

All of `Informativity/Analytic/{Transfer,Expansion,Bohr}`; `informative_iff`
(`Informativity/Informative`); `windowInformative_iff` (`Informativity/Window`);
`ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero`, `hasDerivAt_laplace`
(`Analysis/Laplace`); `eqOn_zero_of_ae_Ioo` (`Analysis/ExpSums`); `exists_growth_W`,
`IsAnalytic.analyticOnNhd` (`Semigroup/Analytic`); `System.approxControllable_iff`
(`System/Controllability`); `System.L_eq_Lop_windowL`, `System.memLp_mild` (`System/Mild`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

open Complexification

namespace AnalyticSufficiency

/-- A vector orthogonal to the range of a dense-range operator vanishes. -/
theorem eq_zero_of_inner_eq_zero_of_denseRange {E F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : E → F} (hf : DenseRange f) {y : F}
    (h : ∀ x, ⟪y, f x⟫_ℝ = 0) : y = 0 := by
  have hc : IsClosed {z : F | ⟪y, z⟫_ℝ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall : ∀ z, ⟪y, z⟫_ℝ = 0 := fun z =>
    hc.closure_subset_iff.2 (by rintro _ ⟨x, rfl⟩; exact h x) (hf z)
  exact inner_self_eq_zero.1 (hall y)

/-- A bounded linear map vanishing on a total family vanishes. -/
theorem clm_eq_zero_of_total {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {J : Type*} {φ : J → E}
    (hφ : (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤) (ℓ : E →L[ℂ] F)
    (h : ∀ j, ℓ (φ j) = 0) : ℓ = 0 := by
  have hle : Submodule.span ℂ (Set.range φ) ≤ (ℓ : E →ₗ[ℂ] F).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  have hcl := Submodule.topologicalClosure_minimal _ hle ℓ.isClosed_ker
  rw [hφ, top_le_iff] at hcl
  ext v
  have hv : v ∈ (ℓ : E →ₗ[ℂ] F).ker := hcl ▸ Submodule.mem_top
  simpa using hv

/-- `⟨x, T_ℂ w⟩ = ⟨T† x, w⟩` for real `x`. -/
theorem pairing_ofReal_complexify {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (x : F) (w : Complexification E) :
    ⟪(x : Complexification F), T.complexify w⟫_bil =
      ⟪((ContinuousLinearMap.adjoint T x : E) : Complexification E), w⟫_bil := by
  rw [pairing_comm, ContinuousLinearMap.pairing_complexify_left,
    ContinuousLinearMap.complexify_ofReal, pairing_comm]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- **The identity-theorem step** of the proof of `thm:analytic-universal-sufficiency`: let
`Φ(s) ∈ L(U_ℂ, ℂ)` depend holomorphically on `s` in an open preconnected `Ω` containing
`σ + i {ωₗ}‾`, and let `Φ(sₗ) vₗ = 0` for every `ℓ`.  If the harmonic signal is harmonically
persistently exciting (data `φ`, `ℓ`, `a`, `ν` of `def:harmonic-pe`), then `Φ ≡ 0` on `Ω`:
`s ↦ Φ(s) φⱼ` vanishes at `σ + i ω_{j,k} → σ + i νⱼ ∈ Ω`, and `(φⱼ)` is total. -/
theorem eqOn_zero_of_isHarmonicPE {h : HarmonicSignal U} (hh : h.IsHarmonicPE) {σ : ℝ}
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hK : ∀ ω ∈ closure (Set.range h.freq), (σ : ℂ) + ω * Complex.I ∈ Ω)
    (Φ : ℂ → Complexification U →L[ℂ] ℂ) (hΦ : ∀ v, DifferentiableOn ℂ (fun s => Φ s v) Ω)
    (h0 : ∀ l, Φ ((σ : ℂ) + h.freq l * Complex.I) (h.coeff l) = 0) :
    ∀ s ∈ Ω, Φ s = 0 := by
  obtain ⟨J, -, φ, hφ, hj⟩ := hh
  intro s hs
  refine clm_eq_zero_of_total hφ (Φ s) fun j => ?_
  obtain ⟨ℓ, a, ν, hℓ, ha, hcoeff, hlim⟩ := hj j
  set z : ℕ → ℂ := fun k => (σ : ℂ) + h.freq (ℓ k) * Complex.I with hz_def
  set z₀ : ℂ := (σ : ℂ) + ν * Complex.I with hz₀_def
  have hν : ν ∈ closure (Set.range h.freq) :=
    mem_closure_of_tendsto hlim (Eventually.of_forall fun k => Set.mem_range_self _)
  have hz : Tendsto z atTop (𝓝 z₀) :=
    (((Complex.continuous_ofReal.tendsto ν).comp hlim).mul_const Complex.I).const_add _
  have hzinj : Function.Injective z := by
    intro k k' hk
    simp only [hz_def, add_right_inj] at hk
    exact hℓ (h.freq_injective (Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hk)))
  have hne : ∀ᶠ k in atTop, z k ∈ ({z₀}ᶜ : Set ℂ) := by
    by_cases hex : ∃ k₀, z k₀ = z₀
    · obtain ⟨k₀, hk₀⟩ := hex
      filter_upwards [eventually_ne_atTop k₀] with k hk heq
      exact hk (hzinj ((mem_singleton_iff.1 heq).trans hk₀.symm))
    · push Not at hex
      exact Eventually.of_forall fun k heq => hex k (mem_singleton_iff.1 heq)
  have hzero : ∀ k, Φ (z k) (φ j) = 0 := by
    intro k
    have := h0 (ℓ k)
    rw [hcoeff k, map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left (ha k)
  have hfreq : ∃ᶠ w in 𝓝[≠] z₀, Φ w (φ j) = 0 :=
    (tendsto_nhdsWithin_iff.2 ⟨hz, hne⟩).frequently (Frequently.of_forall hzero)
  have han : AnalyticOnNhd ℂ (fun w => Φ w (φ j)) Ω := (hΦ (φ j)).analyticOnNhd hΩo
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩc (hK ν hν) hfreq hs

/-- `ū(t) = e^{σ t} h(t)` is square integrable on every window. -/
theorem memLp_harmonic_input (σ : ℝ) (h : HarmonicSignal U) (τ : ℝ) :
    MemLp (fun t => Real.exp (σ * t) • h t) 2 (μI τ) := by
  have hcont : Continuous fun t => Real.exp (σ * t) • h t :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul h.continuous
  refine MemLp.of_bound hcont.aestronglyMeasurable
    (Real.exp (|σ| * τ) * ∑' l, ‖h.coeff l‖) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (Real.exp_le_exp.2 ?_) (h.norm_apply_le t) (norm_nonneg _)
    (Real.exp_pos _).le
  have h1 : σ * t ≤ |σ| * t := mul_le_mul_of_nonneg_right (le_abs_self σ) ht.1.le
  have h2 : |σ| * t ≤ |σ| * τ := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg σ)
  linarith

/-- The reflection `r ↦ c - r` maps `(0, c]` onto `[0, c)`, measure preservingly. -/
theorem measurePreserving_const_sub_Ioc (c : ℝ) :
    MeasurePreserving (fun r => c - r) (volume.restrict (Ioc 0 c))
      (volume.restrict (Ico 0 c)) := by
  have := (volume.measurePreserving_sub_left c).restrict_preimage
    (measurableSet_Ico (a := (0 : ℝ)) (b := c))
  rwa [preimage_const_sub_Ico, sub_self, sub_zero] at this

/-- The reflection `r ↦ c - r` maps `[0, c)` onto `(0, c]`, measure preservingly. -/
theorem measurePreserving_const_sub_Ico (c : ℝ) :
    MeasurePreserving (fun r => c - r) (volume.restrict (Ico 0 c))
      (volume.restrict (Ioc 0 c)) := by
  have := (volume.measurePreserving_sub_left c).restrict_preimage
    (measurableSet_Ioc (a := (0 : ℝ)) (b := c))
  rwa [preimage_const_sub_Ioc, sub_self, sub_zero] at this

/-- `t ↦ e^{y t} f(t)` is integrable on `(0, T]` with `f`. -/
theorem integrable_cexp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℝ → E}
    {T : ℝ} (hf : Integrable f (μI T)) (y : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (y * t) • f t) (μI T) := by
  refine Integrable.bdd_smul (φ := fun t : ℝ => Complex.exp (y * t)) hf (Real.exp (|y.re| * T))
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (y * t)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.exp_le_exp]
  have h1 : y.re * t ≤ |y.re| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht.1.le
  have h2 : |y.re| * t ≤ |y.re| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
  linarith

end AnalyticSufficiency

open AnalyticSufficiency

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {sys : System U W X V Y}

/-- If `η ∈ X` annihilates `im L_T`, then `ιW† η` annihilates every `L_t u`, `0 < t ≤ T`. -/
theorem inner_adjoint_ιW_L_eq_zero {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {η : X}
    (hη : ∀ u : L2 U T, ⟪η, sys.ιW (sys.Lop T u)⟫_ℝ = 0) {t : ℝ} (ht : t ≤ T) {u : ℝ → U}
    (hu : MemLp u 2 (μI T)) :
    ⟪ContinuousLinearMap.adjoint sys.ιW η, sys.L t u⟫_ℝ = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_left,
    L_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht)
      hu.coeFn_toLp.symm), L_eq_Lop_windowL hH1 hT ht]
  exact hη _

/-- The open preconnected `Ω_⋆ ⊆ ρ(A)` containing `{Re s > σ}` and `σ + i {ωₗ}‾`. -/
theorem exists_Ω_harmonic {σ M : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ IsPreconnected Ω ∧ Ω ⊆ resolventSet sys.A.complexify ∧
      {s : ℂ | σ < s.re} ⊆ Ω ∧
      ∀ ω ∈ closure (Set.range h.freq), (σ : ℂ) + ω * Complex.I ∈ Ω := by
  obtain ⟨Ω, hΩo, hΩc, hΩρ, hΩH, hΩK⟩ := exists_isPreconnected_resolventSet (sys := sys) hS
    (K := (fun ω : ℝ => (σ : ℂ) + ω * Complex.I) '' closure (Set.range h.freq))
    (by rintro _ ⟨ω, hω, rfl⟩; exact hρ ω hω) (by rintro _ ⟨ω, hω, rfl⟩; simp)
  exact ⟨Ω, hΩo, hΩc, hΩρ, hΩH, fun ω hω => hΩK ⟨ω, hω, rfl⟩⟩

/-- **(i) ⇒ (ii)** of `thm:analytic-universal-sufficiency`: if `(A, B)` is approximately
controllable in time `T`, then for every `x₀ ∈ W` the record `(ū, x̄)`,
`ū(t) = e^{σ t} h(t)`, is informative in `U × W` on `I = (0, T)`. -/
theorem informative_of_approxControllable_harmonic [TopologicalSpace.SeparableSpace U]
    [TopologicalSpace.SeparableSpace X] {T σ M : ℝ} (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hH1 : sys.H1 T) (hc : sys.Compat) {h : HarmonicSignal U} (hh : h.IsHarmonicPE)
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t))
    (hctrl : sys.ApproxControllable T) (w₀ : W) :
    Informative T (fun t => Real.exp (σ * t) • h t)
      (sys.mildW w₀ (fun t => Real.exp (σ * t) • h t)) := by
  have hρ' : ∀ l, (σ : ℂ) + h.freq l * Complex.I ∈ resolventSet sys.A.complexify :=
    fun l => hρ _ (subset_closure (Set.mem_range_self l))
  rw [informative_iff]
  intro a b hab
  set α : Complexification U := (a : Complexification U) with hα_def
  set η : Complexification W := (b : Complexification W) with hη_def
  -- the harmonic coefficients `dₗ` vanish (`lem:bohr-annihilator` on `W`)
  have hd : sys.annihilatorCoeff σ h α η = 0 := by
    obtain ⟨MW, -, hMW⟩ := exists_growth_W hA hc hS
    refine C0Semigroup.bohr_annihilator sys.SW (analyticOnNhd_SW hA hc) hMW h.freq_injective
      h.exists_abs_freq_le (fun l => resolventSet_complexify_subset_W hc (hρ' l))
      ((w₀ : Complexification W) - ∑' l, sys.stateCoeff σ h l) η
      (summable_annihilatorCoeff hH1 hT hc hρ α η) le_rfl hT ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hab,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [← annihilator_expansion hH1 hT hc hρ w₀ α η htI.1.le, hα_def, hη_def,
      pairing_ofReal_ofReal, pairing_ofReal_ofReal, ← Complex.ofReal_add, ht,
      Complex.ofReal_zero]
  -- `f(s) = ⟨α, ·⟩ + ⟨η, 𝐇(s) ·⟩` vanishes on `Ω_⋆` (identity theorem)
  obtain ⟨Ω, hΩo, hΩc, hΩρ, hΩH, hΩK⟩ := exists_Ω_harmonic hρ hS
  set Φ : ℂ → Complexification U →L[ℂ] ℂ :=
    fun s => pairingCLM α + (pairingCLM η).comp (sys.transfer s) with hΦ_def
  have hΦv : ∀ s v, Φ s v = ⟪α, v⟫_bil + ⟪η, sys.transfer s v⟫_bil := fun s v => by
    simp only [hΦ_def, add_apply, ContinuousLinearMap.comp_apply,
      pairingCLM_apply]
  have hΦ : ∀ s ∈ Ω, Φ s = 0 := by
    refine eqOn_zero_of_isHarmonicPE hh hΩo hΩc hΩK Φ (fun v => ?_) fun l => ?_
    · simp only [hΦv]
      exact (differentiableOn_const _).add ((pairingCLM η).differentiable.comp_differentiableOn
        (((differentiableOn_transfer hH1 hT hc).mono hΩρ).clm_apply (differentiableOn_const v)))
    · rw [hΦv]
      exact congrFun hd l
  -- `α = 0`: let `s = r → +∞` and use the decay of `𝐇(r)`
  obtain ⟨K, r₀, -, hdec⟩ := transfer_decay hH1 hT hc
  have ha : a = 0 := by
    have hbound : ∀ r : ℝ, max r₀ (σ + 1) ≤ r →
        ‖⟪α, α⟫_bil‖ ≤ ‖η‖ * (K / Real.sqrt r) * ‖α‖ := by
      intro r hr
      have hrΩ : (r : ℂ) ∈ Ω := hΩH (by
        show σ < (r : ℂ).re
        rw [Complex.ofReal_re]
        linarith [le_max_right r₀ (σ + 1)])
      have h0 : ⟪α, α⟫_bil + ⟪η, sys.transfer r α⟫_bil = 0 := by
        rw [← hΦv, hΦ _ hrΩ, zero_apply]
      rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
      calc ‖⟪η, sys.transfer r α⟫_bil‖ ≤ ‖η‖ * ‖sys.transfer r α‖ := norm_pairing_le _ _
        _ ≤ ‖η‖ * (‖sys.transfer r‖ * ‖α‖) := by
          gcongr; exact (sys.transfer r).le_opNorm α
        _ ≤ ‖η‖ * (K / Real.sqrt r * ‖α‖) := by
          gcongr; exact (hdec r (le_of_max_le_left hr)).2
        _ = ‖η‖ * (K / Real.sqrt r) * ‖α‖ := by ring
    have htend : Tendsto (fun r => ‖η‖ * (K / Real.sqrt r) * ‖α‖) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := K)).div_atTop Real.tendsto_sqrt_atTop
      simpa using (this.const_mul ‖η‖).mul_const ‖α‖
    have hle : ‖⟪α, α⟫_bil‖ ≤ 0 := ge_of_tendsto htend (eventually_atTop.2 ⟨_, hbound⟩)
    have hαα : ⟪α, α⟫_bil = 0 := norm_le_zero_iff.1 hle
    rw [hα_def, pairing_ofReal_ofReal, Complex.ofReal_eq_zero] at hαα
    exact inner_self_eq_zero.1 hαα
  -- `η ⊥ im L_T` (`lem:transfer-laplace`), so `η = 0` by density of `im L_T` in `W`
  have h0 : ∀ s : ℂ, σ < s.re → ∀ v, ⟪η, sys.transfer s v⟫_bil = 0 := by
    intro s hs v
    have := hΦv s v
    rw [hΦ s (hΩH hs), zero_apply, hα_def, ha, Complexification.ofReal_zero,
      pairing_zero_left, zero_add] at this
    exact this.symm
  obtain ⟨-, hL⟩ := psiC_eq_zero_of_inner_transfer_eq_zero hH1 hT hA hc hS h0
  refine ⟨ha, eq_zero_of_inner_eq_zero_of_denseRange (denseRange_Lop_W hH1 hT hA hc hctrl)
    fun u => ?_⟩
  have := hL T u hT (Lp.memLp u)
  rw [hη_def, pairing_ofReal_ofReal, Complex.ofReal_eq_zero] at this
  rwa [Lop_apply hH1 hT]

/-- **(i) ⇒ (iii)** of `thm:analytic-universal-sufficiency`: if `(A, B)` is approximately
controllable in time `T`, then for every `x₀ ∈ X` the record `(ū, x̄)` on `[0, T + T']`,
`ū(t) = e^{σ t} h(t)`, is window informative. -/
theorem windowInformative_of_approxControllable_harmonic [TopologicalSpace.SeparableSpace U]
    [TopologicalSpace.SeparableSpace X] {T T' σ M : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hA : sys.SX.IsAnalytic) (hH1 : sys.H1 T) (hc : sys.Compat) {h : HarmonicSignal U}
    (hh : h.IsHarmonicPE)
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t))
    (hctrl : sys.ApproxControllable T) (x₀ : X) :
    WindowInformative T T' (fun t => Real.exp (σ * t) • h t)
      (sys.mild x₀ (fun t => Real.exp (σ * t) • h t)) := by
  have hρ' : ∀ l, (σ : ℂ) + h.freq l * Complex.I ∈ resolventSet sys.A.complexify :=
    fun l => hρ _ (subset_closure (Set.mem_range_self l))
  rw [windowInformative_iff (memLp_harmonic_input σ h (T + T'))
    (memLp_mild hH1 hT (memLp_harmonic_input σ h T') x₀)]
  intro p hp
  set g : L2 U T := p.fst with hg_def
  set ξ : X := p.snd with hξ_def
  -- the coefficients `Dₗ` vanish (`lem:bohr-annihilator` on `X`)
  have hD : sys.windowCoeff σ h g ξ = 0 := by
    refine C0Semigroup.bohr_annihilator sys.SX hA.analyticOnNhd hS h.freq_injective
      h.exists_abs_freq_le hρ'
      ((x₀ : Complexification X) - ∑' l, sys.ιW.complexify (sys.stateCoeff σ h l))
      (ξ : Complexification X) (summable_windowCoeff hH1 hT hc hρ g ξ) le_rfl hT' ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hp,
      ae_restrict_mem measurableSet_Ioo] with s hs hsI
    rw [← window_expansion hH1 hT hc hρ x₀ g ξ hsI.1.le, hs, Complex.ofReal_zero]
  -- `F(s) = ∫₀ᵀ e^{s t} ⟨g(t), ·⟩ dt + ⟨ξ, 𝐇(s) ·⟩` vanishes on `Ω_⋆` (identity theorem)
  obtain ⟨Ω, hΩo, hΩc, hΩρ, hΩH, hΩK⟩ := exists_Ω_harmonic hρ hS
  set ξ' : W := ContinuousLinearMap.adjoint sys.ιW ξ with hξ'_def
  set q : ℝ → Complexification U :=
    (Ioc 0 T).indicator (fun t => ((g t : U) : Complexification U)) with hq_def
  have hgC : Integrable (fun t => ((g t : U) : Complexification U)) (μI T) :=
    (ofRealCLM (X := U)).integrable_comp ((Lp.memLp g).integrable one_le_two)
  have hq : ∀ σ' : ℝ, LaplaceIntegrable q σ' := by
    intro σ'
    have h1 := ((integrable_indicator_iff measurableSet_Ioc).2
      (integrable_cexp_smul hgC (-(σ' : ℂ)))).integrableOn (s := Ioi 0)
    refine h1.congr_fun (fun r _ => ?_) measurableSet_Ioi
    rw [hq_def]
    simp only [neg_mul]
    exact indicator_smul_apply _ _ _ r
  have hlap : ∀ s v, ⟪laplace q (-s), v⟫_bil =
      ∫ t in Ioc 0 T, Complex.exp (s * t) * ⟪((g t : U) : Complexification U), v⟫_bil := by
    intro s v
    have hint : ∀ r : ℝ, ⟪v, Complex.exp (-(-s * r)) • q r⟫_bil = (Ioc 0 T).indicator
        (fun t => Complex.exp (s * t) * ⟪((g t : U) : Complexification U), v⟫_bil) r := by
      intro r
      by_cases hr : r ∈ Ioc 0 T
      · rw [hq_def, indicator_of_mem hr, indicator_of_mem hr, pairing_smul_right, neg_mul,
          neg_neg, pairing_comm]
      · rw [hq_def, indicator_of_notMem hr, indicator_of_notMem hr, smul_zero,
          pairing_zero_right]
    rw [laplace, pairing_comm, pairing_integral v ((hq (-s).re).integrableOn le_rfl)]
    simp_rw [hint]
    rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self]
  have hlapd : Differentiable ℂ (fun s => laplace q (-s)) := fun s =>
    (hasDerivAt_laplace (hq ((-s).re - 1)) (by linarith)).differentiableAt.comp s
      differentiable_neg.differentiableAt
  set Φ : ℂ → Complexification U →L[ℂ] ℂ := fun s =>
    pairingCLM (laplace q (-s)) + (pairingCLM (ξ' : Complexification W)).comp (sys.transfer s)
    with hΦ_def
  have hΦv : ∀ s v, Φ s v = ⟪laplace q (-s), v⟫_bil +
      ⟪(ξ' : Complexification W), sys.transfer s v⟫_bil := fun s v => by
    simp only [hΦ_def, add_apply, ContinuousLinearMap.comp_apply, pairingCLM_apply]
  have hΦd : ∀ v, DifferentiableOn ℂ (fun s => Φ s v) Ω := by
    intro v
    simp only [hΦv]
    have h1 : Differentiable ℂ (fun s => ⟪laplace q (-s), v⟫_bil) := by
      have h := (pairingCLM v).differentiable.comp hlapd
      have he : (⇑(pairingCLM v) ∘ fun s => laplace q (-s)) =
          fun s => ⟪laplace q (-s), v⟫_bil := by
        funext s
        simp only [Function.comp_apply, pairingCLM_apply]
        exact pairing_comm _ _
      rwa [he] at h
    exact h1.differentiableOn.add ((pairingCLM _).differentiable.comp_differentiableOn
      (((differentiableOn_transfer hH1 hT hc).mono hΩρ).clm_apply (differentiableOn_const v)))
  have hΦ : ∀ s ∈ Ω, Φ s = 0 := by
    refine eqOn_zero_of_isHarmonicPE hh hΩo hΩc hΩK Φ hΦd fun l => ?_
    rw [hΦv, hlap]
    have := congrFun hD l
    rw [windowCoeff, pairing_ofReal_complexify] at this
    exact this
  -- `g = 0`: `F(x) = 0` for real `x > σ` is a vanishing Laplace transform on `(-T, ∞)`
  -- (`lem:transfer-laplace`), and `(φⱼ)` is total
  obtain ⟨J, hJ, φ, hφ, hj⟩ := hh
  have hGj : ∀ j, ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ⟪((g t : U) : Complexification U), φ j⟫_bil = 0 := by
    intro j
    set G : ℝ → ℂ := fun t => ⟪((g t : U) : Complexification U), φ j⟫_bil with hG_def
    set Ψ : ℝ → ℂ := fun r => ⟪sys.psiC (ξ' : Complexification W) r, φ j⟫_bil with hΨ_def
    set P : ℝ → ℂ := fun r => (Ico 0 T).indicator G (-r) + (Ioi 0).indicator Ψ r with hP_def
    have hGint : Integrable G (μI T) := by
      have h := (pairingCLM (φ j)).integrable_comp hgC
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp only [hG_def, pairingCLM_apply]
      exact pairing_comm _ _
    -- the reflected part `r ↦ G(-r)` on `(-T, 0]`
    have hF : ∀ (y : ℝ) (r : ℝ), Complex.exp (-(y * r)) • (Ico 0 T).indicator G (-r) =
        (Ico 0 T).indicator (fun t => Complex.exp (y * t) * G t) (-r) := by
      intro y r
      by_cases hr : -r ∈ Ico 0 T
      · rw [indicator_of_mem hr, indicator_of_mem hr, smul_eq_mul, Complex.ofReal_neg, mul_neg]
      · rw [indicator_of_notMem hr, indicator_of_notMem hr, smul_zero]
    have hI1 : ∀ y : ℝ,
        Integrable (fun r : ℝ => Complex.exp (-(y * r)) • (Ico 0 T).indicator G (-r)) := by
      intro y
      simp_rw [hF y]
      refine Integrable.comp_neg (f := (Ico 0 T).indicator fun t => Complex.exp (y * t) * G t) ?_
      refine (integrable_indicator_iff measurableSet_Ico).2 ?_
      rw [IntegrableOn, Measure.restrict_congr_set Ico_ae_eq_Ioc]
      simpa only [smul_eq_mul] using integrable_cexp_smul hGint (y : ℂ)
    have hI2 : ∀ y : ℝ, σ < y →
        Integrable (fun r : ℝ => Complex.exp (-(y * r)) • (Ioi 0).indicator Ψ r) := by
      intro y hy
      have h := (integrable_indicator_iff measurableSet_Ioi).2
        (laplaceIntegrable_psiC hH1 hT hA hc hS (ξ' : Complexification W) (φ j) hy)
      exact h.congr (Eventually.of_forall fun r => indicator_smul_apply _ _ _ r)
    have hP0 : P =ᵐ[volume.restrict (Ioi (-T))] 0 := by
      refine ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero (σ := σ + 1) ?_ ?_
      · refine ((hI1 (σ + 1)).add (hI2 (σ + 1) (by linarith))).integrableOn.congr_fun
          (fun r _ => ?_) measurableSet_Ioi
        simp only [hP_def, smul_add, Pi.add_apply]
      · filter_upwards [eventually_gt_atTop σ] with x hx
        have hsplit : ∫ r in Ioi (-T), Complex.exp (-(x * r)) • P r =
            (∫ r in Ioi (-T), Complex.exp (-(x * r)) • (Ico 0 T).indicator G (-r)) +
              ∫ r in Ioi (-T), Complex.exp (-(x * r)) • (Ioi 0).indicator Ψ r := by
          rw [← integral_add (hI1 x).integrableOn (hI2 x hx).integrableOn]
          simp only [hP_def, smul_add]
        have e1 : ∫ r in Ioi (-T), Complex.exp (-(x * r)) • (Ico 0 T).indicator G (-r) =
            ∫ t in Ioc 0 T, Complex.exp (x * t) * G t := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => ?_)]
          · simp_rw [hF x]
            rw [integral_neg_eq_self ((Ico 0 T).indicator fun t => Complex.exp (x * t) * G t)
              volume, integral_indicator measurableSet_Ico, setIntegral_congr_set Ico_ae_eq_Ioc]
          · have : -r ∉ Ico 0 T := fun h' => hr (by
              simp only [mem_Ioi]
              linarith [h'.2])
            rw [indicator_of_notMem this, smul_zero]
        have e2 : ∫ r in Ioi (-T), Complex.exp (-(x * r)) • (Ioi 0).indicator Ψ r =
            laplace Ψ x := by
          have : (Ioi 0).indicator (fun r : ℝ => Complex.exp (-(x * r)) • Ψ r) =
              fun r : ℝ => Complex.exp (-(x * r)) • (Ioi 0).indicator Ψ r :=
            funext fun r => indicator_smul_apply _ _ _ r
          rw [← this, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
            max_eq_right (by linarith : -T ≤ 0)]
          rfl
        have hxs : σ < (x : ℂ).re := by rw [Complex.ofReal_re]; exact hx
        rw [hsplit, e1, e2, hΨ_def,
          ← inner_transfer_eq_laplace hH1 hT hA hc hS _ hxs (φ j)]
        have := hΦv x (φ j)
        rw [hΦ _ (hΩH hxs), zero_apply, hlap] at this
        exact this.symm
    -- restrict to `(-T, 0)` and reflect
    have h1 : ∀ᵐ r ∂(volume.restrict (Ioo (-T) 0)), G (-r) = 0 := by
      have h := ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioi_self : Ioo (-T) 0 ⊆ Ioi (-T)) hP0
      filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with r hr hrI
      have hr1 : -r ∈ Ico 0 T := ⟨by linarith [hrI.2], by linarith [hrI.1]⟩
      have hr2 : r ∉ Ioi 0 := fun h' => absurd hrI.2 (not_lt.2 (le_of_lt h'))
      have := hr
      simp only [hP_def, indicator_of_mem hr1, indicator_of_notMem hr2, add_zero,
        Pi.zero_apply] at this
      exact this
    have hmp : MeasurePreserving Neg.neg (volume.restrict (Ioo 0 T))
        (volume.restrict (Ioo (-T) 0)) := by
      have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
        (measurableSet_Ioo (a := -T) (b := 0))
      have hpre : Neg.neg ⁻¹' Ioo (-T) (0 : ℝ) = Ioo 0 T := by
        ext t
        simp only [mem_preimage, mem_Ioo]
        constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
      rwa [hpre] at h
    filter_upwards [hmp.quasiMeasurePreserving.ae h1] with t ht
    simpa [hG_def] using ht
  have hg0 : ∀ᵐ t ∂(μI T), g t = 0 := by
    change ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), _
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_all_iff.2 hGj] with t ht
    have hz : pairingCLM ((g t : U) : Complexification U) = 0 :=
      clm_eq_zero_of_total hφ _ fun j => by rw [pairingCLM_apply]; exact ht j
    have := congrArg (fun F => F ((g t : U) : Complexification U)) hz
    simp only [pairingCLM_apply, zero_apply, pairing_ofReal_ofReal,
      Complex.ofReal_eq_zero] at this
    exact inner_self_eq_zero.1 this
  -- `ξ = 0`: `⟨ξ, 𝐇(s) ·⟩ = 0` for `Re s > σ`, so `ξ ⊥ im L_T`
  have h0 : ∀ s : ℂ, σ < s.re → ∀ v, ⟪(ξ' : Complexification W), sys.transfer s v⟫_bil = 0 := by
    intro s hs v
    have hint : ∫ t in Ioc 0 T, Complex.exp (s * t) *
        ⟪((g t : U) : Complexification U), v⟫_bil = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hg0] with t ht
      rw [ht, Complexification.ofReal_zero, pairing_zero_left, mul_zero, Pi.zero_apply]
    have := hΦv s v
    rw [hΦ s (hΩH hs), zero_apply, hlap, hint, zero_add] at this
    exact this.symm
  obtain ⟨-, hL⟩ := psiC_eq_zero_of_inner_transfer_eq_zero hH1 hT hA hc hS h0
  have hξ : ξ = 0 := by
    refine (approxControllable_iff hH1 hT).1 hctrl ξ fun u => ?_
    have := hL T u hT (Lp.memLp u)
    rw [pairing_ofReal_ofReal, Complex.ofReal_eq_zero, hξ'_def,
      ContinuousLinearMap.adjoint_inner_left] at this
    rwa [Lop_apply hH1 hT]
  have hg : g = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hg0
  rw [WithLp.ext_iff]
  exact Prod.ext hg hξ

set_option linter.unusedVariables false in
/-- **(ii) at `x₀ = 0` ⇒ (i)** (the "moreover" clause of `thm:analytic-universal-sufficiency`):
if the record generated from `x₀ = 0` is informative in `U × W` on `(0, T)`, then `(A, B)` is
approximately controllable in time `T`.  Stated for any input `u ∈ L²(0, T; U)` (see the module
docstring). -/
theorem approxControllable_of_informative_zero {T : ℝ} (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hH1 : sys.H1 T) (hc : sys.Compat) {u : ℝ → U} (hu : MemLp u 2 (μI T))
    (hinf : Informative T u (sys.mildW 0 u)) : sys.ApproxControllable T := by
  rw [approxControllable_iff hH1 hT]
  intro η hη
  obtain ⟨-, hb⟩ := hinf.eq_zero (a := 0) (b := ContinuousLinearMap.adjoint sys.ιW η) <|
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => by
      rw [inner_zero_left, zero_add, mildW, map_zero, zero_add]
      exact inner_adjoint_ιW_L_eq_zero hH1 hT hη ht.2 hu)
  refine eq_zero_of_inner_eq_zero_of_denseRange sys.ιW_denseRange fun w => ?_
  rw [← ContinuousLinearMap.adjoint_inner_left, hb, inner_zero_left]

set_option linter.unusedVariables false in
/-- **(iii) at `x₀ = 0` ⇒ (i)** (the "moreover" clause of `thm:analytic-universal-sufficiency`):
if the record on `[0, T + T']` generated from `x₀ = 0` is window informative, then `(A, B)` is
approximately controllable in time `T`.  Stated for any input `u ∈ L²(0, T + T'; U)` (see the
module docstring). -/
theorem approxControllable_of_windowInformative_zero {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hA : sys.SX.IsAnalytic) (hH1 : sys.H1 T) (hc : sys.Compat) {u : ℝ → U}
    (hu : MemLp u 2 (μI (T + T'))) (hwin : WindowInformative T T' u (sys.mild 0 u)) :
    sys.ApproxControllable T := by
  have hu' : MemLp u 2 (μI T') := memLp_μI_of_le hu (by linarith)
  rw [windowInformative_iff hu (memLp_mild hH1 hT hu' 0)] at hwin
  rw [approxControllable_iff hH1 hT]
  intro β hβ
  set η : W := ContinuousLinearMap.adjoint sys.ιW β with hη_def
  -- `ψ_η` vanishes on `(0, ∞)`: on `(0, T)` by testing with `v(r) = ψ_η(T - r)`, then by
  -- analyticity
  have hψ : ∀ r, 0 < r → sys.psi η r = 0 := by
    have hψT : MemLp (sys.psi η) 2 (volume.restrict (Ico 0 T)) := by
      rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
      exact memLp_psi hH1 hT hA hc η T
    have hv : MemLp (fun r => sys.psi η (T - r)) 2 (μI T) :=
      hψT.comp_measurePreserving (measurePreserving_const_sub_Ioc T)
    set V : L2 U T := hv.toLp _
    have h1 := inner_adjoint_ιW_L_eq_zero hH1 hT hβ le_rfl (Lp.memLp V)
    rw [inner_L_eq_integral_psi hH1 hT hA hc hT.le (Lp.memLp V)] at h1
    have hV : V = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ), MeasureTheory.L2.inner_def, ← h1]
      refine integral_congr_ae ?_
      filter_upwards [hv.coeFn_toLp] with r hr
      rw [hr]
    have h2 : (fun r => sys.psi η (T - r)) =ᵐ[μI T] 0 := by
      have hc' : ⇑V =ᵐ[μI T] fun r => sys.psi η (T - r) := hv.coeFn_toLp
      filter_upwards [hc', Lp.coeFn_zero U 2 (μI T)] with r hr h0
      rw [← hr, hV, h0]
    have h3 : ∀ᵐ r ∂(volume.restrict (Ioo 0 T)), sys.psi η r = 0 := by
      have h4 := (measurePreserving_const_sub_Ico T).quasiMeasurePreserving.ae h2
      have h5 : ∀ᵐ r ∂(volume.restrict (Ico 0 T)), sys.psi η r = 0 := by
        filter_upwards [h4] with r hr
        simpa using hr
      exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ico_self h5
    intro r hr
    exact eqOn_zero_of_ae_Ioo (analyticOnNhd_psi hA hc η) isPreconnected_Ioi hT
      Ioo_subset_Ioi_self h3 hr
  -- hence `⟨β, x̄(s)⟩ = ⟨η, L_s u⟩ = 0` for every `s`
  have hβx : ∀ s, 0 ≤ s → s ≤ T + T' → ⟪β, sys.mild 0 u s⟫_ℝ = 0 := by
    intro s hs hsT
    rw [mild_zero_left, ← ContinuousLinearMap.adjoint_inner_left, ← hη_def,
      inner_L_eq_integral_psi hH1 hT hA hc hs (memLp_μI_of_le hu hsT) η]
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [hψ (s - r) (by linarith [hr.2]), inner_zero_left, Pi.zero_apply]
  have h0 := hwin (WithLp.toLp 2 (0, β)) ?_
  · simpa using congrArg WithLp.snd h0
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [integral_eq_zero_of_ae ?_, hβx s hs.1.le (by linarith [hs.2]), add_zero]
    filter_upwards [Lp.coeFn_zero U 2 (μI T)] with t ht
    rw [ht, Pi.zero_apply, inner_zero_left, Pi.zero_apply]

/-- **Universal sufficiency for analytic semigroups** (`thm:analytic-universal-sufficiency`).
Let `U`, `X` be separable, `A` generate an analytic semigroup, `hyp:H1` and `hyp:compat` hold,
`h` be harmonically persistently exciting with frequencies `ωₗ`, `T' > 0` and `σ ∈ ℝ` with
`σ + i {ωₗ}‾ ⊆ ρ(A)` and `‖S(t)‖ ≤ M e^{σ t}` (`eq:analytic-growth-bound`).  For the input
`ū(t) = e^{σ t} h(t)` on `[0, T + T']` the following are equivalent:
(i) `(A, B)` is approximately controllable in time `T`;
(ii) `(ū, x̄)` is informative in `U × W` on `I = (0, T)` for every `x₀ ∈ W`;
(iii) `(ū, x̄)` is window informative for every `x₀ ∈ X`.
The "moreover" clause is `approxControllable_of_informative_zero` and
`approxControllable_of_windowInformative_zero`. -/
theorem analytic_universal_sufficiency [TopologicalSpace.SeparableSpace U]
    [TopologicalSpace.SeparableSpace X] {T T' σ M : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hA : sys.SX.IsAnalytic) (hH1 : sys.H1 T) (hc : sys.Compat) {h : HarmonicSignal U}
    (hh : h.IsHarmonicPE)
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) :
    [sys.ApproxControllable T,
      ∀ w₀ : W, Informative T (fun t => Real.exp (σ * t) • h t)
        (sys.mildW w₀ (fun t => Real.exp (σ * t) • h t)),
      ∀ x₀ : X, WindowInformative T T' (fun t => Real.exp (σ * t) • h t)
        (sys.mild x₀ (fun t => Real.exp (σ * t) • h t))].TFAE := by
  have hu : MemLp (fun t => Real.exp (σ * t) • h t) 2 (μI (T + T')) :=
    memLp_harmonic_input σ h (T + T')
  tfae_have 1 → 2 := fun hctrl w₀ =>
    informative_of_approxControllable_harmonic hT hA hH1 hc hh hρ hS hctrl w₀
  tfae_have 1 → 3 := fun hctrl x₀ =>
    windowInformative_of_approxControllable_harmonic hT hT' hA hH1 hc hh hρ hS hctrl x₀
  tfae_have 2 → 1 := fun h2 =>
    approxControllable_of_informative_zero hT hA hH1 hc
      (hu.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right (by linarith)) le_rfl))
      (h2 0)
  tfae_have 3 → 1 := fun h3 =>
    approxControllable_of_windowInformative_zero hT hT' hA hH1 hc hu (h3 0)
  tfae_finish

end System

end DataDrivenControl
