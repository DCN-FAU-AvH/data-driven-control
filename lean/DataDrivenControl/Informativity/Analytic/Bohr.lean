module

public import DataDrivenControl.Informativity.Analytic.Expansion
public import DataDrivenControl.Analysis.BohrMean
public import DataDrivenControl.Analysis.Laplace
public import DataDrivenControl.Analysis.ExpSums
public import DataDrivenControl.System.Controllability

/-!
# Vanishing of the harmonic coefficients; the transfer map as a Laplace transform

Paper: `lem:bohr-annihilator`, `lem:transfer-laplace` (`eq:analytic-transfer-laplace`), and the
smoothing facts before them in `app:analytic-universal-sufficiency` (`S(δ) ∈ L(X, W)`, analytic
orbits, `r ↦ S(r)† η` analytic into `D(A†)` for `η ∈ W'`).

## Conventions

As in `Analytic/Transfer` and `Analytic/Expansion`.  The paper's `W'` is modelled by `W` itself
(Riesz): `η ∈ W` acts by `w ↦ ⟪η, w⟫_W`, and `ξ ∈ X ↪ W'` is `ιW† ξ`.  For `η ∈ W`,
`S(r)† η ∈ X` is the Hilbert adjoint of the smoothing operator `S(r) ∈ L(X, W)`
(`sys.smoothing r`, `ιW_smoothing`), and `ψ_η(r) = B† S(r)† η` (`sys.psi η r`) uses
`B† : D(A†) → U` (`System.Bstar`, extended by `0` off `D(A†)` in `sys.BstarExt`).  Complex
`η ∈ W_ℂ` act through `sys.psiC η = ψ_{re η} + i ψ_{im η}`.

## Main declarations

* `C0Semigroup.bohr_annihilator` (`lem:bohr-annihilator`), for a semigroup on `E` (the paper's
  `E = W` or `X`) with real-analytic orbits on `(0, ∞)`, growth bound `‖S t‖ ≤ M e^{σ t}` and
  `sₗ = σ + i ωₗ ∈ ρ(A_E)`: if `⟨ζ, S(t) c⟩ + e^{σ t} ∑ₗ dₗ e^{i ωₗ t} = 0` for a.e. `t` in a
  nonempty open subinterval of `(0, ∞)` (`c, ζ ∈ E_ℂ`, `∑ |dₗ| < ∞`), then every `dₗ = 0`.
* `System.analyticOnNhd_SW`: under analyticity and `hyp:compat`, the orbits of `S` on `W` are
  real analytic on `(0, ∞)` (the case `E = W`; `E = X` is `IsAnalytic.analyticOnNhd`).
* `sys.smoothing`, `ιW_smoothing`, `adjoint_smoothing_mem_domain`; `sys.BstarExt`, `sys.psi`,
  `sys.psiC`, `psi_adjoint_ιW` (`X ↪ W'`).
* `lem:transfer-laplace`: `analyticOnNhd_psi` (analytic on `(0, ∞)`), `memLp_psi`
  (`L²_loc([0, ∞); U)`), `norm_psi_le` (`‖ψ_η(r)‖ = O(e^{σ r})`), `inner_L_eq_integral_psi`
  (`(L_t† η)(τ) = ψ_η(t - τ)`), `laplaceIntegrable_psiC`, `inner_transfer_eq_laplace`
  (`eq:analytic-transfer-laplace`), `psiC_eq_zero_of_inner_transfer_eq_zero` (a vanishing
  transform forces `ψ_η = 0` and `η ⊥ im L_τ` for all `τ`), `denseRange_Lop_W`
  (approximate controllability in time `T` gives `im L_T` dense in `W`).

## Upstream results used

`hasBohrMean_zero_of_bounded_integral`, `eq_zero_of_add_bohrSeries_ae_eq_zero`
(`Analysis/BohrMean`); `eqOn_zero_of_ae_Ioo`, `analyticOnNhd_harmonic` (`Analysis/ExpSums`);
`laplace`, `LaplaceIntegrable`, `laplaceIntegrable_of_le_exp`, `LaplaceIntegrable.comp_clm`,
`tendsto_setIntegral_Ioc_laplace`, `ae_eq_zero_of_laplace_inner_eq_zero` (`Analysis/Laplace`);
`IsAnalytic.analyticOnNhd`, `IsAnalytic.adjoint`, `IsAnalytic.adjoint_real_mem_adjoint_domain`,
`IsAnalytic.gen`, `System.exists_smoothing`, `System.exists_growth_W` (`Semigroup/Analytic`);
`C0Semigroup.integral_exp_smul_eq` (`Semigroup/Resolvent`); `System.adjoint_Lop_ae_eq`,
`System.inner_L_eq_integral`, `System.exists_norm_Bstar_le` (`System/ControlRealization`);
`Lop_apply`, `L_congr_ae`, `memLp_μI_of_continuousOn` (`System/Mild`); `Lc_cexp_smul`
(`Analytic/Expansion`); `C0Semigroup.complexify`, `complexify_generator`,
`C0Semigroup.mem_resolventSet_complexify` (`Analytic/Transfer`); `approxControllable_iff`
(`System/Controllability`); `denseRange_iff_adjoint_eq_zero` (`Signal/Shift`).

## Proof notes

* `bohr_annihilator`: the identity is real analytic on `(0, ∞)` (orbits by hypothesis, the
  harmonic part is entire), so the identity theorem (`eqOn_zero_of_ae_Ioo`) upgrades "a.e. on
  `(a, b)`" to "every `t > 0`".  The free response has Bohr mean `0` at every `ωₗ`: with
  `d = R(sₗ, A_ℂ) c` and the complexified semigroup `S_ℂ` (`C0Semigroup.complexify`,
  `Analytic/Transfer`), the finite-time Laplace identity gives
  `∫₀^R e^{-sₗ t} ⟨ζ, S(t) c⟩ dt = ⟨ζ, d - e^{-sₗ R} S(R) d⟩`, bounded by the growth bound
  (`exists_bound_integral_pairing`).
* Smoothing: `S(δ + ρ) = S(δ) S(ρ)` as maps `X → W` (`smoothing_add`), so
  `S(δ + ρ)† η = S(ρ)† S(δ)† η` and `ψ_η(δ + ε + ρ) = P_ε S(ρ)† S(δ)† η` with the bounded
  operator `P_ε = B† S(ε)† ∈ L(X, U)` (`exists_clm_BstarExt`, from the graph-norm bound of `B†`
  and `A† S(ε)† = (A S(ε))†`).  This gives `analyticOnNhd_psi` (the adjoint semigroup is
  analytic) and `norm_psi_le` (`ε = δ = 1/2`).
* Duality (`adjoint_Lop_ae_eq_psi`): for `ε > 0`, `S(ε)† η ∈ D(A†)`, and the `X`-duality
  `System.adjoint_Lop_ae_eq` gives `L_t† S_W(ε)† η = ψ_η(ε + t - ·)` a.e.  As `ε → 0⁺`, the
  left side converges in `L²` (strong continuity of the adjoint semigroup on `W`) and the right
  side pointwise on `(0, t)` (continuity of `ψ_η`); limits in measure are a.e. unique.  So
  `L_t† η = ψ_η(t - ·)` a.e., whence `memLp_psi` (reflection `r ↦ t - r` preserves the window
  measure) and `inner_L_eq_integral_psi`.  This replaces the paper's "controls supported away
  from the terminal time, then `hyp:H1`".
* `inner_transfer_eq_laplace`: pair `Lc_cexp_smul` with `η` (`pairing_Lc_eq_integral`),
  substitute `r ↦ t - r`, and let `t → ∞` (`exists_growth_W`).
* `psiC_eq_zero_of_inner_transfer_eq_zero`: weak uniqueness of the Laplace transform in the
  Hilbert space `U_ℂ` (`ae_eq_zero_of_laplace_inner_eq_zero`; separability is not needed), then
  analyticity of `ψ` turns "a.e." into "every `r > 0`".
* `denseRange_Lop_W`: as in the paper; the last step pairs with `η` itself:
  `⟪η, S_W(r) η⟫_W = ⟪S(r)† η, ιW η⟫_X = 0` and `r → 0⁺` (no adjoint semigroup on `W`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

open Complexification

/-- Reflection `r ↦ τ - r` preserves the window measure `μI τ` (Lebesgue measure on `(0, τ]`). -/
theorem measurePreserving_sub_left_μI (τ : ℝ) :
    MeasurePreserving (fun r : ℝ => τ - r) (μI τ) (μI τ) := by
  have h := (Measure.measurePreserving_sub_left volume τ).restrict_preimage
    (measurableSet_Ioc (a := (0 : ℝ)) (b := τ))
  have hpre : (fun r : ℝ => τ - r) ⁻¹' Ioc 0 τ = Ico 0 τ := by
    ext r
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre, Measure.restrict_congr_set Ico_ae_eq_Ioc] at h
  exact h

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The orbit pairing `t ↦ ⟪ζ, S(t)_ℂ c⟫` is real analytic on `(0, ∞)` when the orbits are. -/
theorem analyticOnNhd_pairing_complexify (S : C0Semigroup ℝ E)
    (hS_an : ∀ x : E, AnalyticOnNhd ℝ (fun t => S.real t x) (Ioi 0))
    (c ζ : Complexification E) :
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪ζ, (S.real t).complexify c⟫_bil) (Ioi 0) := by
  have hP : ∀ x : E, AnalyticOnNhd ℝ
      (fun t : ℝ => ⟪ζ, ((S.real t x : E) : Complexification E)⟫_bil) (Ioi 0) := by
    intro x t ht
    have hL : AnalyticAt ℝ (((pairingCLM ζ).restrictScalars ℝ).comp
        (ofRealCLM : E →L[ℝ] Complexification E)) (S.real t x) :=
      ContinuousLinearMap.analyticAt _ _
    exact AnalyticAt.comp (f := fun t : ℝ => S.real t x) hL (hS_an x t ht)
  have e : ∀ t : ℝ, ⟪ζ, (S.real t).complexify c⟫_bil =
      ⟪ζ, ((S.real t c.re : E) : Complexification E)⟫_bil +
        Complex.I * ⟪ζ, ((S.real t c.im : E) : Complexification E)⟫_bil := by
    intro t
    rw [ContinuousLinearMap.complexify_apply, mk_eq_add_I_smul, pairing_add_right,
      pairing_smul_right]
  simp_rw [e]
  intro t ht
  exact (hP c.re t ht).add (analyticAt_const.mul (hP c.im t ht))

/-- The free response averages away: `∫₀^R e^{-s t} ⟪ζ, S(t)_ℂ c⟫ dt` stays bounded when
`s ∈ ρ(A_ℂ)` and `‖S t‖ ≤ M e^{(Re s) t}`. -/
theorem exists_bound_integral_pairing (S : C0Semigroup ℝ E) {M : ℝ}
    {s : ℂ} (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (s.re * t))
    (hs : s ∈ resolventSet S.generator.complexify) (c ζ : Complexification E) :
    ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      ‖∫ t in (0 : ℝ)..R, Complex.exp (-(t * s)) * ⟪ζ, (S.real t).complexify c⟫_bil‖ ≤ C := by
  rw [← S.complexify_generator] at hs
  set SC := S.complexify
  set d := resolvent SC.generator s c
  refine ⟨‖ζ‖ * (‖d‖ + M * ‖d‖), fun R hR => ?_⟩
  have hint : IntervalIntegrable (fun t : ℝ => NormedSpace.exp (-((t : ℂ) * s)) • SC.real t c)
      volume 0 R := by
    refine Continuous.intervalIntegrable ?_ _ _
    rw [← Complex.exp_eq_exp_ℂ]
    exact Continuous.smul (f := fun t : ℝ => Complex.exp (-(↑t * s))) (by fun_prop)
      (SC.continuous_real_apply c)
  have key := SC.integral_exp_smul_eq hs hR c
  have e : (fun t : ℝ => Complex.exp (-(t * s)) * ⟪ζ, (S.real t).complexify c⟫_bil) =
      fun t : ℝ => pairingCLM ζ (NormedSpace.exp (-((t : ℂ) * s)) • SC.real t c) := by
    funext t
    rw [pairingCLM_apply, pairing_smul_right, ← Complex.exp_eq_exp_ℂ]; rfl
  rw [e, (pairingCLM ζ).intervalIntegral_comp_comm hint]
  erw [key]
  rw [pairingCLM_apply, ← Complex.exp_eq_exp_ℂ]
  refine (norm_pairing_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Complex.norm_exp]
  have h1 : (-((R : ℂ) * s)).re = -(s.re * R) := by simp [mul_comm]
  erw [h1]
  have h2 : ‖SC.real R d‖ ≤ M * Real.exp (s.re * R) * ‖d‖ := by
    rw [complexify_real]
    refine (ContinuousLinearMap.norm_complexify_apply_le _ _).trans ?_
    gcongr
    rw [S.real_of_nonneg hR]; exact hS _
  calc Real.exp (-(s.re * R)) * ‖SC.real R d‖
      ≤ Real.exp (-(s.re * R)) * (M * Real.exp (s.re * R) * ‖d‖) := by gcongr
    _ = M * ‖d‖ := by
        rw [show Real.exp (-(s.re * R)) * (M * Real.exp (s.re * R) * ‖d‖) =
          M * ‖d‖ * (Real.exp (-(s.re * R)) * Real.exp (s.re * R)) by ring, ← Real.exp_add]
        simp

/-- **Vanishing of the harmonic coefficients** (`lem:bohr-annihilator`).  Let `S` be a
C₀-semigroup on `E` (the paper's `E = W` or `X`) whose orbits are real analytic on `(0, ∞)`,
with growth bound `‖S t‖ ≤ M e^{σ t}`, and let `ωₗ` be pairwise distinct bounded frequencies
with `sₗ = σ + i ωₗ ∈ ρ(A_E)`.  Let `c, ζ ∈ E_ℂ` and let `(dₗ)` be absolutely summable with
`⟨ζ, S(t) c⟩ + e^{σ t} ∑ₗ dₗ e^{i ωₗ t} = 0` for a.e. `t` in a nonempty open subinterval
`(a, b)` of `(0, ∞)`.  Then `dₗ = 0` for every `ℓ`. -/
theorem bohr_annihilator (S : C0Semigroup ℝ E)
    (hS_an : ∀ x : E, AnalyticOnNhd ℝ (fun t => S.real t x) (Ioi 0)) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (σ * t))
    {ι : Type*} [Countable ι] {ω : ι → ℝ} (hω : Function.Injective ω)
    (hωb : ∃ Ω : ℝ, ∀ l, |ω l| ≤ Ω)
    (hρ : ∀ l, (σ : ℂ) + ω l * Complex.I ∈ resolventSet S.generator.complexify)
    (c ζ : Complexification E) {d : ι → ℂ} (hd : Summable fun l => ‖d l‖)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ⟪ζ, (S.real t).complexify c⟫_bil +
        Real.exp (σ * t) * ∑' l, d l * Complex.exp (ω l * t * Complex.I) = 0) :
    d = 0 := by
  obtain ⟨Ω, hΩ⟩ := hωb
  -- the harmonic part, written as `bohrSeries`
  have hser : ∀ t : ℝ, ∑' l, d l * Complex.exp (ω l * t * Complex.I) = bohrSeries ω d t := by
    intro t
    rw [bohrSeries_apply]
    exact tsum_congr fun l => by rw [smul_eq_mul, mul_comm]
  -- analyticity of the identity on `(0, ∞)`
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => ⟪ζ, (S.real t).complexify c⟫_bil +
      Real.exp (σ * t) * ∑' l, d l * Complex.exp (ω l * t * Complex.I)) (Ioi 0) := by
    intro t ht
    refine (S.analyticOnNhd_pairing_complexify hS_an c ζ t ht).add ?_
    have h1 : AnalyticAt ℝ (fun t : ℝ => ((Real.exp (σ * t) : ℝ) : ℂ)) t :=
      (Complex.ofRealCLM.analyticAt _).comp
        (analyticAt_rexp.comp (analyticAt_const.mul analyticAt_id))
    have h2 : AnalyticAt ℝ (fun t : ℝ => ∑' l, d l * Complex.exp (ω l * t * Complex.I)) t := by
      have := analyticOnNhd_harmonic hΩ hd t (mem_univ t)
      simp_rw [hser]
      simpa [bohrSeries_apply] using this
    exact h1.mul h2
  have hF0 := eqOn_zero_of_ae_Ioo hF (convex_Ioi (0 : ℝ)).isPreconnected hab
    (fun t ht => lt_of_le_of_lt ha ht.1) h
  -- divide by `e^{σ t}`
  set g : ℝ → ℂ := fun t => ((Real.exp (-(σ * t)) : ℝ) : ℂ) * ⟪ζ, (S.real t).complexify c⟫_bil
    with hg
  have hgd : ∀ t, 0 < t → g t + bohrSeries ω d t = 0 := by
    intro t ht
    have := hF0 ht
    simp only [Pi.zero_apply] at this
    rw [← hser, hg]
    have e1 : ((Real.exp (-(σ * t)) : ℝ) : ℂ) * ((Real.exp (σ * t) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    calc ((Real.exp (-(σ * t)) : ℝ) : ℂ) * ⟪ζ, (S.real t).complexify c⟫_bil +
          ∑' l, d l * Complex.exp (ω l * t * Complex.I)
        = ((Real.exp (-(σ * t)) : ℝ) : ℂ) * (⟪ζ, (S.real t).complexify c⟫_bil +
          Real.exp (σ * t) * ∑' l, d l * Complex.exp (ω l * t * Complex.I)) := by
          rw [mul_add, ← mul_assoc, e1, one_mul]
      _ = 0 := by rw [this, mul_zero]
  refine eq_zero_of_add_bohrSeries_ae_eq_zero hd hω (g := g) (fun l => ?_)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => hgd t ht)
  -- the free response has Bohr mean zero
  set s : ℂ := (σ : ℂ) + ω l * Complex.I with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  obtain ⟨C, hC⟩ := S.exists_bound_integral_pairing (s := s) (M := M)
    (by rw [hsre]; exact hS) (hρ l) c ζ
  refine hasBohrMean_zero_of_bounded_integral (C := C) ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  convert hC R hR using 3
  funext t
  rw [smul_eq_mul, hg]
  simp only
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  rw [hs_def]; push_cast; ring

end C0Semigroup

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

open scoped Classical in
/-- The **smoothing operator** `S(δ) ∈ L(X, W)` (`app:analytic-universal-sufficiency`; it exists
for `δ > 0` under analyticity and `hyp:compat`, `System.exists_smoothing`; junk `0` otherwise). -/
def smoothing (δ : ℝ) : X →L[ℝ] W :=
  if h : ∃ K : X →L[ℝ] W, ∀ x : X, sys.ιW (K x) = sys.SX.real δ x then h.choose else 0

open scoped Classical in
/-- `B† : D(A†) → U` (`System.Bstar`), extended by `0` outside `D(A†)`. -/
def BstarExt (x : X) : U :=
  if hx : x ∈ sys.A.adjoint.domain then sys.Bstar ⟨x, hx⟩ else 0

/-- **`ψ_η(r) = B† S(r)† η`** (`lem:transfer-laplace`) for `η ∈ W ≅ W'` and `r > 0`: `S(r)† η`
is the Hilbert adjoint of `S(r) ∈ L(X, W)` applied to `η`, which lies in `D(A†)`
(`adjoint_smoothing_mem_domain`). -/
def psi (η : W) (r : ℝ) : U :=
  sys.BstarExt (ContinuousLinearMap.adjoint (sys.smoothing r) η)

/-- `ψ_η` for complex `η ∈ W_ℂ`: `ψ_{re η} + i ψ_{im η}`. -/
def psiC (η : Complexification W) (r : ℝ) : Complexification U :=
  ⟨sys.psi η.re r, sys.psi η.im r⟩

variable {sys}

/-- `sys.smoothing δ` is `S(δ) ∈ L(X, W)` for `δ > 0`. -/
theorem ιW_smoothing (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ : ℝ} (hδ : 0 < δ) (x : X) :
    sys.ιW (sys.smoothing δ x) = sys.SX.real δ x := by
  have h := exists_smoothing hA hc hδ
  rw [smoothing, dite_eq_left h]
  exact h.choose_spec x

/-! ### Smoothing -/

/-- `S(δ + ρ) = S(δ) S(ρ)` as operators `X → W` (`δ > 0`, `ρ ≥ 0`). -/
theorem smoothing_add (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : 0 ≤ ρ) : sys.smoothing (δ + ρ) = (sys.smoothing δ).comp (sys.SX.real ρ) := by
  ext x
  apply sys.ιW_injective
  rw [ιW_smoothing hA hc (by linarith), ContinuousLinearMap.comp_apply, ιW_smoothing hA hc hδ,
    ← sys.SX.real_add_apply hδ.le hρ]

/-- `S(δ) ιW = S_W(δ)` on `W` (`δ > 0`). -/
theorem smoothing_comp_ιW (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ : ℝ} (hδ : 0 < δ) :
    (sys.smoothing δ).comp sys.ιW = sys.SW.real δ := by
  ext w
  apply sys.ιW_injective
  rw [ContinuousLinearMap.comp_apply, ιW_smoothing hA hc hδ, ιW_SW]

/-- `ιW S(δ) = S(δ)` on `X` (`δ > 0`; operator form of `ιW_smoothing`). -/
theorem ιW_comp_smoothing (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ : ℝ} (hδ : 0 < δ) :
    sys.ιW.comp (sys.smoothing δ) = sys.SX.real δ := by
  ext x; exact ιW_smoothing hA hc hδ x

/-- `S(δ + ρ)† η = S(ρ)† S(δ)† η` for `η ∈ W` (`δ > 0`, `ρ ≥ 0`). -/
theorem adjoint_smoothing_add (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (η : W) :
    ContinuousLinearMap.adjoint (sys.smoothing (δ + ρ)) η =
      sys.SX.adjoint.real ρ (ContinuousLinearMap.adjoint (sys.smoothing δ) η) := by
  rw [smoothing_add hA hc hδ hρ, ContinuousLinearMap.adjoint_comp, C0Semigroup.adjoint_real]
  rfl

/-- `S(r)† η ∈ D(A†)` for `η ∈ W'` and `r > 0` (dualise `S(r/2) : X → W`, then a further positive
time maps `X` into `D(A†)`). -/
theorem adjoint_smoothing_mem_domain (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {r : ℝ}
    (hr : 0 < r) (η : W) :
    ContinuousLinearMap.adjoint (sys.smoothing r) η ∈ sys.A.adjoint.domain := by
  have e : r = r / 2 + r / 2 := by ring
  rw [e, adjoint_smoothing_add hA hc (half_pos hr) (half_pos hr).le]
  exact (hA.adjoint_real_mem_adjoint_domain (half_pos hr) _).1

/-- `X ↪ W'`: for `ξ ∈ X` (acting on `W` through `ιW† ξ`) and `r > 0`,
`ψ_ξ(r) = B† S(r)† ξ` with the adjoint semigroup on `X`. -/
theorem psi_adjoint_ιW (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {r : ℝ} (hr : 0 < r) (ξ : X) :
    sys.psi (ContinuousLinearMap.adjoint sys.ιW ξ) r = sys.BstarExt (sys.SX.adjoint.real r ξ) := by
  rw [psi, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    ιW_comp_smoothing hA hc hr, C0Semigroup.adjoint_real]

/-- `BstarExt` is `B†` on `D(A†)`. -/
theorem BstarExt_eq {x : X} (hx : x ∈ sys.A.adjoint.domain) :
    sys.BstarExt x = sys.Bstar ⟨x, hx⟩ := by
  rw [BstarExt, dite_eq_left hx]

/-- For `ε > 0`, `x ↦ B† S(ε)† x` is a bounded operator `P_ε ∈ L(X, U)` (graph-norm bound of
`B†` and `A† S(ε)† = (A S(ε))†`, analyticity). -/
theorem exists_clm_BstarExt (hA : sys.SX.IsAnalytic) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[ℝ] U, ∀ x, P x = sys.BstarExt (sys.SX.adjoint.real ε x) := by
  have hmem : ∀ x, sys.SX.adjoint.real ε x ∈ sys.A.adjoint.domain := fun x =>
    (hA.adjoint_real_mem_adjoint_domain hε x).1
  let f : X →ₗ[ℝ] U := sys.Bstar.toFun ∘ₗ
    ((sys.SX.adjoint.real ε : X →ₗ[ℝ] X).codRestrict sys.Bstar.domain hmem)
  have hf : ∀ x, f x = sys.BstarExt (sys.SX.adjoint.real ε x) := fun x =>
    (BstarExt_eq (hmem x)).symm
  obtain ⟨c, hc0, hc⟩ := exists_norm_Bstar_le (sys := sys)
  refine ⟨f.mkContinuous (c * (‖sys.SX.real ε‖ + ‖hA.gen ε‖)) fun x => ?_, fun x => hf x⟩
  rw [hf, BstarExt_eq (hmem x)]
  refine (hc ⟨_, hmem x⟩).trans ?_
  obtain ⟨h1, h2⟩ := hA.adjoint_real_mem_adjoint_domain hε x
  have h2' : sys.A.adjoint ⟨_, hmem x⟩ = ContinuousLinearMap.adjoint (hA.gen ε) x := h2
  rw [h2']
  have n1 : ‖sys.SX.adjoint.real ε x‖ ≤ ‖sys.SX.real ε‖ * ‖x‖ := by
    rw [C0Semigroup.adjoint_real]
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  have n2 : ‖ContinuousLinearMap.adjoint (hA.gen ε) x‖ ≤ ‖hA.gen ε‖ * ‖x‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  calc c * (‖sys.SX.adjoint.real ε x‖ + ‖ContinuousLinearMap.adjoint (hA.gen ε) x‖)
      ≤ c * (‖sys.SX.real ε‖ * ‖x‖ + ‖hA.gen ε‖ * ‖x‖) := by gcongr
    _ = c * (‖sys.SX.real ε‖ + ‖hA.gen ε‖) * ‖x‖ := by ring

/-- `ψ_η(δ + ρ) = B† S(ρ)† S(δ)† η` (`δ > 0`, `ρ ≥ 0`). -/
theorem psi_add (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (η : W) : sys.psi η (δ + ρ) =
      sys.BstarExt (sys.SX.adjoint.real ρ (ContinuousLinearMap.adjoint (sys.smoothing δ) η)) := by
  rw [psi, adjoint_smoothing_add hA hc hδ hρ]

/-- `ψ_η(δ + ε + ρ) = P_ε S(ρ)† S(δ)† η` with `P_ε = B† S(ε)†` (`exists_clm_BstarExt`). -/
theorem psi_eq_clm (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ ε ρ : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hρ : 0 ≤ ρ) {P : X →L[ℝ] U}
    (hP : ∀ x, P x = sys.BstarExt (sys.SX.adjoint.real ε x)) (η : W) :
    sys.psi η (δ + ε + ρ) =
      P (sys.SX.adjoint.real ρ (ContinuousLinearMap.adjoint (sys.smoothing δ) η)) := by
  rw [add_assoc, psi_add hA hc hδ (by linarith), sys.SX.adjoint.real_add_apply hε.le hρ, hP]

/-- The orbits of `S` on `W` are real analytic on `(0, ∞)` under analyticity and
`hyp:compat` (`S(t) c` is analytic into `D(A) ↪ W`; the case `E = W` of
`lem:bohr-annihilator`). -/
theorem analyticOnNhd_SW (hA : sys.SX.IsAnalytic) (hc : sys.Compat) (w : W) :
    AnalyticOnNhd ℝ (fun t => sys.SW.real t w) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀ : 0 < t₀ := ht₀
  have hδ : 0 < t₀ / 2 := half_pos ht₀
  have h1 : AnalyticAt ℝ (fun t => sys.SX.real (t - t₀ / 2) (sys.ιW w)) t₀ := by
    have := hA.analyticOnNhd (sys.ιW w) (t₀ - t₀ / 2) (by simp only [mem_Ioi]; linarith)
    exact this.comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  have h2 := AnalyticAt.comp (f := fun t => sys.SX.real (t - t₀ / 2) (sys.ιW w))
    ((sys.smoothing (t₀ / 2)).analyticAt _) h1
  refine h2.congr ?_
  filter_upwards [lt_mem_nhds (show t₀ / 2 < t₀ by linarith)] with t ht
  apply sys.ιW_injective
  simp only [Function.comp_apply]
  rw [ιW_smoothing hA hc hδ, ← sys.SX.real_add_apply hδ.le (sub_nonneg.2 ht.le), add_sub_cancel,
    ιW_SW]

/-- `ψ_η` is real analytic on `(0, ∞)` (`lem:transfer-laplace`). -/
theorem analyticOnNhd_psi (hA : sys.SX.IsAnalytic) (hc : sys.Compat) (η : W) :
    AnalyticOnNhd ℝ (sys.psi η) (Ioi 0) := by
  intro r₀ hr₀
  have hr₀ : 0 < r₀ := hr₀
  have hδ : 0 < r₀ / 4 := by positivity
  obtain ⟨P, hP⟩ := exists_clm_BstarExt hA hδ
  set ξ := ContinuousLinearMap.adjoint (sys.smoothing (r₀ / 4)) η
  have h1 : AnalyticAt ℝ (fun r => sys.SX.adjoint.real (r - r₀ / 2) ξ) r₀ := by
    have := hA.adjoint.analyticOnNhd ξ (r₀ - r₀ / 2) (by simp only [mem_Ioi]; linarith)
    exact this.comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  have h2 := AnalyticAt.comp (f := fun r => sys.SX.adjoint.real (r - r₀ / 2) ξ) (P.analyticAt _) h1
  refine h2.congr ?_
  filter_upwards [lt_mem_nhds (show r₀ / 2 < r₀ by linarith)] with r hr
  have := psi_eq_clm hA hc hδ hδ (sub_nonneg.2 hr.le) hP η
  rw [show r₀ / 4 + r₀ / 4 + (r - r₀ / 2) = r by ring] at this
  rw [this]; rfl

/-- `‖ψ_η(r)‖ = O(e^{σ r})` for `r ≥ 1` (proof of `lem:transfer-laplace`: smoothing over a fixed
positive time and `eq:analytic-W-growth-bound`). -/
theorem norm_psi_le (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) (η : W) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ‖sys.psi η r‖ ≤ C * Real.exp (σ * r) := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨P, hP⟩ := exists_clm_BstarExt hA hh
  set ξ := ContinuousLinearMap.adjoint (sys.smoothing (1 / 2)) η
  refine ⟨‖P‖ * M * Real.exp (-σ) * ‖ξ‖, fun r hr => ?_⟩
  have e := psi_eq_clm hA hc hh hh (sub_nonneg.2 hr) hP η
  rw [show (1 / 2 : ℝ) + 1 / 2 + (r - 1) = r by ring] at e
  rw [e]
  have hSr : ‖sys.SX.adjoint.real (r - 1)‖ ≤ M * Real.exp (σ * (r - 1)) := by
    rw [C0Semigroup.adjoint_real, LinearIsometryEquiv.norm_map,
      sys.SX.real_of_nonneg (sub_nonneg.2 hr)]
    exact hS _
  calc ‖P (sys.SX.adjoint.real (r - 1) ξ)‖
      ≤ ‖P‖ * (‖sys.SX.adjoint.real (r - 1)‖ * ‖ξ‖) :=
        (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _)) (norm_nonneg _))
    _ ≤ ‖P‖ * (M * Real.exp (σ * (r - 1)) * ‖ξ‖) := by gcongr
    _ = ‖P‖ * M * Real.exp (-σ) * ‖ξ‖ * Real.exp (σ * r) := by
        rw [show σ * (r - 1) = -σ + σ * r by ring, Real.exp_add]; ring

/-! ### Duality -/

/-- `ιW† S(ε)† η = S_W(ε)† η` for `η ∈ W` (the smoothing operator read on `W`). -/
theorem adjoint_ιW_adjoint_smoothing (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {ε : ℝ}
    (hε : 0 < ε) (η : W) :
    ContinuousLinearMap.adjoint sys.ιW (ContinuousLinearMap.adjoint (sys.smoothing ε) η) =
      ContinuousLinearMap.adjoint (sys.SW.real ε) η := by
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    smoothing_comp_ιW hA hc hε]

/-- `L_t† S_W(ε)† η = ψ_η(ε + t - ·)` a.e. on `(0, t)` (`ε > 0`), from the `X`-duality
`System.adjoint_Lop_ae_eq` at `S(ε)† η ∈ D(A†)`. -/
theorem adjoint_Lop_SW_ae_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (η : W) :
    ⇑(ContinuousLinearMap.adjoint (sys.Lop t) (ContinuousLinearMap.adjoint (sys.SW.real ε) η))
      =ᵐ[μI t] fun r => sys.psi η (ε + (t - r)) := by
  have hξ := adjoint_smoothing_mem_domain hA hc hε η
  have h := adjoint_Lop_ae_eq hH1 hT t hξ
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    adjoint_ιW_adjoint_smoothing hA hc hε] at h
  refine h.trans ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [psi_add hA hc hε (sub_nonneg.2 hr.2), BstarExt_eq]

/-- **Duality** in `L²`: `(L_t† η)(r) = ψ_η(t - r)` for a.e. `r ∈ (0, t)`, `η ∈ W ≅ W'`. -/
theorem adjoint_Lop_ae_eq_psi {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) (t : ℝ) (η : W) :
    ⇑(ContinuousLinearMap.adjoint (sys.Lop t) η) =ᵐ[μI t] fun r => sys.psi η (t - r) := by
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε_def
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set G := ContinuousLinearMap.adjoint (sys.Lop t)
  set f : ℕ → L2 U t := fun n => G (ContinuousLinearMap.adjoint (sys.SW.real (ε n)) η)
  have hf : Tendsto f atTop (𝓝 (G η)) := by
    refine (G.continuous.tendsto η).comp ?_
    have h1 : Tendsto (fun s : ℝ => ContinuousLinearMap.adjoint (sys.SW.real s) η) (𝓝 0)
        (𝓝 η) := by
      have := (sys.SW.adjoint.continuous_real_apply η).tendsto 0
      simpa using this
    exact h1.comp hε0
  have hfe : ∀ n, ⇑(f n) =ᵐ[μI t] fun r => sys.psi η (ε n + (t - r)) := fun n =>
    adjoint_Lop_SW_ae_eq hH1 hT hA hc (hε n) t η
  have hm2 : TendstoInMeasure (μI t) (fun n r => sys.psi η (ε n + (t - r))) atTop ⇑(G η) :=
    (tendstoInMeasure_of_tendsto_Lp hf).congr_left hfe
  have hm3 : TendstoInMeasure (μI t) (fun n r => sys.psi η (ε n + (t - r))) atTop
      (fun r => sys.psi η (t - r)) := by
    refine tendstoInMeasure_of_tendsto_ae
      (fun n => (Lp.aestronglyMeasurable (f n)).congr (hfe n)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume t)] with r hr hrt
    have hpos : 0 < t - r := sub_pos.2 (lt_of_le_of_ne hr.2 hrt)
    have hcont := (analyticOnNhd_psi hA hc η (t - r) hpos).continuousAt
    refine hcont.tendsto.comp ?_
    simpa using hε0.add_const (t - r)
  exact tendstoInMeasure_ae_unique hm2 hm3

/-- `ψ_η ∈ L²_loc([0, ∞); U)` (`lem:transfer-laplace`). -/
theorem memLp_psi {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) (η : W) (τ : ℝ) : MemLp (sys.psi η) 2 (μI τ) := by
  have h1 : MemLp (fun r => sys.psi η (τ - r)) 2 (μI τ) :=
    (Lp.memLp (ContinuousLinearMap.adjoint (sys.Lop τ) η)).ae_eq
      (adjoint_Lop_ae_eq_psi hH1 hT hA hc τ η)
  have := h1.comp_measurePreserving (measurePreserving_sub_left_μI τ)
  simpa [Function.comp_def] using this

set_option linter.unusedVariables false in
/-- **Duality** (proof of `lem:transfer-laplace`): `(L_t† η)(τ) = ψ_η(t - τ)`, i.e.
`⟨η, L_t u⟩_{W', W} = ∫₀ᵗ ⟨ψ_η(t - r), u(r)⟩ dr` for `η ∈ W ≅ W'`. -/
theorem inner_L_eq_integral_psi {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {t : ℝ} (ht : 0 ≤ t) {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) (η : W) :
    ⟪η, sys.L t u⟫_ℝ = ∫ r in Ioc 0 t, ⟪sys.psi η (t - r), u r⟫_ℝ := by
  have hL : sys.L t u = sys.Lop t (hu.toLp u) := by
    rw [Lop_apply hH1 hT, L_congr_ae hu.coeFn_toLp]
  rw [hL, ← ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [adjoint_Lop_ae_eq_psi hH1 hT hA hc t η, hu.coeFn_toLp] with r h1 h2
  rw [h1, h2]

/-- `r ↦ ⟪ψ_η(t - r), g r⟫` is integrable on `(0, t]` for `g ∈ L²(0, t; U)`. -/
theorem integrable_inner_psi {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) (t : ℝ) (η : W) {g : ℝ → U} (hg : MemLp g 2 (μI t)) :
    Integrable (fun r => ⟪sys.psi η (t - r), g r⟫_ℝ) (μI t) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (ContinuousLinearMap.adjoint (sys.Lop t) η)
    (hg.toLp g)).congr ?_
  filter_upwards [adjoint_Lop_ae_eq_psi hH1 hT hA hc t η, hg.coeFn_toLp] with r h1 h2
  rw [h1, h2]

/-! ### Complex test vectors -/

/-- `ψ_η ∈ L²_loc([0, ∞); U_ℂ)` for complex `η ∈ W_ℂ`. -/
theorem memLp_psiC {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) (η : Complexification W) (τ : ℝ) : MemLp (sys.psiC η) 2 (μI τ) := by
  have h1 := memLp_psi hH1 hT hA hc η.re τ
  have h2 := memLp_psi hH1 hT hA hc η.im τ
  have e : sys.psiC η = fun r => (ofRealCLM : U →L[ℝ] Complexification U) (sys.psi η.re r) +
      Complex.I • (ofRealCLM : U →L[ℝ] Complexification U) (sys.psi η.im r) := by
    funext r; rw [psiC, mk_eq_add_I_smul]; rfl
  rw [e]
  exact (ofRealCLM.comp_memLp' h1).add ((ofRealCLM.comp_memLp' h2).const_smul Complex.I)

/-- The `U_ℂ`-valued Laplace integral of `ψ_η` converges absolutely on `Re s ≥ σ'` for every
`σ' > σ`. -/
theorem laplaceIntegrable_psiC_vec {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) (η : Complexification W)
    {σ' : ℝ} (hσ' : σ < σ') : LaplaceIntegrable (sys.psiC η) σ' := by
  obtain ⟨C₁, hC₁⟩ := norm_psi_le hA hc hS η.re
  obtain ⟨C₂, hC₂⟩ := norm_psi_le hA hc hS η.im
  refine laplaceIntegrable_of_le_exp (C := C₁ + C₂) (σ₀ := σ) (fun T' => ?_) ?_ hσ'
  · exact (memLp_psiC hH1 hT hA hc η T').integrable one_le_two
  · filter_upwards [eventually_ge_atTop 1] with r hr
    refine (norm_le_norm_re_add_norm_im _).trans ?_
    have := add_le_add (hC₁ r hr) (hC₂ r hr)
    simp only [psiC]
    linarith

/-- The Laplace integral of `⟨ψ_η, v⟩` converges absolutely on `Re s ≥ σ'` for every `σ' > σ`. -/
theorem laplaceIntegrable_psiC {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) (η : Complexification W)
    (v : Complexification U) {σ' : ℝ} (hσ' : σ < σ') :
    LaplaceIntegrable (fun r => ⟪sys.psiC η r, v⟫_bil) σ' := by
  have := (laplaceIntegrable_psiC_vec hH1 hT hA hc hS η hσ').comp_clm (pairingCLM v)
  convert this using 2 with r
  rw [pairingCLM_apply, pairing_comm]

/-- **Complex duality**: `⟨η, L_t f⟩ = ∫₀ᵗ ⟨ψ_η(t - r), f(r)⟩ dr` for `η ∈ W_ℂ` and
`f ∈ L²(0, t; U_ℂ)` (bilinear pairings). -/
theorem pairing_Lc_eq_integral {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) {t : ℝ} (ht : 0 ≤ t) {f : ℝ → Complexification U}
    (hre : MemLp (fun r => (f r).re) 2 (μI t)) (him : MemLp (fun r => (f r).im) 2 (μI t))
    (η : Complexification W) :
    ⟪η, sys.Lc t f⟫_bil = ∫ r in Ioc 0 t, ⟪sys.psiC η (t - r), f r⟫_bil := by
  have i11 := integrable_inner_psi hH1 hT hA hc t η.re hre
  have i12 := integrable_inner_psi hH1 hT hA hc t η.re him
  have i21 := integrable_inner_psi hH1 hT hA hc t η.im hre
  have i22 := integrable_inner_psi hH1 hT hA hc t η.im him
  have e : ∀ r, ⟪sys.psiC η (t - r), f r⟫_bil =
      ((⟪sys.psi η.re (t - r), (f r).re⟫_ℝ - ⟪sys.psi η.im (t - r), (f r).im⟫_ℝ : ℝ) : ℂ) +
      ((⟪sys.psi η.re (t - r), (f r).im⟫_ℝ + ⟪sys.psi η.im (t - r), (f r).re⟫_ℝ : ℝ) : ℂ) *
        Complex.I := by
    intro r; apply Complex.ext <;> simp [psiC]
  have j1 : Integrable (fun r => ((⟪sys.psi η.re (t - r), (f r).re⟫_ℝ -
      ⟪sys.psi η.im (t - r), (f r).im⟫_ℝ : ℝ) : ℂ)) (μI t) := (i11.sub i22).ofReal
  have j2 : Integrable (fun r => ((⟪sys.psi η.re (t - r), (f r).im⟫_ℝ +
      ⟪sys.psi η.im (t - r), (f r).re⟫_ℝ : ℝ) : ℂ) * Complex.I) (μI t) :=
    ((i12.add i21).ofReal).mul_const _
  simp_rw [e]
  rw [integral_add j1 j2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sub i11 i22, integral_add i12 i21,
    ← inner_L_eq_integral_psi hH1 hT hA hc ht hre η.re,
    ← inner_L_eq_integral_psi hH1 hT hA hc ht him η.re,
    ← inner_L_eq_integral_psi hH1 hT hA hc ht hre η.im,
    ← inner_L_eq_integral_psi hH1 hT hA hc ht him η.im]
  apply Complex.ext <;> simp [Lc]

/-- **`eq:analytic-transfer-laplace`** (`lem:transfer-laplace`): for `η ∈ W'_ℂ`, `Re s > σ` and
`v ∈ U_ℂ`, `⟨η, 𝐇(s) v⟩_{W', W} = ∫₀^∞ e^{-s r} ⟨ψ_η(r), v⟩ dr`. -/
theorem inner_transfer_eq_laplace {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) (η : Complexification W) {s : ℂ}
    (hs : σ < s.re) (v : Complexification U) :
    ⟪η, sys.transfer s v⟫_bil = laplace (fun r => ⟪sys.psiC η r, v⟫_bil) s := by
  have hsρ : s ∈ resolventSet sys.A.complexify := sys.SX.mem_resolventSet_complexify hS hs
  obtain ⟨MW, -, hMW⟩ := exists_growth_W hA hc hS
  set F : ℝ → ℂ := fun r => ⟪sys.psiC η r, v⟫_bil with hF_def
  set H := sys.transfer s v with hH_def
  have hF : LaplaceIntegrable F s.re := laplaceIntegrable_psiC hH1 hT hA hc hS η v hs
  have key : ∀ t : ℝ, 0 ≤ t → ∫ r in Ioc (0 : ℝ) t, Complex.exp (-(s * r)) • F r =
      ⟪η, H⟫_bil - Complex.exp (-(s * t)) * ⟪η, (sys.SW.real t).complexify H⟫_bil := by
    intro t ht
    have hcont : Continuous fun r : ℝ => Complex.exp (s * r) • v := by fun_prop
    have h1 := pairing_Lc_eq_integral hH1 hT hA hc ht (f := fun r => Complex.exp (s * r) • v)
      (memLp_μI_of_continuousOn (Complexification.continuous_re.comp hcont).continuousOn)
      (memLp_μI_of_continuousOn (Complexification.continuous_im.comp hcont).continuousOn) η
    rw [Lc_cexp_smul hH1 hT hc hsρ ht v, pairing_sub_right, pairing_smul_right] at h1
    have h2 : ∫ r in Ioc 0 t, ⟪sys.psiC η (t - r), Complex.exp (s * r) • v⟫_bil =
        Complex.exp (s * t) * ∫ r in Ioc 0 t, Complex.exp (-(s * r)) • F r := by
      rw [← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le ht,
        ← intervalIntegral.integral_const_mul]
      have hc' := intervalIntegral.integral_comp_sub_left
        (fun r : ℝ => Complex.exp (s * (t - r)) * F r) t (a := 0) (b := t)
      simp only [sub_self, sub_zero, Complex.ofReal_sub] at hc'
      calc ∫ r in (0 : ℝ)..t, ⟪sys.psiC η (t - r), Complex.exp (s * r) • v⟫_bil
          = ∫ r in (0 : ℝ)..t, Complex.exp (s * (t - (t - r))) * F (t - r) := by
            refine intervalIntegral.integral_congr fun r _ => ?_
            simp only [hF_def, pairing_smul_right, sub_sub_cancel]
        _ = ∫ r in (0 : ℝ)..t, Complex.exp (s * (t - r)) * F r := hc'
        _ = ∫ r in (0 : ℝ)..t, Complex.exp (s * t) * (Complex.exp (-(s * r)) • F r) := by
            refine intervalIntegral.integral_congr fun r _ => ?_
            simp only [smul_eq_mul]
            rw [← mul_assoc, ← Complex.exp_add]
            ring_nf
    rw [h2] at h1
    have hexp : Complex.exp (-(s * t)) * Complex.exp (s * t) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (-Complex.exp (-(s * t))) * h1 +
      (⟪η, H⟫_bil - ∫ r in Ioc 0 t, Complex.exp (-(s * r)) • F r) * hexp
  have hlim1 := tendsto_setIntegral_Ioc_laplace hF (le_refl s.re)
  have hlim2 : Tendsto (fun t : ℝ => ⟪η, H⟫_bil -
      Complex.exp (-(s * t)) * ⟪η, (sys.SW.real t).complexify H⟫_bil) atTop
      (𝓝 ⟪η, H⟫_bil) := by
    have h0 : Tendsto (fun t : ℝ => Complex.exp (-(s * t)) *
        ⟪η, (sys.SW.real t).complexify H⟫_bil) atTop (𝓝 0) := by
      have hδ : 0 < s.re - σ := sub_pos.2 hs
      have hb : Tendsto (fun t : ℝ => MW * ‖η‖ * ‖H‖ * Real.exp (-((s.re - σ) * t))) atTop
          (𝓝 0) := by
        have : Tendsto (fun t : ℝ => Real.exp (-((s.re - σ) * t))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp
            (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδ))
        simpa using this.const_mul (MW * ‖η‖ * ‖H‖)
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_ge_atTop 0] with t ht
      rw [norm_mul, Complex.norm_exp]
      have h1 : (-(s * t)).re = -(s.re * t) := by simp
      rw [h1]
      have h2 : ‖⟪η, (sys.SW.real t).complexify H⟫_bil‖ ≤
          ‖η‖ * (MW * Real.exp (σ * t) * ‖H‖) := by
        refine (norm_pairing_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (ContinuousLinearMap.norm_complexify_apply_le _ _).trans ?_
        gcongr
        rw [sys.SW.real_of_nonneg ht]; exact hMW _
      calc Real.exp (-(s.re * t)) * ‖⟪η, (sys.SW.real t).complexify H⟫_bil‖
          ≤ Real.exp (-(s.re * t)) * (‖η‖ * (MW * Real.exp (σ * t) * ‖H‖)) := by gcongr
        _ = MW * ‖η‖ * ‖H‖ * Real.exp (-((s.re - σ) * t)) := by
            rw [show -((s.re - σ) * t) = -(s.re * t) + σ * t by ring, Real.exp_add]; ring
    simpa using tendsto_const_nhds.sub h0
  exact tendsto_nhds_unique
    (hlim2.congr' ((eventually_ge_atTop 0).mono fun t ht => (key t ht).symm)) hlim1

/-- `ψ_η` vanishing a.e. on some `(0, ε)` vanishes on `(0, ∞)` (real analyticity). -/
theorem psi_eq_zero_of_ae (hA : sys.SX.IsAnalytic) (hc : sys.Compat) (η : W) {ε : ℝ}
    (hε : 0 < ε) (h : ∀ᵐ r ∂(volume.restrict (Ioo 0 ε)), sys.psi η r = 0) {r : ℝ}
    (hr : 0 < r) : sys.psi η r = 0 :=
  eqOn_zero_of_ae_Ioo (analyticOnNhd_psi hA hc η) (convex_Ioi (0 : ℝ)).isPreconnected hε
    Ioo_subset_Ioi_self h hr

/-- **A vanishing transform** (`lem:transfer-laplace`): if `⟨η, 𝐇(s) v⟩ = 0` for every `Re s > σ`
and `v ∈ U_ℂ`, then `ψ_η ≡ 0` on `(0, ∞)` and `η` annihilates `im L_τ` for every `τ > 0`
(weak uniqueness of the Laplace transform in `U_ℂ`; the proof does not use the separability of
`U`). -/
theorem psiC_eq_zero_of_inner_transfer_eq_zero [TopologicalSpace.SeparableSpace U] {T : ℝ}
    (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) {η : Complexification W}
    (h0 : ∀ s : ℂ, σ < s.re → ∀ v : Complexification U, ⟪η, sys.transfer s v⟫_bil = 0) :
    (∀ r : ℝ, 0 < r → sys.psiC η r = 0) ∧
      ∀ (τ : ℝ) (u : ℝ → U), 0 < τ → MemLp u 2 (μI τ) →
        ⟪η, ((sys.L τ u : W) : Complexification W)⟫_bil = 0 := by
  have hint := laplaceIntegrable_psiC_vec hH1 hT hA hc hS η (lt_add_one σ)
  have hae : sys.psiC η =ᵐ[volume.restrict (Ioi 0)] 0 := by
    refine ae_eq_zero_of_laplace_inner_eq_zero hint fun v s hs => ?_
    have e : (fun r => ⟪v, sys.psiC η r⟫_ℂ) = fun r => ⟪sys.psiC η r, star v⟫_bil := by
      funext r; rw [inner_eq_pairing_star, pairing_comm]
    rw [e, ← inner_transfer_eq_laplace hH1 hT hA hc hS η (by linarith) (star v)]
    exact h0 s (by linarith) (star v)
  have hae' : ∀ᵐ r ∂(volume.restrict (Ioo 0 1)), sys.psiC η r = 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hae
  have hre : ∀ r, 0 < r → sys.psi η.re r = 0 := fun r hr =>
    psi_eq_zero_of_ae hA hc η.re one_pos
      (hae'.mono fun r h => by simpa [psiC] using congrArg Complexification.re h) hr
  have him : ∀ r, 0 < r → sys.psi η.im r = 0 := fun r hr =>
    psi_eq_zero_of_ae hA hc η.im one_pos
      (hae'.mono fun r h => by simpa [psiC] using congrArg Complexification.im h) hr
  refine ⟨fun r hr => ?_, fun τ u hτ hu => ?_⟩
  · ext
    · exact hre r hr
    · exact him r hr
  have z : ∀ η' : W, (∀ r, 0 < r → sys.psi η' r = 0) →
      ∫ r in Ioc 0 τ, ⟪sys.psi η' (τ - r), u r⟫_ℝ = 0 := by
    intro η' hη'
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume τ)] with r hr hrτ
    rw [hη' _ (sub_pos.2 (lt_of_le_of_ne hr.2 hrτ)), inner_zero_left]
    rfl
  rw [pairing_ofReal_right, inner_L_eq_integral_psi hH1 hT hA hc hτ.le hu η.re,
    inner_L_eq_integral_psi hH1 hT hA hc hτ.le hu η.im, z _ hre, z _ him]
  rfl

/-- **Density in `W`** (`lem:transfer-laplace`): if `(A, B)` is approximately controllable in
time `T`, then `im L_T` is dense in `W`, `(im L_T)‾^W = W`. -/
theorem denseRange_Lop_W {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    (hc : sys.Compat) (hctrl : sys.ApproxControllable T) : DenseRange (sys.Lop T) := by
  rw [denseRange_iff_adjoint_eq_zero]
  intro η hη
  -- `ψ_η = 0` a.e. on `(0, T)`, hence on `(0, ∞)`
  have h1 : ∀ᵐ r ∂(μI T), sys.psi η (T - r) = 0 := by
    filter_upwards [adjoint_Lop_ae_eq_psi hH1 hT hA hc T η, Lp.coeFn_zero U 2 (μI T)]
      with r h1 h2
    rw [← h1, hη, h2]
    rfl
  have h2 : ∀ᵐ r ∂(μI T), sys.psi η r = 0 := by
    have := (measurePreserving_sub_left_μI T).quasiMeasurePreserving.ae h1
    simpa using this
  have hψ : ∀ r, 0 < r → sys.psi η r = 0 := fun r hr =>
    psi_eq_zero_of_ae hA hc η hT
      (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self h2) hr
  -- `ξ_r = S(r)† η ⊥ im L_T` in `X`, so `ξ_r = 0`
  have hξ : ∀ r, 0 < r → ContinuousLinearMap.adjoint (sys.smoothing r) η = 0 := by
    intro r hr
    refine (approxControllable_iff hH1 hT).1 hctrl _ fun u => ?_
    rw [Lop_apply hH1 hT, inner_L_eq_integral hH1 hT (Lp.memLp u)
      (adjoint_smoothing_mem_domain hA hc hr η)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    rw [← BstarExt_eq, ← psi_add hA hc hr (sub_nonneg.2 hρ.2),
      hψ _ (by linarith [hρ.2]), inner_zero_left]
    rfl
  -- `⟪η, S_W(r) η⟫ = ⟪ξ_r, ιW η⟫ = 0`, and `r → 0⁺`
  have h0 : ∀ r, 0 < r → ⟪η, sys.SW.real r η⟫_ℝ = 0 := by
    intro r hr
    rw [← smoothing_comp_ιW hA hc hr, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, hξ r hr, inner_zero_left]
  have hlim : Tendsto (fun r => ⟪η, sys.SW.real r η⟫_ℝ) (𝓝[>] 0) (𝓝 ⟪η, η⟫_ℝ) := by
    have hc' : Continuous fun r : ℝ => ⟪η, sys.SW.real r η⟫_ℝ :=
      continuous_const.inner (sys.SW.continuous_real_apply η)
    have := (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have : ⟪η, η⟫_ℝ = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr'
      (eventually_nhdsWithin_of_forall fun r hr => (h0 r hr).symm))
  exact inner_self_eq_zero.1 this

end System

end DataDrivenControl
