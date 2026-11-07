module

public import DataDrivenControl.Informativity.Analytic.Transfer
public import DataDrivenControl.Informativity.Harmonic

/-!
# The state expansion of a harmonic record

Paper: `app:analytic-universal-sufficiency`: `eq:analytic-qsummable`,
`eq:analytic-exp-convolution`, `eq:analytic-state-expansion`,
`eq:analytic-annihilator-expansion`, and the expansion of the window kernel identity in the
proof of (i) ⇒ (iii).

## Conventions

As in `Analytic/Transfer`: `X_ℂ = Complexification X`, `ρ(A) = resolventSet sys.A.complexify`,
`S(t)` acts on `X_ℂ` (`W_ℂ`) as `(sys.SX.real t).complexify` (`(sys.SW.real t).complexify`),
the paper's pairing is `⟪·, ·⟫_bil`, and the paper's `W'` is `W` (Riesz), with `⟨η, w⟩_{W',W}`
read as `⟪η, w⟫_bil` for `η ∈ W_ℂ`.  The harmonic input is `ū(t) = e^{σ t} h(t)` for a
`HarmonicSignal` `h` with frequencies `ωₗ = h.freq l` and coefficients `vₗ = h.coeff l`;
`sₗ = σ + i ωₗ`.

## Main declarations

* `sys.Lc t f`: the complexified control convolution `L_t f = L_t (re f) + i L_t (im f) ∈ W_ℂ`
  of a `U_ℂ`-valued input.
* `Lc_cexp_smul` (`eq:analytic-exp-convolution`):
  `L_t (e^{s ·} v) = e^{s t} 𝐇(s) v - S(t) 𝐇(s) v` in `W_ℂ`, `s ∈ ρ(A)`, `v ∈ U_ℂ`.
* `sys.stateCoeff σ h l = qₗ = 𝐇(sₗ) vₗ ∈ W_ℂ`; `summable_stateCoeff`
  (`eq:analytic-qsummable`): `∑ ‖qₗ‖_W < ∞` when `σ + i {ωₗ}‾ ⊆ ρ(A)`.
* `mild_harmonic` and `mildW_harmonic` (`eq:analytic-state-expansion`):
  `x̄(t) = S(t) c + ∑ₗ qₗ e^{sₗ t}`, `c = x₀ - ∑ₗ qₗ`, in `X_ℂ` for `x₀ ∈ X` and in `W_ℂ` for
  `x₀ ∈ W`.
* `annihilator_expansion` (`eq:analytic-annihilator-expansion`): for `x₀ ∈ W` and
  `(α, η) ∈ U_ℂ × W_ℂ`,
  `⟨α, ū(t)⟩ + ⟨η, x̄(t)⟩ = ⟨η, S(t) c⟩ + e^{σ t} ∑ₗ dₗ e^{i ωₗ t}`,
  `dₗ = ⟨α, vₗ⟩ + ⟨η, qₗ⟩`, with `∑ |dₗ| < ∞` (`summable_annihilatorCoeff`).
* `window_expansion` (proof of (i) ⇒ (iii)): for `x₀ ∈ X`, `g ∈ L²(0, T; U)`, `ξ ∈ X`,
  `∫₀ᵀ ⟨g(t), ū(s + t)⟩ dt + ⟨ξ, x̄(s)⟩ = ⟨ξ, S(s) c⟩ + e^{σ s} ∑ₗ Dₗ e^{i ωₗ s}`,
  `Dₗ = ∫₀ᵀ e^{sₗ t} ⟨g(t), vₗ⟩ dt + ⟨ξ, qₗ⟩`, with `∑ |Dₗ| < ∞`
  (`summable_windowCoeff`).

## Proof notes

* `Lc_cexp_smul` (`eq:analytic-exp-convolution`).  Instead of the finite-time Laplace identity
  on `X₋₁` applied to `B_X v`, both sides are mapped by the injective `R(a, A) ∘ ιW` for an
  admissible real `a` (`QSpec a`).  The left side becomes
  `R(a, A) L_t (e^{s ·} v) = ∫₀ᵗ e^{s r} S(t - r) Q_a v dr` (`resolvent_ιW_L`, componentwise),
  which the finite-time Laplace identity on `X_ℂ` (`C0Semigroup.integral_exp_smul_eq` for the
  complexified semigroup) turns into `e^{s t} R(s) Q_a v - S(t) R(s) Q_a v`; the right side
  becomes the same vector because `R(a) 𝐇(s) = R(s) Q_a` (`transferX_eq` and the resolvent
  identity) and `R(a)` commutes with `S(t)`.
* `summable_stateCoeff` (`eq:analytic-qsummable`): `𝐇` is continuous on the compact
  `K = σ + i {ωₗ}‾ ⊆ ρ(A)` (`differentiableOn_transfer`), hence bounded there.
* The state expansion: `ū(r) = ∑ₗ e^{sₗ r} vₗ` (`HarmonicSignal.ofReal_apply`), with
  `‖e^{sₗ r} vₗ‖ ≤ e^{|σ| t} ‖vₗ‖` on `(0, t]`.  The sum is interchanged with `L_t`
  (`hasSum_L`): the `V`-valued convolutions are integrated termwise
  (`hasSum_integral_of_summable_integral_norm`), the `W`-norms `‖L_t gₗ‖ ≤ b ‖gₗ‖_{L²}` are
  summable by `hyp:H1`, and `ιWV` is injective.  Summing `eq:analytic-exp-convolution` then
  gives `L_t ū = ∑ₗ e^{sₗ t} qₗ - S(t) ∑ₗ qₗ` (`ofReal_L_eq`); `ιW` and the pairings commute with
  the absolutely convergent sums.
* `window_expansion`: the `L²(0, T₀; U)`-integral is integrated termwise, with
  `|e^{sₗ t} ⟨g(t), vₗ⟩| ≤ e^{|σ| T₀} ‖vₗ‖ ‖g(t)‖`.

## Upstream results used

`transferX_eq`, `ιW_transfer`, `differentiableOn_transfer`, `C0Semigroup.complexify`,
`ofReal_mem_resolventSet_complexify`, `resolvent_complexify_ofReal`, `injective_ιW_complexify`
(`Analytic/Transfer`); `exists_QSpec`, `resolvent_ιW_L` (`System/ControlRealization`);
`C0Semigroup.integral_exp_smul_eq`, `resolvent_sub_resolvent`,
`C0Semigroup.resolvent_real_apply` (`Semigroup/Resolvent`); `ιWV_L`, `exists_norm_L_le`,
`integrableOn_convV` (`System/Mild`); `HarmonicSignal.ofReal_apply`,
`HarmonicSignal.summable_norm_coeff` (`Informativity/Harmonic`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

open Complexification

/-- A resolvent is injective. -/
private theorem resolvent_injective {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {A : E →ₗ.[𝕜] E} {μ : 𝕜} (hμ : μ ∈ resolventSet A) :
    Function.Injective (resolvent A μ) := by
  intro x x' hxx
  have h1 := sub_resolvent hμ x
  have h2 := sub_resolvent hμ x'
  rw [← h1, ← h2]
  congr 1
  · rw [hxx]
  · congr 1
    exact Subtype.ext hxx

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-- The **complexified control convolution** `L_t f = L_t (re f) + i L_t (im f) ∈ W_ℂ` of a
`U_ℂ`-valued input `f`. -/
def Lc (t : ℝ) (f : ℝ → Complexification U) : Complexification W :=
  ⟨sys.L t (fun r => (f r).re), sys.L t (fun r => (f r).im)⟩

/-- The coefficient `qₗ = 𝐇(sₗ) vₗ ∈ W_ℂ`, `sₗ = σ + i ωₗ`, of the state expansion
`eq:analytic-state-expansion` for the harmonic input `ū(t) = e^{σ t} h(t)`. -/
def stateCoeff (σ : ℝ) (h : HarmonicSignal U) (l : h.ι) : Complexification W :=
  sys.transfer ((σ : ℂ) + h.freq l * Complex.I) (h.coeff l)

/-- The coefficient `dₗ = ⟨α, vₗ⟩ + ⟨η, qₗ⟩` of `eq:analytic-annihilator-expansion`. -/
def annihilatorCoeff (σ : ℝ) (h : HarmonicSignal U) (α : Complexification U)
    (η : Complexification W) (l : h.ι) : ℂ :=
  ⟪α, h.coeff l⟫_bil + ⟪η, sys.stateCoeff σ h l⟫_bil

/-- The coefficient `Dₗ = ∫₀ᵀ e^{sₗ t} ⟨g(t), vₗ⟩ dt + ⟨ξ, qₗ⟩` of the window expansion (proof of
(i) ⇒ (iii) in `app:analytic-universal-sufficiency`), for `g ∈ L²(0, T; U)` and `ξ ∈ X`. -/
def windowCoeff (σ : ℝ) (h : HarmonicSignal U) {T : ℝ} (g : L2 U T) (ξ : X) (l : h.ι) : ℂ :=
  (∫ t in Ioc 0 T, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
      ⟪((g t : U) : Complexification U), h.coeff l⟫_bil) +
    ⟪(ξ : Complexification X), sys.ιW.complexify (sys.stateCoeff σ h l)⟫_bil

variable {sys}

/-- `ιW ∘ S_W(t) = S(t) ∘ ιW` on the complexifications. -/
private theorem ιW_SW_cplx (t : ℝ) (w : Complexification W) :
    sys.ιW.complexify ((sys.SW.real t).complexify w) =
      (sys.SX.real t).complexify (sys.ιW.complexify w) := by
  ext <;> simp [ιW_SW]

/-- The finite-time Laplace identity on `X_ℂ`, convolution form:
`∫₀ᵗ e^{s r} S(t - r) y dr = e^{s t} R(s) y - S(t) R(s) y` for `s ∈ ρ(A)`. -/
private theorem integral_cexp_smul_SX {s : ℂ} (hs : s ∈ resolventSet sys.A.complexify) {t : ℝ}
    (ht : 0 ≤ t) (y : Complexification X) :
    ∫ r in Ioc 0 t, Complex.exp (s * r) • (sys.SX.real (t - r)).complexify y =
      Complex.exp (s * t) • resolvent sys.A.complexify s y -
        (sys.SX.real t).complexify (resolvent sys.A.complexify s y) := by
  set Sc := sys.SX.complexify
  have hgen : Sc.generator = sys.A.complexify := sys.SX.complexify_generator
  have hs' : s ∈ resolventSet Sc.generator := hgen ▸ hs
  have hL := Sc.integral_exp_smul_eq hs' ht y
  rw [hgen] at hL
  simp only [← Complex.exp_eq_exp_ℂ, RCLike.ofReal_eq_complex_ofReal] at hL
  rw [← intervalIntegral.integral_of_le ht]
  set f : ℝ → Complexification X := fun r => Complex.exp (s * (t - r)) • Sc.real r y with hf
  calc ∫ x in (0 : ℝ)..t, Complex.exp (s * x) • (sys.SX.real (t - x)).complexify y
      = ∫ x in (0 : ℝ)..t, f (t - x) := by
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [hf]
        congr 2
        push_cast; ring
    _ = ∫ x in (0 : ℝ)..t, f x := by
        rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
    _ = Complex.exp (s * t) • ∫ x in (0 : ℝ)..t, Complex.exp (-(x * s)) • Sc.real x y := by
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [hf, smul_smul, ← Complex.exp_add]
        congr 2; ring
    _ = _ := by
        rw [hL, smul_sub, smul_smul, ← Complex.exp_add,
          show s * t + -(t * s) = 0 by ring, Complex.exp_zero, one_smul]
        rfl

/-- **`eq:analytic-exp-convolution`**: for `s ∈ ρ(A)`, `v ∈ U_ℂ` and `t ≥ 0`,
`L_t (e^{s ·} v) = e^{s t} 𝐇(s) v - S(t) 𝐇(s) v`, both sides in `W_ℂ`.  Instead of the
finite-time Laplace identity on `X₋₁`, both sides are compared after applying the injective
`R(a, A) ∘ ιW` (see the module docstring). -/
theorem Lc_cexp_smul {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) {t : ℝ} (ht : 0 ≤ t) (v : Complexification U) :
    sys.Lc t (fun r => Complex.exp (s * r) • v) =
      Complex.exp (s * t) • sys.transfer s v - (sys.SW.real t).complexify (sys.transfer s v) := by
  obtain ⟨a, ha⟩ : ∃ a, sys.QSpec a := by
    obtain ⟨r₀, hr₀⟩ := exists_QSpec hH1 hT
    exact ⟨r₀, hr₀ r₀ le_rfl⟩
  have haρ : (a : ℂ) ∈ resolventSet sys.A.complexify := ofReal_mem_resolventSet_complexify ha.1
  set P : Complexification U →L[ℂ] Complexification X := (sys.ιW.comp (sys.Q a)).complexify
    with hP
  have hRa : resolvent sys.A.complexify (a : ℂ) = (resolvent sys.A a).complexify :=
    resolvent_complexify_ofReal ha.1
  -- `R(a)` commutes with `S(t)`
  have hcomm : ∀ z, resolvent sys.A.complexify (a : ℂ) ((sys.SX.real t).complexify z) =
      (sys.SX.real t).complexify (resolvent sys.A.complexify (a : ℂ) z) := by
    intro z
    have := sys.SX.complexify.resolvent_real_apply (μ := (a : ℂ))
      ((sys.SX.complexify_generator).symm ▸ haρ) t z
    rw [C0Semigroup.complexify_generator] at this
    exact this
  -- `R(a) 𝐇(s) v = R(s) Q_a v`
  have hRH : resolvent sys.A.complexify (a : ℂ) (sys.transferX s v) =
      resolvent sys.A.complexify s (P v) := by
    rw [transferX_eq hH1 hT ha hs]
    have h' := congrArg (fun F => F (P v)) (resolvent_sub_resolvent haρ hs)
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply] at h'
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul, ← hP]
    rw [← h']; abel
  -- the components of the input are square integrable
  have hcont : Continuous fun r : ℝ => Complex.exp (s * r) • v := by fun_prop
  have hre : MemLp (fun r : ℝ => (Complex.exp (s * r) • v).re) 2 (μI t) :=
    memLp_μI_of_continuousOn (reCLM.continuous.comp hcont).continuousOn
  have him : MemLp (fun r : ℝ => (Complex.exp (s * r) • v).im) 2 (μI t) :=
    memLp_μI_of_continuousOn (imCLM.continuous.comp hcont).continuousOn
  refine injective_ιW_complexify (sys := sys) (resolvent_injective haρ ?_)
  -- the right-hand side
  have hHx : sys.ιW.complexify (sys.transfer s v) = sys.transferX s v := by
    rw [← ιW_transfer hH1 hT hc hs]; rfl
  rw [map_sub, map_smul, ιW_SW_cplx, hHx, map_sub, map_smul, hcomm, hRH]
  -- the left-hand side
  rw [← integral_cexp_smul_SX hs ht (P v)]
  have e : ∀ r : ℝ, Complex.exp (s * r) • (sys.SX.real (t - r)).complexify (P v) =
      (sys.SX.real (t - r)).complexify (P (Complex.exp (s * r) • v)) := fun r => by
    rw [map_smul, map_smul]
  simp only [e]
  have hF : IntegrableOn
      (fun r : ℝ => (sys.SX.real (t - r)).complexify (P (Complex.exp (s * r) • v))) (Ioc 0 t) := by
    refine Continuous.integrableOn_Ioc ?_
    simp only [← e]
    exact (by fun_prop : Continuous fun r : ℝ => Complex.exp (s * r)).smul
      ((sys.SX.complexify.continuous_real_apply (P v)).comp
        (continuous_const.sub continuous_id))
  rw [hRa]
  ext
  · simp only [Lc, ContinuousLinearMap.complexify_apply_re]
    rw [resolvent_ιW_L hH1 hT ha hre, integral_re hF]
    rfl
  · simp only [Lc, ContinuousLinearMap.complexify_apply_im]
    rw [resolvent_ιW_L hH1 hT ha him, integral_im hF]
    rfl

/-- **`eq:analytic-qsummable`**: if `σ + i {ωₗ}‾ ⊆ ρ(A)`, then `C_K = sup_{s ∈ K} ‖𝐇(s)‖ < ∞` on
the compact `K = σ + i {ωₗ}‾` and `∑ₗ ‖qₗ‖_W ≤ C_K ∑ₗ ‖vₗ‖ < ∞`. -/
theorem summable_stateCoeff {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify) :
    Summable fun l => ‖sys.stateCoeff σ h l‖ := by
  set K : Set ℂ := (fun ω : ℝ => (σ : ℂ) + ω * Complex.I) '' closure (Set.range h.freq)
  have hKc : IsCompact K := by
    obtain ⟨Ω, hΩ⟩ := h.exists_abs_freq_le
    have hb : Bornology.IsBounded (Set.range h.freq) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨Ω, by rintro _ ⟨l, rfl⟩; exact hΩ l⟩
    exact hb.isCompact_closure.image (by fun_prop)
  have hKρ : K ⊆ resolventSet sys.A.complexify := by
    rintro _ ⟨ω, hω, rfl⟩; exact hρ ω hω
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := sys.transfer)
    ((differentiableOn_transfer hH1 hT hc).continuousOn.mono hKρ)
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
    (h.summable_norm_coeff.mul_left C)
  calc ‖sys.stateCoeff σ h l‖
      ≤ ‖sys.transfer ((σ : ℂ) + h.freq l * Complex.I)‖ * ‖h.coeff l‖ :=
        (sys.transfer _).le_opNorm _
    _ ≤ C * ‖h.coeff l‖ :=
        mul_le_mul_of_nonneg_right (hC _ ⟨h.freq l, subset_closure ⟨l, rfl⟩, rfl⟩)
          (norm_nonneg _)

/-- `sₗ = σ + i ωₗ ∈ ρ(A)` for every frequency of `h`. -/
private theorem mem_resolventSet_freq {σ : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify) (l : h.ι) :
    (σ : ℂ) + h.freq l * Complex.I ∈ resolventSet sys.A.complexify :=
  hρ _ (subset_closure ⟨l, rfl⟩)

/-- `e^{(σ + i ω) t} = e^{σ t} e^{i ω t}`. -/
private theorem cexp_freq (σ ω t : ℝ) :
    Complex.exp (((σ : ℂ) + ω * Complex.I) * t) =
      (Real.exp (σ * t) : ℂ) * Complex.exp (ω * t * Complex.I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring

/-- `|e^{(σ + i ω) t}| = e^{σ t}`. -/
private theorem norm_cexp_freq (σ ω t : ℝ) :
    ‖Complex.exp (((σ : ℂ) + ω * Complex.I) * t)‖ = Real.exp (σ * t) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `|e^{(σ + i ω) r}| ≤ e^{|σ| R}` for `0 ≤ r ≤ R`. -/
private theorem norm_cexp_freq_le {σ ω r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    ‖Complex.exp (((σ : ℂ) + ω * Complex.I) * r)‖ ≤ Real.exp (|σ| * R) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have : (((σ : ℂ) + ω * Complex.I) * r).re = σ * r := by simp
  rw [this]
  calc σ * r ≤ |σ| * r := mul_le_mul_of_nonneg_right (le_abs_self σ) hr
    _ ≤ |σ| * R := mul_le_mul_of_nonneg_left hrR (abs_nonneg σ)

/-- Pairs of sums in `E_ℂ`. -/
private theorem hasSum_mk {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b : ι → E} {A B : E} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun i => (⟨a i, b i⟩ : Complexification E)) ⟨A, B⟩ := by
  have := (ha.mapL ofRealCLM).add ((hb.mapL ofRealCLM).const_smul Complex.I)
  simpa only [ofRealCLM_apply, ← mk_eq_add_I_smul] using this

/-- **Termwise control convolution**: if `∑ᵢ gᵢ = u` pointwise on `(0, t]` with
`‖gᵢ‖ ≤ Mᵢ` there and `∑ Mᵢ < ∞` (so that the partial sums converge in `L²(0, t; U)`), then
`∑ᵢ L_t gᵢ = L_t u` in `W` (`hyp:H1`; the series of `V`-valued convolutions is integrated
termwise). -/
private theorem hasSum_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {ι : Type*} [Countable ι]
    {t : ℝ} {g : ι → ℝ → U} {u : ℝ → U} {M : ι → ℝ}
    (hg : ∀ i, MemLp (g i) 2 (μI t)) (hM : Summable M)
    (hgM : ∀ i, ∀ r ∈ Ioc 0 t, ‖g i r‖ ≤ M i)
    (hgu : ∀ r ∈ Ioc 0 t, HasSum (fun i => g i r) (u r)) :
    HasSum (fun i => sys.L t (g i)) (sys.L t u) := by
  rcases le_or_gt t 0 with ht | ht
  · simp only [L_of_nonpos ht]; exact hasSum_zero
  have hM0 : ∀ i, 0 ≤ M i := fun i =>
    (norm_nonneg _).trans (hgM i (t / 2) ⟨by linarith, by linarith⟩)
  -- the terms are summable in `W`
  obtain ⟨b, hb⟩ := exists_norm_L_le hH1 hT t
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ‖(hg i).toLp (g i)‖ ≤ K * M i := by
    refine ⟨_, by positivity, fun i => Lp.norm_le_of_ae_bound (hM0 i) ?_⟩
    filter_upwards [(hg i).coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with r hr hr'
    rw [hr]; exact hgM i r hr'
  have hLg : ∀ i, ‖sys.L t (g i)‖ ≤ max b 0 * K * M i := by
    intro i
    have e : sys.L t (g i) = sys.L t ⇑((hg i).toLp (g i)) := L_congr_ae (hg i).coeFn_toLp.symm
    rw [e, mul_assoc]
    refine (hb _ t ⟨ht.le, le_rfl⟩).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left b 0) (norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left (hK i) (le_max_right b 0)
  obtain ⟨S, hS⟩ : Summable fun i => sys.L t (g i) :=
    Summable.of_norm_bounded (hM.mul_left (max b 0 * K)) hLg
  -- its image in `V` is the sum of the `V`-valued convolutions
  have hιS : HasSum (fun i => sys.convV t (g i)) (sys.ιWV S) := by
    have h1 := hS.mapL sys.ιWV
    have e : (fun i => sys.ιWV (sys.L t (g i))) = fun i => sys.convV t (g i) :=
      funext fun i => ιWV_L hH1 hT (hg i)
    rwa [e] at h1
  -- which is the convolution of the sum (termwise integration)
  obtain ⟨CS, hCS0, hCS⟩ := sys.SV.exists_norm_real_le t
  set F : ι → ℝ → V := fun i r => sys.SV.real (t - r) (sys.B (g i r)) with hF
  have hFint : ∀ i, Integrable (F i) (μI t) := fun i => integrableOn_convV (hg i)
  have hFbd : ∀ i, ∀ r ∈ Ioc 0 t, ‖F i r‖ ≤ CS * ‖sys.B‖ * M i := by
    intro i r hr
    calc ‖F i r‖ ≤ ‖sys.SV.real (t - r)‖ * ‖sys.B (g i r)‖ := (sys.SV.real _).le_opNorm _
      _ ≤ CS * (‖sys.B‖ * M i) :=
          mul_le_mul (hCS _ (by linarith [hr.1]))
            ((sys.B.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hgM i r hr) (norm_nonneg _)))
            (norm_nonneg _) hCS0
      _ = CS * ‖sys.B‖ * M i := by ring
  have hFsum : Summable fun i => ∫ r, ‖F i r‖ ∂(μI t) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun r => norm_nonneg _)
      (fun i => ?_) (hM.mul_left ((μI t).real univ * (CS * ‖sys.B‖)))
    calc ∫ r, ‖F i r‖ ∂(μI t) ≤ ∫ _r, CS * ‖sys.B‖ * M i ∂(μI t) :=
          integral_mono_of_nonneg (ae_of_all _ fun r => norm_nonneg _) (integrable_const _)
            (ae_restrict_of_forall_mem measurableSet_Ioc (hFbd i))
      _ = (μI t).real univ * (CS * ‖sys.B‖) * M i := by
          rw [integral_const, smul_eq_mul]; ring
  have hconv := hasSum_integral_of_summable_integral_norm hFint hFsum
  have e2 : ∫ r, ∑' i, F i r ∂(μI t) = sys.convV t u := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    exact ((hgu r hr).mapL ((sys.SV.real (t - r)).comp sys.B)).tsum_eq
  rw [e2] at hconv
  rw [L_eq_of_ιWV (hιS.unique hconv)]
  exact hS

/-- Termwise complexified control convolution (`hasSum_L` on real and imaginary parts). -/
private theorem hasSum_Lc {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {ι : Type*} [Countable ι]
    {t : ℝ} {f : ι → ℝ → Complexification U} {u : ℝ → Complexification U} {M : ι → ℝ}
    (hf : ∀ i, Continuous (f i)) (hM : Summable M)
    (hfM : ∀ i, ∀ r ∈ Ioc 0 t, ‖f i r‖ ≤ M i)
    (hfu : ∀ r ∈ Ioc 0 t, HasSum (fun i => f i r) (u r)) :
    HasSum (fun i => sys.Lc t (f i)) (sys.Lc t u) := by
  have hmem : ∀ g : ℝ → U, Continuous g → MemLp g 2 (μI t) := fun g hg =>
    memLp_μI_of_continuousOn hg.continuousOn
  refine hasSum_mk ?_ ?_
  · exact hasSum_L hH1 hT (fun i => hmem _ (reCLM.continuous.comp (hf i))) hM
      (fun i r hr => (norm_re_le _).trans (hfM i r hr))
      (fun r hr => (hfu r hr).mapL reCLM)
  · exact hasSum_L hH1 hT (fun i => hmem _ (imCLM.continuous.comp (hf i))) hM
      (fun i r hr => (norm_im_le _).trans (hfM i r hr))
      (fun r hr => (hfu r hr).mapL imCLM)

/-- The harmonic input as an absolutely convergent series in `U_ℂ`:
`ū(r) = e^{σ r} h(r) = ∑ₗ e^{sₗ r} vₗ`. -/
private theorem hasSum_input (σ : ℝ) (h : HarmonicSignal U) (r : ℝ) :
    HasSum (fun l => Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * r) • h.coeff l)
      ((Real.exp (σ * r) • h r : U) : Complexification U) := by
  have hs : Summable fun l => Complex.exp (h.freq l * r * Complex.I) • h.coeff l := by
    refine Summable.of_norm_bounded h.summable_norm_coeff fun l => ?_
    rw [norm_smul, Complex.norm_exp]
    simp
  have := hs.hasSum.const_smul ((Real.exp (σ * r) : ℝ) : ℂ)
  rw [ofReal_smul, h.ofReal_apply, bohrSeries_apply, ← Complex.coe_smul]
  convert this using 2 with l
  rw [smul_smul, cexp_freq]

/-- `‖e^{sₗ r} vₗ‖ ≤ e^{|σ| t} ‖vₗ‖` on `(0, t]`. -/
private theorem norm_cexp_smul_le {σ ω t r : ℝ} (hr : r ∈ Ioc 0 t) (v : Complexification U) :
    ‖Complex.exp (((σ : ℂ) + ω * Complex.I) * r) • v‖ ≤ Real.exp (|σ| * t) * ‖v‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_cexp_freq_le hr.1.le hr.2) (norm_nonneg _)

/-- **Summing `eq:analytic-exp-convolution`**: for `t ≥ 0`,
`L_t ū = ∑ₗ (e^{sₗ t} qₗ - S(t) qₗ)` in `W_ℂ`. -/
private theorem hasSum_ofReal_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat)
    {σ : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun l => Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) • sys.stateCoeff σ h l -
        (sys.SW.real t).complexify (sys.stateCoeff σ h l))
      ((sys.L t (fun r => Real.exp (σ * r) • h r) : W) : Complexification W) := by
  have hLc : ((sys.L t (fun r => Real.exp (σ * r) • h r) : W) : Complexification W) =
      sys.Lc t (fun r => ((Real.exp (σ * r) • h r : U) : Complexification U)) := by
    ext
    · rfl
    · simp only [ofReal_im, Lc]
      exact (L_eq_of_ιWV (by simp [convV])).symm
  rw [hLc]
  have key := hasSum_Lc (sys := sys) hH1 hT (t := t)
    (f := fun l r => Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * r) • h.coeff l)
    (u := fun r => ((Real.exp (σ * r) • h r : U) : Complexification U))
    (M := fun l => Real.exp (|σ| * t) * ‖h.coeff l‖)
    (fun l => by fun_prop) (h.summable_norm_coeff.mul_left _)
    (fun l r hr => norm_cexp_smul_le hr _) (fun r _ => hasSum_input σ h r)
  convert key using 1
  funext l
  exact (Lc_cexp_smul hH1 hT hc (mem_resolventSet_freq hρ l) ht _).symm

/-- `∑ₗ ‖e^{sₗ t} qₗ‖ < ∞`. -/
private theorem summable_cexp_smul_stateCoeff {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hc : sys.Compat) {σ : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify) (t : ℝ) :
    Summable fun l =>
      Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) • sys.stateCoeff σ h l := by
  refine Summable.of_norm_bounded
    ((summable_stateCoeff hH1 hT hc hρ).mul_left (Real.exp (σ * t))) fun l => ?_
  rw [norm_smul, Complex.norm_exp]
  simp

/-- The state expansion of the forced response: `L_t ū = ∑ₗ e^{sₗ t} qₗ - S(t) ∑ₗ qₗ`. -/
private theorem ofReal_L_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat)
    {σ : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify) {t : ℝ} (ht : 0 ≤ t) :
    ((sys.L t (fun r => Real.exp (σ * r) • h r) : W) : Complexification W) =
      (∑' l, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) • sys.stateCoeff σ h l) -
        (sys.SW.real t).complexify (∑' l, sys.stateCoeff σ h l) := by
  have hq : Summable fun l => sys.stateCoeff σ h l :=
    (summable_stateCoeff hH1 hT hc hρ).of_norm
  exact (hasSum_ofReal_L hH1 hT hc hρ ht).unique
    ((summable_cexp_smul_stateCoeff hH1 hT hc hρ t).hasSum.sub
      (hq.hasSum.mapL (sys.SW.real t).complexify))
/-- **`eq:analytic-state-expansion`, in `X`**: for `x₀ ∈ X` and the input
`ū(t) = e^{σ t} h(t)`, the state is `x̄(t) = S(t) c + ∑ₗ qₗ e^{sₗ t}` with `c = x₀ - ∑ₗ qₗ`, as
an identity in `X_ℂ`, for every `t ≥ 0`. -/
theorem mild_harmonic {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (x₀ : X) {t : ℝ} (ht : 0 ≤ t) :
    ((sys.mild x₀ (fun r => Real.exp (σ * r) • h r) t : X) : Complexification X) =
      (sys.SX.real t).complexify
          ((x₀ : Complexification X) - ∑' l, sys.ιW.complexify (sys.stateCoeff σ h l)) +
        ∑' l, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) •
          sys.ιW.complexify (sys.stateCoeff σ h l) := by
  have hq : Summable fun l => sys.stateCoeff σ h l :=
    (summable_stateCoeff hH1 hT hc hρ).of_norm
  have he := summable_cexp_smul_stateCoeff hH1 hT hc hρ t
  rw [mild, ofReal_add, ← ContinuousLinearMap.complexify_ofReal (sys.SX.real t) x₀,
    ← ContinuousLinearMap.complexify_ofReal sys.ιW, ofReal_L_eq hH1 hT hc hρ ht]
  simp only [map_sub, ιW_SW_cplx, sys.ιW.complexify.map_tsum hq,
    sys.ιW.complexify.map_tsum he, map_smul]
  abel

/-- **`eq:analytic-state-expansion`, in `W`**: for `x₀ ∈ W` and the input `ū(t) = e^{σ t} h(t)`,
the `W`-valued state is `x̄(t) = S(t) c + ∑ₗ qₗ e^{sₗ t}` with `c = x₀ - ∑ₗ qₗ`, as an identity in
`W_ℂ`, for every `t ≥ 0`. -/
theorem mildW_harmonic {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (w₀ : W) {t : ℝ} (ht : 0 ≤ t) :
    ((sys.mildW w₀ (fun r => Real.exp (σ * r) • h r) t : W) : Complexification W) =
      (sys.SW.real t).complexify ((w₀ : Complexification W) - ∑' l, sys.stateCoeff σ h l) +
        ∑' l, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) • sys.stateCoeff σ h l := by
  rw [mildW, ofReal_add, ← ContinuousLinearMap.complexify_ofReal (sys.SW.real t) w₀,
    ofReal_L_eq hH1 hT hc hρ ht, map_sub]
  abel

/-- The coefficients `dₗ = ⟨α, vₗ⟩ + ⟨η, qₗ⟩` are absolutely summable
(`eq:analytic-annihilator-expansion`, by `eq:analytic-qsummable`). -/
theorem summable_annihilatorCoeff {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat)
    {σ : ℝ} {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (α : Complexification U) (η : Complexification W) :
    Summable fun l => ‖sys.annihilatorCoeff σ h α η l‖ := by
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
    ((h.summable_norm_coeff.mul_left ‖α‖).add
      ((summable_stateCoeff hH1 hT hc hρ).mul_left ‖η‖))
  exact (norm_add_le _ _).trans (add_le_add (norm_pairing_le _ _) (norm_pairing_le _ _))

/-- **`eq:analytic-annihilator-expansion`**: for `x₀ ∈ W`, `(α, η) ∈ U_ℂ × W_ℂ` and `t ≥ 0`,
`⟨α, ū(t)⟩ + ⟨η, x̄(t)⟩ = ⟨η, S(t) c⟩ + e^{σ t} ∑ₗ dₗ e^{i ωₗ t}`, with `c = x₀ - ∑ₗ qₗ` and
`dₗ = ⟨α, vₗ⟩ + ⟨η, qₗ⟩`.  If `(α, η)` annihilates the record a.e. on `I`, the right-hand side
vanishes a.e. on `I`, which is the paper's display. -/
theorem annihilator_expansion {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (w₀ : W) (α : Complexification U) (η : Complexification W) {t : ℝ} (ht : 0 ≤ t) :
    ⟪α, ((Real.exp (σ * t) • h t : U) : Complexification U)⟫_bil +
        ⟪η, ((sys.mildW w₀ (fun r => Real.exp (σ * r) • h r) t : W) : Complexification W)⟫_bil =
      ⟪η, (sys.SW.real t).complexify
          ((w₀ : Complexification W) - ∑' l, sys.stateCoeff σ h l)⟫_bil +
        Real.exp (σ * t) *
          ∑' l, sys.annihilatorCoeff σ h α η l * Complex.exp (h.freq l * t * Complex.I) := by
  have he := summable_cexp_smul_stateCoeff hH1 hT hc hρ t
  have h1 := (hasSum_input σ h t).mapL (pairingCLM α)
  have h2 := he.hasSum.mapL (pairingCLM η)
  have hd : Summable fun l =>
      sys.annihilatorCoeff σ h α η l * Complex.exp (h.freq l * t * Complex.I) := by
    refine Summable.of_norm_bounded (summable_annihilatorCoeff hH1 hT hc hρ α η) fun l => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  have h3 := hd.hasSum.mul_left (Real.exp (σ * t) : ℂ)
  rw [mildW_harmonic hH1 hT hc hρ w₀ ht, pairing_add_right, add_left_comm]
  congr 1
  refine (h1.add h2).unique ?_
  convert h3 using 1
  funext l
  simp only [pairingCLM_apply, pairing_smul_right, annihilatorCoeff, cexp_freq]
  ring

/-- `|e^{sₗ t} ⟨g(t), v⟩| ≤ e^{|σ| T₀} ‖v‖ ‖g(t)‖` on `(0, T₀]`. -/
private theorem norm_windowIntegrand_le {σ ω T₀ : ℝ} (g : L2 U T₀) (v : Complexification U)
    {t : ℝ} (ht : t ∈ Ioc 0 T₀) :
    ‖Complex.exp (((σ : ℂ) + ω * Complex.I) * t) * ⟪((g t : U) : Complexification U), v⟫_bil‖ ≤
      Real.exp (|σ| * T₀) * ‖v‖ * ‖(g t : U)‖ := by
  rw [norm_mul]
  calc _ ≤ Real.exp (|σ| * T₀) * (‖((g t : U) : Complexification U)‖ * ‖v‖) :=
        mul_le_mul (norm_cexp_freq_le ht.1.le ht.2) (norm_pairing_le _ _) (norm_nonneg _)
          (Real.exp_pos _).le
    _ = _ := by rw [norm_ofReal]; ring

private theorem integrable_windowIntegrand (σ ω : ℝ) {T₀ : ℝ} (g : L2 U T₀)
    (v : Complexification U) :
    Integrable (fun t : ℝ => Complex.exp (((σ : ℂ) + ω * Complex.I) * t) *
      ⟪((g t : U) : Complexification U), v⟫_bil) (μI T₀) := by
  have hg : Integrable (fun t => (g t : U)) (μI T₀) := (Lp.memLp g).integrable one_le_two
  refine Integrable.mono' (hg.norm.const_mul (Real.exp (|σ| * T₀) * ‖v‖)) ?_
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => norm_windowIntegrand_le g v ht)
  refine (Continuous.aestronglyMeasurable (by fun_prop)).mul ?_
  exact (ofRealCLM.continuous.pairing continuous_const).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable g)

private theorem integral_norm_windowIntegrand_le (σ ω : ℝ) {T₀ : ℝ} (g : L2 U T₀)
    (v : Complexification U) :
    ∫ t, ‖Complex.exp (((σ : ℂ) + ω * Complex.I) * t) *
        ⟪((g t : U) : Complexification U), v⟫_bil‖ ∂(μI T₀) ≤
      Real.exp (|σ| * T₀) * ‖v‖ * ∫ t, ‖(g t : U)‖ ∂(μI T₀) := by
  have hg : Integrable (fun t => (g t : U)) (μI T₀) := (Lp.memLp g).integrable one_le_two
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hg.norm.const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => norm_windowIntegrand_le g v ht)

/-- The coefficients `Dₗ` of the window expansion are absolutely summable
(`|∫₀ᵀ e^{sₗ t} ⟨g(t), vₗ⟩ dt| ≤ √T e^{|σ| T} ‖g‖ ‖vₗ‖`, and `eq:analytic-qsummable`). -/
theorem summable_windowCoeff {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    {T₀ : ℝ} (g : L2 U T₀) (ξ : X) :
    Summable fun l => ‖sys.windowCoeff σ h g ξ l‖ := by
  refine Summable.of_nonneg_of_le (fun l => norm_nonneg _) (fun l => ?_)
    ((h.summable_norm_coeff.mul_left
      (Real.exp (|σ| * T₀) * ∫ t, ‖(g t : U)‖ ∂(μI T₀))).add
      ((summable_stateCoeff hH1 hT hc hρ).mul_left (‖ξ‖ * ‖sys.ιW‖)))
  simp only [windowCoeff]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc _ ≤ _ := norm_integral_le_integral_norm _
      _ ≤ _ := integral_norm_windowIntegrand_le σ (h.freq l) g (h.coeff l)
      _ = _ := by ring
  · calc _ ≤ ‖(ξ : Complexification X)‖ * ‖sys.ιW.complexify (sys.stateCoeff σ h l)‖ :=
          norm_pairing_le _ _
      _ ≤ ‖ξ‖ * (‖sys.ιW‖ * ‖sys.stateCoeff σ h l‖) := by
          rw [norm_ofReal]
          exact mul_le_mul_of_nonneg_left (sys.ιW.norm_complexify_apply_le _) (norm_nonneg _)
      _ = _ := by ring

/-- **The window expansion** (proof of (i) ⇒ (iii), `app:analytic-universal-sufficiency`): for
`x₀ ∈ X`, `g ∈ L²(0, T₀; U)`, `ξ ∈ X` and `s ≥ 0`, substituting `eq:analytic-state-expansion`
and integrating termwise,
`∫₀^{T₀} ⟨g(t), ū(s + t)⟩ dt + ⟨ξ, x̄(s)⟩ = ⟨ξ, S(s) c⟩ + e^{σ s} ∑ₗ Dₗ e^{i ωₗ s}`, with
`c = x₀ - ∑ₗ qₗ` and `Dₗ = ∫₀^{T₀} e^{sₗ t} ⟨g(t), vₗ⟩ dt + ⟨ξ, qₗ⟩`. -/
theorem window_expansion {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {σ : ℝ}
    {h : HarmonicSignal U}
    (hρ : ∀ ω ∈ closure (Set.range h.freq),
      (σ : ℂ) + ω * Complex.I ∈ resolventSet sys.A.complexify)
    (x₀ : X) {T₀ : ℝ} (g : L2 U T₀) (ξ : X) {s : ℝ} (hs : 0 ≤ s) :
    ((((∫ t in Ioc 0 T₀, ⟪(g t : U), Real.exp (σ * (s + t)) • h (s + t)⟫_ℝ) +
        ⟪ξ, sys.mild x₀ (fun r => Real.exp (σ * r) • h r) s⟫_ℝ : ℝ)) : ℂ) =
      ⟪(ξ : Complexification X), (sys.SX.real s).complexify
          ((x₀ : Complexification X) - ∑' l, sys.ιW.complexify (sys.stateCoeff σ h l))⟫_bil +
        Real.exp (σ * s) *
          ∑' l, sys.windowCoeff σ h g ξ l * Complex.exp (h.freq l * s * Complex.I) := by
  have hGint : ∀ l, Integrable (fun t : ℝ =>
      Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
        ⟪((g t : U) : Complexification U), h.coeff l⟫_bil) (μI T₀) :=
    fun l => integrable_windowIntegrand σ (h.freq l) g (h.coeff l)
  have hFint : ∀ l, Integrable (fun t : ℝ =>
      Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s) *
        (Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
          ⟪((g t : U) : Complexification U), h.coeff l⟫_bil)) (μI T₀) :=
    fun l => (hGint l).const_mul _
  have hFsum : Summable fun l => ∫ t, ‖Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s) *
        (Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
          ⟪((g t : U) : Complexification U), h.coeff l⟫_bil)‖ ∂(μI T₀) := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun _ => norm_nonneg _)
      (fun l => ?_) (h.summable_norm_coeff.mul_left
        (Real.exp (σ * s) * (Real.exp (|σ| * T₀) * ∫ t, ‖(g t : U)‖ ∂(μI T₀))))
    simp only [norm_mul (Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s)), norm_cexp_freq]
    rw [integral_const_mul]
    calc _ ≤ Real.exp (σ * s) *
          (Real.exp (|σ| * T₀) * ‖h.coeff l‖ * ∫ t, ‖(g t : U)‖ ∂(μI T₀)) :=
          mul_le_mul_of_nonneg_left
            (integral_norm_windowIntegrand_le σ (h.freq l) g (h.coeff l)) (Real.exp_pos _).le
      _ = _ := by ring
  have hpt : ∀ t : ℝ, ∑' l, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s) *
        (Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
          ⟪((g t : U) : Complexification U), h.coeff l⟫_bil) =
      ⟪((g t : U) : Complexification U),
        ((Real.exp (σ * (s + t)) • h (s + t) : U) : Complexification U)⟫_bil := fun t => by
    refine HasSum.tsum_eq ?_
    convert (hasSum_input σ h (s + t)).mapL (pairingCLM ((g t : U) : Complexification U))
      using 1
    · funext l
      simp only [pairingCLM_apply, pairing_smul_right]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    · exact (pairingCLM_apply _ _).symm
  have hint : ((∫ t in Ioc 0 T₀, ⟪(g t : U), Real.exp (σ * (s + t)) • h (s + t)⟫_ℝ : ℝ) : ℂ) =
      ∑' l, ∫ t, Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s) *
        (Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * t) *
          ⟪((g t : U) : Complexification U), h.coeff l⟫_bil) ∂(μI T₀) := by
    rw [integral_tsum_of_summable_integral_norm hFint hFsum, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [hpt t, pairing_ofReal_ofReal]
  have he := summable_cexp_smul_stateCoeff hH1 hT hc hρ s
  have hιe : Summable fun l => Complex.exp (((σ : ℂ) + h.freq l * Complex.I) * s) •
      sys.ιW.complexify (sys.stateCoeff σ h l) := by
    simpa only [map_smul] using sys.ιW.complexify.summable he
  have hD : Summable fun l =>
      sys.windowCoeff σ h g ξ l * Complex.exp (h.freq l * s * Complex.I) := by
    refine Summable.of_norm_bounded (summable_windowCoeff hH1 hT hc hρ g ξ) fun l => ?_
    rw [norm_mul, Complex.norm_exp]
    simp
  have h1 := (hasSum_integral_of_summable_integral_norm hFint hFsum).summable.hasSum
  have h2 := hιe.hasSum.mapL (pairingCLM (ξ : Complexification X))
  have h3 := hD.hasSum.mul_left (Real.exp (σ * s) : ℂ)
  rw [Complex.ofReal_add, hint, ← pairing_ofReal_ofReal, mild_harmonic hH1 hT hc hρ x₀ hs,
    pairing_add_right, add_left_comm]
  congr 1
  refine (h1.add h2).unique ?_
  convert h3 using 1
  funext l
  simp only [pairingCLM_apply, pairing_smul_right, windowCoeff, integral_const_mul, cexp_freq]
  ring

end System

end DataDrivenControl
