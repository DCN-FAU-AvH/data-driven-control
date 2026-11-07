module

public import DataDrivenControl.System.ControlRealization
public import DataDrivenControl.Semigroup.Analytic
public import DataDrivenControl.Analysis.Complexification

/-!
# The transfer map `𝐇(s) = (s - A_{X,-1})⁻¹ B_X`

Paper: `app:analytic-universal-sufficiency`, first two paragraphs (the transfer map, its
holomorphy into `L(U, W)` on `ρ(A)` and its decay `‖𝐇(r)‖_{L(U,W)} = O(r^{-1/2})`;
`ρ(A) ⊆ ρ(A_W)`; the component `Ω_⋆` of `ρ(A)` containing `{Re s > σ}`), building on
`app:control-realization` (`eq:control-resolvent-decay`).

## Conventions

Complex spectra of the real system go through `Analysis/Complexification`: `ρ(A)` is
`resolventSet sys.A.complexify ⊆ ℂ` (resolvent set of the complexified generator on `X_ℂ`),
`R(s, A) = resolvent sys.A.complexify s`, operators `T ∈ L(X, Y)` act on `X_ℂ` as
`T.complexify`, and the paper's pairing `⟨·, ·⟩` on `X_ℂ` is the bilinear `⟪·, ·⟫_bil`.
No complexified extrapolation space is used, and statements let `S(t)` act on `X_ℂ` as
`(sys.SX.real t).complexify`; the complexified semigroup `S.complexify` (below) is that family
(`C0Semigroup.complexify_real`).  Here it places `{Re s > σ}` in `ρ(A)`; `Analytic/Expansion` and
`Analytic/Bohr` use its finite-time Laplace identity.

## Main declarations

* `sys.transferX s : U_ℂ →L[ℂ] X_ℂ`: `𝐇(s) = Q_a - (s - a) R(s, A) Q_a` for the admissible real
  `a` chosen by `sys.BX` (`QSpec`); by the resolvent identity this is
  `(s - A_{X,-1})⁻¹ B_X` for `s ∈ ρ(A)`.  The characterisation of the paper's definition is
  `transferX_spec` with uniqueness `eq_transferX`: `x = 𝐇(s) v` iff
  `s ⟨η, x⟩ - ⟨A† η, x⟩ = ⟨B† η, v⟩` for all `η ∈ D(A†)`, i.e. `(s - A_{X,-1}) x = B_X v` in
  `X₋₁` (dual model).  `transferX_eq`: the formula holds for every admissible `a`;
  `transferX_sub`: `𝐇(s) = 𝐇(r) - (s - r) R(s, A) 𝐇(r)`.
* `sys.transfer s : U_ℂ →L[ℂ] W_ℂ`: `𝐇(s)` as an operator into `W_ℂ` (`ιW_transfer`), junk `0`
  where it is not one; `transfer_ofReal`: `𝐇(r) = Q_r` for admissible real `r`.
* `differentiableOn_transfer`: `𝐇` is holomorphic on `ρ(A)` into `L(U_ℂ, W_ℂ)`;
  `transfer_decay`: `‖𝐇(r)‖_{L(U_ℂ, W_ℂ)} = O(r^{-1/2})` as `r → +∞`.
* `resolventSet_complexify_subset_W`, `ιW_resolvent_W`: `ρ(A) ⊆ ρ(A_W)` and the resolvents agree
  on `W`.
* `C0Semigroup.mem_resolventSet_complexify`: a growth bound `‖S t‖ ≤ M e^{σ t}` gives
  `{Re s > σ} ⊆ ρ(A)`.
* `exists_isPreconnected_resolventSet`: a compact `K ⊆ ρ(A)` on the line `Re s = σ` lies, with the
  half-plane `{Re s > σ}`, in an open preconnected subset `Ω_⋆ ⊆ ρ(A)`.

## Additional declarations

* `IsResolvent.complexify`, `ofReal_mem_resolventSet_complexify`,
  `resolvent_complexify_ofReal`: for real `μ ∈ ρ(A)`, `μ ∈ ρ(A_ℂ)` and `R(μ, A_ℂ) = R(μ, A)_ℂ`.
* `C0Semigroup.complexify` (`S_ℂ(t) = S(t)_ℂ`, a `C0Semigroup ℂ E_ℂ`) with
  `complexify_generator : S.complexify.generator = S.generator.complexify`.
* `C0Semigroup.pairing_generator_adjoint` (`⟨A† η, y⟩ = ⟨η, A_ℂ y⟩`),
  `C0Semigroup.pairing_resolvent` (`s ⟨η, R(s) y⟩ - ⟨A† η, R(s) y⟩ = ⟨η, y⟩`),
  `C0Semigroup.eq_zero_of_forall_pairing` (uniqueness for `(s - A_{-1}) z = 0`, `s ∈ ρ(A)`),
  `Complexification.inner_eq_pairing_re_sub_pairing_im`.
* `System.mem_AW_domain_of_ιW` (the part of `A` in `W` is `A_W`),
  `System.exists_ιW_eq_of_mem_domain` (`D(A) ⊆ W` under `hyp:compat`),
  `System.exists_isResolvent_W` (`R(s, A_W) = R(s, A)|_W`, bounded by the closed graph
  theorem), `System.ιW_comp_transferW`, `System.transfer_eq`
  (`𝐇(s) = Q_a - (s - a) R(s, A_W) Q_a` in `L(U_ℂ, W_ℂ)` for every admissible `a`).

## Upstream results used

`System.QSpec`, `exists_QSpec`, `Q_decay`, `ιW_Q_sub_ιW_Q`, `Bstar`, `inner_Bstar_eq`
(`System/ControlRealization`); `resolvent_sub_resolvent`, `isOpen_resolventSet`,
`differentiableOn_resolvent`, `C0Semigroup.mem_resolventSet`, `Consistent.resolvent`
(`Semigroup/Resolvent`); `LinearPMap.adjoint_complexify`, `ContinuousLinearMap.complexify_comp`,
`ContinuousLinearMap.norm_complexify`, `ContinuousLinearMap.injective_complexify_iff`
(`Analysis/Complexification`); `System.Compat` (`System/Setting`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

open Complexification

/-! ### Complexified resolvents of real operators -/

section ResolventComplexify

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The complexification of a real resolvent is a resolvent of the complexified operator:
`R(μ, A)_ℂ = R(μ, A_ℂ)` for real `μ`. -/
theorem IsResolvent.complexify {A : X →ₗ.[ℝ] X} {μ : ℝ} {R : X →L[ℝ] X}
    (h : IsResolvent A μ R) : IsResolvent A.complexify (μ : ℂ) R.complexify := by
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨h1, e1⟩ := h.1 y.re
    obtain ⟨h2, e2⟩ := h.1 y.im
    refine ⟨Submodule.mem_complexify.2 ⟨h1, h2⟩, ?_⟩
    ext
    · show (μ : ℂ).re • R y.re - (μ : ℂ).im • R y.im - A ⟨R y.re, h1⟩ = y.re
      simpa using e1
    · show (μ : ℂ).re • R y.im + (μ : ℂ).im • R y.re - A ⟨R y.im, h2⟩ = y.im
      simpa using e2
  · obtain ⟨x, hx1, hx2⟩ := x
    have e1 := h.2 ⟨x.re, hx1⟩
    have e2 := h.2 ⟨x.im, hx2⟩
    ext
    · show R ((μ : ℂ).re • x.re - (μ : ℂ).im • x.im - A ⟨x.re, hx1⟩) = x.re
      simpa using e1
    · show R ((μ : ℂ).re • x.im + (μ : ℂ).im • x.re - A ⟨x.im, hx2⟩) = x.im
      simpa using e2

/-- A real point of `ρ(A)` lies in `ρ(A_ℂ)`. -/
theorem ofReal_mem_resolventSet_complexify {A : X →ₗ.[ℝ] X} {μ : ℝ}
    (h : μ ∈ resolventSet A) : (μ : ℂ) ∈ resolventSet A.complexify :=
  ⟨_, (isResolvent_resolvent h).complexify⟩

/-- `R(μ, A_ℂ) = R(μ, A)_ℂ` for real `μ ∈ ρ(A)`. -/
theorem resolvent_complexify_ofReal {A : X →ₗ.[ℝ] X} {μ : ℝ} (h : μ ∈ resolventSet A) :
    resolvent A.complexify (μ : ℂ) = (resolvent A μ).complexify :=
  resolvent_eq (isResolvent_resolvent h).complexify

end ResolventComplexify

namespace Complexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hermitian product through the bilinear pairing with real vectors:
`⟪v, z⟫_ℂ = ⟪re v, z⟫_bil - i ⟪im v, z⟫_bil`. -/
theorem inner_eq_pairing_re_sub_pairing_im (v z : Complexification E) :
    ⟪v, z⟫_ℂ = ⟪(v.re : Complexification E), z⟫_bil -
      Complex.I * ⟪(v.im : Complexification E), z⟫_bil := by
  apply Complex.ext
  · simp [Complexification.inner_re, Complex.mul_re]
  · simp [Complexification.inner_im, Complex.mul_im]

end Complexification

/-! ### The complexified semigroup -/

namespace C0Semigroup

section Complexify

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **complexified semigroup** `S_ℂ(t) = S(t)_ℂ` on `E_ℂ`; its generator is `A_ℂ`
(`complexify_generator`). -/
def complexify (S : C0Semigroup ℝ E) : C0Semigroup ℂ (Complexification E) where
  toFun t := (S t).complexify
  map_zero' := by rw [S.map_zero]; exact ContinuousLinearMap.complexify_one
  map_add' s t := by rw [S.map_add]; exact ContinuousLinearMap.complexify_comp _ _
  continuous_apply' z :=
    Complexification.continuous_mk (S.continuous_apply z.re) (S.continuous_apply z.im)

variable (S : C0Semigroup ℝ E)

/-- `S_ℂ(t) = S(t)_ℂ`. -/
@[simp] theorem complexify_apply (t : ℝ≥0) : S.complexify t = (S t).complexify := rfl

/-- `S_ℂ(t) = S(t)_ℂ` at real times. -/
theorem complexify_real (t : ℝ) : S.complexify.real t = (S.real t).complexify := rfl

/-- The difference quotients of `S_ℂ` are those of `S`, componentwise. -/
theorem diffQuot_complexify (z : Complexification E) (h : ℝ) :
    S.complexify.diffQuot z h = ⟨S.diffQuot z.re h, S.diffQuot z.im h⟩ := by
  ext <;> simp [diffQuot, complexify_real]

/-- The generator of the complexified semigroup is the complexified generator: `(A_ℂ)` is
the generator of `S_ℂ`, domains included. -/
theorem complexify_generator : S.complexify.generator = S.generator.complexify := by
  have hdom : ∀ z, z ∈ S.complexify.generator.domain ↔ z ∈ S.generator.complexify.domain := by
    intro z
    rw [mem_generator_domain_iff, LinearPMap.complexify_domain, Submodule.mem_complexify,
      mem_generator_domain_iff, mem_generator_domain_iff]
    constructor
    · rintro ⟨y, hy⟩
      rw [Complexification.tendsto_iff] at hy
      simp only [diffQuot_complexify] at hy
      exact ⟨⟨y.re, hy.1⟩, ⟨y.im, hy.2⟩⟩
    · rintro ⟨⟨y1, h1⟩, ⟨y2, h2⟩⟩
      refine ⟨⟨y1, y2⟩, Complexification.tendsto_iff.2 ?_⟩
      simp only [diffQuot_complexify]
      exact ⟨h1, h2⟩
  refine LinearPMap.ext (Submodule.ext hdom) fun z hz hz' => ?_
  apply S.complexify.generator_apply_eq hz
  rw [Complexification.tendsto_iff]
  simp only [diffQuot_complexify, LinearPMap.complexify_apply_re, LinearPMap.complexify_apply_im]
  exact ⟨S.tendsto_generator _, S.tendsto_generator _⟩

end Complexify

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A growth bound `‖S t‖ ≤ M e^{σ t}` puts the open half-plane `{Re s > σ}` in the resolvent
set of the complexified generator (`app:analytic-universal-sufficiency`). -/
theorem mem_resolventSet_complexify (S : C0Semigroup ℝ E) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (σ * t)) {s : ℂ} (hs : σ < s.re) :
    s ∈ resolventSet S.generator.complexify := by
  rw [← S.complexify_generator]
  refine S.complexify.mem_resolventSet (M := M) (ω := σ) (fun t => ?_) (by simpa using hs)
  rw [complexify_apply, ContinuousLinearMap.norm_complexify]
  exact hS t

variable (S : C0Semigroup ℝ E)

/-- `⟪A† η, y⟫_bil = ⟪η, A_ℂ y⟫_bil` for real `η ∈ D(A†)` and `y ∈ D(A_ℂ)`. -/
theorem pairing_generator_adjoint (η : S.generator.adjoint.domain)
    (y : S.generator.complexify.domain) :
    ⟪((S.generator.adjoint η : E) : Complexification E), (y : Complexification E)⟫_bil =
      ⟪((η : E) : Complexification E), S.generator.complexify y⟫_bil := by
  have hf := LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain
  obtain ⟨y, hy1, hy2⟩ := y
  have e1 := hf η ⟨y.re, hy1⟩
  have e2 := hf η ⟨y.im, hy2⟩
  apply Complex.ext
  · simp only [pairing_re, ofReal_re, ofReal_im, inner_zero_left, sub_zero,
      LinearPMap.complexify_apply_re]
    exact e1
  · simp only [pairing_im, ofReal_re, ofReal_im, inner_zero_left, add_zero,
      LinearPMap.complexify_apply_im]
    exact e2

/-- `s ⟪η, R(s, A) y⟫ - ⟪A† η, R(s, A) y⟫ = ⟪η, y⟫` for real `η ∈ D(A†)` and `s ∈ ρ(A)`:
`R(s, A) y` solves `(s - A_{-1}) x = y` weakly. -/
theorem pairing_resolvent {s : ℂ} (hs : s ∈ resolventSet S.generator.complexify) {η : E}
    (hη : η ∈ S.generator.adjoint.domain) (y : Complexification E) :
    s * ⟪(η : Complexification E), resolvent S.generator.complexify s y⟫_bil -
        ⟪((S.generator.adjoint ⟨η, hη⟩ : E) : Complexification E),
          resolvent S.generator.complexify s y⟫_bil =
      ⟪(η : Complexification E), y⟫_bil := by
  rw [S.pairing_generator_adjoint ⟨η, hη⟩ ⟨_, resolvent_mem_domain hs y⟩]
  conv_rhs => rw [← sub_resolvent hs y]
  rw [pairing_sub_right, pairing_smul_right]

/-- **Uniqueness for `(s - A_{-1}) z = 0`**: for `s ∈ ρ(A)`, if `s ⟪η, z⟫ - ⟪A† η, z⟫ = 0` for
every real `η ∈ D(A†)`, then `z = 0`.  (With `w = R(s, A_ℂ)† z`, `(A_ℂ)† w = s̄ w - z`, and
`(A_ℂ)† = (A†)_ℂ`; testing with `re w`, `im w` gives `⟪z, z⟫_ℂ = 0`.) -/
theorem eq_zero_of_forall_pairing {s : ℂ} (hs : s ∈ resolventSet S.generator.complexify)
    {z : Complexification E}
    (hz : ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain),
      s * ⟪(η : Complexification E), z⟫_bil -
        ⟪((S.generator.adjoint ⟨η, hη⟩ : E) : Complexification E), z⟫_bil = 0) :
    z = 0 := by
  set A := S.generator with hA
  have hAd : Dense (A.complexify.domain : Set (Complexification E)) :=
    (LinearPMap.dense_complexify_domain_iff A).2 S.dense_generator_domain
  set w := ContinuousLinearMap.adjoint (resolvent A.complexify s) z
  have hw_eq : ∀ x : A.complexify.domain,
      ⟪(starRingEnd ℂ s) • w - z, (x : Complexification E)⟫_ℂ = ⟪w, A.complexify x⟫_ℂ := by
    intro x
    have h1 := resolvent_sub hs x
    rw [map_sub, map_smul] at h1
    have h2 : resolvent A.complexify s (A.complexify x) =
        s • resolvent A.complexify s x - x := by
      linear_combination (norm := module) -h1
    rw [ContinuousLinearMap.adjoint_inner_left, h2, inner_sub_left, inner_smul_left,
      inner_sub_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
      Complex.conj_conj]
  have hw : w ∈ A.complexify.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists w ⟨_, hw_eq⟩
  have hAw : A.complexify.adjoint ⟨w, hw⟩ = (starRingEnd ℂ s) • w - z :=
    LinearPMap.adjoint_apply_eq hAd ⟨w, hw⟩ hw_eq
  have hadj := LinearPMap.adjoint_complexify A
  have hw' : w ∈ A.adjoint.complexify.domain := hadj ▸ hw
  have hval : A.complexify.adjoint ⟨w, hw⟩ = A.adjoint.complexify ⟨w, hw'⟩ :=
    (LinearPMap.ext_iff.1 hadj).2 (hf := hw) (hg := hw')
  obtain ⟨hre, him⟩ := Submodule.mem_complexify.1 hw'
  have e1 := hz w.re hre
  have e2 := hz w.im him
  have key : ⟪(starRingEnd ℂ s) • w - A.complexify.adjoint ⟨w, hw⟩, z⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, Complex.conj_conj, inner_eq_pairing_re_sub_pairing_im w,
      inner_eq_pairing_re_sub_pairing_im (A.complexify.adjoint ⟨w, hw⟩), hval,
      LinearPMap.complexify_apply_re, LinearPMap.complexify_apply_im]
    linear_combination e1 - Complex.I * e2
  rw [hAw, sub_sub_cancel] at key
  exact inner_self_eq_zero.1 key

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
/-- The **transfer map** with values in `X_ℂ`: `𝐇(s) = Q_a - (s - a) R(s, A) Q_a`, for the
admissible real parameter `a` (`QSpec a`, chosen as in `sys.BX`; junk `0` if there is none).
For `s ∈ ρ(A)` it is the paper's `(s - A_{X,-1})⁻¹ B_X` (`transferX_spec`, `eq_transferX`),
and it does not depend on `a` (`transferX_eq`). -/
def transferX (s : ℂ) : Complexification U →L[ℂ] Complexification X :=
  if h : ∃ a, sys.QSpec a then
    (sys.ιW.comp (sys.Q h.choose)).complexify -
      (s - (h.choose : ℂ)) • (resolvent sys.A.complexify s).comp
        (sys.ιW.comp (sys.Q h.choose)).complexify
  else 0

open scoped Classical in
/-- The **transfer map** `𝐇(s) = (s - A_{X,-1})⁻¹ B_X ∈ L(U_ℂ, W_ℂ)`
(`app:analytic-universal-sufficiency`): the operator into `W_ℂ` whose composition with the
embedding `W_ℂ ↪ X_ℂ` is `transferX s` (`ιW_transfer`; junk `0` if there is none). -/
def transfer (s : ℂ) : Complexification U →L[ℂ] Complexification W :=
  if h : ∃ H : Complexification U →L[ℂ] Complexification W,
      sys.ιW.complexify.comp H = sys.transferX s then h.choose else 0

variable {sys}

set_option linter.unusedVariables false in
/-- `𝐇(s) = Q_a - (s - a) R(s, A) Q_a` for **every** admissible real `a` and `s ∈ ρ(A)`
(independence of `a`, resolvent identity). -/
theorem transferX_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {a : ℝ} (ha : sys.QSpec a) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) :
    sys.transferX s = (sys.ιW.comp (sys.Q a)).complexify -
      (s - (a : ℂ)) • (resolvent sys.A.complexify s).comp (sys.ιW.comp (sys.Q a)).complexify := by
  have h : ∃ a, sys.QSpec a := ⟨a, ha⟩
  rw [transferX, dite_eq_left h]
  set b := h.choose
  have hb : sys.QSpec b := h.choose_spec
  have hb' := ofReal_mem_resolventSet_complexify hb.1
  have hQr : sys.ιW.comp (sys.Q b) = sys.ιW.comp (sys.Q a) +
      (a - b) • (resolvent sys.A b).comp (sys.ιW.comp (sys.Q a)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      smul_apply]
    rw [← ιW_Q_sub_ιW_Q hb ha v]; abel
  rw [hQr, ContinuousLinearMap.complexify_add, ContinuousLinearMap.complexify_smul,
    ContinuousLinearMap.complexify_comp (resolvent sys.A b), ← resolvent_complexify_ofReal hb.1]
  ext1 v
  have hres := congrArg (fun L => L ((sys.ιW.comp (sys.Q a)).complexify v))
    (resolvent_sub_resolvent hs hb')
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, add_apply, map_add, map_smul] at hres ⊢
  push_cast
  linear_combination (norm := module) (-((a : ℂ) - b)) • hres

/-- **`𝐇(s) = (s - A_{X,-1})⁻¹ B_X`**, existence: for `s ∈ ρ(A)`, `x = 𝐇(s) v` solves
`(s - A_{X,-1}) x = B_X v` in `X₋₁`, i.e. (dual model, `η ∈ D(A†)`)
`s ⟨η, x⟩ - ⟨A† η, x⟩ = ⟨B† η, v⟩`. -/
theorem transferX_spec {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) (v : Complexification U)
    (η : X) (hη : η ∈ sys.A.adjoint.domain) :
    s * ⟪(η : Complexification X), sys.transferX s v⟫_bil -
        ⟪((sys.A.adjoint ⟨η, hη⟩ : X) : Complexification X), sys.transferX s v⟫_bil =
      ⟪((sys.Bstar ⟨η, hη⟩ : U) : Complexification U), v⟫_bil := by
  obtain ⟨r₀, hr₀⟩ := exists_QSpec hH1 hT
  have h : ∃ a, sys.QSpec a := ⟨r₀, hr₀ r₀ le_rfl⟩
  rw [transferX, dite_eq_left h]
  set a := h.choose
  have ha : sys.QSpec a := h.choose_spec
  have h1 := sys.SX.pairing_resolvent hs hη ((sys.ιW.comp (sys.Q a)).complexify v)
  have e1 : ⟪(sys.Bstar ⟨η, hη⟩ : U), v.re⟫_ℝ =
      ⟪sys.ιW (sys.Q a v.re), a • η - sys.A.adjoint ⟨η, hη⟩⟫_ℝ := inner_Bstar_eq ha ⟨η, hη⟩ v.re
  have e2 : ⟪(sys.Bstar ⟨η, hη⟩ : U), v.im⟫_ℝ =
      ⟪sys.ιW (sys.Q a v.im), a • η - sys.A.adjoint ⟨η, hη⟩⟫_ℝ := inner_Bstar_eq ha ⟨η, hη⟩ v.im
  have h2 : ⟪((sys.Bstar ⟨η, hη⟩ : U) : Complexification U), v⟫_bil =
      a * ⟪(η : Complexification X), (sys.ιW.comp (sys.Q a)).complexify v⟫_bil -
        ⟪((sys.A.adjoint ⟨η, hη⟩ : X) : Complexification X),
          (sys.ιW.comp (sys.Q a)).complexify v⟫_bil := by
    simp only [inner_sub_right, real_inner_smul_right] at e1 e2
    apply Complex.ext
    · simp only [pairing_re, ofReal_re, ofReal_im, inner_zero_left, sub_zero, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        ContinuousLinearMap.complexify_apply_re, ContinuousLinearMap.comp_apply]
      rw [e1, real_inner_comm η, real_inner_comm (sys.A.adjoint ⟨η, hη⟩)]
    · simp only [pairing_im, ofReal_re, ofReal_im, inner_zero_left, add_zero, Complex.sub_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        ContinuousLinearMap.complexify_apply_im, ContinuousLinearMap.comp_apply]
      rw [e2, real_inner_comm η, real_inner_comm (sys.A.adjoint ⟨η, hη⟩)]
  rw [h2]
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, pairing_sub_right, pairing_smul_right] at h1 ⊢
  linear_combination (-(s - (a : ℂ))) * h1

/-- **`𝐇(s) = (s - A_{X,-1})⁻¹ B_X`**, uniqueness: for `s ∈ ρ(A)`, the only solution
`x ∈ X_ℂ` of `(s - A_{X,-1}) x = B_X v` (weak form) is `𝐇(s) v`. -/
theorem eq_transferX {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) {v : Complexification U} {x : Complexification X}
    (hx : ∀ (η : X) (hη : η ∈ sys.A.adjoint.domain),
      s * ⟪(η : Complexification X), x⟫_bil -
          ⟪((sys.A.adjoint ⟨η, hη⟩ : X) : Complexification X), x⟫_bil =
        ⟪((sys.Bstar ⟨η, hη⟩ : U) : Complexification U), v⟫_bil) :
    x = sys.transferX s v := by
  refine sub_eq_zero.1 (sys.SX.eq_zero_of_forall_pairing hs fun η hη => ?_)
  rw [pairing_sub_right, pairing_sub_right]
  linear_combination hx η hη - transferX_spec hH1 hT hs v η hη

/-- The resolvent identity for the transfer map (`app:analytic-universal-sufficiency`):
`𝐇(s) = 𝐇(r) - (s - r) R(s, A) 𝐇(r)` for `s, r ∈ ρ(A)`. -/
theorem transferX_sub {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {s r : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) (hr : r ∈ resolventSet sys.A.complexify) :
    sys.transferX s =
      sys.transferX r - (s - r) • (resolvent sys.A.complexify s).comp (sys.transferX r) := by
  obtain ⟨r₀, hr₀⟩ := exists_QSpec hH1 hT
  have h : ∃ a, sys.QSpec a := ⟨r₀, hr₀ r₀ le_rfl⟩
  simp only [transferX, dite_eq_left h]
  ext1 v
  have hres := congrArg (fun L => L ((sys.ιW.comp (sys.Q h.choose)).complexify v))
    (resolvent_sub_resolvent hs hr)
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul] at hres ⊢
  linear_combination (norm := module) (-(r - (h.choose : ℂ))) • hres

/-! ### `ρ(A) ⊆ ρ(A_W)` -/

/-- The part of `A` in `W` is `A_W`: if `x = ι_W w ∈ D(A)` and `A x = ι_W g`, then
`w ∈ D(A_W)` and `A_W w = g`. -/
theorem mem_AW_domain_of_ιW {w g : W} {x : X} (hwx : sys.ιW w = x) (hx : x ∈ sys.A.domain)
    (hAx : sys.A ⟨x, hx⟩ = sys.ιW g) : ∃ hw : w ∈ sys.AW.domain, sys.AW ⟨w, hw⟩ = g := by
  subst hwx
  obtain ⟨MW, ωW, -, hMW⟩ := sys.SW.exists_norm_le_exp
  obtain ⟨MX, ωX, -, hMX⟩ := sys.SX.exists_norm_le_exp
  set l : ℝ := max ωW ωX + 1
  have hlW : l ∈ resolventSet sys.AW := sys.SW.mem_resolventSet (𝕜 := ℝ) hMW
    (by rw [RCLike.re_to_real]; linarith [le_max_left ωW ωX])
  have hlX : l ∈ resolventSet sys.A := sys.SX.mem_resolventSet (𝕜 := ℝ) hMX
    (by rw [RCLike.re_to_real]; linarith [le_max_right ωW ωX])
  have hd := resolvent_mem_domain hlW (l • w - g)
  have e1 : sys.ιW (resolvent sys.AW l (l • w - g)) = sys.ιW w := by
    rw [sys.consistentW.resolvent sys.SX hlW hlX, map_sub, map_smul, ← hAx]
    exact resolvent_sub hlX ⟨_, hx⟩
  have e := sys.ιW_injective e1
  have hw : w ∈ sys.AW.domain := e ▸ hd
  refine ⟨hw, ?_⟩
  have h2 := sub_resolvent hlW (l • w - g)
  have h3 : sys.AW ⟨resolvent sys.AW l (l • w - g), hd⟩ = sys.AW ⟨w, hw⟩ :=
    congrArg sys.AW (Subtype.ext e)
  rw [h3, e] at h2
  exact (sub_right_inj.1 h2)

/-- Under `hyp:compat`, `D(A) ⊆ W`. -/
theorem exists_ιW_eq_of_mem_domain (hc : sys.Compat) {x : X} (hx : x ∈ sys.A.domain) :
    ∃ w : W, sys.ιW w = x := by
  obtain ⟨⟨c, hc1⟩, -⟩ := hc
  obtain ⟨w, hw, -⟩ := hc1 _ (sys.consistentV.mem_generator_domain sys.SV hx)
  exact ⟨w, sys.ιV_injective (by rw [← ιWV_apply]; exact hw)⟩

/-- `W_ℂ ↪ X_ℂ` is injective. -/
theorem injective_ιW_complexify : Function.Injective sys.ιW.complexify :=
  (ContinuousLinearMap.injective_complexify_iff _).2 sys.ιW_injective

/-- The resolvent of `A_{W,ℂ}` at `s ∈ ρ(A_ℂ)`: the restriction of `R(s, A_ℂ)` to `W_ℂ`. -/
theorem exists_isResolvent_W (hc : sys.Compat) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) :
    ∃ R : Complexification W →L[ℂ] Complexification W, IsResolvent sys.AW.complexify s R ∧
      ∀ f, sys.ιW.complexify (R f) = resolvent sys.A.complexify s (sys.ιW.complexify f) := by
  have hinj := injective_ιW_complexify (sys := sys)
  have hex : ∀ f, ∃ w, sys.ιW.complexify w =
      resolvent sys.A.complexify s (sys.ιW.complexify f) := by
    intro f
    obtain ⟨h1, h2⟩ := Submodule.mem_complexify.1 (resolvent_mem_domain hs (sys.ιW.complexify f))
    obtain ⟨w1, e1⟩ := exists_ιW_eq_of_mem_domain hc h1
    obtain ⟨w2, e2⟩ := exists_ιW_eq_of_mem_domain hc h2
    exact ⟨⟨w1, w2⟩, by ext <;> simp [e1, e2]⟩
  choose T hT using hex
  let Tl : Complexification W →ₗ[ℂ] Complexification W :=
    { toFun := T
      map_add' := fun f g => hinj (by rw [hT, map_add, map_add, map_add, hT, hT])
      map_smul' := fun c f => hinj (by rw [hT, map_smul, map_smul, map_smul, hT]; rfl) }
  have hcont : Continuous Tl := Tl.continuous_of_seq_closed_graph fun u x y hu hy => by
    apply hinj
    have h1 : Tendsto (fun n => sys.ιW.complexify (T (u n))) atTop
        (𝓝 (sys.ιW.complexify y)) := (sys.ιW.complexify.continuous.tendsto y).comp hy
    have h2 : Tendsto (fun n => sys.ιW.complexify (T (u n))) atTop
        (𝓝 (resolvent sys.A.complexify s (sys.ιW.complexify x))) := by
      simp_rw [hT]
      exact (((resolvent sys.A.complexify s).comp sys.ιW.complexify).continuous.tendsto x).comp hu
    rw [tendsto_nhds_unique h1 h2]
    exact (hT x).symm
  refine ⟨⟨Tl, hcont⟩, ⟨fun f => ?_, fun w => ?_⟩, hT⟩
  · have hx := resolvent_mem_domain hs (sys.ιW.complexify f)
    have hAx := sub_resolvent hs (sys.ιW.complexify f)
    have hAx' : sys.A.complexify ⟨_, hx⟩ = sys.ιW.complexify (s • T f - f) := by
      rw [map_sub, map_smul, hT]
      linear_combination (norm := module) -hAx
    obtain ⟨hw1, hA1⟩ := mem_AW_domain_of_ιW (w := (T f).re) (g := (s • T f - f).re)
      (congrArg Complexification.re (hT f)) hx.1 (congrArg Complexification.re hAx')
    obtain ⟨hw2, hA2⟩ := mem_AW_domain_of_ιW (w := (T f).im) (g := (s • T f - f).im)
      (congrArg Complexification.im (hT f)) hx.2 (congrArg Complexification.im hAx')
    refine ⟨⟨hw1, hw2⟩, ?_⟩
    ext
    · show (s • T f).re - sys.AW ⟨(T f).re, hw1⟩ = f.re
      rw [hA1, sub_re, sub_sub_cancel]
    · show (s • T f).im - sys.AW ⟨(T f).im, hw2⟩ = f.im
      rw [hA2, sub_im, sub_sub_cancel]
  · obtain ⟨w, hw1, hw2⟩ := w
    apply hinj
    show sys.ιW.complexify (T _) = _
    rw [hT]
    have hd : sys.ιW.complexify w ∈ sys.A.complexify.domain :=
      ⟨sys.consistentW.mem_generator_domain sys.SX hw1,
        sys.consistentW.mem_generator_domain sys.SX hw2⟩
    have e : sys.ιW.complexify (s • w - sys.AW.complexify ⟨w, hw1, hw2⟩) =
        s • sys.ιW.complexify w - sys.A.complexify ⟨_, hd⟩ := by
      rw [map_sub, map_smul]
      congr 1
      ext
      · exact (sys.consistentW.generator_apply sys.SX hw1).symm
      · exact (sys.consistentW.generator_apply sys.SX hw2).symm
    rw [e]
    exact resolvent_sub hs ⟨_, hd⟩

/-- `ρ(A) ⊆ ρ(A_W)` under `hyp:compat` (`app:analytic-universal-sufficiency`: for `f ∈ W`,
`w = R(s, A) f` has `A w = s w - f ∈ W`, so `w ∈ D(A_W)`). -/
theorem resolventSet_complexify_subset_W (hc : sys.Compat) :
    resolventSet sys.A.complexify ⊆ resolventSet sys.AW.complexify := fun _ hs =>
  let ⟨R, hR, _⟩ := exists_isResolvent_W hc hs
  ⟨R, hR⟩

/-- The resolvents of `A` and `A_W` agree on `W` (`app:analytic-universal-sufficiency`). -/
theorem ιW_resolvent_W (hc : sys.Compat) {s : ℂ} (hs : s ∈ resolventSet sys.A.complexify)
    (w : Complexification W) :
    sys.ιW.complexify (resolvent sys.AW.complexify s w) =
      resolvent sys.A.complexify s (sys.ιW.complexify w) := by
  obtain ⟨R, hR, hRι⟩ := exists_isResolvent_W hc hs
  rw [resolvent_eq hR, hRι]

/-- `Q_a - (s - a) R(s, A_W) Q_a ∈ L(U_ℂ, W_ℂ)` represents `transferX s` (formula with any
real `a`). -/
theorem ιW_comp_transferW (hc : sys.Compat) {a : ℝ} {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) :
    sys.ιW.complexify.comp ((sys.Q a).complexify -
        (s - (a : ℂ)) • (resolvent sys.AW.complexify s).comp (sys.Q a).complexify) =
      (sys.ιW.comp (sys.Q a)).complexify -
        (s - (a : ℂ)) • (resolvent sys.A.complexify s).comp
          (sys.ιW.comp (sys.Q a)).complexify := by
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, sub_apply, smul_apply, map_sub, map_smul,
    ιW_resolvent_W hc hs, ContinuousLinearMap.complexify_comp]

/-- **`𝐇(s) ∈ L(U_ℂ, W_ℂ)`** for `s ∈ ρ(A)` (`app:analytic-universal-sufficiency`): under
`hyp:H1` and `hyp:compat`, `𝐇(s) = ιW ∘ transfer s`. -/
theorem ιW_transfer {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {s : ℂ}
    (hs : s ∈ resolventSet sys.A.complexify) :
    sys.ιW.complexify.comp (sys.transfer s) = sys.transferX s := by
  obtain ⟨r₀, hr₀⟩ := exists_QSpec hH1 hT
  have h : ∃ a, sys.QSpec a := ⟨r₀, hr₀ r₀ le_rfl⟩
  have hex : ∃ H : Complexification U →L[ℂ] Complexification W,
      sys.ιW.complexify.comp H = sys.transferX s := by
    refine ⟨_, ιW_comp_transferW (a := h.choose) hc hs |>.trans ?_⟩
    rw [transferX, dite_eq_left h]
  rw [transfer, dite_eq_left hex]
  exact hex.choose_spec

/-- `𝐇(s) = Q_a - (s - a) R(s, A_W) Q_a` in `L(U_ℂ, W_ℂ)` for every admissible real `a` and
`s ∈ ρ(A)` (`app:analytic-universal-sufficiency`). -/
theorem transfer_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {a : ℝ}
    (ha : sys.QSpec a) {s : ℂ} (hs : s ∈ resolventSet sys.A.complexify) :
    sys.transfer s = (sys.Q a).complexify -
      (s - (a : ℂ)) • (resolvent sys.AW.complexify s).comp (sys.Q a).complexify := by
  ext1 v
  apply injective_ιW_complexify (sys := sys)
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ιW_transfer hH1 hT hc hs,
    ιW_comp_transferW hc hs, transferX_eq hH1 hT ha hs]

/-- For admissible real `r`, `𝐇(r) = Q_r = (r - A_V)⁻¹ B` (`app:control-realization`). -/
theorem transfer_ofReal {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) {r : ℝ}
    (hr : sys.QSpec r) : sys.transfer (r : ℂ) = (sys.Q r).complexify := by
  rw [transfer_eq hH1 hT hc hr (ofReal_mem_resolventSet_complexify hr.1)]
  ext1 v
  simp

/-- **Holomorphy of the transfer map** (`app:analytic-universal-sufficiency`): under `hyp:H1`
and `hyp:compat`, `𝐇` is holomorphic on `ρ(A)` with values in `L(U_ℂ, W_ℂ)`. -/
theorem differentiableOn_transfer {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) :
    DifferentiableOn ℂ sys.transfer (resolventSet sys.A.complexify) := by
  obtain ⟨r₀, hr₀⟩ := exists_QSpec hH1 hT
  have ha := hr₀ r₀ le_rfl
  -- `s ↦ s • id` as a bounded linear map (avoids scalar-function `smul` lemmas)
  set Φ : ℂ →L[ℂ] (Complexification U →L[ℂ] Complexification U) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ (Complexification U))
  have hΦ : ∀ s : ℂ, Φ s = s • ContinuousLinearMap.id ℂ (Complexification U) := fun s => rfl
  have h := (differentiableOn_const (sys.Q r₀).complexify).sub
    ((((differentiableOn_resolvent sys.AW.complexify).mono
      (resolventSet_complexify_subset_W hc)).clm_comp
      (differentiableOn_const (sys.Q r₀).complexify)).clm_comp
      ((Φ.differentiable.comp (differentiable_id.sub_const (r₀ : ℂ))).differentiableOn))
  refine h.congr fun s hs => ?_
  rw [transfer_eq hH1 hT hc ha hs]
  simp only [Pi.sub_apply, Function.comp_apply, hΦ, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, id]

/-- **Decay of the transfer map** (`app:analytic-universal-sufficiency`, from
`eq:control-resolvent-decay`): `‖𝐇(r)‖_{L(U_ℂ, W_ℂ)} = O(r^{-1/2})` as `r → +∞`. -/
theorem transfer_decay {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hc : sys.Compat) :
    ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      (r : ℂ) ∈ resolventSet sys.A.complexify ∧ ‖sys.transfer (r : ℂ)‖ ≤ K / Real.sqrt r := by
  obtain ⟨K, r₁, hr₁, hK⟩ := Q_decay hH1 hT
  obtain ⟨r₂, hr₂⟩ := exists_QSpec hH1 hT
  refine ⟨K, max r₁ r₂, lt_max_of_lt_left hr₁, fun r hr => ?_⟩
  have hq := hr₂ r (le_of_max_le_right hr)
  refine ⟨ofReal_mem_resolventSet_complexify hq.1, ?_⟩
  rw [transfer_ofReal hH1 hT hc hq, ContinuousLinearMap.norm_complexify]
  exact hK r (le_of_max_le_left hr)

/-- **The component `Ω_⋆`** (`app:analytic-universal-sufficiency`): if `‖S t‖ ≤ M e^{σ t}` and
`K ⊆ ρ(A)` lies in `{Re s ≥ σ}`, then there is an open preconnected `Ω_⋆ ⊆ ρ(A)` containing `K`
and the half-plane `{Re s > σ}` (every point of `K` has a disc in `ρ(A)` meeting the
half-plane). -/
theorem exists_isPreconnected_resolventSet {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) {K : Set ℂ}
    (hK : K ⊆ resolventSet sys.A.complexify) (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ IsPreconnected Ω ∧ Ω ⊆ resolventSet sys.A.complexify ∧
      {s : ℂ | σ < s.re} ⊆ Ω ∧ K ⊆ Ω := by
  set H : Set ℂ := {s : ℂ | σ < s.re} with hHdef
  have hH : H ⊆ resolventSet sys.A.complexify := fun s hs =>
    sys.SX.mem_resolventSet_complexify hS hs
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hHc : IsPreconnected H := (convex_halfSpace_re_gt σ).isPreconnected
  have hε : ∀ s ∈ K, ∃ ε > 0, Metric.ball s ε ⊆ resolventSet sys.A.complexify := fun s hs =>
    Metric.isOpen_iff.1 (isOpen_resolventSet sys.A.complexify) s (hK hs)
  choose! ε hεpos hεsub using hε
  let F : Option K → Set ℂ := fun o => match o with
    | none => H
    | some s => H ∪ Metric.ball (s : ℂ) (ε s)
  have hσ1 : ((σ + 1 : ℝ) : ℂ) ∈ H := by simp [hHdef]
  refine ⟨⋃ o, F o, isOpen_iUnion fun o => ?_, isPreconnected_iUnion ⟨((σ + 1 : ℝ) : ℂ), mem_iInter.2 fun o => ?_⟩
    fun o => ?_, iUnion_subset fun o => ?_, subset_iUnion F none,
    fun s hs => mem_iUnion.2 ⟨some ⟨s, hs⟩, Or.inr (Metric.mem_ball_self (hεpos s hs))⟩⟩
  · rcases o with _ | s
    · exact hHo
    · exact hHo.union Metric.isOpen_ball
  · rcases o with _ | s
    · exact hσ1
    · exact Or.inl hσ1
  · rcases o with _ | ⟨s, hs⟩
    · exact hHc
    · refine IsPreconnected.union' ⟨s + ((ε s / 2 : ℝ) : ℂ), ?_, ?_⟩ hHc
        (convex_ball _ _).isPreconnected
      · show σ < (s + ((ε s / 2 : ℝ) : ℂ)).re
        have := hεpos s hs
        have := hKσ s hs
        simp only [Complex.add_re, Complex.ofReal_re]
        linarith
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos (hεpos s hs))]
        exact half_lt_self (hεpos s hs)
  · rcases o with _ | ⟨s, hs⟩
    · exact hH
    · exact union_subset hH (hεsub s hs)

end System

end DataDrivenControl
