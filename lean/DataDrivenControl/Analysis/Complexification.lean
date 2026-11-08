module

public import Mathlib

/-!
# Complexification of real Hilbert spaces

The paper states every theorem for **real** Hilbert spaces and passes to the complexification
`H_ℂ` where complex spectra or frequencies enter: Sec. 3.5 (`def:harmonic-signal`,
`def:harmonic-pe`, `thm:analytic-universal-sufficiency`, with proofs in `app:harmonic-pe` and
`app:analytic-universal-sufficiency`) and Sec. 5 (`prop:fattorini-hautus`,
`thm:data-fattorini-hautus`, `thm:io-window-controllability`, with proofs in
`app:data-fattorini-hautus` and `app:io-window-controllability`).  Mathlib has no
complexification of real normed spaces, so this file builds one.

## The pairing convention

The paper (Introduction, *Notation*) writes `⟨·,·⟩_H` on `H_ℂ` for the **complex-bilinear**
extension of the real inner product,
`⟨a + i b, c + i d⟩ = ⟨a, c⟩ - ⟨b, d⟩ + i (⟨a, d⟩ + ⟨b, c⟩)`.
The proofs depend on this choice: in `app:data-fattorini-hautus`, `A^⋆ η = λ η` gives
`d/dt ⟨η, x̄(t)⟩ = ⟨A^⋆ η, x̄(t)⟩ = λ ⟨η, x̄(t)⟩` (Step 1), and Step 2 says explicitly "using
the complex-bilinear convention for the pairing gives `ẏ_η = λ y_η = ⟨λη, x̄⟩`".  With a
Hermitian product, Step 1 would produce `conj λ` instead of `λ`.  We therefore keep two products
on `X_ℂ`:

* the Hermitian inner product `⟪η, ζ⟫_ℂ`, Mathlib's (conjugate-linear in `η`), which makes
  `Complexification X` a complex Hilbert space, so that Mathlib's adjoints, orthogonal
  complements and `L²` spaces apply;
* the bilinear pairing `⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ`, the paper's `⟨η, ζ⟩`.

For the complexification of a *real* operator, the Hermitian adjoint and the bilinear transpose
are the same operator (`ContinuousLinearMap.adjoint_complexify`,
`ContinuousLinearMap.pairing_complexify_left`, `LinearPMap.adjoint_complexify`), so the
paper's `A^⋆` on `X_ℂ` is unambiguous: it is `A.adjoint.complexify`.

## Main definitions

* `Complexification X`: the paper's `X_ℂ`, pairs `⟨re, im⟩` read as `re + i im`, so that
  `Complex.I • ⟨x, y⟩ = ⟨-y, x⟩`.  It is a complex inner product space
  (`‖z‖² = ‖z.re‖² + ‖z.im‖²`), complete and separable when `X` is, with the Borel σ-algebra;
  as a real space (`Module.complexToReal`, an instance here) its inner product is
  `⟪z, w⟫_ℝ = ⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ`.
* `(x : Complexification X)` (`Complexification.ofReal`): the real embedding; `ofRealCLM`,
  `ofRealLI`, `reCLM`, `imCLM`; `mk_eq_add_I_smul : ⟨x, y⟩ = ↑x + I • ↑y`;
  `tendsto_iff`, `continuous_iff` (componentwise); `integral_re`, `integral_im`,
  `integral_ofReal`.
* `star z`: the conjugation `re - i im` (a `StarModule ℂ`); `star z = z ↔ z.im = 0`.
* `Complexification.pairing η ζ`, notation `⟪η, ζ⟫_bil`, and `pairingCLM`; it is symmetric,
  bilinear, nondegenerate already on real vectors (`pairing_ofReal_eq_zero_forall_iff`),
  bounded (`norm_pairing_le`), commutes with integrals (`pairing_integral`), and
  `⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ` (`pairing_eq_inner_star`).
* `LinearMap.complexify`, `ContinuousLinearMap.complexify`, `LinearPMap.complexify`,
  `Submodule.complexify`: `T_ℂ (x + i y) = T x + i T y`, `D_ℂ = D + i D`.

## Main statements

* `ContinuousLinearMap.complexify` is functorial (`complexify_id`, `complexify_comp`,
  `complexify_one`), real-linear, isometric (`norm_complexify`), and commutes with adjoints
  (`adjoint_complexify`) and kernels (`ker_complexify`, `injective_complexify_iff`).
* `LinearPMap.adjoint_complexify`: `(A_ℂ)† = (A†)_ℂ` for every real `A`, domains included
  (`mem_adjoint_domain_complexify_iff`); this is what makes `ker (A^⋆ - λ id_{X_ℂ})` in
  `prop:fattorini-hautus` the kernel of a complexified operator.
* `Submodule.topologicalClosure_complexify`, `Submodule.dense_complexify_iff`.
* `pairing_ofReal_add_pairing_ofReal_eq_zero_iff`: a complex test vector annihilates a
  two-component real record iff its real and imaginary parts do.

C₀-semigroups are not complexified here: `C0Semigroup.complexify` is in
`Informativity/Analytic/Transfer`, built on `complexify_one`, `complexify_comp` and
`Complexification.continuous_mk`.
-/

@[expose] public section

open Filter Topology MeasureTheory

noncomputable section

namespace DataDrivenControl

/-- The complexification `X_ℂ = X ⊕ i X` of a real vector space `X`: a vector `z` is the pair
`(z.re, z.im)`, read as `z.re + i z.im`.  It is the paper's `X_ℂ` (Introduction, *Notation*). -/
@[ext]
structure Complexification (X : Type*) where
  /-- The real part of `z = z.re + i z.im`. -/
  re : X
  /-- The imaginary part of `z = z.re + i z.im`. -/
  im : X

namespace Complexification

variable {X Y Z : Type*}

/-! ### Additive structure, the real embedding and conjugation -/

section AddCommGroup

variable [AddCommGroup X]

instance : Zero (Complexification X) := ⟨⟨0, 0⟩⟩
instance : Add (Complexification X) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Complexification X) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Complexification X) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance instSMulNat : SMul ℕ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance instSMulInt : SMul ℤ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Complexification X).re = 0 := rfl
@[simp] theorem zero_im : (0 : Complexification X).im = 0 := rfl
@[simp] theorem add_re (z w : Complexification X) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Complexification X) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Complexification X) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Complexification X) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Complexification X) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Complexification X) : (z - w).im = z.im - w.im := rfl

/-- The underlying pair `(z.re, z.im)`. -/
def toProd (z : Complexification X) : X × X := (z.re, z.im)

omit [AddCommGroup X] in
theorem toProd_injective : Function.Injective (toProd : Complexification X → X × X) := by
  intro z w h
  simp only [toProd, Prod.mk.injEq] at h
  exact Complexification.ext h.1 h.2

instance : AddCommGroup (Complexification X) :=
  toProd_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem nsmul_re (n : ℕ) (z : Complexification X) : (n • z).re = n • z.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (z : Complexification X) : (n • z).im = n • z.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (z : Complexification X) : (n • z).re = n • z.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (z : Complexification X) : (n • z).im = n • z.im := rfl

omit [AddCommGroup X] in
@[simp] theorem eta (z : Complexification X) : (⟨z.re, z.im⟩ : Complexification X) = z := rfl

theorem mk_add_mk (x y x' y' : X) :
    (⟨x, y⟩ + ⟨x', y'⟩ : Complexification X) = ⟨x + x', y + y'⟩ := rfl

/-- The real embedding `x ↦ x + i 0` of `X` into `X_ℂ`, used as a coercion. -/
@[coe] def ofReal (x : X) : Complexification X := ⟨x, 0⟩

instance : Coe X (Complexification X) := ⟨ofReal⟩

@[simp] theorem ofReal_re (x : X) : (x : Complexification X).re = x := rfl
@[simp] theorem ofReal_im (x : X) : (x : Complexification X).im = 0 := rfl

@[simp, norm_cast] theorem ofReal_zero : ((0 : X) : Complexification X) = 0 := rfl

@[simp, norm_cast] theorem ofReal_add (x y : X) :
    ((x + y : X) : Complexification X) = x + y := by
  ext <;> simp

@[simp, norm_cast] theorem ofReal_neg (x : X) : ((-x : X) : Complexification X) = -x := by
  ext <;> simp

@[simp, norm_cast] theorem ofReal_sub (x y : X) :
    ((x - y : X) : Complexification X) = x - y := by
  ext <;> simp

theorem ofReal_injective : Function.Injective (ofReal : X → Complexification X) :=
  fun _ _ h => congrArg re h

@[simp, norm_cast] theorem ofReal_inj {x y : X} :
    (x : Complexification X) = y ↔ x = y :=
  ofReal_injective.eq_iff

@[simp] theorem ofReal_eq_zero {x : X} : (x : Complexification X) = 0 ↔ x = 0 := by
  rw [← ofReal_zero, ofReal_inj]

/-- Conjugation `z̄ = z.re - i z.im` is `star`; the paper's `v̄` (`def:harmonic-signal`). -/
instance : Star (Complexification X) := ⟨fun z => ⟨z.re, -z.im⟩⟩

@[simp] theorem star_re (z : Complexification X) : (star z).re = z.re := rfl
@[simp] theorem star_im (z : Complexification X) : (star z).im = -z.im := rfl

instance : StarAddMonoid (Complexification X) where
  star_involutive z := by ext <;> simp
  star_add z w := by ext <;> simp [add_comm]

@[simp] theorem star_ofReal (x : X) : star (x : Complexification X) = x := by
  ext <;> simp

theorem eq_ofReal_re_iff {z : Complexification X} : z = (z.re : Complexification X) ↔ z.im = 0 := by
  simp [Complexification.ext_iff]

end AddCommGroup

/-! ### The complex vector space structure -/

section Module

variable [AddCommGroup X] [Module ℝ X]

/-- `(a + i b) • (x + i y) = (a x - b y) + i (a y + b x)`. -/
instance : SMul ℂ (Complexification X) :=
  ⟨fun c z => ⟨c.re • z.re - c.im • z.im, c.re • z.im + c.im • z.re⟩⟩

@[simp] theorem smul_re (c : ℂ) (z : Complexification X) :
    (c • z).re = c.re • z.re - c.im • z.im := rfl
@[simp] theorem smul_im (c : ℂ) (z : Complexification X) :
    (c • z).im = c.re • z.im + c.im • z.re := rfl

instance : Module ℂ (Complexification X) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by
    ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul c d z := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re, Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

/-- The real scalar multiplication (restriction of scalars, `Module.complexToReal`) acts
componentwise. -/
@[simp] theorem real_smul_re (r : ℝ) (z : Complexification X) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, smul_re, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

@[simp] theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, smul_im, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- A vector of `X_ℂ` is real iff it is fixed by conjugation. -/
theorem star_eq_self_iff {z : Complexification X} : star z = z ↔ z.im = 0 := by
  simp only [Complexification.ext_iff, star_re, star_im, true_and]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have h2 : (2 : ℝ) • z.im = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel _
  simpa using h2

@[simp] theorem I_smul_re (z : Complexification X) : (Complex.I • z).re = -z.im := by simp
@[simp] theorem I_smul_im (z : Complexification X) : (Complex.I • z).im = z.re := by simp

@[simp, norm_cast] theorem ofReal_smul (r : ℝ) (x : X) :
    ((r • x : X) : Complexification X) = r • (x : Complexification X) := by
  ext <;> simp

/-- The paper's notation `x + i y` for `⟨x, y⟩`. -/
theorem mk_eq_add_I_smul (x y : X) :
    (⟨x, y⟩ : Complexification X) = (x : Complexification X) + Complex.I • (y : Complexification X) := by
  ext <;> simp

theorem re_add_I_smul_im (z : Complexification X) :
    (z.re : Complexification X) + Complex.I • (z.im : Complexification X) = z := by
  ext <;> simp

instance : StarModule ℂ (Complexification X) where
  star_smul c z := by ext <;> simp [add_comm]

end Module

/-! ### The Hermitian inner product, the norm and completeness -/

section Inner

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open scoped InnerProductSpace

/-- The Hermitian inner product of `X_ℂ` (conjugate-linear in the first argument, as in Mathlib):
`⟪a + i b, c + i d⟫_ℂ = ⟪a, c⟫ + ⟪b, d⟫ + i (⟪a, d⟫ - ⟪b, c⟫)`. -/
instance : Inner ℂ (Complexification X) :=
  ⟨fun z w => ⟨⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ, ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ⟩⟩

theorem inner_re (z w : Complexification X) :
    (⟪z, w⟫_ℂ).re = ⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ := rfl

theorem inner_im (z w : Complexification X) :
    (⟪z, w⟫_ℂ).im = ⟪z.re, w.im⟫_ℝ - ⟪z.im, w.re⟫_ℝ := rfl

/-- The inner-product core of `X_ℂ`. -/
@[instance_reducible]
def innerCore : InnerProductSpace.Core ℂ (Complexification X) where
  toInner := inferInstance
  conj_inner_symm z w := by
    apply Complex.ext
    · simp only [Complex.conj_re, inner_re, real_inner_comm]
    · simp only [Complex.conj_im, inner_im, real_inner_comm]; ring
  re_inner_nonneg z := by
    simp only [RCLike.re_to_complex, inner_re]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left z w u := by
    apply Complex.ext
    · simp only [Complex.add_re, inner_re, add_re, add_im, inner_add_left]; ring
    · simp only [Complex.add_im, inner_im, add_re, add_im, inner_add_left]; ring
  smul_left z w c := by
    apply Complex.ext
    · simp only [inner_re, inner_im, smul_re, smul_im, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    · simp only [inner_re, inner_im, smul_re, smul_im, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
  definite z h := by
    have h' : ⟪z.re, z.re⟫_ℝ + ⟪z.im, z.im⟫_ℝ = 0 := by rw [← inner_re, h]; rfl
    have h1 := real_inner_self_nonneg (x := z.re)
    have h2 := real_inner_self_nonneg (x := z.im)
    ext
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)

instance : NormedAddCommGroup (Complexification X) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Complexification X) _ _ _ innerCore

instance : InnerProductSpace ℂ (Complexification X) :=
  InnerProductSpace.ofCore _

/-- `X_ℂ` is also a real inner product space (restriction of scalars).  Mathlib does not make
`InnerProductSpace.complexToReal` a global instance because of diamonds on `PiLp`; on
`Complexification X` there is no competing real structure. -/
instance : InnerProductSpace ℝ (Complexification X) :=
  InnerProductSpace.complexToReal

/-- The real inner product of `X_ℂ` (restriction of scalars) is that of `X × X`. -/
theorem real_inner_eq (z w : Complexification X) :
    ⟪z, w⟫_ℝ = ⟪z.re, w.re⟫_ℝ + ⟪z.im, w.im⟫_ℝ := by
  rw [real_inner_eq_re_inner ℂ]; rfl

theorem norm_sq_eq (z : Complexification X) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_eq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_eq (z : Complexification X) : ‖z‖ = √(‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) := by
  rw [← norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem norm_ofReal (x : X) : ‖(x : Complexification X)‖ = ‖x‖ := by
  simp [norm_eq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_re_le (z : Complexification X) : ‖z.re‖ ≤ ‖z‖ := by
  rw [norm_eq]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.im‖])

theorem norm_im_le (z : Complexification X) : ‖z.im‖ ≤ ‖z‖ := by
  rw [norm_eq]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.re‖])

theorem norm_le_norm_re_add_norm_im (z : Complexification X) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ := by
  rw [norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg z.re, norm_nonneg z.im]

@[simp] theorem inner_ofReal_ofReal (x y : X) :
    ⟪(x : Complexification X), (y : Complexification X)⟫_ℂ = (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp [inner_re, inner_im]

instance : NormedStarGroup (Complexification X) :=
  ⟨fun z => by simp [norm_eq]⟩

/-! ### The real embedding and the real and imaginary parts as operators -/

/-- `re : X_ℂ → X` as a real continuous linear map. -/
def reCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := re, map_add' := add_re, map_smul' := fun r z => by simp } 1
    (fun z => by simpa using norm_re_le z)

/-- `im : X_ℂ → X` as a real continuous linear map. -/
def imCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := im, map_add' := add_im, map_smul' := fun r z => by simp } 1
    (fun z => by simpa using norm_im_le z)

/-- The real embedding `X → X_ℂ` as a real continuous linear map. -/
def ofRealCLM : X →L[ℝ] Complexification X :=
  LinearMap.mkContinuous
    { toFun := ofReal, map_add' := ofReal_add, map_smul' := fun r x => by simp } 1
    (fun x => by simp)

@[simp] theorem reCLM_apply (z : Complexification X) : reCLM z = z.re := rfl
@[simp] theorem imCLM_apply (z : Complexification X) : imCLM z = z.im := rfl
@[simp] theorem ofRealCLM_apply (x : X) : ofRealCLM x = (x : Complexification X) := rfl

@[continuity, fun_prop] theorem continuous_re : Continuous (re : Complexification X → X) :=
  reCLM.continuous

@[continuity, fun_prop] theorem continuous_im : Continuous (im : Complexification X → X) :=
  imCLM.continuous

@[continuity, fun_prop] theorem continuous_ofReal : Continuous (ofReal : X → Complexification X) :=
  ofRealCLM.continuous

/-- The real embedding `X → X_ℂ` as a real linear isometry. -/
def ofRealLI : X →ₗᵢ[ℝ] Complexification X :=
  { (ofRealCLM : X →L[ℝ] Complexification X) with norm_map' := norm_ofReal }

@[simp] theorem ofRealLI_apply (x : X) : ofRealLI x = (x : Complexification X) := rfl

/-- Convergence in `X_ℂ` is convergence of the real and imaginary parts. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {f : ι → Complexification X}
    {z : Complexification X} :
    Tendsto f l (𝓝 z) ↔
      Tendsto (fun i => (f i).re) l (𝓝 z.re) ∧ Tendsto (fun i => (f i).im) l (𝓝 z.im) := by
  refine ⟨fun h => ⟨(continuous_re.tendsto z).comp h, (continuous_im.tendsto z).comp h⟩, ?_⟩
  rintro ⟨h1, h2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2 ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa using h1.add h2)
  exact norm_le_norm_re_add_norm_im (f i - z)

theorem continuous_iff {α : Type*} [TopologicalSpace α] {f : α → Complexification X} :
    Continuous f ↔ Continuous (fun a => (f a).re) ∧ Continuous (fun a => (f a).im) := by
  refine ⟨fun h => ⟨continuous_re.comp h, continuous_im.comp h⟩, fun ⟨h1, h2⟩ => ?_⟩
  exact continuous_iff_continuousAt.2 fun a => tendsto_iff.2 ⟨h1.continuousAt, h2.continuousAt⟩

@[continuity, fun_prop] theorem continuous_mk {α : Type*} [TopologicalSpace α] {f g : α → X}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => (⟨f a, g a⟩ : Complexification X)) :=
  continuous_iff.2 ⟨hf, hg⟩

instance [CompleteSpace X] : CompleteSpace (Complexification X) := by
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    ((reCLM : Complexification X →L[ℝ] X).uniformContinuous.comp_cauchySeq hu)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete
    ((imCLM : Complexification X →L[ℝ] X).uniformContinuous.comp_cauchySeq hu)
  exact ⟨⟨a, b⟩, tendsto_iff.2 ⟨ha, hb⟩⟩

instance : MeasurableSpace (Complexification X) := borel _

instance : BorelSpace (Complexification X) := ⟨rfl⟩

instance [TopologicalSpace.SeparableSpace X] :
    TopologicalSpace.SeparableSpace (Complexification X) := by
  have hc : Continuous (fun p : X × X => (⟨p.1, p.2⟩ : Complexification X)) :=
    continuous_mk continuous_fst continuous_snd
  exact DenseRange.separableSpace (Function.Surjective.denseRange fun z => ⟨(z.re, z.im), rfl⟩) hc

/-- Real and imaginary parts commute with Bochner integrals. -/
theorem integral_re {α : Type*} [MeasurableSpace α] {μ : Measure α} [CompleteSpace X]
    {f : α → Complexification X} (hf : Integrable f μ) :
    (∫ a, f a ∂μ).re = ∫ a, (f a).re ∂μ :=
  ((reCLM : Complexification X →L[ℝ] X).integral_comp_comm hf).symm

theorem integral_im {α : Type*} [MeasurableSpace α] {μ : Measure α} [CompleteSpace X]
    {f : α → Complexification X} (hf : Integrable f μ) :
    (∫ a, f a ∂μ).im = ∫ a, (f a).im ∂μ :=
  ((imCLM : Complexification X →L[ℝ] X).integral_comp_comm hf).symm

/-- The integral of a real signal, computed in `X_ℂ`, is real. -/
theorem integral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [CompleteSpace X]
    (f : α → X) :
    ∫ a, (f a : Complexification X) ∂μ = ((∫ a, f a ∂μ : X) : Complexification X) :=
  (ofRealLI : X →ₗᵢ[ℝ] Complexification X).integral_comp_comm f

end Inner

/-! ### The complex-bilinear pairing -/

section Pairing

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open scoped InnerProductSpace

/-- The complex-bilinear extension of the real inner product to `X_ℂ`, the paper's `⟨η, ζ⟩_X`
on complexified spaces (Introduction, *Notation*):
`⟨a + i b, c + i d⟩ = ⟨a, c⟩ - ⟨b, d⟩ + i (⟨a, d⟩ + ⟨b, c⟩)`.
It is `ℂ`-linear in both arguments, symmetric, and `⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ`. -/
def pairing (η ζ : Complexification X) : ℂ :=
  ⟨⟪η.re, ζ.re⟫_ℝ - ⟪η.im, ζ.im⟫_ℝ, ⟪η.re, ζ.im⟫_ℝ + ⟪η.im, ζ.re⟫_ℝ⟩

@[inherit_doc] notation:max "⟪" η ", " ζ "⟫_bil" => DataDrivenControl.Complexification.pairing η ζ

@[simp] theorem pairing_re (η ζ : Complexification X) :
    (⟪η, ζ⟫_bil).re = ⟪η.re, ζ.re⟫_ℝ - ⟪η.im, ζ.im⟫_ℝ := rfl

@[simp] theorem pairing_im (η ζ : Complexification X) :
    (⟪η, ζ⟫_bil).im = ⟪η.re, ζ.im⟫_ℝ + ⟪η.im, ζ.re⟫_ℝ := rfl

theorem pairing_comm (η ζ : Complexification X) : ⟪η, ζ⟫_bil = ⟪ζ, η⟫_bil := by
  apply Complex.ext <;> simp [real_inner_comm, add_comm]

@[simp] theorem pairing_add_left (η η' ζ : Complexification X) :
    ⟪η + η', ζ⟫_bil = ⟪η, ζ⟫_bil + ⟪η', ζ⟫_bil := by
  apply Complex.ext <;> simp [inner_add_left] <;> ring

@[simp] theorem pairing_add_right (η ζ ζ' : Complexification X) :
    ⟪η, ζ + ζ'⟫_bil = ⟪η, ζ⟫_bil + ⟪η, ζ'⟫_bil := by
  rw [pairing_comm, pairing_add_left, pairing_comm, pairing_comm ζ']

@[simp] theorem pairing_smul_left (c : ℂ) (η ζ : Complexification X) :
    ⟪c • η, ζ⟫_bil = c * ⟪η, ζ⟫_bil := by
  apply Complex.ext <;>
    simp [inner_sub_left, inner_add_left, real_inner_smul_left, Complex.mul_re,
      Complex.mul_im] <;> ring

@[simp] theorem pairing_smul_right (c : ℂ) (η ζ : Complexification X) :
    ⟪η, c • ζ⟫_bil = c * ⟪η, ζ⟫_bil := by
  rw [pairing_comm, pairing_smul_left, pairing_comm]

@[simp] theorem pairing_zero_left (ζ : Complexification X) : ⟪0, ζ⟫_bil = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem pairing_zero_right (η : Complexification X) : ⟪η, 0⟫_bil = 0 := by
  apply Complex.ext <;> simp

@[simp] theorem pairing_neg_left (η ζ : Complexification X) : ⟪-η, ζ⟫_bil = -⟪η, ζ⟫_bil := by
  rw [← neg_one_smul ℂ η, pairing_smul_left, neg_one_mul]

@[simp] theorem pairing_neg_right (η ζ : Complexification X) : ⟪η, -ζ⟫_bil = -⟪η, ζ⟫_bil := by
  rw [← neg_one_smul ℂ ζ, pairing_smul_right, neg_one_mul]

@[simp] theorem pairing_sub_left (η η' ζ : Complexification X) :
    ⟪η - η', ζ⟫_bil = ⟪η, ζ⟫_bil - ⟪η', ζ⟫_bil := by
  rw [sub_eq_add_neg, pairing_add_left, pairing_neg_left, ← sub_eq_add_neg]

@[simp] theorem pairing_sub_right (η ζ ζ' : Complexification X) :
    ⟪η, ζ - ζ'⟫_bil = ⟪η, ζ⟫_bil - ⟪η, ζ'⟫_bil := by
  rw [sub_eq_add_neg, pairing_add_right, pairing_neg_right, ← sub_eq_add_neg]

/-- On real vectors the pairing is the real inner product. -/
@[simp] theorem pairing_ofReal_ofReal (x y : X) :
    ⟪(x : Complexification X), (y : Complexification X)⟫_bil = (⟪x, y⟫_ℝ : ℂ) := by
  apply Complex.ext <;> simp

/-- Pairing a complex vector with a real one: the real and imaginary parts are real inner
products. -/
theorem pairing_ofReal_right (η : Complexification X) (x : X) :
    ⟪η, (x : Complexification X)⟫_bil = ⟨⟪η.re, x⟫_ℝ, ⟪η.im, x⟫_ℝ⟩ := by
  apply Complex.ext <;> simp

/-- The bilinear pairing is the Hermitian product with the first argument conjugated. -/
theorem pairing_eq_inner_star (η ζ : Complexification X) : ⟪η, ζ⟫_bil = ⟪star η, ζ⟫_ℂ := by
  apply Complex.ext <;> simp [inner_re, inner_im]
  ring

/-- The Hermitian product is the bilinear pairing with the first argument conjugated. -/
theorem inner_eq_pairing_star (η ζ : Complexification X) : ⟪η, ζ⟫_ℂ = ⟪star η, ζ⟫_bil := by
  rw [pairing_eq_inner_star, star_star]

theorem norm_pairing_le (η ζ : Complexification X) : ‖⟪η, ζ⟫_bil‖ ≤ ‖η‖ * ‖ζ‖ := by
  rw [pairing_eq_inner_star, ← norm_star η]
  exact norm_inner_le_norm _ _

/-- The pairing as a continuous bilinear map. -/
def pairingCLM : Complexification X →L[ℂ] Complexification X →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ pairing pairing_add_left (fun c η ζ => pairing_smul_left c η ζ)
      pairing_add_right (fun c η ζ => pairing_smul_right c η ζ)) 1
    (fun η ζ => by simpa using norm_pairing_le η ζ)

@[simp] theorem pairingCLM_apply (η ζ : Complexification X) : pairingCLM η ζ = ⟪η, ζ⟫_bil :=
  rfl

@[continuity, fun_prop] theorem _root_.Continuous.pairing {α : Type*} [TopologicalSpace α]
    {f g : α → Complexification X} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun a => ⟪f a, g a⟫_bil :=
  (pairingCLM : Complexification X →L[ℂ] _).continuous₂.comp (hf.prodMk hg)

/-- The pairing commutes with Bochner integrals. -/
theorem pairing_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [CompleteSpace X]
    (η : Complexification X) {f : α → Complexification X} (hf : Integrable f μ) :
    ⟪η, ∫ a, f a ∂μ⟫_bil = ∫ a, ⟪η, f a⟫_bil ∂μ :=
  ((pairingCLM η).integral_comp_comm hf).symm

/-- A complex test vector annihilates a real vector iff its real and imaginary parts do. -/
theorem pairing_ofReal_eq_zero_iff (η : Complexification X) (x : X) :
    ⟪η, (x : Complexification X)⟫_bil = 0 ↔ ⟪η.re, x⟫_ℝ = 0 ∧ ⟪η.im, x⟫_ℝ = 0 := by
  rw [pairing_ofReal_right, Complex.ext_iff]
  simp

/-- Nondegeneracy, tested on real vectors: `η = 0` iff `⟪η, x⟫_bil = 0` for all real `x`. -/
theorem pairing_ofReal_eq_zero_forall_iff {η : Complexification X} :
    (∀ x : X, ⟪η, (x : Complexification X)⟫_bil = 0) ↔ η = 0 := by
  refine ⟨fun h => ?_, fun h x => by simp [h]⟩
  have h1 := ((pairing_ofReal_eq_zero_iff η η.re).1 (h η.re)).1
  have h2 := ((pairing_ofReal_eq_zero_iff η η.im).1 (h η.im)).2
  ext
  · simpa using (inner_self_eq_zero (𝕜 := ℝ)).1 h1
  · simpa using (inner_self_eq_zero (𝕜 := ℝ)).1 h2

theorem ext_pairing {η η' : Complexification X} (h : ∀ x : X, ⟪η, (x : Complexification X)⟫_bil =
    ⟪η', (x : Complexification X)⟫_bil) : η = η' :=
  sub_eq_zero.1 <| pairing_ofReal_eq_zero_forall_iff.1 fun x => by simp [h x]

/-- Two-component version (records `(u, x) ∈ U × X` with test vectors `(α, β) ∈ U_ℂ × X_ℂ`, as
in `def:hilbert-informative` and `app:data-fattorini-hautus`, Step 2): a complex annihilator
splits into two real ones. -/
theorem pairing_ofReal_add_pairing_ofReal_eq_zero_iff [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] (α : Complexification Y) (β : Complexification X) (u : Y) (x : X) :
    ⟪α, (u : Complexification Y)⟫_bil + ⟪β, (x : Complexification X)⟫_bil = 0 ↔
      ⟪α.re, u⟫_ℝ + ⟪β.re, x⟫_ℝ = 0 ∧ ⟪α.im, u⟫_ℝ + ⟪β.im, x⟫_ℝ = 0 := by
  rw [pairing_ofReal_right, pairing_ofReal_right, Complex.ext_iff]
  simp

end Pairing

/-! ### Annihilators of real signals -/

section Annihilator

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

open scoped InnerProductSpace

end Annihilator

end Complexification

end DataDrivenControl

/-!
### Complexified subspaces and operators

These extend Mathlib's namespaces (`Submodule`, `LinearMap`, `ContinuousLinearMap`,
`LinearPMap`), so that dot notation works: `K.complexify`, `T.complexify`, `A.complexify`.
-/

open DataDrivenControl (Complexification)

open scoped InnerProductSpace

/-! #### Subspaces -/

namespace Submodule

section Algebraic

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The complexification `K_ℂ = K + i K` of a real subspace `K`. -/
def complexify (K : Submodule ℝ X) : Submodule ℂ (Complexification X) where
  carrier := {z | z.re ∈ K ∧ z.im ∈ K}
  add_mem' hz hw := ⟨K.add_mem hz.1 hw.1, K.add_mem hz.2 hw.2⟩
  zero_mem' := ⟨K.zero_mem, K.zero_mem⟩
  smul_mem' _ _ hz := ⟨K.sub_mem (K.smul_mem _ hz.1) (K.smul_mem _ hz.2),
    K.add_mem (K.smul_mem _ hz.2) (K.smul_mem _ hz.1)⟩

@[simp] theorem mem_complexify {K : Submodule ℝ X} {z : Complexification X} :
    z ∈ K.complexify ↔ z.re ∈ K ∧ z.im ∈ K :=
  Iff.rfl

@[simp] theorem ofReal_mem_complexify {K : Submodule ℝ X} {x : X} :
    (x : Complexification X) ∈ K.complexify ↔ x ∈ K := by
  simp [K.zero_mem]

theorem complexify_mono {K L : Submodule ℝ X} (h : K ≤ L) : K.complexify ≤ L.complexify :=
  fun _ hz => ⟨h hz.1, h hz.2⟩

@[simp] theorem complexify_le_complexify_iff {K L : Submodule ℝ X} :
    K.complexify ≤ L.complexify ↔ K ≤ L :=
  ⟨fun h _ hx => ofReal_mem_complexify.1 (h (ofReal_mem_complexify.2 hx)), complexify_mono⟩

theorem complexify_injective :
    Function.Injective (complexify : Submodule ℝ X → Submodule ℂ (Complexification X)) :=
  fun _ _ h => le_antisymm (complexify_le_complexify_iff.1 h.le) (complexify_le_complexify_iff.1 h.ge)

@[simp] theorem complexify_inj {K L : Submodule ℝ X} : K.complexify = L.complexify ↔ K = L :=
  complexify_injective.eq_iff

@[simp] theorem complexify_bot : (⊥ : Submodule ℝ X).complexify = ⊥ := by
  ext z
  simp [Complexification.ext_iff]

@[simp] theorem complexify_top : (⊤ : Submodule ℝ X).complexify = ⊤ := by
  ext z
  simp

@[simp] theorem complexify_eq_bot_iff {K : Submodule ℝ X} : K.complexify = ⊥ ↔ K = ⊥ := by
  rw [← complexify_bot, complexify_inj]

@[simp] theorem complexify_eq_top_iff {K : Submodule ℝ X} : K.complexify = ⊤ ↔ K = ⊤ := by
  rw [← complexify_top, complexify_inj]

end Algebraic

section Normed

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Closure commutes with complexification. -/
theorem topologicalClosure_complexify (K : Submodule ℝ X) :
    K.complexify.topologicalClosure = K.topologicalClosure.complexify := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (complexify_mono K.le_topologicalClosure) ?_
    exact (K.isClosed_topologicalClosure.preimage Complexification.continuous_re).inter
      (K.isClosed_topologicalClosure.preimage Complexification.continuous_im)
  · have hofReal : ∀ x ∈ K.topologicalClosure,
        (x : Complexification X) ∈ K.complexify.topologicalClosure := by
      intro x hx
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx ⊢
      refine closure_mono ?_ (image_closure_subset_closure_image
        Complexification.continuous_ofReal ⟨x, hx, rfl⟩)
      rintro _ ⟨y, hy, rfl⟩
      exact ofReal_mem_complexify.2 hy
    intro z hz
    rw [← Complexification.re_add_I_smul_im z]
    exact add_mem (hofReal _ hz.1) (Submodule.smul_mem _ _ (hofReal _ hz.2))

theorem isClosed_complexify_iff {K : Submodule ℝ X} :
    IsClosed (K.complexify : Set (Complexification X)) ↔ IsClosed (K : Set X) := by
  constructor
  · intro h
    have hK : (K : Set X) = Complexification.ofReal ⁻¹' (K.complexify : Set (Complexification X)) := by
      ext x
      simp
    rw [hK]
    exact h.preimage Complexification.continuous_ofReal
  · intro h
    exact (h.preimage Complexification.continuous_re).inter
      (h.preimage Complexification.continuous_im)

/-- `K_ℂ` is dense in `X_ℂ` iff `K` is dense in `X`. -/
theorem dense_complexify_iff {K : Submodule ℝ X} :
    Dense (K.complexify : Set (Complexification X)) ↔ Dense (K : Set X) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.dense_iff_topologicalClosure_eq_top,
    topologicalClosure_complexify, complexify_eq_top_iff]

end Normed

end Submodule

/-! #### Linear maps -/

namespace LinearMap

variable {X Y Z : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup Z] [Module ℝ Z]

/-- The complexification `T_ℂ (x + i y) = T x + i T y` of a real linear map. -/
def complexify (T : X →ₗ[ℝ] Y) : Complexification X →ₗ[ℂ] Complexification Y where
  toFun z := ⟨T z.re, T z.im⟩
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp

@[simp] theorem complexify_apply_re (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    (T.complexify z).re = T z.re :=
  rfl

@[simp] theorem complexify_apply_im (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    (T.complexify z).im = T z.im :=
  rfl

theorem complexify_apply (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    T.complexify z = ⟨T z.re, T z.im⟩ :=
  rfl

@[simp] theorem complexify_ofReal (T : X →ₗ[ℝ] Y) (x : X) :
    T.complexify (x : Complexification X) = (T x : Complexification Y) := by
  ext <;> simp

theorem complexify_star (T : X →ₗ[ℝ] Y) (z : Complexification X) :
    T.complexify (star z) = star (T.complexify z) := by
  ext <;> simp

@[simp] theorem complexify_id : (LinearMap.id : X →ₗ[ℝ] X).complexify = LinearMap.id := by
  ext <;> rfl

theorem complexify_comp (S : Y →ₗ[ℝ] Z) (T : X →ₗ[ℝ] Y) :
    (S ∘ₗ T).complexify = S.complexify ∘ₗ T.complexify := by
  ext <;> rfl

theorem ker_complexify (T : X →ₗ[ℝ] Y) : ker T.complexify = (ker T).complexify := by
  ext z
  simp [Complexification.ext_iff]

theorem injective_complexify_iff (T : X →ₗ[ℝ] Y) :
    Function.Injective T.complexify ↔ Function.Injective T := by
  rw [← ker_eq_bot, ← ker_eq_bot, ker_complexify, Submodule.complexify_eq_bot_iff]

end LinearMap

/-! #### Bounded operators -/

namespace ContinuousLinearMap

variable {X Y Z : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- The complexification `T_ℂ ∈ L(X_ℂ, Y_ℂ)` of a bounded real operator `T ∈ L(X, Y)`,
`T_ℂ (x + i y) = T x + i T y`.  It has the same norm (`norm_complexify`). -/
def complexify (T : X →L[ℝ] Y) : Complexification X →L[ℂ] Complexification Y :=
  LinearMap.mkContinuous (T : X →ₗ[ℝ] Y).complexify ‖T‖ fun z => by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm z.re) 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm z.im) 2
    have h : ‖(T : X →ₗ[ℝ] Y).complexify z‖ ^ 2 ≤ (‖T‖ * ‖z‖) ^ 2 := by
      rw [mul_pow, Complexification.norm_sq_eq, Complexification.norm_sq_eq]
      simp only [LinearMap.complexify_apply_re, LinearMap.complexify_apply_im, coe_coe]
      rw [mul_pow] at h1 h2
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

@[simp] theorem complexify_apply_re (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).re = T z.re :=
  rfl

@[simp] theorem complexify_apply_im (T : X →L[ℝ] Y) (z : Complexification X) :
    (T.complexify z).im = T z.im :=
  rfl

theorem complexify_apply (T : X →L[ℝ] Y) (z : Complexification X) :
    T.complexify z = ⟨T z.re, T z.im⟩ :=
  rfl

@[simp] theorem coe_complexify (T : X →L[ℝ] Y) :
    (T.complexify : Complexification X →ₗ[ℂ] Complexification Y) =
      (T : X →ₗ[ℝ] Y).complexify :=
  rfl

@[simp] theorem complexify_ofReal (T : X →L[ℝ] Y) (x : X) :
    T.complexify (x : Complexification X) = (T x : Complexification Y) := by
  ext <;> simp

theorem complexify_star (T : X →L[ℝ] Y) (z : Complexification X) :
    T.complexify (star z) = star (T.complexify z) := by
  ext <;> simp

theorem norm_complexify_apply_le (T : X →L[ℝ] Y) (z : Complexification X) :
    ‖T.complexify z‖ ≤ ‖T‖ * ‖z‖ :=
  (T.complexify.le_opNorm z).trans <| mul_le_mul_of_nonneg_right
    (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _) (norm_nonneg z)

@[simp] theorem complexify_id :
    (ContinuousLinearMap.id ℝ X).complexify = ContinuousLinearMap.id ℂ (Complexification X) := by
  ext <;> rfl

theorem complexify_comp (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y) :
    (S.comp T).complexify = S.complexify.comp T.complexify := by
  ext <;> rfl

@[simp] theorem complexify_one :
    (1 : X →L[ℝ] X).complexify = (1 : Complexification X →L[ℂ] Complexification X) :=
  complexify_id

@[simp] theorem complexify_zero : (0 : X →L[ℝ] Y).complexify = 0 := by
  ext <;> simp

theorem complexify_add (S T : X →L[ℝ] Y) : (S + T).complexify = S.complexify + T.complexify := by
  ext <;> simp

theorem complexify_smul (r : ℝ) (T : X →L[ℝ] Y) : (r • T).complexify = (r : ℂ) • T.complexify := by
  ext <;> simp

/-- Complexification preserves the operator norm. -/
@[simp] theorem norm_complexify (T : X →L[ℝ] Y) : ‖T.complexify‖ = ‖T‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _)
    (T.opNorm_le_bound (norm_nonneg T.complexify) fun x => ?_)
  simpa using T.complexify.le_opNorm (x : Complexification X)

/-- The Hermitian adjoint of a complexified operator is the complexified adjoint. -/
theorem adjoint_complexify [CompleteSpace X] [CompleteSpace Y] (T : X →L[ℝ] Y) :
    adjoint T.complexify = (adjoint T).complexify := by
  refine ((eq_adjoint_iff _ _).2 fun y x => ?_).symm
  apply Complex.ext
  · simp [Complexification.inner_re, adjoint_inner_left]
  · simp [Complexification.inner_im, adjoint_inner_left]

/-- The bilinear transpose of `T_ℂ` is `(T†)_ℂ`: `⟨T_ℂ η, ζ⟩ = ⟨η, (T†)_ℂ ζ⟩`. -/
theorem pairing_complexify_left [CompleteSpace X] [CompleteSpace Y] (T : X →L[ℝ] Y)
    (η : Complexification X) (ζ : Complexification Y) :
    ⟪T.complexify η, ζ⟫_bil = ⟪η, (adjoint T).complexify ζ⟫_bil := by
  apply Complex.ext <;> simp [adjoint_inner_right]

theorem ker_complexify (T : X →L[ℝ] Y) : T.complexify.ker = T.ker.complexify :=
  LinearMap.ker_complexify (T : X →ₗ[ℝ] Y)

theorem injective_complexify_iff (T : X →L[ℝ] Y) :
    Function.Injective T.complexify ↔ Function.Injective T :=
  LinearMap.injective_complexify_iff (T : X →ₗ[ℝ] Y)

end ContinuousLinearMap

/-! #### Unbounded operators -/

namespace LinearPMap

section Algebraic

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- The complexification of a partially defined real operator `A` with domain `D`: the operator
`A_ℂ (x + i y) = A x + i A y` with domain `D_ℂ = D + i D`. -/
def complexify (A : X →ₗ.[ℝ] Y) : Complexification X →ₗ.[ℂ] Complexification Y where
  domain := A.domain.complexify
  toFun :=
    { toFun := fun z => ⟨A ⟨(z : Complexification X).re, (Submodule.mem_complexify.1 z.2).1⟩,
        A ⟨(z : Complexification X).im, (Submodule.mem_complexify.1 z.2).2⟩⟩
      map_add' := fun z w => by
        ext
        · change A ⟨_, _⟩ = A ⟨_, _⟩ + A ⟨_, _⟩
          rw [← LinearPMap.map_add]; rfl
        · change A ⟨_, _⟩ = A ⟨_, _⟩ + A ⟨_, _⟩
          rw [← LinearPMap.map_add]; rfl
      map_smul' := fun c z => by
        ext
        · change A ⟨_, _⟩ = c.re • A ⟨_, _⟩ - c.im • A ⟨_, _⟩
          rw [← LinearPMap.map_smul, ← LinearPMap.map_smul, ← LinearPMap.map_sub]; rfl
        · change A ⟨_, _⟩ = c.re • A ⟨_, _⟩ + c.im • A ⟨_, _⟩
          rw [← LinearPMap.map_smul, ← LinearPMap.map_smul, ← LinearPMap.map_add]; rfl }

@[simp] theorem complexify_domain (A : X →ₗ.[ℝ] Y) : A.complexify.domain = A.domain.complexify :=
  rfl

@[simp] theorem complexify_apply_re (A : X →ₗ.[ℝ] Y) (z : A.complexify.domain) :
    (A.complexify z).re = A ⟨(z : Complexification X).re, (Submodule.mem_complexify.1 z.2).1⟩ :=
  rfl

@[simp] theorem complexify_apply_im (A : X →ₗ.[ℝ] Y) (z : A.complexify.domain) :
    (A.complexify z).im = A ⟨(z : Complexification X).im, (Submodule.mem_complexify.1 z.2).2⟩ :=
  rfl

theorem complexify_apply_ofReal (A : X →ₗ.[ℝ] Y) (x : A.domain) :
    A.complexify ⟨(x : Complexification X), Submodule.ofReal_mem_complexify.2 x.2⟩ =
      (A x : Complexification Y) := by
  ext
  · rfl
  · exact A.map_zero

end Algebraic

section Normed

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem dense_complexify_domain_iff (A : X →ₗ.[ℝ] Y) :
    Dense (A.complexify.domain : Set (Complexification X)) ↔ Dense (A.domain : Set X) :=
  Submodule.dense_complexify_iff

/-- The domain of `(A_ℂ)†` is `D(A†)_ℂ`. -/
theorem mem_adjoint_domain_complexify_iff [CompleteSpace X] (A : X →ₗ.[ℝ] Y)
    (η : Complexification Y) :
    η ∈ A.complexify.adjoint.domain ↔ η.re ∈ A.adjoint.domain ∧ η.im ∈ A.adjoint.domain := by
  rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff, mem_adjoint_domain_iff]
  have hf : ⇑((innerₛₗ ℂ η).comp A.complexify.toFun) =
      fun ζ => ⟪η, A.complexify ζ⟫_ℂ :=
    rfl
  have hg : ∀ y : Y, ⇑((innerₛₗ ℝ y).comp A.toFun) = fun x => ⟪y, A x⟫_ℝ := by
    intro y
    ext x
    simp
  rw [hf, hg, hg]
  have hι : Continuous (fun x : A.domain => (⟨(x : Complexification X),
      Submodule.ofReal_mem_complexify.2 x.2⟩ : A.complexify.domain)) :=
    (Complexification.continuous_ofReal.comp continuous_subtype_val).subtype_mk _
  have hre : Continuous (fun ζ : A.complexify.domain => (⟨(ζ : Complexification X).re,
      (Submodule.mem_complexify.1 ζ.2).1⟩ : A.domain)) :=
    (Complexification.continuous_re.comp continuous_subtype_val).subtype_mk _
  have him : Continuous (fun ζ : A.complexify.domain => (⟨(ζ : Complexification X).im,
      (Submodule.mem_complexify.1 ζ.2).2⟩ : A.domain)) :=
    (Complexification.continuous_im.comp continuous_subtype_val).subtype_mk _
  constructor
  · intro h
    constructor
    · convert Complex.continuous_re.comp (h.comp hι) using 1
      ext x
      simp only [Function.comp_apply]
      rw [complexify_apply_ofReal, Complexification.inner_re]
      simp
    · convert (Complex.continuous_im.comp (h.comp hι)).neg using 1
      ext x
      simp only [Pi.neg_apply, Function.comp_apply]
      rw [complexify_apply_ofReal, Complexification.inner_im]
      simp
  · rintro ⟨h1, h2⟩
    have key : (fun ζ : A.complexify.domain => ⟪η, A.complexify ζ⟫_ℂ) = fun ζ =>
        (((⟪η.re, A ⟨_, (Submodule.mem_complexify.1 ζ.2).1⟩⟫_ℝ +
          ⟪η.im, A ⟨_, (Submodule.mem_complexify.1 ζ.2).2⟩⟫_ℝ : ℝ) : ℂ) +
        ((⟪η.re, A ⟨_, (Submodule.mem_complexify.1 ζ.2).2⟩⟫_ℝ -
          ⟪η.im, A ⟨_, (Submodule.mem_complexify.1 ζ.2).1⟩⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
      funext ζ
      apply Complex.ext
      · rw [Complexification.inner_re]
        simp
      · rw [Complexification.inner_im]
        simp
    rw [key]
    exact (Complex.continuous_ofReal.comp ((h1.comp hre).add (h2.comp him))).add
      ((Complex.continuous_ofReal.comp ((h1.comp him).sub (h2.comp hre))).mul continuous_const)

/-- The adjoint of the complexification of a real (unbounded) operator is the complexification
of its adjoint: `(A_ℂ)† = (A†)_ℂ`, domains included.  Thus the paper's `A^⋆` on `X_ℂ`
(`prop:fattorini-hautus`, `thm:data-fattorini-hautus`) is `A.adjoint.complexify`. -/
theorem adjoint_complexify [CompleteSpace X] (A : X →ₗ.[ℝ] Y) :
    A.complexify.adjoint = A.adjoint.complexify := by
  have hdom : A.complexify.adjoint.domain = A.adjoint.complexify.domain := by
    ext η
    exact mem_adjoint_domain_complexify_iff A η
  refine LinearPMap.ext hdom fun η hη hη' => ?_
  by_cases hA : Dense (A.domain : Set X)
  · have hAc : Dense (A.complexify.domain : Set (Complexification X)) :=
      (dense_complexify_domain_iff A).2 hA
    refine LinearPMap.adjoint_apply_eq hAc ⟨η, hη⟩ fun ζ => ?_
    have hf := LinearPMap.adjoint_isFormalAdjoint hA
    obtain ⟨hη1, hη2⟩ := Submodule.mem_complexify.1 hη'
    obtain ⟨hζ1, hζ2⟩ := Submodule.mem_complexify.1 ζ.2
    have e11 := hf ⟨η.re, hη1⟩ ⟨_, hζ1⟩
    have e12 := hf ⟨η.re, hη1⟩ ⟨_, hζ2⟩
    have e21 := hf ⟨η.im, hη2⟩ ⟨_, hζ1⟩
    have e22 := hf ⟨η.im, hη2⟩ ⟨_, hζ2⟩
    dsimp only at e11 e12 e21 e22
    apply Complex.ext
    · simp only [Complexification.inner_re, complexify_apply_re, complexify_apply_im]
      linarith
    · simp only [Complexification.inner_im, complexify_apply_re, complexify_apply_im]
      linarith
  · rw [LinearPMap.adjoint_apply_of_not_dense (mt (dense_complexify_domain_iff A).1 hA)]
    ext
    · exact (LinearPMap.adjoint_apply_of_not_dense hA _).symm
    · exact (LinearPMap.adjoint_apply_of_not_dense hA _).symm

end Normed

end LinearPMap

/-! ### Transfer of informativity -/

namespace DataDrivenControl.Complexification

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  {α : Type*} [MeasurableSpace α]

end DataDrivenControl.Complexification
