module

public import DataDrivenControl.Semigroup.Diagonal
public import DataDrivenControl.Semigroup.Resolvent
public import DataDrivenControl.Analysis.Complexification

/-!
# Modal models: diagonal maps, resolvents, approximate controllability with unbounded `B`

Extends `Semigroup/Diagonal`.

## Main declarations

* `Diagonal.diagMap e f d C hd : X →L[ℝ] Y` for Hilbert bases `e` of `X` and `f` of `Y`
  indexed by the same `ι` and a bounded multiplier `|dₙ| ≤ C`: the bounded map with
  `⟪fₙ, diagMap x⟫ = dₙ ⟪eₙ, x⟫` (`inner_diagMap`, `diagMap_apply_basis`, `norm_diagMap_le`); it
  is injective
  and has dense range when every `dₙ ≠ 0` (`injective_diagMap`, `denseRange_diagMap`), and it
  intertwines the diagonal semigroups with the same eigenvalues (`consistent_diagMap`).  All
  embeddings of the heat example are of this form.
* `Diagonal.separableSpace`: a space with a countable Hilbert basis is separable.
* `resolventSet_complexify_diag`, `mem_resolventSet_complexify_diag_of_notMem_closure`:
  `ρ(A_ℂ) ⊇ ℂ \ closure {λₙ}` for the real diagonal generator `A`.
* `System.approxControllable_of_modal`: approximate controllability from the modal coordinates
  `⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪βₙ, u r⟫ dr`, for distinct `λₙ` with
  `∑ₙ e^{λₙ s} < ∞` (`s > 0`) and a bounded family `βₙ ≠ 0` that need not be square summable
  (an unbounded `B`).  This extends `approxControllable_diag` to unbounded control operators;
  the heat example (`ex:boundary-heat-informative`) has `βₙ ∈ {-1, -√2}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace Diagonal

/-! ### Diagonal maps between spaces with Hilbert bases -/

section Map

variable {ι X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The vector of `Y` with coordinates `dₙ ⟪eₙ, x⟫` in the basis `f`. -/
def diagMapFun (e : HilbertBasis ι ℝ X) (f : HilbertBasis ι ℝ Y) (d : ι → ℝ) (C : ℝ)
    (hd : ∀ n, |d n| ≤ C) (x : X) : Y :=
  (exists_inner_eq f _ (summable_mul_inner_sq e hd x)).choose

theorem inner_diagMapFun (e : HilbertBasis ι ℝ X) (f : HilbertBasis ι ℝ Y) {d : ι → ℝ}
    {C : ℝ} (hd : ∀ n, |d n| ≤ C) (x : X) (n : ι) :
    ⟪f n, diagMapFun e f d C hd x⟫_ℝ = d n * ⟪e n, x⟫_ℝ :=
  (exists_inner_eq f _ (summable_mul_inner_sq e hd x)).choose_spec n

/-- A norm bound from coordinatewise bounds in two Hilbert bases with the same index set. -/
theorem norm_le_of_abs_inner_le₂ (e : HilbertBasis ι ℝ X) (f : HilbertBasis ι ℝ Y) {x : X}
    {y : Y} {K : ℝ} (hK : 0 ≤ K) (h : ∀ n, |⟪f n, y⟫_ℝ| ≤ K * |⟪e n, x⟫_ℝ|) :
    ‖y‖ ≤ K * ‖x‖ := by
  have h1 : ‖y‖ ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n => ?_) (hasSum_inner_sq f y) ((hasSum_inner_sq e x).mul_left (K ^ 2))
    rw [← sq_abs, ← sq_abs ⟪e n, x⟫_ℝ, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (h n) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- The **diagonal map** `x ↦ ∑ₙ dₙ ⟪eₙ, x⟫ fₙ` between spaces with Hilbert bases `e` and `f`
indexed by the same set, for a bounded multiplier `|dₙ| ≤ C`. -/
def diagMap (e : HilbertBasis ι ℝ X) (f : HilbertBasis ι ℝ Y) (d : ι → ℝ) (C : ℝ)
    (hd : ∀ n, |d n| ≤ C) : X →L[ℝ] Y :=
  LinearMap.mkContinuous
    { toFun := diagMapFun e f d C hd
      map_add' := fun x y => ext_inner f fun n => by
        simp only [inner_add_right, inner_diagMapFun]
        ring
      map_smul' := fun c x => ext_inner f fun n => by
        simp only [real_inner_smul_right, RingHom.id_apply, inner_diagMapFun]
        ring }
    |C| fun x => norm_le_of_abs_inner_le₂ e f (abs_nonneg C) fun n => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_diagMapFun, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hd n).trans (le_abs_self C)) (abs_nonneg _)

variable (e : HilbertBasis ι ℝ X) (f : HilbertBasis ι ℝ Y) {d : ι → ℝ} {C : ℝ}
  (hd : ∀ n, |d n| ≤ C)

/-- Coordinates of the diagonal map: `⟪fₙ, diagMap x⟫ = dₙ ⟪eₙ, x⟫`. -/
theorem inner_diagMap (x : X) (n : ι) : ⟪f n, diagMap e f d C hd x⟫_ℝ = d n * ⟪e n, x⟫_ℝ :=
  inner_diagMapFun e f hd x n

/-- `diagMap eₙ = dₙ fₙ`. -/
theorem diagMap_apply_basis (n : ι) : diagMap e f d C hd (e n) = d n • f n := by
  classical
  refine ext_inner f fun m => ?_
  rw [inner_diagMap, real_inner_smul_right, orthonormal_iff_ite.1 e.orthonormal,
    orthonormal_iff_ite.1 f.orthonormal]
  split_ifs with h
  · subst h; rfl
  · simp

/-- `‖diagMap‖ ≤ |C|`. -/
theorem norm_diagMap_le : ‖diagMap e f d C hd‖ ≤ |C| :=
  LinearMap.mkContinuous_norm_le _ (abs_nonneg C) _

/-- A diagonal map with nonzero multipliers is injective. -/
theorem injective_diagMap (h0 : ∀ n, d n ≠ 0) : Function.Injective (diagMap e f d C hd) := by
  intro x y hxy
  refine ext_inner e fun n => ?_
  have h1 := congrArg (fun z => ⟪f n, z⟫_ℝ) hxy
  simp only [inner_diagMap] at h1
  exact mul_left_cancel₀ (h0 n) h1

/-- A diagonal map with nonzero multipliers has dense range. -/
theorem denseRange_diagMap (h0 : ∀ n, d n ≠ 0) : DenseRange (diagMap e f d C hd) := by
  have hsub : Submodule.span ℝ (Set.range f) ≤
      LinearMap.range (diagMap e f d C hd : X →ₗ[ℝ] Y) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    refine ⟨(d n)⁻¹ • e n, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, diagMap_apply_basis, smul_smul,
      inv_mul_cancel₀ (h0 n), one_smul]
  have hdense : Dense (Submodule.span ℝ (Set.range f) : Set Y) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact f.dense_span
  refine hdense.mono fun y hy => ?_
  obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (hsub hy)
  exact ⟨x, hx⟩

/-- Diagonal maps intertwine the diagonal semigroups with the same eigenvalues:
`diagMap ∘ S_X t = S_Y t ∘ diagMap`. -/
theorem consistent_diagMap [CompleteSpace X] [CompleteSpace Y] (lam : ι → ℝ)
    (hlam : BddAbove (Set.range lam)) :
    C0Semigroup.Consistent (diagMap e f d C hd) (diagSemigroup e lam hlam)
      (diagSemigroup f lam hlam) := fun t x => ext_inner f fun n => by
  simp only [inner_diagMap, inner_diagSemigroup]
  ring

end Map

/-! ### Separability -/

/-- A real inner product space with a countable Hilbert basis is separable. -/
theorem separableSpace {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [Countable ι] (e : HilbertBasis ι ℝ X) : TopologicalSpace.SeparableSpace X := by
  have h1 : TopologicalSpace.IsSeparable (Submodule.span ℝ (Set.range e) : Set X) :=
    (Set.countable_range e).isSeparable.span
  have h2 : closure (Submodule.span ℝ (Set.range e) : Set X) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe]
  rw [← TopologicalSpace.isSeparable_univ_iff, ← h2]
  exact h1.closure

end Diagonal

open Diagonal

/-! ### The resolvent of a real diagonal generator -/

section Resolvent

variable {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The real part of the coordinate `⟪eₙ, z⟫_bil` is `⟪eₙ, z.re⟫`. -/
theorem Diagonal.pairing_ofReal_re (x : X) (z : Complexification X) :
    (⟪(x : Complexification X), z⟫_bil).re = ⟪x, z.re⟫_ℝ := by
  simp [Complexification.pairing_re]

/-- The imaginary part of the coordinate `⟪eₙ, z⟫_bil` is `⟪eₙ, z.im⟫`. -/
theorem Diagonal.pairing_ofReal_im (x : X) (z : Complexification X) :
    (⟪(x : Complexification X), z⟫_bil).im = ⟪x, z.im⟫_ℝ := by
  simp [Complexification.pairing_im]

/-- A vector of `X_ℂ` is determined by its (complex) coordinates `⟪eₙ, z⟫_bil`. -/
theorem Diagonal.ext_pairing (e : HilbertBasis ι ℝ X) {z z' : Complexification X}
    (h : ∀ n, ⟪(e n : Complexification X), z⟫_bil = ⟪(e n : Complexification X), z'⟫_bil) :
    z = z' := by
  ext
  · exact ext_inner e fun n => by
      rw [← Diagonal.pairing_ofReal_re, h, Diagonal.pairing_ofReal_re]
  · exact ext_inner e fun n => by
      rw [← Diagonal.pairing_ofReal_im, h, Diagonal.pairing_ofReal_im]

/-- The complex diagonal operator `z ↦ ∑ₙ mₙ ⟪eₙ, z⟫ eₙ` on `X_ℂ`, for a bounded complex
multiplier `‖mₙ‖ ≤ K`: `(diagOp Re m)_ℂ + i (diagOp Im m)_ℂ`. -/
def Diagonal.cdiagOp (e : HilbertBasis ι ℝ X) (m : ι → ℂ) (K : ℝ) (hm : ∀ n, ‖m n‖ ≤ K) :
    Complexification X →L[ℂ] Complexification X :=
  (diagOp e (fun n => (m n).re) K fun n => (Complex.abs_re_le_norm _).trans (hm n)).complexify +
    Complex.I •
      (diagOp e (fun n => (m n).im) K fun n => (Complex.abs_im_le_norm _).trans (hm n)).complexify

/-- Coordinates of the complex diagonal operator: `⟪eₙ, cdiagOp z⟫ = mₙ ⟪eₙ, z⟫`. -/
theorem Diagonal.pairing_cdiagOp (e : HilbertBasis ι ℝ X) {m : ι → ℂ} {K : ℝ}
    (hm : ∀ n, ‖m n‖ ≤ K) (z : Complexification X) (n : ι) :
    ⟪(e n : Complexification X), Diagonal.cdiagOp e m K hm z⟫_bil =
      m n * ⟪(e n : Complexification X), z⟫_bil := by
  apply Complex.ext
  · rw [Diagonal.pairing_ofReal_re, Complex.mul_re, Diagonal.pairing_ofReal_re,
      Diagonal.pairing_ofReal_im]
    simp only [Diagonal.cdiagOp, add_apply, smul_apply,
      Complexification.add_re, Complexification.I_smul_re,
      ContinuousLinearMap.complexify_apply_re, ContinuousLinearMap.complexify_apply_im,
      inner_add_right, inner_neg_right, inner_diagOp]
    ring
  · rw [Diagonal.pairing_ofReal_im, Complex.mul_im, Diagonal.pairing_ofReal_re,
      Diagonal.pairing_ofReal_im]
    simp only [Diagonal.cdiagOp, add_apply, smul_apply,
      Complexification.add_im, Complexification.I_smul_im,
      ContinuousLinearMap.complexify_apply_re, ContinuousLinearMap.complexify_apply_im,
      inner_add_right, inner_diagOp]

variable [CompleteSpace X] (e : HilbertBasis ι ℝ X) (lam : ι → ℝ)
  (hlam : BddAbove (Set.range lam))

/-- A vector `y` with `⟪eₙ, v⟫ = λₙ ⟪eₙ, y⟫` for some `v` lies in `D(A)`, and `A y = v`. -/
theorem Diagonal.exists_generator_diag {y v : X}
    (h : ∀ n, ⟪e n, v⟫_ℝ = lam n * ⟪e n, y⟫_ℝ) :
    ∃ hy : y ∈ (diagSemigroup e lam hlam).generator.domain,
      (diagSemigroup e lam hlam).generator ⟨y, hy⟩ = v := by
  have hs : Summable fun n => (lam n * ⟪e n, y⟫_ℝ) ^ 2 := by
    simpa only [h] using summable_inner_sq e v
  have hy := (mem_generator_domain_diag_iff e lam hlam y).2 hs
  exact ⟨hy, ext_inner e fun n => by rw [inner_generator_diag, h]⟩

/-- The complexified diagonal generator acts on coordinates: `⟪eₙ, A_ℂ w⟫ = λₙ ⟪eₙ, w⟫`. -/
theorem Diagonal.pairing_generator_complexify_diag
    (w : (diagSemigroup e lam hlam).generator.complexify.domain) (n : ι) :
    ⟪(e n : Complexification X), (diagSemigroup e lam hlam).generator.complexify w⟫_bil =
      lam n * ⟪(e n : Complexification X), (w : Complexification X)⟫_bil := by
  apply Complex.ext
  · rw [Diagonal.pairing_ofReal_re, LinearPMap.complexify_apply_re, inner_generator_diag,
      Complex.mul_re, Diagonal.pairing_ofReal_re]
    simp
  · rw [Diagonal.pairing_ofReal_im, LinearPMap.complexify_apply_im, inner_generator_diag,
      Complex.mul_im, Diagonal.pairing_ofReal_im]
    simp

/-- A vector `w ∈ X_ℂ` with `⟪eₙ, v⟫ = λₙ ⟪eₙ, w⟫` for some `v` lies in `D(A_ℂ)`, and
`A_ℂ w = v`. -/
theorem Diagonal.exists_generator_complexify_diag {w v : Complexification X}
    (h : ∀ n, ⟪(e n : Complexification X), v⟫_bil = lam n * ⟪(e n : Complexification X), w⟫_bil) :
    ∃ hw : w ∈ (diagSemigroup e lam hlam).generator.complexify.domain,
      (diagSemigroup e lam hlam).generator.complexify ⟨w, hw⟩ = v := by
  obtain ⟨hre, hAre⟩ := Diagonal.exists_generator_diag e lam hlam (y := w.re) (v := v.re)
    fun n => by
      have := congrArg Complex.re (h n)
      rwa [Diagonal.pairing_ofReal_re, Complex.mul_re, Diagonal.pairing_ofReal_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at this
  obtain ⟨him, hAim⟩ := Diagonal.exists_generator_diag e lam hlam (y := w.im) (v := v.im)
    fun n => by
      have := congrArg Complex.im (h n)
      rwa [Diagonal.pairing_ofReal_im, Complex.mul_im, Diagonal.pairing_ofReal_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at this
  refine ⟨Submodule.mem_complexify.2 ⟨hre, him⟩, ?_⟩
  ext
  · rw [LinearPMap.complexify_apply_re]; exact hAre
  · rw [LinearPMap.complexify_apply_im]; exact hAim

variable {lam}

private theorem norm_inv_sub_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : ∀ n, δ ≤ ‖s - (lam n : ℂ)‖)
    (n : ι) : ‖(s - (lam n : ℂ))⁻¹‖ ≤ δ⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hδ (hs n)

private theorem sub_ne_zero_of_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ n, δ ≤ ‖s - (lam n : ℂ)‖) (n : ι) : s - (lam n : ℂ) ≠ 0 := fun h0 => by
  have := hs n
  rw [h0, norm_zero] at this
  linarith

private theorem norm_mul_inv_sub_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ n, δ ≤ ‖s - (lam n : ℂ)‖) (n : ι) :
    ‖(lam n : ℂ) * (s - (lam n : ℂ))⁻¹‖ ≤ ‖s‖ * δ⁻¹ + 1 := by
  have e1 : (lam n : ℂ) * (s - (lam n : ℂ))⁻¹ = s * (s - (lam n : ℂ))⁻¹ - 1 := by
    field_simp [sub_ne_zero_of_le hδ hs n]
    ring
  rw [e1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_one]
  gcongr
  exact norm_inv_sub_le hδ hs n

/-- The explicit resolvent of the complexified diagonal generator. -/
private theorem isResolvent_complexify_diag {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ n, δ ≤ ‖s - (lam n : ℂ)‖) :
    IsResolvent (diagSemigroup e lam hlam).generator.complexify s
      (Diagonal.cdiagOp e (fun n => (s - (lam n : ℂ))⁻¹) δ⁻¹ (norm_inv_sub_le hδ hs)) := by
  have hne := sub_ne_zero_of_le hδ hs
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨hw, hA⟩ := Diagonal.exists_generator_complexify_diag e lam hlam
      (w := Diagonal.cdiagOp e (fun n => (s - (lam n : ℂ))⁻¹) δ⁻¹ (norm_inv_sub_le hδ hs) y)
      (v := Diagonal.cdiagOp e (fun n => (lam n : ℂ) * (s - (lam n : ℂ))⁻¹) (‖s‖ * δ⁻¹ + 1)
        (norm_mul_inv_sub_le hδ hs) y)
      fun n => by rw [Diagonal.pairing_cdiagOp, Diagonal.pairing_cdiagOp, mul_assoc]
    refine ⟨hw, ?_⟩
    rw [hA]
    refine Diagonal.ext_pairing e fun n => ?_
    rw [Complexification.pairing_sub_right, Complexification.pairing_smul_right,
      Diagonal.pairing_cdiagOp, Diagonal.pairing_cdiagOp]
    field_simp [hne n]
  · refine Diagonal.ext_pairing e fun n => ?_
    rw [Diagonal.pairing_cdiagOp, Complexification.pairing_sub_right,
      Complexification.pairing_smul_right, Diagonal.pairing_generator_complexify_diag]
    field_simp [hne n]

variable (lam)

/-- **`ρ(A_ℂ) ⊇ ℂ \ closure {λₙ}`** for a real diagonal generator: if `s` stays at distance at
least `δ > 0` from every eigenvalue `λₙ`, then `s` is in the resolvent set of the
complexified generator. -/
theorem resolventSet_complexify_diag {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ n, δ ≤ ‖s - (lam n : ℂ)‖) :
    s ∈ resolventSet (diagSemigroup e lam hlam).generator.complexify :=
  ⟨_, isResolvent_complexify_diag e hlam hδ hs⟩

/-- `ρ(A_ℂ) ⊇ ℂ \ closure {λₙ}` for a real diagonal generator. -/
theorem mem_resolventSet_complexify_diag_of_notMem_closure {s : ℂ}
    (hs : s ∉ closure (Set.range fun n => (lam n : ℂ))) :
    s ∈ resolventSet (diagSemigroup e lam hlam).generator.complexify := by
  rw [Metric.mem_closure_iff] at hs
  push Not at hs
  obtain ⟨ε, hε, h⟩ := hs
  refine resolventSet_complexify_diag e lam hlam hε fun n => ?_
  have := h _ ⟨n, rfl⟩
  rwa [dist_eq_norm] at this

end Resolvent

/-! ### Approximate controllability from modal coordinates -/

namespace System

variable {ι U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Approximate controllability from modal coordinates** (extends `approxControllable_diag`
to unbounded `B`).  Let `e` be a Hilbert basis of `X`, `λₙ` distinct reals with
`∑ₙ e^{λₙ s} < ∞` for every `s > 0`, and `βₙ ∈ U` a bounded family of nonzero vectors (not
necessarily square summable).  If `hyp:H1` holds at `T > 0` and the modal coordinates of the
input-to-state map are `⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪βₙ, u r⟫ dr`, then `(A, B)` is
approximately controllable in time `T`.  (In applications `sys.SX = diagSemigroup e lam _`
and `βₙ = B† eₙ`; neither is needed here.)

Proof: for `η ⊥ im L_T`, `g(s) = ∑ₙ ⟪eₙ, η⟫ ⟪βₙ, βₘ⟫ e^{λₙ s}` is continuous on `(0, ∞)` and
its integrals over subintervals of `(0, T)` vanish (inputs `1_{[a, b]} βₘ`), so `g = 0` on
`(0, T)`; after the shift `s ↦ s + T/2` the coefficients are absolutely summable and
`Diagonal.coeff_eq_zero_of_tsum_eq_zero` gives `⟪eₘ, η⟫ ‖βₘ‖² = 0`. -/
theorem approxControllable_of_modal (sys : System U W X V Y) (e : HilbertBasis ι ℝ X)
    {lam : ι → ℝ} (hinj : Function.Injective lam)
    (hsum : ∀ s : ℝ, 0 < s → Summable fun n => Real.exp (lam n * s))
    {β : ι → U} {Cβ : ℝ} (hβb : ∀ n, ‖β n‖ ≤ Cβ) (hβ : ∀ n, β n ≠ 0)
    {T : ℝ} (hT : 0 < T) (hH1 : sys.H1 T)
    (hmodal : ∀ (u : L2 U T) (n : ι), ⟪e n, sys.ιW (sys.Lop T u)⟫_ℝ =
      ∫ r in Ioc 0 T, Real.exp (lam n * (T - r)) * ⟪β n, u r⟫_ℝ) :
    sys.ApproxControllable T := by
  -- The exponents are bounded above and the index set is countable.
  set ω := ∑' k, Real.exp (lam k * 1) with hωdef
  have hω : ∀ n, lam n ≤ ω := fun n => by
    have h1 := le_hasSum (hsum 1 one_pos).hasSum n (fun j _ => (Real.exp_pos _).le)
    have h2 := Real.add_one_le_exp (lam n * 1)
    rw [mul_one] at h1 h2
    linarith
  have : Countable ι := by
    have hc := (hsum 1 one_pos).countable_support
    have hsupp : Function.support (fun n => Real.exp (lam n * 1)) = Set.univ :=
      Set.eq_univ_of_forall fun n => (Real.exp_pos _).ne'
    rw [hsupp] at hc
    exact Set.countable_univ_iff.1 hc
  rw [System.approxControllable_iff hH1 hT]
  intro η hη
  set x : ι → ℝ := fun n => ⟪η, e n⟫_ℝ with hx
  have hx2 : Summable fun n => x n ^ 2 :=
    (summable_inner_sq e η).congr fun n => by rw [real_inner_comm]
  have hxe : ∀ ε : ℝ, 0 < ε → Summable fun n => |x n| * Real.exp (lam n * ε) := by
    intro ε hε
    refine (hx2.add (hsum (2 * ε) (by positivity))).of_nonneg_of_le (fun n => by positivity)
      fun n => ?_
    have h1 : Real.exp (lam n * (2 * ε)) = Real.exp (lam n * ε) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [h1]
    nlinarith [two_mul_le_add_sq |x n| (Real.exp (lam n * ε)), sq_abs (x n),
      mul_nonneg (abs_nonneg (x n)) (Real.exp_pos (lam n * ε)).le]
  suffices h : ∀ m, x m = 0 from
    ext_inner e fun m => by rw [inner_zero_right, real_inner_comm]; exact h m
  intro m
  set p : ι → ℝ := fun n => ⟪β n, β m⟫_ℝ with hp
  have hpb : ∀ n, |p n| ≤ Cβ * ‖β m‖ := fun n =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hβb n) (norm_nonneg _))
  set F : ι → ℝ → ℝ := fun n r => x n * (Real.exp (lam n * (T - r)) * p n) with hF
  set K : ℝ := Real.exp (max ω 0 * T) * (Cβ * ‖β m‖) with hK
  -- (1) Testing `η ⊥ im L_T` with `u = 1_{(0, b]} βₘ`.
  have h1 : ∀ b ∈ Ioo 0 T,
      ∑' n, x n * ∫ r in Ioc 0 b, Real.exp (lam n * (T - r)) * p n = 0 := by
    intro b hb
    set u : L2 U T :=
      indicatorConstLp 2 (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) b))
        (measure_ne_top (μI T) _) (β m) with hu
    have hae : ⇑u =ᵐ[μI T] (Ioc 0 b).indicator fun _ => β m := indicatorConstLp_coeFn
    have h0 := hη u
    rw [← (e.hasSum_inner_mul_inner η (sys.ιW (sys.Lop T u))).tsum_eq] at h0
    refine (tsum_congr fun n => ?_).trans h0
    rw [hmodal u n]
    congr 1
    calc ∫ r in Ioc 0 b, Real.exp (lam n * (T - r)) * p n
        = ∫ r in Ioc 0 T ∩ Ioc 0 b, Real.exp (lam n * (T - r)) * p n := by
          rw [inter_eq_right.2 (Ioc_subset_Ioc_right hb.2.le)]
      _ = ∫ r in Ioc 0 T, (Ioc 0 b).indicator (fun r => Real.exp (lam n * (T - r)) * p n) r :=
          (setIntegral_indicator measurableSet_Ioc).symm
      _ = ∫ r in Ioc 0 T, Real.exp (lam n * (T - r)) * ⟪β n, u r⟫_ℝ := by
          refine integral_congr_ae (hae.mono fun r hr => ?_)
          dsimp only
          rw [hr]
          by_cases h : r ∈ Ioc 0 b <;> simp [h, hp]
  -- (2) Uniform bounds on `[0, b]`, `b < T`.
  have hexp : ∀ b ∈ Ioo 0 T, ∀ r ∈ Icc 0 b, ∀ n,
      Real.exp (lam n * (T - r)) ≤ Real.exp (lam n * (T - b)) * Real.exp (max ω 0 * T) := by
    intro b hb r hr n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e2 : lam n * (b - r) ≤ max ω 0 * (b - r) :=
      mul_le_mul_of_nonneg_right ((hω n).trans (le_max_left _ _)) (by linarith [hr.2])
    have e3 : max ω 0 * (b - r) ≤ max ω 0 * T :=
      mul_le_mul_of_nonneg_left (by linarith [hr.1, hb.2]) (le_max_right _ _)
    nlinarith
  have hFb : ∀ b ∈ Ioo 0 T, ∀ r ∈ Icc 0 b, ∀ n,
      ‖F n r‖ ≤ |x n| * Real.exp (lam n * (T - b)) * K := by
    intro b hb r hr n
    simp only [hF, hK, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |x n| * (Real.exp (lam n * (T - r)) * |p n|)
        ≤ |x n| * ((Real.exp (lam n * (T - b)) * Real.exp (max ω 0 * T)) * (Cβ * ‖β m‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hexp b hb r hr n) (hpb n) (abs_nonneg _)
            (by positivity)) (abs_nonneg _)
      _ = _ := by ring
  have hsumb : ∀ b ∈ Ioo 0 T, Summable fun n => |x n| * Real.exp (lam n * (T - b)) * K :=
    fun b hb => (hxe (T - b) (by linarith [hb.2])).mul_right K
  have hFc : ∀ n, Continuous (F n) := fun n => by
    simp only [hF]
    fun_prop
  -- (3) `f = ∑ₙ Fₙ` is continuous on `[0, b]`.
  have hcont : ∀ b ∈ Ioo 0 T, ContinuousOn (fun r => ∑' n, F n r) (Icc 0 b) := fun b hb =>
    continuousOn_tsum (fun n => (hFc n).continuousOn) (hsumb b hb)
      (fun n r hr => hFb b hb r hr n)
  -- (4) Its integrals over `(0, b]` vanish.
  have h2 : ∀ b ∈ Ioo 0 T, ∫ r in Ioc 0 b, ∑' n, F n r = 0 := by
    intro b hb
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc 0 b)) := fun n =>
      ((hFc n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hnorm : Summable fun n => ∫ r in Ioc 0 b, ‖F n r‖ := by
      refine ((hsumb b hb).mul_right ((volume.restrict (Ioc 0 b)).real Set.univ)).of_nonneg_of_le
        (fun n => integral_nonneg fun r => norm_nonneg _) fun n => ?_
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le_const ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      rw [norm_norm]
      exact hFb b hb r (Ioc_subset_Icc_self hr) n
    rw [← integral_tsum_of_summable_integral_norm hint hnorm]
    refine (tsum_congr fun n => ?_).trans (h1 b hb)
    exact integral_const_mul (x n) _
  -- (5) Hence `f = 0` on `(0, T)` (fundamental theorem of calculus).
  have h3 : ∀ r₀ ∈ Ioo 0 T, ∑' n, F n r₀ = 0 := by
    intro r₀ hr₀
    have hb' : (r₀ + T) / 2 ∈ Ioo 0 T := ⟨by linarith [hr₀.1, hr₀.2], by linarith [hr₀.2]⟩
    have hr₀b : r₀ < (r₀ + T) / 2 := by linarith [hr₀.2]
    have hc := hcont _ hb'
    have hcat : ContinuousAt (fun r => ∑' n, F n r) r₀ :=
      hc.continuousAt (Icc_mem_nhds hr₀.1 hr₀b)
    have hd1 : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, ∑' n, F n r) (∑' n, F n r₀) r₀ :=
      intervalIntegral.integral_hasDerivAt_right
        ((hc.mono (Icc_subset_Icc_right hr₀b.le)).intervalIntegrable_of_Icc hr₀.1.le)
        ((hc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r₀
          ⟨hr₀.1, hr₀b⟩)
        hcat
    have hd2 : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, ∑' n, F n r) 0 r₀ := by
      refine (hasDerivAt_const r₀ (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hr₀.1 hr₀.2] with u hu
      rw [intervalIntegral.integral_of_le hu.1.le]
      exact h2 u hu
    exact hd1.unique hd2
  -- (6) Shift by `T / 2` and use uniqueness of Dirichlet series.
  set a : ι → ℝ := fun n => x n * p n * Real.exp (lam n * (T / 2)) with ha
  have has : Summable fun n => |a n| := by
    refine ((hxe (T / 2) (half_pos hT)).mul_right (Cβ * ‖β m‖)).of_nonneg_of_le
      (fun n => abs_nonneg _) fun n => ?_
    simp only [ha, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [show |x n| * |p n| * Real.exp (lam n * (T / 2)) =
      |x n| * Real.exp (lam n * (T / 2)) * |p n| by ring]
    exact mul_le_mul_of_nonneg_left (hpb n) (by positivity)
  have hzero : ∀ t ∈ Ioo 0 (T / 2), ∑' n, a n * Real.exp (lam n * t) = 0 := by
    intro t ht
    have h4 := h3 (T / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine (tsum_congr fun n => ?_).trans h4
    simp only [ha, hF]
    rw [show T - (T / 2 - t) = T / 2 + t by ring, mul_add, Real.exp_add]
    ring
  have hcoef := Diagonal.coeff_eq_zero_of_tsum_eq_zero hinj hω has (half_pos hT) hzero m
  simp only [ha, hp, real_inner_self_eq_norm_sq] at hcoef
  rcases mul_eq_zero.1 hcoef with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact h'
    · exact absurd h' (pow_ne_zero 2 (norm_ne_zero_iff.2 (hβ m)))
  · exact absurd h (Real.exp_pos _).ne'

end System

end DataDrivenControl
