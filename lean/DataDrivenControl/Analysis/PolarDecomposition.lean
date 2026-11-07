module

public import Mathlib
public import DataDrivenControl.Analysis.Complexification

/-!
# The absolute value `|T|` and the polar decomposition

Paper: `eq:hilbert-gramian` calls the Gramian trace class; the textbook definition of the trace
class is `tr |T| < ∞` with `|T| = (T† T)^{1/2}`.  Mathlib v4.35 has `CFC.abs` on complex
C⋆-algebras, in particular on `E →L[ℂ] E` for a complex Hilbert space `E`, but neither a polar
decomposition nor an absolute value on **real** Hilbert spaces, which are the paper's setting.
This file supplies both; `Analysis/TraceClassAbs` uses them to show that the nuclear definition
`TraceClass.IsTraceClass` is the textbook one.

## Main definitions (namespace `DataDrivenControl.TraceClass`)

* `initialSpace P = closure (range P)` and `toInitialSpace P : E →ₗ[𝕜] initialSpace P`;
* `polarPart T P`, over any `RCLike 𝕜`: if `‖T x‖ = ‖P x‖` for all `x`, the partial isometry `U`
  with `U (P x) = T x` on `range P`, extended by continuity to `closure (range P)`
  (`LinearMap.extendOfIsometry`) and by `0` on `(range P)ᗮ`; `0` if the hypothesis fails.  For
  `P = |T|` it is the polar part of `T`;
* `sqrtOp A = CFC.sqrt A` on a complex Hilbert space, as a function of the Hilbert-space
  structure only (see *Deviations*);
* `realSqrt A`: the positive square root of a positive operator `A` on a **real** Hilbert space,
  `realSqrt A x = re ((A_ℂ)^{1/2} x)`, the restriction of `sqrtOp A_ℂ` to `X ⊆ X_ℂ`;
* `realAbs T = realSqrt (T† T)`: the absolute value on a real Hilbert space.

## Main results

* Polar decomposition relative to `P` (`polarPart_comp`, `adjoint_polarPart_comp`,
  `adjoint_polarPart_comp_polarPart`, `norm_polarPart_le`, `norm_polarPart_apply`,
  `polarPart_apply_of_mem_orthogonal`): if `‖T x‖ = ‖P x‖` for all `x`, then `U = polarPart T P`
  satisfies `T = U P`, `U† T = P`, `U† U = proj_{closure (range P)}`, `‖U‖ ≤ 1`; `U` is isometric
  on `closure (range P)` and zero on `(range P)ᗮ`.  `norm_apply_eq_of_comp_self`: the hypothesis
  holds for every self-adjoint `P` with `P P = T† T`.
* Complex Hilbert spaces, `|T| = CFC.abs T`: `cfcAbs_eq_sqrtOp` (`|T| = (T† T)^{1/2}`),
  `isPositive_cfcAbs`, `cfcAbs_comp_cfcAbs` (`|T|² = T† T`), `norm_cfcAbs_apply`
  (`‖|T| x‖ = ‖T x‖`), `cfcAbs_unique` (the unique positive square root of `T† T`),
  `cfcAbs_of_isPositive`, and the **polar decomposition** `polar_decomposition_cfcAbs`.
  `sqrtOp_apply_conj`: `A^{1/2}` commutes with every antiunitary involution commuting with `A`
  (by uniqueness of the positive square root).
* Real Hilbert spaces: `sqrtOp_complexify_star` (`(A_ℂ)^{1/2}` commutes with the conjugation),
  `complexify_realSqrt` (`(realSqrt A)_ℂ = (A_ℂ)^{1/2}`), `isPositive_realSqrt`,
  `realSqrt_comp_realSqrt`, `realSqrt_unique` (the unique positive square root);
  `complexify_realAbs` (`(realAbs T)_ℂ = (T_ℂ† T_ℂ)^{1/2} = |T_ℂ|`), `isPositive_realAbs`,
  `realAbs_comp_realAbs`, `norm_realAbs_apply`, `realAbs_unique` (the unique positive square
  root of `T† T`), `realAbs_of_isPositive`, and the **polar decomposition**
  `polar_decomposition_realAbs`.
* Complexification: `inner_star_star` (the conjugation is antiunitary), `complexify_injective`,
  `isPositive_complexify_iff`.

## Deviations

* The polar part is built for any `P` with `‖T x‖ = ‖P x‖`, so the complex case
  (`P = CFC.abs T`) and the real case (`P = realAbs T`) share one construction.  Its uniqueness
  is not stated.
* `CFC.sqrt` and `CFC.abs` need the C⋆-algebra and order instances of `E →L[ℂ] E`; Lean does
  not synthesise them for `E = Complexification X` (it fails on
  `IsScalarTower ℝ (X_ℂ →L[ℂ] X_ℂ) (X_ℂ →L[ℂ] X_ℂ)`).  The real case therefore goes through
  `sqrtOp`, which takes only `[InnerProductSpace ℂ E] [CompleteSpace E]` and is `CFC.sqrt` by
  definition (`sqrtOp_eq_cfcSqrt`); `|T_ℂ|` is written `sqrtOp (T_ℂ† T_ℂ)`, which is
  `CFC.abs T_ℂ` by `cfcAbs_eq_sqrtOp`.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace DataDrivenControl

namespace TraceClass

open ContinuousLinearMap

/-! ### The polar part of `T` relative to `P` -/

section Polar

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The initial space `closure (range P)` of the polar part `polarPart T P`. -/
abbrev initialSpace (P : E →L[𝕜] E) : Submodule 𝕜 E :=
  P.range.topologicalClosure

theorem apply_mem_initialSpace (P : E →L[𝕜] E) (x : E) : P x ∈ initialSpace P :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self (P : E →ₗ[𝕜] E) x)

/-- `P` as a linear map into its initial space `closure (range P)`. -/
def toInitialSpace (P : E →L[𝕜] E) : E →ₗ[𝕜] initialSpace P :=
  (P : E →ₗ[𝕜] E).codRestrict _ (apply_mem_initialSpace P)

@[simp] theorem coe_toInitialSpace (P : E →L[𝕜] E) (x : E) :
    (toInitialSpace P x : E) = P x := rfl

/-- `range P` is dense in `closure (range P)`. -/
theorem denseRange_toInitialSpace (P : E →L[𝕜] E) : DenseRange (toInitialSpace P) := by
  refine (IsInducing.subtypeVal.dense_iff).2 fun ⟨y, hy⟩ => ?_
  have hk : y ∈ closure (Set.range P) := by
    have h1 : y ∈ ((P.range.topologicalClosure : Submodule 𝕜 E) : Set E) := hy
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range, ContinuousLinearMap.coe_coe] at h1
  refine closure_mono ?_ hk
  rintro _ ⟨x, rfl⟩
  exact ⟨toInitialSpace P x, ⟨x, rfl⟩, rfl⟩

variable [CompleteSpace E]

/-- `closure (range P)` is closed, hence complete, so it has an orthogonal projection. -/
instance (P : E →L[𝕜] E) : (initialSpace P).HasOrthogonalProjection :=
  have : CompleteSpace (initialSpace P) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  inferInstance

/-- The isometry `closure (range P) → E` extending `P x ↦ T x`, when `‖T x‖ = ‖P x‖`. -/
def polarIsometry (T P : E →L[𝕜] E) (h : ∀ x, ‖T x‖ = ‖P x‖) : initialSpace P →ₗᵢ[𝕜] E :=
  (T : E →ₗ[𝕜] E).extendOfIsometry (denseRange_toInitialSpace P) fun x => by
    simpa using h x

theorem polarIsometry_toInitialSpace {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) (x : E) :
    polarIsometry T P h (toInitialSpace P x) = T x :=
  LinearMap.extendOfIsometry_eq _ _ _ x

/-- The **polar part** of `T` relative to `P`: if `‖T x‖ = ‖P x‖` for all `x`, the partial
isometry `U` with `U (P x) = T x`, isometric on `closure (range P)` and zero on `(range P)ᗮ`;
otherwise `0`.  For `P = |T|` it is the partial isometry of the polar decomposition
`T = U |T|`. -/
def polarPart (T P : E →L[𝕜] E) : E →L[𝕜] E :=
  open scoped Classical in
  if h : ∀ x, ‖T x‖ = ‖P x‖ then
    (polarIsometry T P h).toContinuousLinearMap ∘L (initialSpace P).orthogonalProjectionOnto
  else 0

theorem polarPart_apply {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) (x : E) :
    polarPart T P x = polarIsometry T P h ((initialSpace P).orthogonalProjectionOnto x) := by
  simp [polarPart, h]

/-- `U (P x) = T x`. -/
theorem polarPart_apply_apply {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) (x : E) :
    polarPart T P (P x) = T x := by
  rw [polarPart_apply h]
  have hx : (initialSpace P).orthogonalProjectionOnto (P x) = toInitialSpace P x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (toInitialSpace P x)
  rw [hx, polarIsometry_toInitialSpace]

/-- `T = U P`. -/
theorem polarPart_comp {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) :
    polarPart T P ∘L P = T :=
  ext fun x => polarPart_apply_apply h x

/-- `‖U‖ ≤ 1`. -/
theorem norm_polarPart_le (T P : E →L[𝕜] E) : ‖polarPart T P‖ ≤ 1 := by
  unfold polarPart
  split_ifs with h
  · refine opNorm_le_bound _ zero_le_one fun x => ?_
    rw [comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x
  · simp

/-- `U` is isometric on `closure (range P)`. -/
theorem norm_polarPart_apply {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) {x : E}
    (hx : x ∈ initialSpace P) : ‖polarPart T P x‖ = ‖x‖ := by
  rw [polarPart_apply h, LinearIsometry.norm_map,
    Submodule.norm_orthogonalProjectionOnto_apply _ hx]

/-- `U` vanishes on `(range P)ᗮ`. -/
theorem polarPart_apply_of_mem_orthogonal {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) {x : E}
    (hx : x ∈ P.rangeᗮ) : polarPart T P x = 0 := by
  rw [polarPart_apply h, (Submodule.orthogonalProjectionOnto_eq_zero_iff).2
    (by rwa [Submodule.orthogonal_closure]), map_zero]

/-- `⟪U x, U y⟫ = ⟪proj x, y⟫`, the projection onto `closure (range P)`. -/
theorem inner_polarPart_polarPart {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) (x y : E) :
    ⟪polarPart T P x, polarPart T P y⟫_𝕜 = ⟪(initialSpace P).starProjection x, y⟫_𝕜 := by
  rw [polarPart_apply h, polarPart_apply h, LinearIsometry.inner_map_map,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.starProjection_apply]

/-- `U` is a partial isometry with initial space `closure (range P)`:
`U† U = proj_{closure (range P)}`. -/
theorem adjoint_polarPart_comp_polarPart {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) :
    adjoint (polarPart T P) ∘L polarPart T P = (initialSpace P).starProjection := by
  ext x
  refine ext_inner_right 𝕜 fun y => ?_
  rw [comp_apply, adjoint_inner_left, inner_polarPart_polarPart h]

/-- `U† T = P`. -/
theorem adjoint_polarPart_comp {T P : E →L[𝕜] E} (h : ∀ x, ‖T x‖ = ‖P x‖) :
    adjoint (polarPart T P) ∘L T = P := by
  ext x
  rw [comp_apply, ← polarPart_apply_apply h x, ← comp_apply (adjoint _),
    adjoint_polarPart_comp_polarPart h]
  exact Submodule.starProjection_eq_self_iff.2 (apply_mem_initialSpace P x)

/-- A self-adjoint square root `P` of `T† T` satisfies `‖P x‖ = ‖T x‖`. -/
theorem norm_apply_eq_of_comp_self {T P : E →L[𝕜] E} (hP : IsSelfAdjoint P)
    (h : P ∘L P = adjoint T ∘L T) (x : E) : ‖P x‖ = ‖T x‖ := by
  have h1 : ⟪P x, P x⟫_𝕜 = ⟪T x, T x⟫_𝕜 := by
    rw [← adjoint_inner_right, hP.adjoint_eq, ← comp_apply, h, comp_apply, adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖P x‖ ^ 2 = ‖T x‖ ^ 2 := by exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

end Polar


/-! ### Complex Hilbert spaces: `|T| = CFC.abs T` -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The positive square root `A^{1/2} = CFC.sqrt A` of an operator on a complex Hilbert space,
as a function of the Hilbert-space structure of `E` alone.  `CFC.sqrt` needs the C⋆-algebra
instances of `E →L[ℂ] E`, which Lean does not synthesise for `E = Complexification X`; there
the real case uses `sqrtOp`. -/
def sqrtOp (A : E →L[ℂ] E) : E →L[ℂ] E :=
  CFC.sqrt A

theorem sqrtOp_eq_cfcSqrt (A : E →L[ℂ] E) : sqrtOp A = CFC.sqrt A := rfl

/-- `A^{1/2} ≥ 0`. -/
theorem isPositive_sqrtOp (A : E →L[ℂ] E) : (sqrtOp A).IsPositive :=
  nonneg_iff_isPositive.1 (CFC.sqrt_nonneg A)

/-- `(A^{1/2})² = A` for positive `A`. -/
theorem sqrtOp_comp_sqrtOp {A : E →L[ℂ] E} (hA : A.IsPositive) :
    sqrtOp A ∘L sqrtOp A = A := by
  rw [sqrtOp, ← mul_def, CFC.sqrt_mul_sqrt_self A (nonneg_iff_isPositive.2 hA)]

/-- `A^{1/2}` is the unique positive square root of `A`. -/
theorem sqrtOp_unique {A R : E →L[ℂ] E} (hR : R.IsPositive) (h : R ∘L R = A) :
    sqrtOp A = R :=
  CFC.sqrt_unique (by rw [mul_def, h]) (nonneg_iff_isPositive.2 hR)

/-- The square root commutes with every antiunitary involution `J` (conjugate linear,
`J² = 1`, `⟪J z, J w⟫ = ⟪w, z⟫`) that commutes with the positive operator `A`: `J A^{1/2} J` is a
positive square root of `J A J = A`, so it is `A^{1/2}`. -/
theorem sqrtOp_apply_conj {A : E →L[ℂ] E} (hA : A.IsPositive) {J : E → E}
    (hadd : ∀ z w, J (z + w) = J z + J w) (hsmul : ∀ (c : ℂ) z, J (c • z) = star c • J z)
    (hJJ : ∀ z, J (J z) = z) (hJi : ∀ z w, ⟪J z, J w⟫_ℂ = ⟪w, z⟫_ℂ)
    (hJA : ∀ z, A (J z) = J (A z)) (z : E) : sqrtOp A (J z) = J (sqrtOp A z) := by
  have hnorm : ∀ z, ‖J z‖ = ‖z‖ := fun z => by
    have h := hJi z z
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖J z‖ ^ 2 = ‖z‖ ^ 2 := by exact_mod_cast h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  have hS := isPositive_sqrtOp A
  let S' : E →L[ℂ] E := LinearMap.mkContinuous
    { toFun := fun z => J (sqrtOp A (J z))
      map_add' := fun z w => by simp only [hadd, map_add]
      map_smul' := fun c z => by simp only [hsmul, map_smul, star_star, RingHom.id_apply] }
    ‖sqrtOp A‖ fun z => by
      change ‖J (sqrtOp A (J z))‖ ≤ ‖sqrtOp A‖ * ‖z‖
      rw [hnorm, ← hnorm z]
      exact (sqrtOp A).le_opNorm _
  have hS'apply : ∀ z, S' z = J (sqrtOp A (J z)) := fun z => rfl
  have hS'pos : S'.IsPositive := by
    refine ⟨fun z w => ?_, fun z => ?_⟩
    · change ⟪S' z, w⟫_ℂ = ⟪z, S' w⟫_ℂ
      calc ⟪S' z, w⟫_ℂ = ⟪J (sqrtOp A (J z)), J (J w)⟫_ℂ := by rw [hS'apply, hJJ w]
        _ = ⟪J w, sqrtOp A (J z)⟫_ℂ := hJi _ _
        _ = ⟪sqrtOp A (J w), J z⟫_ℂ := (hS.inner_left_eq_inner_right _ _).symm
        _ = ⟪J (J z), J (sqrtOp A (J w))⟫_ℂ := (hJi _ _).symm
        _ = ⟪z, S' w⟫_ℂ := by rw [hS'apply, hJJ z]
    · have h1 : ⟪S' z, z⟫_ℂ = ⟪J z, sqrtOp A (J z)⟫_ℂ :=
        calc ⟪S' z, z⟫_ℂ = ⟪J (sqrtOp A (J z)), J (J z)⟫_ℂ := by rw [hS'apply, hJJ z]
          _ = ⟪J z, sqrtOp A (J z)⟫_ℂ := hJi _ _
      rw [reApplyInnerSelf_apply, h1]
      exact hS.re_inner_nonneg_right _
  have hS'sq : S' ∘L S' = A := by
    ext z
    rw [comp_apply, hS'apply, hS'apply, hJJ, ← comp_apply (sqrtOp A) (sqrtOp A),
      sqrtOp_comp_sqrtOp hA, hJA, hJJ]
  have heq : sqrtOp A = S' := sqrtOp_unique hS'pos hS'sq
  have h2 := hS'apply (J z)
  rw [← heq, hJJ] at h2
  exact h2

/-- `|T| = (T† T)^{1/2}`. -/
theorem cfcAbs_eq_sqrtOp (T : E →L[ℂ] E) : CFC.abs T = sqrtOp (adjoint T ∘L T) := by
  rw [CFC.abs, star_eq_adjoint, mul_def, sqrtOp]

/-- `|T| ≥ 0`. -/
theorem isPositive_cfcAbs (T : E →L[ℂ] E) : (CFC.abs T).IsPositive :=
  nonneg_iff_isPositive.1 (CFC.abs_nonneg T)

/-- `|T|² = T† T`. -/
theorem cfcAbs_comp_cfcAbs (T : E →L[ℂ] E) : CFC.abs T ∘L CFC.abs T = adjoint T ∘L T := by
  rw [← mul_def, CFC.abs_mul_abs, star_eq_adjoint, mul_def]

/-- `‖|T| x‖ = ‖T x‖`. -/
theorem norm_cfcAbs_apply (T : E →L[ℂ] E) (x : E) : ‖CFC.abs T x‖ = ‖T x‖ :=
  norm_apply_eq_of_comp_self (isPositive_cfcAbs T).isSelfAdjoint (cfcAbs_comp_cfcAbs T) x

/-- `|T|` is the unique positive square root of `T† T`. -/
theorem cfcAbs_unique {T R : E →L[ℂ] E} (hR : R.IsPositive) (h : R ∘L R = adjoint T ∘L T) :
    CFC.abs T = R := by
  rw [cfcAbs_eq_sqrtOp]
  exact sqrtOp_unique hR h

/-- `|T| = T` for positive `T`. -/
theorem cfcAbs_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) : CFC.abs T = T :=
  CFC.abs_of_nonneg T (nonneg_iff_isPositive.2 hT)

/-- **Polar decomposition** on a complex Hilbert space: `U = polarPart T |T|` is a partial
isometry with initial space `closure (range |T|)` (`U† U` is the orthogonal projection onto it,
`U` is isometric on it and zero on `(range |T|)ᗮ`), `‖U‖ ≤ 1`, `T = U |T|` and `U† T = |T|`. -/
theorem polar_decomposition_cfcAbs (T : E →L[ℂ] E) :
    polarPart T (CFC.abs T) ∘L CFC.abs T = T ∧
      adjoint (polarPart T (CFC.abs T)) ∘L T = CFC.abs T ∧
      ‖polarPart T (CFC.abs T)‖ ≤ 1 ∧
      adjoint (polarPart T (CFC.abs T)) ∘L polarPart T (CFC.abs T) =
        (initialSpace (CFC.abs T)).starProjection ∧
      (∀ x ∈ initialSpace (CFC.abs T), ‖polarPart T (CFC.abs T) x‖ = ‖x‖) ∧
      ∀ x ∈ (CFC.abs T).rangeᗮ, polarPart T (CFC.abs T) x = 0 := by
  have h : ∀ x, ‖T x‖ = ‖CFC.abs T x‖ := fun x => (norm_cfcAbs_apply T x).symm
  exact ⟨polarPart_comp h, adjoint_polarPart_comp h, norm_polarPart_le _ _,
    adjoint_polarPart_comp_polarPart h, fun x hx => norm_polarPart_apply h hx,
    fun x hx => polarPart_apply_of_mem_orthogonal h hx⟩

end Complex

/-! ### Real Hilbert spaces: `|T|` through the complexification -/

section Real

open Complexification

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The conjugation of `X_ℂ` is antiunitary: `⟪z̄, w̄⟫ = ⟪w, z⟫`. -/
theorem inner_star_star (z w : Complexification X) :
    ⟪star z, star w⟫_ℂ = ⟪w, z⟫_ℂ := by
  apply Complex.ext
  · simp only [Complexification.inner_re, star_re, star_im, inner_neg_neg]
    linarith [real_inner_comm z.re w.re, real_inner_comm z.im w.im]
  · simp only [Complexification.inner_im, star_re, star_im, inner_neg_left, inner_neg_right]
    linarith [real_inner_comm z.re w.im, real_inner_comm z.im w.re]

/-- Complexification of operators is injective. -/
theorem complexify_injective {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] :
    Function.Injective (fun A : X →L[ℝ] Y => A.complexify) := by
  intro A B h
  ext x
  simpa using congrArg (fun S => (S (x : Complexification X)).re) h

/-- `A_ℂ ≥ 0 ↔ A ≥ 0`. -/
theorem isPositive_complexify_iff [CompleteSpace X] (A : X →L[ℝ] X) :
    A.complexify.IsPositive ↔ A.IsPositive := by
  have hsa : IsSelfAdjoint A.complexify ↔ IsSelfAdjoint A := by
    rw [IsSelfAdjoint, IsSelfAdjoint, star_eq_adjoint, star_eq_adjoint, adjoint_complexify]
    exact complexify_injective.eq_iff
  have hre : ∀ z : Complexification X, A.complexify.reApplyInnerSelf z =
      A.reApplyInnerSelf z.re + A.reApplyInnerSelf z.im := by
    intro z
    simp [reApplyInnerSelf_apply, Complexification.inner_re]
  rw [isPositive_def', isPositive_def', hsa]
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h z => ?_⟩
  · simpa [hre, reApplyInnerSelf_apply] using h (x : Complexification X)
  · rw [hre]
    exact add_nonneg (h _) (h _)

variable [CompleteSpace X]

/-- `(A_ℂ)^{1/2}` commutes with the conjugation, for positive `A`. -/
theorem sqrtOp_complexify_star {A : X →L[ℝ] X} (hA : A.IsPositive) (z : Complexification X) :
    sqrtOp A.complexify (star z) = star (sqrtOp A.complexify z) :=
  sqrtOp_apply_conj ((isPositive_complexify_iff A).2 hA) star_add star_smul star_star
    inner_star_star (complexify_star A) z

/-- The positive square root of a positive operator `A` on a real Hilbert space: the
restriction `x ↦ re ((A_ℂ)^{1/2} x)` of `(A_ℂ)^{1/2}` to `X ⊆ X_ℂ` (`complexify_realSqrt`). -/
def realSqrt (A : X →L[ℝ] X) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x => (sqrtOp A.complexify (x : Complexification X)).re
      map_add' := fun x y => by simp only [ofReal_add, map_add, add_re]
      map_smul' := fun r x => by
        rw [ofReal_smul, ← Complex.coe_smul, map_smul, Complex.coe_smul, real_smul_re,
          RingHom.id_apply] }
    ‖sqrtOp A.complexify‖ fun x => by
      refine (norm_re_le _).trans ?_
      simpa using (sqrtOp A.complexify).le_opNorm (x : Complexification X)

theorem realSqrt_apply (A : X →L[ℝ] X) (x : X) :
    realSqrt A x = (sqrtOp A.complexify (x : Complexification X)).re := rfl

/-- `(realSqrt A)_ℂ = (A_ℂ)^{1/2}` for positive `A`. -/
theorem complexify_realSqrt {A : X →L[ℝ] X} (hA : A.IsPositive) :
    (realSqrt A).complexify = sqrtOp A.complexify := by
  have hreal : ∀ x : X, (sqrtOp A.complexify (x : Complexification X)).im = 0 := fun x => by
    rw [← star_eq_self_iff, ← sqrtOp_complexify_star hA, star_ofReal]
  ext z
  · conv_rhs => rw [← re_add_I_smul_im z]
    simp [realSqrt_apply, hreal]
  · conv_rhs => rw [← re_add_I_smul_im z]
    simp [realSqrt_apply, hreal]

/-- `realSqrt A ≥ 0`. -/
theorem isPositive_realSqrt {A : X →L[ℝ] X} (hA : A.IsPositive) : (realSqrt A).IsPositive := by
  rw [← isPositive_complexify_iff, complexify_realSqrt hA]
  exact isPositive_sqrtOp _

/-- `(realSqrt A)² = A`. -/
theorem realSqrt_comp_realSqrt {A : X →L[ℝ] X} (hA : A.IsPositive) :
    realSqrt A ∘L realSqrt A = A := by
  apply complexify_injective
  change (realSqrt A ∘L realSqrt A).complexify = A.complexify
  rw [complexify_comp, complexify_realSqrt hA,
    sqrtOp_comp_sqrtOp ((isPositive_complexify_iff A).2 hA)]

/-- `realSqrt A` is the unique positive square root of `A`. -/
theorem realSqrt_unique {A R : X →L[ℝ] X} (hR : R.IsPositive) (h : R ∘L R = A) :
    realSqrt A = R := by
  have hA : A.IsPositive := by
    have h' := isPositive_adjoint_comp_self R
    rwa [hR.isSelfAdjoint.adjoint_eq, h] at h'
  apply complexify_injective
  change (realSqrt A).complexify = R.complexify
  rw [complexify_realSqrt hA]
  exact sqrtOp_unique ((isPositive_complexify_iff R).2 hR) (by rw [← complexify_comp, h])

/-- The absolute value `|T| = (T† T)^{1/2}` on a real Hilbert space. -/
def realAbs (T : X →L[ℝ] X) : X →L[ℝ] X :=
  realSqrt (adjoint T ∘L T)

/-- `(realAbs T)_ℂ = (T_ℂ† T_ℂ)^{1/2}`, which is `|T_ℂ|` (`cfcAbs_eq_sqrtOp`). -/
theorem complexify_realAbs (T : X →L[ℝ] X) :
    (realAbs T).complexify = sqrtOp (adjoint T.complexify ∘L T.complexify) := by
  rw [realAbs, complexify_realSqrt (isPositive_adjoint_comp_self T), complexify_comp,
    adjoint_complexify]

/-- `realAbs T ≥ 0`. -/
theorem isPositive_realAbs (T : X →L[ℝ] X) : (realAbs T).IsPositive :=
  isPositive_realSqrt (isPositive_adjoint_comp_self T)

/-- `(realAbs T)² = T† T`. -/
theorem realAbs_comp_realAbs (T : X →L[ℝ] X) : realAbs T ∘L realAbs T = adjoint T ∘L T :=
  realSqrt_comp_realSqrt (isPositive_adjoint_comp_self T)

/-- `‖realAbs T x‖ = ‖T x‖`. -/
theorem norm_realAbs_apply (T : X →L[ℝ] X) (x : X) : ‖realAbs T x‖ = ‖T x‖ :=
  norm_apply_eq_of_comp_self (isPositive_realAbs T).isSelfAdjoint (realAbs_comp_realAbs T) x

/-- `realAbs T` is the unique positive square root of `T† T`. -/
theorem realAbs_unique {T R : X →L[ℝ] X} (hR : R.IsPositive) (h : R ∘L R = adjoint T ∘L T) :
    realAbs T = R :=
  realSqrt_unique hR h

/-- `realAbs T = T` for positive `T`. -/
theorem realAbs_of_isPositive {T : X →L[ℝ] X} (hT : T.IsPositive) : realAbs T = T :=
  realAbs_unique hT (by rw [hT.isSelfAdjoint.adjoint_eq])

/-- **Polar decomposition** on a real Hilbert space, with `|T| = realAbs T`: the same
statement as `polar_decomposition_cfcAbs`. -/
theorem polar_decomposition_realAbs (T : X →L[ℝ] X) :
    polarPart T (realAbs T) ∘L realAbs T = T ∧
      adjoint (polarPart T (realAbs T)) ∘L T = realAbs T ∧
      ‖polarPart T (realAbs T)‖ ≤ 1 ∧
      adjoint (polarPart T (realAbs T)) ∘L polarPart T (realAbs T) =
        (initialSpace (realAbs T)).starProjection ∧
      (∀ x ∈ initialSpace (realAbs T), ‖polarPart T (realAbs T) x‖ = ‖x‖) ∧
      ∀ x ∈ (realAbs T).rangeᗮ, polarPart T (realAbs T) x = 0 := by
  have h : ∀ x, ‖T x‖ = ‖realAbs T x‖ := fun x => (norm_realAbs_apply T x).symm
  exact ⟨polarPart_comp h, adjoint_polarPart_comp h, norm_polarPart_le _ _,
    adjoint_polarPart_comp_polarPart h, fun x hx => norm_polarPart_apply h hx,
    fun x hx => polarPart_apply_of_mem_orthogonal h hx⟩

end Real

end TraceClass

end DataDrivenControl
