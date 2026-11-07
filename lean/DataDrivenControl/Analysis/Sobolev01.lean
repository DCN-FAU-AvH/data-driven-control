module

public import Mathlib
public import DataDrivenControl.Analysis.SineBasis

/-!
# `H¹₀(0, 1)` and `H⁻¹(0, 1)`

Paper: `ex:intro-wave` (`introduction.tex`): the velocity of the wave equation lives in
`H⁻¹(0, 1)`, the dual of `H¹₀(0, 1)`.

## The model

* **`H¹₀(0, 1)` by derivatives.**  `H10` is the closed subspace `(ℝ ∙ e₀)ᗮ` of `L²(0, 1)`, the
  mean-zero classes.  An element `φ : H10` stands for the function `h10Fun φ = ∫₀^· φ`
  (`hasWeakDeriv_h10Fun`, `h10Fun_zero`, `h10Fun_one`): **the coercion `(φ : L2 ℝ 1)` is the
  derivative `φ'`**, and the norm is `‖φ'‖_{L²}`, the usual norm of `H¹₀(0, 1)` (equivalent to the
  `H¹` norm by Poincaré's inequality).  Every `x ∈ H¹(0, 1)` with `x(0) = x(1) = 0` arises
  (`exists_H10`).  `ofH10 : H10 →L[ℝ] L2 ℝ 1` is the embedding `φ ↦ [h10Fun φ]`.
* **`H⁻¹(0, 1)` is the dual.**  `Hm1 = StrongDual ℝ H10`, the bounded functionals on `H¹₀` with
  the dual norm, made a Hilbert space by the inner product
  `⟪ℓ, ℓ'⟫ = ⟪riesz⁻¹ ℓ, riesz⁻¹ ℓ'⟫` that induces the dual norm.  `riesz : H10 ≃ₗᵢ[ℝ] Hm1` is the
  Riesz isometry `φ ↦ ⟪φ, ·⟫ = (ψ ↦ ∫₀¹ φ' ψ')`, i.e. the Dirichlet Laplacian `-∂_ξξ : H¹₀ → H⁻¹`,
  and `riesz.symm = (-∂_ξξ)⁻¹`.

## Main declarations

* `h10Basis : HilbertBasis ℕ ℝ H10` (`h10Basis n = e_{n+1}` as a derivative), `sinH10 n`
  (`sₙ ∈ H¹₀`, `h10Fun_sinH10`), `integral_sinFun_mul_h10Fun`: `⟪sₙ, φ⟫ = ⟪e_{n+1}, φ'⟫ / ((n + 1)π)`.
* `hm1Basis : HilbertBasis ℕ ℝ Hm1`, `hm1Basis n = riesz (h10Basis n) = (n + 1)π sₙ`
  (`hm1Basis_eq`), and **the `H⁻¹` norm in sine coefficients**: `hasSum_norm_sq`
  (`‖ℓ‖² = ∑ₙ ℓ(sₙ)² / ((n + 1)π)²` for `ℓ ∈ H⁻¹`), `hasSum_norm_embed_sq`
  (`‖v‖²_{H⁻¹} = ∑ₙ ⟪sₙ, v⟫² / ((n + 1)π)²` for `v ∈ L²`).
* **`embed : L2 ℝ 1 →L[ℝ] Hm1`**, `L²(0, 1) ↪ H⁻¹(0, 1)`, `v ↦ (φ ↦ ∫₀¹ v φ)`
  (`embed_apply_eq_integral`), continuous with `‖embed v‖ ≤ π⁻¹ ‖v‖` (`norm_embed_le`),
  injective and with dense range (`injective_embed`, `denseRange_embed`).
* The Dirichlet problem `-ζ'' = ℓ`, `ζ(0) = ζ(1) = 0`: `IsDirichletH2` (`ζ ∈ H²(0, 1) ∩ H¹₀`),
  `riesz_symm_eq_of_weak` (the weak solution is `riesz.symm ℓ`), `riesz_eq_embed`
  (`riesz φ = [-φ'']` when `φ' ∈ H¹`), `exists_isDirichletH2_toH10` (for `ℓ = v ∈ L²` the solution
  is in `H²`, with `ζ'' = -v`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace Sobolev01

open CosineBasis SineBasis

/-! ### Parseval -/

/-- Parseval's identity in a real Hilbert basis: `‖x‖² = ∑ₙ ⟪eₙ, x⟫²`. -/
theorem hasSum_sq_inner {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : HilbertBasis ι ℝ E) (x : E) : HasSum (fun n => ⟪e n, x⟫_ℝ ^ 2) (‖x‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext n
  rw [sq, real_inner_comm (e n) x]

/-! ### `H¹₀(0, 1)` -/

/-- The mean-zero classes `{g ∈ L²(0, 1) : ∫₀¹ g = 0} = (ℝ ∙ e₀)ᗮ`, the derivatives of the
functions of `H¹₀(0, 1)`. -/
def meanZero : Submodule ℝ (L2 ℝ 1) := (ℝ ∙ cosBasis 0)ᗮ

/-- **`H¹₀(0, 1)`, modelled by derivatives**: `φ : H10` stands for the function
`h10Fun φ = ∫₀^· φ`, whose derivative is the class `(φ : L2 ℝ 1)`; the norm is `‖φ'‖_{L²}`. -/
abbrev H10 : Type := ↥meanZero

/-- `H¹₀(0, 1)` is complete: a closed subspace of `L²(0, 1)`. -/
instance : CompleteSpace H10 :=
  inferInstanceAs (CompleteSpace ↥((ℝ ∙ cosBasis 0)ᗮ : Submodule ℝ (L2 ℝ 1)))

/-- `g ∈ meanZero ↔ ∫₀¹ g = 0`. -/
theorem mem_meanZero_iff (g : L2 ℝ 1) : g ∈ meanZero ↔ ∫ t in (0 : ℝ)..1, g t = 0 := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_cosBasis]
  simp only [cosFun_zero, one_mul]

/-- The function `φ ∈ H¹₀(0, 1)` represented by `φ : H10`: `ξ ↦ ∫₀^ξ φ'`. -/
def h10Fun (φ : H10) : ℝ → ℝ := prim ((φ : L2 ℝ 1) : ℝ → ℝ)

/-- `h10Fun φ ∈ H¹(0, 1)` with weak derivative `(φ : L2 ℝ 1)`. -/
theorem hasWeakDeriv_h10Fun (φ : H10) : HasWeakDeriv 1 (h10Fun φ) ((φ : L2 ℝ 1) : ℝ → ℝ) :=
  hasWeakDeriv_prim (Lp.memLp _)

/-- The Dirichlet condition at `0`. -/
@[simp] theorem h10Fun_zero (φ : H10) : h10Fun φ 0 = 0 := prim_zero _

/-- The Dirichlet condition at `1`: `∫₀¹ φ' = 0`. -/
@[simp] theorem h10Fun_one (φ : H10) : h10Fun φ 1 = 0 := (mem_meanZero_iff _).1 φ.2

/-- The inner product of `H¹₀(0, 1)`: `⟪φ, ψ⟫ = ∫₀¹ φ' ψ'`. -/
theorem inner_H10 (φ ψ : H10) :
    ⟪φ, ψ⟫_ℝ = ∫ t in (0 : ℝ)..1, (φ : L2 ℝ 1) t * (ψ : L2 ℝ 1) t := by
  rw [Submodule.coe_inner, inner_eq_integral]

/-- The norm of `H¹₀(0, 1)` is `‖φ'‖_{L²}`. -/
theorem norm_H10 (φ : H10) : ‖φ‖ = ‖(φ : L2 ℝ 1)‖ := rfl

/-- `⟪φ, r • ψ⟫ = r ⟪φ, ψ⟫` in `H10` (stated for `H10`, where `rw [real_inner_smul_right]` does
not find the scalar action of the subtype). -/
theorem inner_smul_right_H10 (φ ψ : H10) (r : ℝ) : ⟪φ, r • ψ⟫_ℝ = r * ⟪φ, ψ⟫_ℝ :=
  real_inner_smul_right (F := H10) _ _ _

/-- `⟪r • φ, ψ⟫ = r ⟪φ, ψ⟫` in `H10`. -/
theorem inner_smul_left_H10 (φ ψ : H10) (r : ℝ) : ⟪r • φ, ψ⟫_ℝ = r * ⟪φ, ψ⟫_ℝ :=
  real_inner_smul_left (F := H10) _ _ _

/-- **Every `H¹₀` function is represented**: if `x ∈ H¹(0, 1)` has weak derivative `g` and
`x(0) = x(1) = 0`, then `x = h10Fun φ` on `[0, 1]` for the class `φ = [g]`. -/
theorem exists_H10 {x g : ℝ → ℝ} (h : HasWeakDeriv 1 x g) (h0 : x 0 = 0) (h1 : x 1 = 0) :
    ∃ φ : H10, ((φ : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] g ∧ EqOn (h10Fun φ) x (Icc 0 1) := by
  have hg := h.memLp_deriv
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, ∫ s in (0 : ℝ)..t, (hg.toLp g : L2 ℝ 1) s = x t := by
    intro t ht
    rw [intervalIntegral_congr_of_ae_eq hg.coeFn_toLp ht, h.eq_add_integral t ht, h0, zero_add]
  have hmem : hg.toLp g ∈ meanZero := by
    rw [mem_meanZero_iff, hint 1 ⟨zero_le_one, le_rfl⟩, h1]
  exact ⟨⟨hg.toLp g, hmem⟩, hg.coeFn_toLp, fun t ht => hint t ht⟩

/-! ### The basis of `H¹₀` -/

/-- `e_{n+1}` has mean zero. -/
theorem cosBasis_succ_mem (n : ℕ) : cosBasis (n + 1) ∈ meanZero := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right,
    orthonormal_iff_ite.1 cosBasis.orthonormal]
  simp

/-- `e_{n+1}` as an element of `H10`. -/
def h10BasisFun (n : ℕ) : H10 := ⟨cosBasis (n + 1), cosBasis_succ_mem n⟩

/-- The `e_{n+1}` are orthonormal in `H10`. -/
theorem orthonormal_h10BasisFun : Orthonormal ℝ h10BasisFun := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [Submodule.coe_inner]
  simp only [h10BasisFun]
  rw [orthonormal_iff_ite.1 cosBasis.orthonormal]
  simp

/-- A mean-zero class orthogonal to every `e_{n+1}` vanishes (completeness of `cosBasis`). -/
theorem orthogonal_span_h10BasisFun : (Submodule.span ℝ (range h10BasisFun))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
  have h : ∀ n, ⟪cosBasis (n + 1), (φ : L2 ℝ 1)⟫_ℝ = 0 := fun n => by
    have := (Submodule.mem_orthogonal _ _).1 hφ _ (Submodule.subset_span ⟨n, rfl⟩)
    rwa [Submodule.coe_inner] at this
  have h0 : ⟪cosBasis 0, (φ : L2 ℝ 1)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 φ.2
  have := eq_smul_cosBasis_zero h
  rw [h0, zero_smul] at this
  exact Subtype.ext this

/-- **The Hilbert basis of `H¹₀(0, 1)`**: the derivatives `e_{n+1} = √2 cos((n + 1)π·)`, i.e. the
functions `sₙ / ((n + 1)π)` (`h10Fun_sinH10`). -/
def h10Basis : HilbertBasis ℕ ℝ H10 :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_h10BasisFun orthogonal_span_h10BasisFun

/-- `h10Basis n` has derivative `e_{n+1}`. -/
theorem coe_h10Basis (n : ℕ) : ((h10Basis n : H10) : L2 ℝ 1) = cosBasis (n + 1) := by
  rw [h10Basis, HilbertBasis.coe_mkOfOrthogonalEqBot]; rfl

/-- The coordinates in `h10Basis`: `⟪h10Basis n, φ⟫ = ⟪e_{n+1}, φ'⟫`. -/
theorem inner_h10Basis (n : ℕ) (φ : H10) :
    ⟪h10Basis n, φ⟫_ℝ = ⟪cosBasis (n + 1), (φ : L2 ℝ 1)⟫_ℝ := by
  rw [Submodule.coe_inner, coe_h10Basis]

/-- `sₙ ∈ H¹₀(0, 1)`: the element with derivative `(n + 1)π e_{n+1}`. -/
def sinH10 (n : ℕ) : H10 := sinFreq n • h10Basis n

/-- `sinH10 n` is the function `sₙ`. -/
theorem h10Fun_sinH10 (n : ℕ) : EqOn (h10Fun (sinH10 n)) (sinFun n) (Icc 0 1) := by
  intro t ht
  have hae : (((sinH10 n : H10) : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1]
      fun s => sinFreq n * cosFun (n + 1) s := by
    have h1 : ((sinH10 n : H10) : L2 ℝ 1) = sinFreq n • cosBasis (n + 1) := by
      rw [sinH10, Submodule.coe_smul, coe_h10Basis]
    rw [h1]
    filter_upwards [Lp.coeFn_smul (sinFreq n) (cosBasis (n + 1)), coeFn_cosBasis (n + 1)]
      with s h2 h3
    rw [h2, Pi.smul_apply, h3, smul_eq_mul]
  rw [h10Fun, prim, intervalIntegral_congr_of_ae_eq hae ht,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_sinFun n s)
      (((continuous_cosFun (n + 1)).const_mul (sinFreq n)).intervalIntegrable _ _),
    sinFun_zero, sub_zero]

/-- `sinH10 n` has coordinates `(n + 1)π` at `n`. -/
theorem inner_h10Basis_sinH10 (m n : ℕ) :
    ⟪h10Basis m, sinH10 n⟫_ℝ = if m = n then sinFreq n else 0 := by
  rw [sinH10, inner_smul_right_H10, orthonormal_iff_ite.1 h10Basis.orthonormal]
  split_ifs <;> simp

/-- **The sine coordinates of `φ ∈ H¹₀`**: `⟪sₙ, φ⟫ = ⟪e_{n+1}, φ'⟫ / ((n + 1)π)` (integration by
parts with `φ(0) = φ(1) = 0`). -/
theorem integral_sinFun_mul_h10Fun (φ : H10) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, sinFun n t * h10Fun φ t = (sinFreq n)⁻¹ * ⟪h10Basis n, φ⟫_ℝ := by
  have h := integral_cosFun_succ_mul_deriv (hasWeakDeriv_h10Fun φ) (h10Fun_zero φ)
    (h10Fun_one φ) n
  rw [inner_h10Basis, inner_cosBasis, h]
  field_simp [(sinFreq_pos n).ne']

/-! ### The embedding `H¹₀ ↪ L²` -/

/-- `h10Fun φ ∈ L²(0, 1)`. -/
theorem memLp_h10Fun (φ : H10) : MemLp (h10Fun φ) 2 (μI 1) := (hasWeakDeriv_h10Fun φ).memLp

/-- The class of `h10Fun φ`. -/
def ofH10Fun (φ : H10) : L2 ℝ 1 := (memLp_h10Fun φ).toLp _

/-- The sine coordinates of `[h10Fun φ]`: `⟪sₙ, [φ]⟫ = ⟪h10Basis n, φ⟫ / ((n + 1)π)`. -/
theorem inner_sinBasis_ofH10Fun (φ : H10) (n : ℕ) :
    ⟪sinBasis n, ofH10Fun φ⟫_ℝ = (sinFreq n)⁻¹ * ⟪h10Basis n, φ⟫_ℝ := by
  rw [ofH10Fun, inner_sinBasis_of_ae_eq (MemLp.coeFn_toLp (memLp_h10Fun φ)),
    integral_sinFun_mul_h10Fun]

/-- The embedding `H¹₀(0, 1) ↪ L²(0, 1)`, `φ ↦ [h10Fun φ]`, with `‖[φ]‖ ≤ ‖φ'‖`. -/
def ofH10 : H10 →L[ℝ] L2 ℝ 1 :=
  LinearMap.mkContinuous
    { toFun := ofH10Fun
      map_add' := fun φ ψ => basis_ext sinBasis fun n => by
        simp only [inner_add_right, inner_sinBasis_ofH10Fun]
        ring
      map_smul' := fun r φ => basis_ext sinBasis fun n => by
        simp only [real_inner_smul_right, RingHom.id_apply, inner_sinBasis_ofH10Fun]
        ring }
    1 fun φ => by
      have h1 : ‖ofH10Fun φ‖ ^ 2 ≤ (1 * ‖φ‖) ^ 2 := by
        rw [one_mul]
        refine hasSum_le (fun n => ?_) (hasSum_sq_inner sinBasis _) (hasSum_sq_inner h10Basis φ)
        rw [inner_sinBasis_ofH10Fun, mul_pow]
        have h2 : ((sinFreq n)⁻¹) ^ 2 ≤ 1 := by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (abs_inv_sinFreq_le n)
        nlinarith [sq_nonneg ⟪h10Basis n, φ⟫_ℝ]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

/-- `ofH10 φ` is the class of `h10Fun φ`. -/
theorem coeFn_ofH10 (φ : H10) : (ofH10 φ : ℝ → ℝ) =ᵐ[μI 1] h10Fun φ :=
  MemLp.coeFn_toLp (memLp_h10Fun φ)

/-- The sine coordinates of `ofH10 φ`. -/
theorem inner_sinBasis_ofH10 (φ : H10) (n : ℕ) :
    ⟪sinBasis n, ofH10 φ⟫_ℝ = (sinFreq n)⁻¹ * ⟪h10Basis n, φ⟫_ℝ :=
  inner_sinBasis_ofH10Fun φ n

/-- `h10Basis n` is the function `sₙ / ((n + 1)π)`. -/
theorem ofH10_h10Basis (n : ℕ) : ofH10 (h10Basis n) = (sinFreq n)⁻¹ • sinBasis n := by
  refine basis_ext sinBasis fun m => ?_
  rw [inner_sinBasis_ofH10, real_inner_smul_right, orthonormal_iff_ite.1 h10Basis.orthonormal,
    orthonormal_iff_ite.1 sinBasis.orthonormal]
  split_ifs with h
  · subst h; rfl
  · simp

/-- `sinH10 n` is the class `sₙ`. -/
theorem ofH10_sinH10 (n : ℕ) : ofH10 (sinH10 n) = sinBasis n := by
  rw [sinH10, map_smul, ofH10_h10Basis, smul_smul, mul_inv_cancel₀ (sinFreq_pos n).ne', one_smul]

/-- `H¹₀ ↪ L²` is injective. -/
theorem injective_ofH10 : Function.Injective ofH10 := by
  intro φ ψ h
  refine basis_ext h10Basis fun n => ?_
  have h1 := congrArg (fun x => ⟪sinBasis n, x⟫_ℝ) h
  simp only [inner_sinBasis_ofH10] at h1
  exact mul_left_cancel₀ (inv_ne_zero (sinFreq_pos n).ne') h1

/-! ### `H⁻¹(0, 1)` -/

/-- **The Riesz isometry `H¹₀ ≃ (H¹₀)'`**, `φ ↦ ⟪φ, ·⟫ = (ψ ↦ ∫₀¹ φ' ψ')`: the Dirichlet Laplacian
`-∂_ξξ : H¹₀(0, 1) → H⁻¹(0, 1)` in weak form. -/
def riesz : H10 ≃ₗᵢ[ℝ] StrongDual ℝ H10 where
  toFun := InnerProductSpace.toDual ℝ H10
  invFun := (InnerProductSpace.toDual ℝ H10).symm
  map_add' := map_add _
  map_smul' r φ := by
    ext ψ
    simp only [InnerProductSpace.toDual_apply_apply, RingHom.id_apply,
      smul_apply, smul_eq_mul]
    exact inner_smul_left_H10 φ ψ r
  left_inv := (InnerProductSpace.toDual ℝ H10).symm_apply_apply
  right_inv := (InnerProductSpace.toDual ℝ H10).apply_symm_apply
  norm_map' := (InnerProductSpace.toDual ℝ H10).norm_map

/-- `riesz φ ψ = ⟪φ, ψ⟫ = ∫₀¹ φ' ψ'`. -/
theorem riesz_apply (φ ψ : H10) : riesz φ ψ = ⟪φ, ψ⟫_ℝ := rfl

/-- `⟪riesz⁻¹ ℓ, ψ⟫ = ℓ ψ`. -/
theorem inner_riesz_symm (ℓ : StrongDual ℝ H10) (ψ : H10) : ⟪riesz.symm ℓ, ψ⟫_ℝ = ℓ ψ :=
  InnerProductSpace.toDual_symm_apply

/-- **`H⁻¹(0, 1)`**: the dual `StrongDual ℝ H10` of `H¹₀(0, 1)`, with its dual norm. -/
abbrev Hm1 : Type := StrongDual ℝ H10

/-- The Hilbert structure of `H⁻¹(0, 1)`: `⟪ℓ, ℓ'⟫ = ⟪riesz⁻¹ ℓ, riesz⁻¹ ℓ'⟫`, which induces the
dual norm. -/
instance : InnerProductSpace ℝ Hm1 where
  inner ℓ ℓ' := ⟪riesz.symm ℓ, riesz.symm ℓ'⟫_ℝ
  norm_sq_eq_re_inner ℓ := by
    show ‖ℓ‖ ^ 2 = RCLike.re ⟪riesz.symm ℓ, riesz.symm ℓ⟫_ℝ
    rw [RCLike.re_to_real, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  conj_inner_symm ℓ ℓ' := by
    show (starRingEnd ℝ) ⟪riesz.symm ℓ', riesz.symm ℓ⟫_ℝ = ⟪riesz.symm ℓ, riesz.symm ℓ'⟫_ℝ
    rw [conj_trivial, real_inner_comm]
  add_left ℓ₁ ℓ₂ ℓ' := by
    show ⟪riesz.symm (ℓ₁ + ℓ₂), riesz.symm ℓ'⟫_ℝ =
      ⟪riesz.symm ℓ₁, riesz.symm ℓ'⟫_ℝ + ⟪riesz.symm ℓ₂, riesz.symm ℓ'⟫_ℝ
    rw [map_add, inner_add_left]
  smul_left ℓ ℓ' r := by
    show ⟪riesz.symm (r • ℓ), riesz.symm ℓ'⟫_ℝ =
      (starRingEnd ℝ) r * ⟪riesz.symm ℓ, riesz.symm ℓ'⟫_ℝ
    rw [map_smul, inner_smul_left_H10, conj_trivial]

/-- The inner product of `H⁻¹(0, 1)`. -/
theorem inner_Hm1 (ℓ ℓ' : Hm1) : ⟪ℓ, ℓ'⟫_ℝ = ⟪riesz.symm ℓ, riesz.symm ℓ'⟫_ℝ := rfl

/-- `⟪ℓ, r • ℓ'⟫ = r ⟪ℓ, ℓ'⟫` in `Hm1`. -/
theorem inner_smul_right_Hm1 (ℓ ℓ' : Hm1) (r : ℝ) : ⟪ℓ, r • ℓ'⟫_ℝ = r * ⟪ℓ, ℓ'⟫_ℝ :=
  real_inner_smul_right (F := Hm1) _ _ _

/-- `⟪riesz φ, ℓ⟫ = ℓ φ`. -/
theorem inner_riesz_left (φ : H10) (ℓ : Hm1) : ⟪riesz φ, ℓ⟫_ℝ = ℓ φ := by
  rw [inner_Hm1, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, inner_riesz_symm]

/-- The images `riesz (h10Basis n)` are orthonormal in `H⁻¹(0, 1)` (`riesz` is an isometry). -/
theorem orthonormal_riesz_h10Basis : Orthonormal ℝ (riesz ∘ h10Basis) :=
  h10Basis.orthonormal.comp_linearIsometryEquiv riesz

/-- A functional orthogonal to every `riesz (h10Basis n)` vanishes. -/
theorem orthogonal_span_riesz_h10Basis :
    (Submodule.span ℝ (range (riesz ∘ h10Basis)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun ℓ hℓ => ?_
  have h : ∀ n, ⟪h10Basis n, riesz.symm ℓ⟫_ℝ = ⟪h10Basis n, (0 : H10)⟫_ℝ := fun n => by
    have := (Submodule.mem_orthogonal _ _).1 hℓ _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [Function.comp_apply, inner_riesz_left] at this
    rw [inner_zero_right, real_inner_comm, inner_riesz_symm, this]
  have h0 := basis_ext h10Basis h
  rw [← riesz.apply_symm_apply ℓ, h0, LinearIsometryEquiv.map_zero]

/-- **The Hilbert basis of `H⁻¹(0, 1)`**: `riesz (h10Basis n)`, which is `(n + 1)π sₙ`
(`hm1Basis_eq`). -/
def hm1Basis : HilbertBasis ℕ ℝ Hm1 :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_riesz_h10Basis orthogonal_span_riesz_h10Basis

/-- `hm1Basis n = riesz (h10Basis n)`. -/
theorem hm1Basis_apply (n : ℕ) : hm1Basis n = riesz (h10Basis n) := by
  rw [hm1Basis, HilbertBasis.coe_mkOfOrthogonalEqBot, Function.comp_apply]

/-- The coordinates in `hm1Basis`: `⟪hm1Basis n, ℓ⟫ = ℓ (h10Basis n) = ℓ(sₙ) / ((n + 1)π)`. -/
theorem inner_hm1Basis (n : ℕ) (ℓ : Hm1) : ⟪hm1Basis n, ℓ⟫_ℝ = ℓ (h10Basis n) := by
  rw [hm1Basis_apply, inner_riesz_left]

/-- `ℓ(sₙ) = (n + 1)π ⟪hm1Basis n, ℓ⟫`. -/
theorem apply_sinH10 (n : ℕ) (ℓ : Hm1) : ℓ (sinH10 n) = sinFreq n * ⟪hm1Basis n, ℓ⟫_ℝ := by
  rw [inner_hm1Basis, sinH10, map_smul, smul_eq_mul]

/-- **The `H⁻¹` norm in sine coefficients**: `‖ℓ‖² = ∑ₙ ℓ(sₙ)² / ((n + 1)π)²` for `ℓ ∈ H⁻¹(0, 1)`,
with `ℓ(sₙ)` the value of `ℓ` at `sₙ ∈ H¹₀(0, 1)`. -/
theorem hasSum_norm_sq (ℓ : Hm1) :
    HasSum (fun n => ℓ (sinH10 n) ^ 2 / sinFreq n ^ 2) (‖ℓ‖ ^ 2) := by
  convert hasSum_sq_inner hm1Basis ℓ using 1
  funext n
  rw [apply_sinH10]
  field_simp [(sinFreq_pos n).ne']

/-! ### The embedding `L² ↪ H⁻¹` -/

/-- The adjoint of `H¹₀ ↪ L²`: `toH10 v ∈ H¹₀` with `⟪toH10 v, φ⟫ = ∫₀¹ v φ`, i.e. the solution of
`-ζ'' = v`, `ζ(0) = ζ(1) = 0`. -/
def toH10 : L2 ℝ 1 →L[ℝ] H10 := ContinuousLinearMap.adjoint ofH10

/-- `⟪toH10 v, φ⟫ = ⟪v, [φ]⟫`. -/
theorem inner_toH10 (v : L2 ℝ 1) (φ : H10) : ⟪toH10 v, φ⟫_ℝ = ⟪v, ofH10 φ⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The coordinates of `toH10 v`: `⟪h10Basis n, toH10 v⟫ = ⟪sₙ, v⟫ / ((n + 1)π)`. -/
theorem inner_h10Basis_toH10 (v : L2 ℝ 1) (n : ℕ) :
    ⟪h10Basis n, toH10 v⟫_ℝ = (sinFreq n)⁻¹ * ⟪sinBasis n, v⟫_ℝ := by
  rw [real_inner_comm, inner_toH10, ofH10_h10Basis, real_inner_smul_right, real_inner_comm]

/-- **The embedding `L²(0, 1) ↪ H⁻¹(0, 1)`**, `v ↦ (φ ↦ ∫₀¹ v φ)` (`embed_apply_eq_integral`). -/
def embed : L2 ℝ 1 →L[ℝ] Hm1 := riesz.toLinearIsometry.toContinuousLinearMap.comp toH10

/-- `embed v φ = ⟪v, [φ]⟫`. -/
theorem embed_apply (v : L2 ℝ 1) (φ : H10) : embed v φ = ⟪v, ofH10 φ⟫_ℝ := by
  show riesz (toH10 v) φ = _
  rw [riesz_apply, inner_toH10]

/-- **`embed v` is the functional `φ ↦ ∫₀¹ v φ`.** -/
theorem embed_apply_eq_integral (v : L2 ℝ 1) (φ : H10) :
    embed v φ = ∫ t in (0 : ℝ)..1, v t * h10Fun φ t := by
  rw [embed_apply, inner_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofH10 φ] with t h
  rw [h]

/-- `riesz⁻¹ (embed v) = toH10 v`. -/
theorem riesz_symm_embed (v : L2 ℝ 1) : riesz.symm (embed v) = toH10 v :=
  riesz.symm_apply_apply (toH10 v)

/-- `(embed v)(sₙ) = ⟪sₙ, v⟫`. -/
theorem embed_sinH10 (v : L2 ℝ 1) (n : ℕ) : embed v (sinH10 n) = ⟪sinBasis n, v⟫_ℝ := by
  rw [embed_apply, ofH10_sinH10, real_inner_comm]

/-- The coordinates of `embed v`: `⟪hm1Basis n, v⟫ = ⟪sₙ, v⟫ / ((n + 1)π)`. -/
theorem inner_hm1Basis_embed (v : L2 ℝ 1) (n : ℕ) :
    ⟪hm1Basis n, embed v⟫_ℝ = (sinFreq n)⁻¹ * ⟪sinBasis n, v⟫_ℝ := by
  rw [inner_hm1Basis, embed_apply, ofH10_h10Basis, real_inner_smul_right, real_inner_comm]

/-- **The `H⁻¹` norm of `v ∈ L²(0, 1)` in sine coefficients**:
`‖v‖²_{H⁻¹} = ∑ₙ ⟪sₙ, v⟫² / ((n + 1)π)²`. -/
theorem hasSum_norm_embed_sq (v : L2 ℝ 1) :
    HasSum (fun n => ⟪sinBasis n, v⟫_ℝ ^ 2 / sinFreq n ^ 2) (‖embed v‖ ^ 2) := by
  simpa only [embed_sinH10] using hasSum_norm_sq (embed v)

/-- `hm1Basis n = (n + 1)π sₙ` in `H⁻¹(0, 1)`. -/
theorem hm1Basis_eq (n : ℕ) : hm1Basis n = sinFreq n • embed (sinBasis n) := by
  refine basis_ext hm1Basis fun m => ?_
  rw [inner_smul_right_Hm1, inner_hm1Basis_embed, orthonormal_iff_ite.1 hm1Basis.orthonormal,
    orthonormal_iff_ite.1 sinBasis.orthonormal]
  split_ifs with h
  · subst h; field_simp [(sinFreq_pos m).ne']
  · simp

/-- **`L² ↪ H⁻¹` is continuous**: `‖v‖_{H⁻¹} ≤ π⁻¹ ‖v‖_{L²}` (Poincaré). -/
theorem norm_embed_le (v : L2 ℝ 1) : ‖embed v‖ ≤ Real.pi⁻¹ * ‖v‖ := by
  have h1 : ‖embed v‖ ^ 2 ≤ (Real.pi⁻¹ * ‖v‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n => ?_) (hasSum_norm_embed_sq v)
      ((hasSum_sq_inner sinBasis v).mul_left _)
    have hp := pi_le_sinFreq n
    have h2 : (sinFreq n ^ 2)⁻¹ ≤ (Real.pi⁻¹) ^ 2 := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ Real.pi_pos.le hp 2)
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg (embed v))
    (mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (norm_nonneg v)) two_ne_zero).1 h1

/-- **`L² ↪ H⁻¹` is injective.** -/
theorem injective_embed : Function.Injective embed := by
  intro v w h
  refine basis_ext sinBasis fun n => ?_
  have h1 := congrArg (fun ℓ => ⟪hm1Basis n, ℓ⟫_ℝ) h
  simp only [inner_hm1Basis_embed] at h1
  exact mul_left_cancel₀ (inv_ne_zero (sinFreq_pos n).ne') h1

/-- **`L² ↪ H⁻¹` has dense range**: its range contains the basis `hm1Basis`. -/
theorem denseRange_embed : DenseRange embed := by
  intro ℓ
  refine mem_closure_of_tendsto (hm1Basis.hasSum_repr ℓ) (Eventually.of_forall fun s => ?_)
  refine ⟨∑ i ∈ s, (hm1Basis.repr ℓ i * sinFreq i) • sinBasis i, ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show _ = hm1Basis.repr ℓ i • hm1Basis i
  rw [map_smul, hm1Basis_eq, smul_smul]

/-! ### The Dirichlet problem -/

/-- **`ζ ∈ H²(0, 1) ∩ H¹₀(0, 1)`** with derivatives `ζ'`, `ζ''`, in the integral form of
`HasWeakDeriv`. -/
structure IsDirichletH2 (ζ ζ' ζ'' : ℝ → ℝ) : Prop where
  /-- `ζ ∈ H¹(0, 1)` with weak derivative `ζ'`. -/
  hasWeakDeriv : HasWeakDeriv 1 ζ ζ'
  /-- `ζ' ∈ H¹(0, 1)` with weak derivative `ζ'' ∈ L²(0, 1)`. -/
  hasWeakDeriv_deriv : HasWeakDeriv 1 ζ' ζ''
  /-- The Dirichlet condition at `0`. -/
  zero : ζ 0 = 0
  /-- The Dirichlet condition at `1`. -/
  one : ζ 1 = 0

/-- **The weak Dirichlet problem**: if `ζ ∈ H¹₀(0, 1)` solves `-ζ'' = ℓ` weakly, i.e.
`∫₀¹ ζ' ψ' = ℓ ψ` for every `ψ ∈ H¹₀`, then `ζ = (-∂_ξξ)⁻¹ ℓ = riesz⁻¹ ℓ`: its derivative is
`riesz⁻¹ ℓ` and `ζ = h10Fun (riesz⁻¹ ℓ)` on `[0, 1]`. -/
theorem riesz_symm_eq_of_weak {ζ ζ' : ℝ → ℝ} (hζ : HasWeakDeriv 1 ζ ζ') (h0 : ζ 0 = 0)
    (h1 : ζ 1 = 0) {ℓ : Hm1}
    (hweak : ∀ ψ : H10, ∫ t in (0 : ℝ)..1, ζ' t * (ψ : L2 ℝ 1) t = ℓ ψ) :
    (((riesz.symm ℓ : H10) : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] ζ' ∧
      EqOn (h10Fun (riesz.symm ℓ)) ζ (Icc 0 1) := by
  obtain ⟨φ, hφ, hφζ⟩ := exists_H10 hζ h0 h1
  have hr : riesz φ = ℓ := by
    ext ψ
    rw [riesz_apply, inner_H10, ← hweak ψ, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    refine integral_congr_ae ?_
    filter_upwards [hφ] with t h
    rw [h]
  rw [← hr, LinearIsometryEquiv.symm_apply_apply]
  exact ⟨hφ, hφζ⟩

/-- **`riesz` is `-∂_ξξ`**: if the derivative `φ'` of `φ ∈ H¹₀` has an `H¹` representative `ζ'`
with weak derivative `ζ''`, then `riesz φ = [-ζ'']` in `H⁻¹`. -/
theorem riesz_eq_embed {φ : H10} {ζ' ζ'' : ℝ → ℝ} (hφ : ((φ : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] ζ')
    (h : HasWeakDeriv 1 ζ' ζ'') : riesz φ = embed (h.memLp_deriv.neg.toLp fun t => -ζ'' t) := by
  refine basis_ext hm1Basis fun n => ?_
  rw [inner_hm1Basis_embed, hm1Basis_apply, inner_riesz_left, riesz_apply, real_inner_comm,
    inner_h10Basis,
    inner_cosBasis_of_ae_eq hφ, inner_sinBasis_of_ae_eq (MemLp.coeFn_toLp _)]
  have h2 := integral_sinFun_mul_deriv h n
  have h3 : ∫ t in (0 : ℝ)..1, sinFun n t * -ζ'' t = -∫ t in (0 : ℝ)..1, sinFun n t * ζ'' t := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext t; ring
  rw [h3, h2]
  field_simp [(sinFreq_pos n).ne']

/-- **Regularity for the Dirichlet problem with `L²` data**: for `v ∈ L²(0, 1)`, the derivative of
`ζ = (-∂_ξξ)⁻¹ v = toH10 v` has an `H¹` representative `ζ'` with `ζ'' = -v`. -/
theorem exists_hasWeakDeriv_toH10 (v : L2 ℝ 1) :
    ∃ ζ' : ℝ → ℝ, HasWeakDeriv 1 ζ' (fun t => -v t) ∧
      (((toH10 v : H10) : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] ζ' := by
  have hv : MemLp (fun t => -v t) 2 (μI 1) := (Lp.memLp v).neg
  have hΨ := hasWeakDeriv_prim hv
  set Ψc : L2 ℝ 1 := hΨ.memLp.toLp (prim fun t => -v t) with hΨc
  have hc : ∀ n, ⟪cosBasis (n + 1), Ψc - ((toH10 v : H10) : L2 ℝ 1)⟫_ℝ = 0 := fun n => by
    have h1 := integral_sinFun_mul_deriv hΨ n
    have h2 : ∫ t in (0 : ℝ)..1, sinFun n t * -v t = -⟪sinBasis n, v⟫_ℝ := by
      rw [inner_sinBasis, ← intervalIntegral.integral_neg]; congr 1; funext t; ring
    rw [h2] at h1
    rw [inner_sub_right, inner_cosBasis_toLp, ← inner_h10Basis, inner_h10Basis_toH10]
    field_simp [(sinFreq_pos n).ne']
    linarith
  set a := ⟪cosBasis 0, Ψc - ((toH10 v : H10) : L2 ℝ 1)⟫_ℝ
  have hae := ae_eq_const_of_inner_cosBasis_succ hc
  refine ⟨fun t => prim (fun t => -v t) t - a, ⟨hv, fun t ht => ?_⟩, ?_⟩
  · have := hΨ.eq_add_integral t ht
    simp only [prim_zero, zero_sub] at this ⊢
    linarith
  · filter_upwards [hae, Lp.coeFn_sub Ψc ((toH10 v : H10) : L2 ℝ 1), hΨ.memLp.coeFn_toLp]
      with t h1 h2 h3
    rw [h2, Pi.sub_apply, h3] at h1
    linarith

/-- **`(-∂_ξξ)⁻¹ v ∈ H²(0, 1) ∩ H¹₀(0, 1)`** for `v ∈ L²(0, 1)`, with `ζ'' = -v`. -/
theorem exists_isDirichletH2_toH10 (v : L2 ℝ 1) :
    ∃ ζ' : ℝ → ℝ, IsDirichletH2 (h10Fun (toH10 v)) ζ' (fun t => -v t) ∧
      (((toH10 v : H10) : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] ζ' := by
  obtain ⟨ζ', h, hae⟩ := exists_hasWeakDeriv_toH10 v
  exact ⟨ζ', ⟨(hasWeakDeriv_h10Fun _).congr (fun _ _ => rfl) hae, h, h10Fun_zero _,
    h10Fun_one _⟩, hae⟩

end Sobolev01

end DataDrivenControl
