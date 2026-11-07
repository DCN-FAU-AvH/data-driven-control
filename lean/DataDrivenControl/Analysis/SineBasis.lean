module

public import Mathlib
public import DataDrivenControl.Analysis.CosineBasis
public import DataDrivenControl.Signal.WeakDerivative

/-!
# The sine basis of `L²(0, 1)`

Paper: `ex:intro-wave` (`introduction.tex`): the Dirichlet eigenfunctions
`sₙ(ξ) = √2 sin(nπξ)`, `n ≥ 1`, of `∂_ξξ` on `(0, 1)` form a Hilbert basis of `L²(0, 1)`.

`L²(0, 1)` is the project's `L2 ℝ 1 = Lp ℝ 2 (μI 1)`, `μI 1 = volume.restrict (Ioc 0 1)`.
Modes count from `0`, as in `Examples/Wave`: Lean's `sinFun n` is the paper's `s_{n+1}`, with
frequency `sinFreq n = (n + 1)π`.

## Main declarations

* `sinFreq n` (`(n + 1)π`), `sinFun n` (`sₙ(ξ) = √2 sin((n + 1)πξ)`): `hasDerivAt_sinFun`
  (`sₙ' = (n + 1)π e_{n+1}`), `hasDerivAt_cosFun_succ` (`e_{n+1}' = -(n + 1)π sₙ`), where
  `eₖ = cosFun k` is the cosine basis of `Analysis/CosineBasis`; `sinFun_zero`, `sinFun_one`
  (Dirichlet conditions);
* `integral_sinFun_mul_sinFun`: `∫₀¹ sₘ sₙ = [m = n]`;
* **`sinBasis : HilbertBasis ℕ ℝ (L2 ℝ 1)`** with `sinBasis n = [sₙ]` (`sinBasis_apply`,
  `coeFn_sinBasis`); `inner_sinBasis`, `inner_sinBasis_of_ae_eq`: `⟪sₙ, f⟫ = ∫₀¹ sₙ f`;
* integration by parts against the eigenfunctions, for `x ∈ H¹(0, 1)` with weak derivative `g`
  (`HasWeakDeriv`): `integral_sinFun_mul_deriv` (`∫₀¹ sₙ g = -(n + 1)π ∫₀¹ e_{n+1} x`) and, when
  `x(0) = x(1) = 0`, `integral_cosFun_succ_mul_deriv` (`∫₀¹ e_{n+1} g = (n + 1)π ∫₀¹ sₙ x`);
* `prim f` (`ξ ↦ ∫₀^ξ f`), `hasWeakDeriv_prim`;
* `ae_eq_const_of_inner_cosBasis_succ`: a class orthogonal to every `e_{n+1}` is constant.

## Auxiliary results

`integral_mul_deriv` (integration by parts of an `H¹` function against a `C¹` function) and
`intervalIntegral_congr_of_ae_eq` are restated from `Examples/Heat/PDE` so that this file does not
depend on the heat example.

## Proof of completeness

Let `f ⊥ sₙ` for every `n`, and `F(ξ) = ∫₀^ξ f`.  Integration by parts gives
`0 = ∫₀¹ sₙ f = -(n + 1)π ∫₀¹ e_{n+1} F` (the boundary terms vanish because `sₙ(0) = sₙ(1) = 0`),
so `[F]` is orthogonal to every `e_{n+1}` and is a.e. constant by completeness of `cosBasis`.
`F` is continuous and `F(0) = 0`, so `F = 0` on `[0, 1]`.  Integrating by parts again,
`⟪eₖ, f⟫ = eₖ(1) F(1) - eₖ(0) F(0) - ∫₀¹ eₖ' F = 0` for every `k`, so `f = 0` by completeness of
`cosBasis`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace DataDrivenControl

namespace SineBasis

open CosineBasis

/-! ### The eigenfunctions -/

/-- The Dirichlet frequencies `(n + 1)π` (Lean's mode `n` is the paper's mode `n + 1`). -/
def sinFreq (n : ℕ) : ℝ := ((n : ℝ) + 1) * Real.pi

/-- The Dirichlet eigenfunctions `sₙ(ξ) = √2 sin((n + 1)πξ)`. -/
def sinFun (n : ℕ) (ξ : ℝ) : ℝ := Real.sqrt 2 * Real.sin (sinFreq n * ξ)

/-- `(n + 1)π > 0`. -/
theorem sinFreq_pos (n : ℕ) : 0 < sinFreq n := by unfold sinFreq; positivity

/-- `(n + 1)π ≥ π`. -/
theorem pi_le_sinFreq (n : ℕ) : Real.pi ≤ sinFreq n := by
  unfold sinFreq
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith [Real.pi_pos]

/-- `1 ≤ (n + 1)π`. -/
theorem one_le_sinFreq (n : ℕ) : 1 ≤ sinFreq n :=
  le_trans (by linarith [Real.pi_gt_three]) (pi_le_sinFreq n)

/-- `|((n + 1)π)⁻¹| ≤ 1`. -/
theorem abs_inv_sinFreq_le (n : ℕ) : |(sinFreq n)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.2 (sinFreq_pos n))]
  exact inv_le_one_of_one_le₀ (one_le_sinFreq n)

/-- The cosine eigenfunctions of positive index: `e_{n+1}(ξ) = √2 cos((n + 1)πξ)`. -/
theorem cosFun_succ (n : ℕ) (ξ : ℝ) :
    cosFun (n + 1) ξ = Real.sqrt 2 * Real.cos (sinFreq n * ξ) := by
  rw [cosFun_of_ne_zero n.succ_ne_zero, sinFreq]
  push_cast
  ring_nf

/-- `e_{n+1}' = -(n + 1)π sₙ`. -/
theorem cosDeriv_succ (n : ℕ) (ξ : ℝ) : cosDeriv (n + 1) ξ = -(sinFreq n * sinFun n ξ) := by
  have h : cosNorm (n + 1) = Real.sqrt 2 := by simp [cosNorm]
  rw [cosDeriv, h, sinFun, sinFreq]
  push_cast
  ring_nf

/-- `sₙ' = (n + 1)π e_{n+1}`. -/
theorem hasDerivAt_sinFun (n : ℕ) (ξ : ℝ) :
    HasDerivAt (sinFun n) (sinFreq n * cosFun (n + 1) ξ) ξ := by
  have h := (((hasDerivAt_id' ξ).const_mul (sinFreq n)).sin).const_mul (Real.sqrt 2)
  have e : sinFreq n * cosFun (n + 1) ξ =
      Real.sqrt 2 * (Real.cos (sinFreq n * ξ) * (sinFreq n * 1)) := by
    rw [cosFun_succ]; ring
  rw [e]; exact h

/-- `e_{n+1}' = -(n + 1)π sₙ`, as a derivative. -/
theorem hasDerivAt_cosFun_succ (n : ℕ) (ξ : ℝ) :
    HasDerivAt (cosFun (n + 1)) (-(sinFreq n * sinFun n ξ)) ξ := by
  rw [← cosDeriv_succ]; exact hasDerivAt_cosFun (n + 1) ξ

/-- `sₙ` is continuous. -/
theorem continuous_sinFun (n : ℕ) : Continuous (sinFun n) := by
  unfold sinFun; fun_prop

/-- The Dirichlet condition at `0`: `sₙ(0) = 0`. -/
@[simp] theorem sinFun_zero (n : ℕ) : sinFun n 0 = 0 := by simp [sinFun]

/-- The Dirichlet condition at `1`: `sₙ(1) = 0`. -/
@[simp] theorem sinFun_one (n : ℕ) : sinFun n 1 = 0 := by
  have h : sinFreq n * 1 = ((n + 1 : ℕ) : ℝ) * Real.pi := by rw [sinFreq]; push_cast; ring
  rw [sinFun, h, Real.sin_nat_mul_pi, mul_zero]

/-- `e_{n+1}(0) = √2`. -/
theorem cosFun_succ_zero (n : ℕ) : cosFun (n + 1) 0 = Real.sqrt 2 := by
  simp [cosFun_succ]

/-- `|sₙ(ξ)| ≤ √2`. -/
theorem abs_sinFun_le (n : ℕ) (ξ : ℝ) : |sinFun n ξ| ≤ Real.sqrt 2 := by
  rw [sinFun, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  calc Real.sqrt 2 * |Real.sin (sinFreq n * ξ)| ≤ Real.sqrt 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 := mul_one _

/-! ### Orthonormality -/

/-- `∫₀¹ sₘ sₙ = [m = n]`. -/
theorem integral_sinFun_mul_sinFun (m n : ℕ) :
    ∫ ξ in (0 : ℝ)..1, sinFun m ξ * sinFun n ξ = if m = n then 1 else 0 := by
  set k₁ : ℤ := ((m + n + 2 : ℕ) : ℤ) with hk₁
  set k₂ : ℤ := (m : ℤ) - (n : ℤ) with hk₂
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hprod : ∀ ξ : ℝ, sinFun m ξ * sinFun n ξ =
      Real.cos ((k₂ : ℝ) * Real.pi * ξ) - Real.cos ((k₁ : ℝ) * Real.pi * ξ) := by
    intro ξ
    have h1 : (k₁ : ℝ) * Real.pi * ξ = sinFreq m * ξ + sinFreq n * ξ := by
      rw [hk₁, sinFreq, sinFreq]; push_cast; ring
    have h2 : (k₂ : ℝ) * Real.pi * ξ = sinFreq m * ξ - sinFreq n * ξ := by
      rw [hk₂, sinFreq, sinFreq]; push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub, sinFun, sinFun]
    linear_combination (Real.sin (sinFreq m * ξ) * Real.sin (sinFreq n * ξ)) * hsq
  simp_rw [hprod]
  have i1 : IntervalIntegrable (fun ξ : ℝ => Real.cos ((k₁ : ℝ) * Real.pi * ξ)) volume 0 1 :=
    (by fun_prop : Continuous fun ξ : ℝ => Real.cos ((k₁ : ℝ) * Real.pi * ξ)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun ξ : ℝ => Real.cos ((k₂ : ℝ) * Real.pi * ξ)) volume 0 1 :=
    (by fun_prop : Continuous fun ξ : ℝ => Real.cos ((k₂ : ℝ) * Real.pi * ξ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i2 i1, integral_cos_int_mul_pi, integral_cos_int_mul_pi]
  have h1 : k₁ ≠ 0 := by rw [hk₁]; exact_mod_cast (by omega : m + n + 2 ≠ 0)
  by_cases hmn : m = n
  · subst hmn; simp [hk₂, h1]
  · have h2 : k₂ ≠ 0 := by rw [hk₂]; exact sub_ne_zero.2 (by exact_mod_cast hmn)
    simp [h1, h2, hmn]

/-- `sₙ` as a bounded continuous function on `ℝ`. -/
def sinBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (sinFun n) (continuous_sinFun n) (Real.sqrt 2)
    fun ξ => by rw [Real.norm_eq_abs]; exact abs_sinFun_le n ξ

/-- `sinBCF n` is `sₙ`. -/
@[simp] theorem sinBCF_apply (n : ℕ) (ξ : ℝ) : sinBCF n ξ = sinFun n ξ := rfl

/-- The class of `sₙ` in `L²(0, 1)`. -/
def sinL2 (n : ℕ) : L2 ℝ 1 := toL2 (sinBCF n)

/-- The classes of the `sₙ` are orthonormal in `L²(0, 1)`. -/
theorem orthonormal_sinL2 : Orthonormal ℝ sinL2 := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [sinL2, sinL2, inner_toL2]
  exact integral_sinFun_mul_sinFun m n

/-! ### Integration by parts and primitives -/

/-- Integration by parts against a `C¹` function `a`:
`∫₀¹ a g = a(1) x(1) - a(0) x(0) - ∫₀¹ a' x` for `x ∈ H¹(0, 1)` with weak derivative `g`. -/
theorem integral_mul_deriv {x g a a' : ℝ → ℝ} (hx : HasWeakDeriv 1 x g)
    (ha : ∀ t, HasDerivAt a (a' t) t) (ha' : Continuous a') :
    ∫ t in (0 : ℝ)..1, a t * g t = a 1 * x 1 - a 0 * x 0 - ∫ t in (0 : ℝ)..1, a' t * x t := by
  have h := (hx.smul ha ha').eq_add_integral 1 ⟨zero_le_one, le_rfl⟩
  simp only [smul_eq_mul] at h
  have hac : Continuous a := continuous_iff_continuousAt.2 fun t => (ha t).continuousAt
  have i1 : IntervalIntegrable (fun t => a' t * x t) volume 0 1 :=
    (ha'.continuousOn.mul hx.continuousOn).intervalIntegrable_of_Icc zero_le_one
  have i2 : IntervalIntegrable (fun t => a t * g t) volume 0 1 :=
    (hx.intervalIntegrable_deriv ⟨zero_le_one, le_rfl⟩).continuousOn_mul hac.continuousOn
  rw [intervalIntegral.integral_add i1 i2] at h
  linarith

/-- Representatives agree on `(0, t]` for `t ≤ 1`. -/
theorem intervalIntegral_congr_of_ae_eq {f g : ℝ → ℝ} (h : f =ᵐ[μI 1] g) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ∫ s in (0 : ℝ)..t, f s = ∫ s in (0 : ℝ)..t, g s := by
  refine intervalIntegral.integral_congr_ae ?_
  have h' : ∀ᵐ s, s ∈ Ioc (0 : ℝ) 1 → f s = g s := (ae_restrict_iff' measurableSet_Ioc).1 h
  filter_upwards [h'] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  exact hs (Ioc_subset_Ioc_right ht.2 hsI)

/-- `∫₀¹ sₙ g = -(n + 1)π ∫₀¹ e_{n+1} x` for `x ∈ H¹(0, 1)` with weak derivative `g` (no boundary
conditions on `x`: `sₙ(0) = sₙ(1) = 0`). -/
theorem integral_sinFun_mul_deriv {x g : ℝ → ℝ} (hx : HasWeakDeriv 1 x g) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, sinFun n t * g t =
      -(sinFreq n * ∫ t in (0 : ℝ)..1, cosFun (n + 1) t * x t) := by
  rw [integral_mul_deriv hx (hasDerivAt_sinFun n)
    ((continuous_cosFun (n + 1)).const_mul (sinFreq n)), sinFun_one, sinFun_zero, zero_mul,
    zero_mul, sub_zero, zero_sub, ← intervalIntegral.integral_const_mul]
  simp only [mul_assoc]

/-- `∫₀¹ e_{n+1} g = (n + 1)π ∫₀¹ sₙ x` for `x ∈ H¹(0, 1)` with weak derivative `g` and
`x(0) = x(1) = 0`. -/
theorem integral_cosFun_succ_mul_deriv {x g : ℝ → ℝ} (hx : HasWeakDeriv 1 x g) (h0 : x 0 = 0)
    (h1 : x 1 = 0) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, cosFun (n + 1) t * g t =
      sinFreq n * ∫ t in (0 : ℝ)..1, sinFun n t * x t := by
  rw [integral_mul_deriv hx (hasDerivAt_cosFun_succ n)
    (((continuous_sinFun n).const_mul (sinFreq n)).neg), h0, h1, mul_zero, mul_zero, sub_zero,
    zero_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  congr 1; funext t; ring

/-- The primitive `ξ ↦ ∫₀^ξ f`. -/
def prim (f : ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ t in (0 : ℝ)..ξ, f t

/-- `prim f (0) = 0`. -/
@[simp] theorem prim_zero (f : ℝ → ℝ) : prim f 0 = 0 := by simp [prim]

/-- The primitive of `f ∈ L²(0, 1)` is in `H¹(0, 1)` with weak derivative `f`. -/
theorem hasWeakDeriv_prim {f : ℝ → ℝ} (hf : MemLp f 2 (μI 1)) : HasWeakDeriv 1 (prim f) f :=
  ⟨hf, fun t _ => by simp [prim]⟩

/-- Primitives of representatives of the same class agree on `[0, 1]`. -/
theorem prim_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[μI 1] g) : EqOn (prim f) (prim g) (Icc 0 1) :=
  fun _ ht => intervalIntegral_congr_of_ae_eq h ht

/-! ### Completeness -/

/-- A vector is determined by its coordinates in a real Hilbert basis. -/
theorem basis_ext {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : HilbertBasis ι ℝ E) {x y : E} (h : ∀ n, ⟪e n, x⟫_ℝ = ⟪e n, y⟫_ℝ) : x = y :=
  e.repr.injective (lp.ext (funext fun n => by rw [e.repr_apply_apply, e.repr_apply_apply, h]))

/-- A class orthogonal to every `e_{n+1}` is the constant `⟪e₀, x⟫` (completeness of the cosine
basis). -/
theorem eq_smul_cosBasis_zero {x : L2 ℝ 1} (hx : ∀ n, ⟪cosBasis (n + 1), x⟫_ℝ = 0) :
    x = ⟪cosBasis 0, x⟫_ℝ • cosBasis 0 := by
  refine basis_ext cosBasis fun k => ?_
  rw [real_inner_smul_right]
  rcases k with _ | n
  · rw [real_inner_self_eq_norm_sq, cosBasis.orthonormal.1 0, one_pow, mul_one]
  · rw [hx n, orthonormal_iff_ite.1 cosBasis.orthonormal]
    simp

/-- A class orthogonal to every `e_{n+1}` is a.e. the constant `⟪e₀, x⟫`. -/
theorem ae_eq_const_of_inner_cosBasis_succ {x : L2 ℝ 1}
    (hx : ∀ n, ⟪cosBasis (n + 1), x⟫_ℝ = 0) :
    (x : ℝ → ℝ) =ᵐ[μI 1] fun _ => ⟪cosBasis 0, x⟫_ℝ := by
  have h := eq_smul_cosBasis_zero hx
  have h2 := Lp.coeFn_smul ⟪cosBasis 0, x⟫_ℝ (cosBasis 0)
  rw [← h] at h2
  filter_upwards [h2, coeFn_cosBasis 0] with ξ h3 h4
  rw [h3, Pi.smul_apply, h4, cosFun_zero, smul_eq_mul, mul_one]

/-- The span of the `sₙ` has trivial orthogonal complement. -/
theorem orthogonal_span_sinL2 : (Submodule.span ℝ (range sinL2))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  have hf' : ∀ n, ⟪sinL2 n, f⟫_ℝ = 0 := fun n =>
    (Submodule.mem_orthogonal _ _).1 hf _ (Submodule.subset_span ⟨n, rfl⟩)
  have hF := hasWeakDeriv_prim (Lp.memLp f)
  set Fc : L2 ℝ 1 := hF.memLp.toLp (prim f) with hFc
  -- `[F] ⊥ e_{n+1}`
  have h1 : ∀ n, ⟪cosBasis (n + 1), Fc⟫_ℝ = 0 := fun n => by
    have h := integral_sinFun_mul_deriv hF n
    have hs : ∫ t in (0 : ℝ)..1, sinFun n t * f t = ⟪sinL2 n, f⟫_ℝ := by
      rw [sinL2, real_inner_comm, inner_eq_integral,
        intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_toL2 (sinBCF n)] with t ht
      rw [ht, sinBCF_apply, mul_comm]
    rw [hs, hf' n] at h
    rw [inner_cosBasis_toLp]
    exact (mul_eq_zero.1 (neg_eq_zero.1 h.symm)).resolve_left (sinFreq_pos n).ne'
  -- `F` is constant, hence `0`, on `[0, 1]`
  have h3 : EqOn (prim f) (fun _ => ⟪cosBasis 0, Fc⟫_ℝ) (Icc 0 1) :=
    eqOn_Icc_of_ae_eq hF.continuousOn continuousOn_const
      (hF.memLp.coeFn_toLp.symm.trans (ae_eq_const_of_inner_cosBasis_succ h1))
  have h4 : ∀ ξ ∈ Icc (0 : ℝ) 1, prim f ξ = 0 := fun ξ hξ => by
    rw [h3 hξ, ← h3 ⟨le_rfl, zero_le_one⟩, prim_zero]
  -- `⟪eₖ, f⟫ = 0`
  refine basis_ext cosBasis fun k => ?_
  rw [inner_zero_right, inner_cosBasis,
    integral_mul_deriv hF (hasDerivAt_cosFun k) (continuous_cosDeriv k),
    h4 1 ⟨zero_le_one, le_rfl⟩, h4 0 ⟨le_rfl, zero_le_one⟩, mul_zero, mul_zero, sub_zero,
    zero_sub, neg_eq_zero]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [h4 t ht, mul_zero]]
  simp

/-- **The sine basis of `L²(0, 1)`**: `sₙ(ξ) = √2 sin((n + 1)πξ)`, the normalised eigenfunctions
of the Dirichlet Laplacian (`ex:intro-wave`). -/
def sinBasis : HilbertBasis ℕ ℝ (L2 ℝ 1) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_sinL2 orthogonal_span_sinL2

/-- The `n`-th vector of the sine basis is the class of `sₙ`. -/
theorem sinBasis_apply (n : ℕ) : sinBasis n = sinL2 n := by
  rw [sinBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- `sinBasis n` is the class of `sₙ`. -/
theorem coeFn_sinBasis (n : ℕ) : (sinBasis n : ℝ → ℝ) =ᵐ[μI 1] sinFun n := by
  rw [sinBasis_apply]; exact coeFn_toL2 _

/-- The coordinates in the sine basis: `⟪sₙ, f⟫ = ∫₀¹ sₙ f`. -/
theorem inner_sinBasis (n : ℕ) (f : L2 ℝ 1) :
    ⟪sinBasis n, f⟫_ℝ = ∫ ξ in (0 : ℝ)..1, sinFun n ξ * f ξ := by
  rw [inner_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sinBasis n] with ξ h
  rw [h]

/-- The coordinates of a class with representative `f`: `⟪sₙ, x⟫ = ∫₀¹ sₙ f`. -/
theorem inner_sinBasis_of_ae_eq {x : L2 ℝ 1} {f : ℝ → ℝ} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] f)
    (n : ℕ) : ⟪sinBasis n, x⟫_ℝ = ∫ ξ in (0 : ℝ)..1, sinFun n ξ * f ξ := by
  rw [inner_sinBasis, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [hx] with ξ h
  rw [h]

/-- The cosine coordinates of a class with representative `f`: `⟪eₙ, x⟫ = ∫₀¹ eₙ f`. -/
theorem inner_cosBasis_of_ae_eq {x : L2 ℝ 1} {f : ℝ → ℝ} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] f)
    (n : ℕ) : ⟪cosBasis n, x⟫_ℝ = ∫ ξ in (0 : ℝ)..1, cosFun n ξ * f ξ := by
  rw [inner_cosBasis, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [hx] with ξ h
  rw [h]

/-- `∑ₙ (aₙ / ((n + 1)π))` converges absolutely when `∑ aₙ² < ∞` (Cauchy–Schwarz against
`∑ 1/n²`). -/
theorem summable_abs_div_sinFreq {a : ℕ → ℝ} (ha : Summable fun n => a n ^ 2) :
    Summable fun n => |a n / sinFreq n| := by
  have hs : Summable fun n : ℕ => (sinFreq n ^ 2)⁻¹ := by
    have h := ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left
      ((Real.pi ^ 2)⁻¹)
    refine h.congr fun n => ?_
    rw [sinFreq]; push_cast; rw [mul_pow, mul_inv]; ring
  refine (ha.add hs).of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
  have hp := sinFreq_pos n
  rw [abs_div, abs_of_pos hp, div_eq_mul_inv]
  have h1 : 0 ≤ (|a n| - (sinFreq n)⁻¹) ^ 2 := sq_nonneg _
  have h2 : (sinFreq n ^ 2)⁻¹ = ((sinFreq n)⁻¹) ^ 2 := (inv_pow _ _).symm
  rw [h2, ← sq_abs (a n)]
  nlinarith [abs_nonneg (a n), inv_pos.2 hp]

end SineBasis

end DataDrivenControl
