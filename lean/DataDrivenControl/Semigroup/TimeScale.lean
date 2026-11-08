module

public import DataDrivenControl.Semigroup.Analytic
public import DataDrivenControl.Analysis.Complexification

/-!
# Time rescaling of C₀-semigroups

For `ν > 0`, `t ↦ S(ν t)` is a C₀-semigroup whose generator is `ν A`, with the domain of `A`.
This is how a diffusivity `ν` enters `ex:intro-pde` (`∂ₜx = ν ∂_ξξ x`): the semigroup is the
one of `∂ₜx = ∂_ξξ x` in the time `ν t`.

## Main declarations

* `C0Semigroup.timeScale S ν`: `t ↦ S(ν t)` (`timeScale_real`; the trivial semigroup for
  `ν ≤ 0`), `Consistent.timeScale`, `norm_timeScale_le` (`M e^{ω t}` becomes `M e^{ν ω t}`).
* `generator_timeScale`: the generator is `ν • A` (`mem_generator_domain_timeScale`: the same
  domain; `generator_timeScale_apply`).
* `IsAnalytic.timeScale`: analyticity is preserved.
* Scalar multiples of a partially defined operator `A`, `c ≠ 0`: `mem_resolventSet_smul_iff`
  (`μ ∈ ρ(c A) ↔ μ / c ∈ ρ(A)`), `resolvent_smul`, `LinearPMap.complexify_smul`
  (`(c A)_ℂ = c A_ℂ`) and `LinearPMap.adjoint_smul` (`(c A)† = c A†`, real `c`).
-/

@[expose] public section

open Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

/-! ### Scalar multiples of a partially defined operator -/

section Smul

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {c μ : 𝕜}

/-- If `R = (μ/c - A)⁻¹`, then `c⁻¹ R = (μ - c A)⁻¹`. -/
theorem IsResolvent.smul (hc : c ≠ 0) {R : E →L[𝕜] E} (h : IsResolvent A (μ / c) R) :
    IsResolvent (c • A) μ (c⁻¹ • R) := by
  refine ⟨fun y => ?_, fun x => ?_⟩
  · obtain ⟨hy, e⟩ := h.1 y
    refine ⟨A.domain.smul_mem c⁻¹ hy, ?_⟩
    show μ • c⁻¹ • R y - c • A (c⁻¹ • ⟨R y, hy⟩) = y
    rw [A.map_smul, smul_smul c c⁻¹, mul_inv_cancel₀ hc, one_smul, smul_smul, ← div_eq_mul_inv]
    exact e
  · have hx : μ • (x : E) - (c • A) x = c • ((μ / c) • (x : E) - A x) := by
      rw [LinearPMap.smul_apply, smul_sub, smul_smul, mul_div_cancel₀ _ hc]
    rw [smul_apply, hx, map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact h.2 x

theorem mem_resolventSet_smul (hc : c ≠ 0) (h : μ / c ∈ resolventSet A) :
    μ ∈ resolventSet (c • A) :=
  let ⟨R, hR⟩ := h
  ⟨c⁻¹ • R, hR.smul hc⟩

/-- `μ ∈ ρ(c A) ↔ μ / c ∈ ρ(A)` for `c ≠ 0`. -/
theorem mem_resolventSet_smul_iff (hc : c ≠ 0) :
    μ ∈ resolventSet (c • A) ↔ μ / c ∈ resolventSet A := by
  refine ⟨fun h => ?_, mem_resolventSet_smul hc⟩
  have := mem_resolventSet_smul (A := c • A) (μ := μ / c) (inv_ne_zero hc)
    (by rwa [div_inv_eq_mul, div_mul_cancel₀ _ hc])
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- `(μ - c A)⁻¹ = c⁻¹ (μ/c - A)⁻¹`. -/
theorem resolvent_smul (hc : c ≠ 0) (h : μ / c ∈ resolventSet A) :
    resolvent (c • A) μ = c⁻¹ • resolvent A (μ / c) :=
  (isResolvent_resolvent (mem_resolventSet_smul hc h)).unique ((isResolvent_resolvent h).smul hc)

end Smul

end DataDrivenControl

open DataDrivenControl (Complexification)

namespace LinearPMap

/-- `(c A)_ℂ = c A_ℂ` for real `c`. -/
theorem complexify_smul {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
    [Module ℝ Y] (c : ℝ) (A : X →ₗ.[ℝ] Y) : (c • A).complexify = (c : ℂ) • A.complexify :=
  ext rfl fun z _ _ => by
    ext <;> simp only [smul_apply, complexify_apply_re, complexify_apply_im,
      Complexification.smul_re, Complexification.smul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_smul, sub_zero, add_zero]

/-- `(c A)† = c A†` for real `c ≠ 0`. -/
theorem adjoint_smul {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] {c : ℝ} (hc : c ≠ 0)
    (A : X →ₗ.[ℝ] Y) : (c • A).adjoint = c • A.adjoint := by
  have hdom : ∀ y : Y, y ∈ (c • A).adjoint.domain ↔ y ∈ A.adjoint.domain := fun y => by
    rw [mem_adjoint_domain_iff, mem_adjoint_domain_iff]
    have : ⇑((innerₛₗ ℝ y).comp (c • A).toFun) = fun x => c • (innerₛₗ ℝ y).comp A.toFun x := by
      funext x; simp [inner_smul_right]
    rw [this]
    exact continuous_const_smul_iff₀ hc
  refine ext (Submodule.ext hdom) fun y hy hy' => ?_
  by_cases hd : Dense (A.domain : Set X)
  · refine adjoint_apply_eq (T := c • A) hd ⟨y, hy⟩ fun x => ?_
    rw [smul_apply, real_inner_smul_left, adjoint_isFormalAdjoint hd ⟨y, hy'⟩ x, smul_apply,
      real_inner_smul_right]
  · rw [adjoint_apply_of_not_dense (T := c • A) hd, smul_apply, adjoint_apply_of_not_dense hd,
      smul_zero]

end LinearPMap

namespace DataDrivenControl

namespace C0Semigroup

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (S : C0Semigroup 𝕜 E) {ν : ℝ}

/-! ### The rescaled semigroup -/

/-- The **time-rescaled semigroup** `t ↦ S(ν t)` (the trivial semigroup for `ν ≤ 0`). -/
def timeScale (ν : ℝ) : C0Semigroup 𝕜 E where
  toFun t := S (ν.toNNReal * t)
  map_zero' := by simp
  map_add' s t := by rw [mul_add, S.map_add]
  continuous_apply' x := (S.continuous_apply x).comp (continuous_const.mul continuous_id)

@[simp] theorem timeScale_apply (t : ℝ≥0) : S.timeScale ν t = S (ν.toNNReal * t) := rfl

theorem timeScale_real (hν : 0 ≤ ν) (t : ℝ) : (S.timeScale ν).real t = S.real (ν * t) := by
  rw [real, real, timeScale_apply, Real.toNNReal_mul hν]

theorem Consistent.timeScale {ι : F →L[𝕜] E} {S₁ : C0Semigroup 𝕜 F} {S₂ : C0Semigroup 𝕜 E}
    (h : Consistent ι S₁ S₂) (ν : ℝ) : Consistent ι (S₁.timeScale ν) (S₂.timeScale ν) :=
  fun _ x => h _ x

/-- A growth bound `‖S t‖ ≤ M e^{ω t}` gives `‖S(ν t)‖ ≤ M e^{ν ω t}`. -/
theorem norm_timeScale_le {M ω : ℝ} (h : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t)) (hν : 0 ≤ ν)
    (t : ℝ≥0) : ‖S.timeScale ν t‖ ≤ M * Real.exp (ν * ω * t) := by
  refine (h (ν.toNNReal * t)).trans_eq ?_
  push_cast [Real.coe_toNNReal _ hν]
  ring_nf

/-! ### The generator -/

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [IsScalarTower ℝ 𝕜 E] in
theorem diffQuot_timeScale (hν : 0 < ν) (x : E) (h : ℝ) :
    (S.timeScale ν).diffQuot x h = ν • S.diffQuot x (ν * h) := by
  rw [diffQuot, diffQuot, timeScale_real S hν.le, smul_smul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hν.ne', one_mul]

private theorem tendsto_mul_nhdsGT (hν : 0 < ν) :
    Tendsto (fun h : ℝ => ν * h) (𝓝[>] 0) (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2
    ⟨((continuous_const.mul continuous_id).tendsto' 0 0 (mul_zero ν)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun _ h => mul_pos hν h⟩

/-- The rescaled generator has the domain of `A`. -/
theorem mem_generator_domain_timeScale (hν : 0 < ν) {x : E} :
    x ∈ (S.timeScale ν).generator.domain ↔ x ∈ S.generator.domain := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨ν⁻¹ • y, ((hy.comp (tendsto_mul_nhdsGT (inv_pos.2 hν))).const_smul ν⁻¹).congr
      fun h => ?_⟩
    rw [Function.comp_apply, diffQuot_timeScale S hν, smul_smul, inv_mul_cancel₀ hν.ne',
      one_smul, mul_inv_cancel_left₀ hν.ne']
  · rintro ⟨y, hy⟩
    exact ⟨ν • y, ((hy.comp (tendsto_mul_nhdsGT hν)).const_smul ν).congr
      fun h => (S.diffQuot_timeScale hν x h).symm⟩

/-- The rescaled generator is `ν A`. -/
theorem generator_timeScale_apply (hν : 0 < ν) (x : (S.timeScale ν).generator.domain) :
    (S.timeScale ν).generator x =
      ν • S.generator ⟨x, (S.mem_generator_domain_timeScale hν).1 x.2⟩ :=
  (S.timeScale ν).generator_apply_eq x.2 ((((S.tendsto_generator _).comp
    (tendsto_mul_nhdsGT hν)).const_smul ν).congr fun h => (S.diffQuot_timeScale hν x h).symm)

/-- **The generator of `t ↦ S(ν t)` is `ν A`**, with the domain of `A`. -/
theorem generator_timeScale (hν : 0 < ν) : (S.timeScale ν).generator = ν • S.generator :=
  LinearPMap.ext (Submodule.ext fun _ => S.mem_generator_domain_timeScale hν) fun _ _ _ =>
    S.generator_timeScale_apply hν _

/-- **Analyticity is preserved**: `‖ν A S(ν t)‖ ≤ K/t` on `(0, 1]`, from `‖A S(s)‖ ≤ C/s` on
`(0, 1]` and `A S(s) = A S(1) S(s - 1)` on `[1, ν]`. -/
theorem IsAnalytic.timeScale [CompleteSpace E] {S : C0Semigroup 𝕜 E} (hS : S.IsAnalytic)
    (hν : 0 < ν) : (S.timeScale ν).IsAnalytic := by
  obtain ⟨C, hC0, hC⟩ := hS.norm_gen_le_of_le_one
  obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le ν
  have key : ∀ s, 0 < s → s ≤ ν → ‖hS.gen s‖ ≤ C * (1 + M * ν) / s := by
    intro s hs hsν
    rcases le_total s 1 with h1 | h1
    · exact (hC s hs h1).trans (div_le_div_of_nonneg_right
        (le_mul_of_one_le_right hC0 (by nlinarith)) hs.le)
    · have e : hS.gen s = (hS.gen 1).comp (S.real (s - 1)) := by
        ext x
        rw [ContinuousLinearMap.comp_apply, ← hS.gen_add_apply one_pos (by linarith),
          add_sub_cancel]
      rw [e, le_div_iff₀ hs]
      calc ‖(hS.gen 1).comp (S.real (s - 1))‖ * s ≤ C / 1 * M * ν :=
            mul_le_mul ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
              (hC 1 one_pos le_rfl) (hM _ (by linarith)) (norm_nonneg _) (by positivity)))
              hsν hs.le (by positivity)
        _ ≤ C * (1 + M * ν) := by rw [div_one]; nlinarith
  refine ⟨C * (1 + M * ν), fun t ht ht1 x => ⟨(S.mem_generator_domain_timeScale hν).2 ?_, ?_⟩⟩
  · rw [timeScale_real S hν.le]; exact hS.mem_generator_domain (mul_pos hν ht) x
  · rw [S.generator_timeScale_apply hν, norm_smul, Real.norm_of_nonneg hν.le]
    have e : S.generator ⟨(S.timeScale ν).real t x, (S.mem_generator_domain_timeScale hν).1
        ((S.mem_generator_domain_timeScale hν).2 (by
          rw [timeScale_real S hν.le]; exact hS.mem_generator_domain (mul_pos hν ht) x))⟩ =
        hS.gen (ν * t) x := by
      rw [hS.gen_apply (mul_pos hν ht)]
      congr 2
      exact S.timeScale_real hν.le t ▸ rfl
    rw [e]
    calc ν * ‖hS.gen (ν * t) x‖ ≤ ν * (C * (1 + M * ν) / (ν * t) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (((hS.gen _).le_opNorm x).trans (mul_le_mul_of_nonneg_right
            (key _ (mul_pos hν ht) (mul_le_of_le_one_right hν.le ht1)) (norm_nonneg _))) hν.le
      _ = C * (1 + M * ν) / t * ‖x‖ := by field_simp

end C0Semigroup

end DataDrivenControl
