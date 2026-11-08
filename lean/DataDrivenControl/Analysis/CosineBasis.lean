module

public import Mathlib
public import DataDrivenControl.Signal.Basic

/-!
# The cosine basis of `L²(0, 1)`

Paper: `ex:intro-pde` (`introduction.tex`), `ex:boundary-heat-informative`
(`informativity.tex`), `app:boundary-heat-informative` (`appendix_proofs.tex`): the Neumann
eigenfunctions `e₀ = 1`, `eₙ(ξ) = √2 cos(nπξ)` of `∂_ξξ` on `(0, 1)`, with eigenvalues
`λₙ = -(nπ)²`, form a Hilbert basis of `L²(0, 1)`.

`L²(0, 1)` is the project's `L2 ℝ 1 = Lp ℝ 2 (μI 1)`, `μI 1 = volume.restrict (Ioc 0 1)`.

## Main declarations

* `cosFun n` (`eₙ`), `cosDeriv n` (`eₙ'`), `cosEig n` (`λₙ`): `hasDerivAt_cosFun`,
  `hasDerivAt_cosDeriv` (`eₙ'' = λₙ eₙ`), `cosDeriv_zero`, `cosDeriv_one` (Neumann conditions),
  `abs_cosFun_le`, `abs_cosDeriv_le`;
* `integral_cosFun_mul_cosFun`: `∫₀¹ eₘ eₙ = [m = n]`;
* **`cosBasis : HilbertBasis ℕ ℝ (L2 ℝ 1)`** with `cosBasis n = [eₙ]` (`cosBasis_apply`,
  `coeFn_cosBasis`); `inner_cosBasis`, `inner_cosBasis_toLp`: `⟪eₙ, f⟫ = ∫₀¹ eₙ f`;
* `cosSeries a : ℝ →ᵇ ℝ`, `ξ ↦ ∑ₙ aₙ eₙ(ξ)` for `∑ |aₙ| < ∞` (`hasSum_cosSeries_apply`), whose
  class is `∑ₙ aₙ eₙ` (`hasSum_cosBasis_cosSeries`, `toL2_cosSeries`);
* `hasSum_cosFun_mul_inner`: **point evaluation**: if `∑ₙ |⟪eₙ, x⟫| < ∞` and `f` is a
  representative of `x` continuous on `[0, 1]`, then `∑ₙ eₙ(ξ) ⟪eₙ, x⟫ = f(ξ)` for every
  `ξ ∈ [0, 1]`;
* `summable_succ_mul_abs`, `summable_abs_of_summable_sq`: `∑ₙ (λₙ aₙ)² < ∞ ⇒
  ∑ₙ (n + 1) |aₙ| < ∞` (Cauchy–Schwarz against `∑ 1/n²`); then `hasDerivAt_tsum_cosFun`,
  `continuous_tsum_cosDeriv`: the cosine series may be differentiated termwise.

## Auxiliary results

* `toL2`: the class map `(ℝ →ᵇ ℝ) →L[ℝ] L2 ℝ 1` (`BoundedContinuousFunction.toLp`),
  `toL2_eq_of_eqOn`, `inner_eq_integral` (`⟪f, g⟫ = ∫₀¹ f g`), `eqOn_Icc_of_ae_eq` (continuous
  representatives are unique on `[0, 1]`).

## Proof of completeness

The span of the cosines `cos(nπξ)` is closed under multiplication
(`cos a cos b = (cos(a + b) + cos(a - b)) / 2`) and contains `1`, so it is a subalgebra of
`C([0, 1], ℝ)`.  It separates points (`cos(πξ)` is injective on `[0, 1]`), so it is dense
(Stone–Weierstrass).  Precomposition with the projection `ℝ → [0, 1]` followed by
`BoundedContinuousFunction.toLp` maps it into the span of the `eₙ` in `L²(0, 1)`, and bounded
continuous functions are dense in `L²(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace DataDrivenControl

namespace CosineBasis

/-! ### The eigenfunctions -/

/-- The normalising constants: `1` for `n = 0`, `√2` for `n ≥ 1`. -/
def cosNorm (n : ℕ) : ℝ := if n = 0 then 1 else Real.sqrt 2

/-- The Neumann eigenfunctions `e₀ = 1`, `eₙ(ξ) = √2 cos(nπξ)` (`n ≥ 1`). -/
def cosFun (n : ℕ) (ξ : ℝ) : ℝ := cosNorm n * Real.cos (n * Real.pi * ξ)

/-- Their derivatives `eₙ'(ξ) = -√2 nπ sin(nπξ)` (`e₀' = 0`). -/
def cosDeriv (n : ℕ) (ξ : ℝ) : ℝ := -(cosNorm n * (n * Real.pi) * Real.sin (n * Real.pi * ξ))

/-- The Neumann eigenvalues `λₙ = -(nπ)²`. -/
def cosEig (n : ℕ) : ℝ := -((n : ℝ) * Real.pi) ^ 2

/-- `cosNorm n > 0`. -/
theorem cosNorm_pos (n : ℕ) : 0 < cosNorm n := by
  unfold cosNorm; split_ifs <;> positivity

/-- `cosNorm n ≤ √2`. -/
theorem cosNorm_le (n : ℕ) : cosNorm n ≤ Real.sqrt 2 := by
  unfold cosNorm
  split_ifs
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · exact le_rfl

/-- `e₀ = 1`. -/
@[simp] theorem cosFun_zero (ξ : ℝ) : cosFun 0 ξ = 1 := by simp [cosFun, cosNorm]

/-- `eₙ(ξ) = √2 cos(nπξ)` for `n ≥ 1`. -/
theorem cosFun_of_ne_zero {n : ℕ} (hn : n ≠ 0) (ξ : ℝ) :
    cosFun n ξ = Real.sqrt 2 * Real.cos (n * Real.pi * ξ) := by
  simp [cosFun, cosNorm, hn]

/-- `eₙ(0) = cosNorm n`. -/
theorem cosFun_apply_zero (n : ℕ) : cosFun n 0 = cosNorm n := by simp [cosFun]

/-- `eₙ` is continuous. -/
theorem continuous_cosFun (n : ℕ) : Continuous (cosFun n) := by
  unfold cosFun; fun_prop

/-- `eₙ'` is continuous. -/
theorem continuous_cosDeriv (n : ℕ) : Continuous (cosDeriv n) := by
  unfold cosDeriv; fun_prop

/-- `eₙ' ` is the derivative of `eₙ`. -/
theorem hasDerivAt_cosFun (n : ℕ) (ξ : ℝ) : HasDerivAt (cosFun n) (cosDeriv n ξ) ξ := by
  have h := (((hasDerivAt_id' ξ).const_mul ((n : ℝ) * Real.pi)).cos).const_mul (cosNorm n)
  have e : cosDeriv n ξ =
      cosNorm n * (-Real.sin (n * Real.pi * ξ) * (n * Real.pi * 1)) := by
    unfold cosDeriv; ring
  rw [e]; exact h

/-- `eₙ'' = λₙ eₙ`. -/
theorem hasDerivAt_cosDeriv (n : ℕ) (ξ : ℝ) :
    HasDerivAt (cosDeriv n) (cosEig n * cosFun n ξ) ξ := by
  have h := ((((hasDerivAt_id' ξ).const_mul ((n : ℝ) * Real.pi)).sin).const_mul
    (cosNorm n * (n * Real.pi))).neg
  have e : cosEig n * cosFun n ξ =
      -(cosNorm n * (n * Real.pi) * (Real.cos (n * Real.pi * ξ) * (n * Real.pi * 1))) := by
    unfold cosEig cosFun; ring
  rw [e]; exact h

/-- The Neumann condition at `0`: `eₙ'(0) = 0`. -/
@[simp] theorem cosDeriv_zero (n : ℕ) : cosDeriv n 0 = 0 := by simp [cosDeriv]

/-- The Neumann condition at `1`: `eₙ'(1) = 0`. -/
@[simp] theorem cosDeriv_one (n : ℕ) : cosDeriv n 1 = 0 := by
  simp [cosDeriv, Real.sin_nat_mul_pi]

/-- `|eₙ(ξ)| ≤ √2`. -/
theorem abs_cosFun_le (n : ℕ) (ξ : ℝ) : |cosFun n ξ| ≤ Real.sqrt 2 := by
  rw [cosFun, abs_mul, abs_of_pos (cosNorm_pos n)]
  calc cosNorm n * |Real.cos (n * Real.pi * ξ)| ≤ Real.sqrt 2 * 1 :=
        mul_le_mul (cosNorm_le n) (Real.abs_cos_le_one _) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 := mul_one _

/-- `|eₙ'(ξ)| ≤ √2 π n`. -/
theorem abs_cosDeriv_le (n : ℕ) (ξ : ℝ) : |cosDeriv n ξ| ≤ Real.sqrt 2 * Real.pi * n := by
  rw [cosDeriv, abs_neg, abs_mul, abs_mul, abs_of_pos (cosNorm_pos n),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n * Real.pi)]
  calc cosNorm n * (n * Real.pi) * |Real.sin (n * Real.pi * ξ)|
      ≤ Real.sqrt 2 * (n * Real.pi) * 1 := by
        gcongr
        · exact cosNorm_le n
        · exact Real.abs_sin_le_one _
    _ = Real.sqrt 2 * Real.pi * n := by ring

/-! ### Orthonormality -/

/-- `∫₀¹ cos(kπξ) dξ = [k = 0]` for `k ∈ ℤ`. -/
theorem integral_cos_int_mul_pi (k : ℤ) :
    ∫ ξ in (0 : ℝ)..1, Real.cos (k * Real.pi * ξ) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : (k : ℝ) * Real.pi ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) Real.pi_ne_zero
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos,
      mul_one, mul_zero, Real.sin_int_mul_pi, Real.sin_zero, sub_zero, smul_zero]

/-- `∫₀¹ eₘ eₙ = [m = n]`. -/
theorem integral_cosFun_mul_cosFun (m n : ℕ) :
    ∫ ξ in (0 : ℝ)..1, cosFun m ξ * cosFun n ξ = if m = n then 1 else 0 := by
  set k₁ : ℤ := ((m + n : ℕ) : ℤ) with hk₁
  set k₂ : ℤ := (m : ℤ) - (n : ℤ) with hk₂
  have hprod : ∀ ξ : ℝ, cosFun m ξ * cosFun n ξ = cosNorm m * cosNorm n / 2 *
      (Real.cos ((k₁ : ℝ) * Real.pi * ξ) + Real.cos ((k₂ : ℝ) * Real.pi * ξ)) := by
    intro ξ
    have h1 : (k₁ : ℝ) * Real.pi * ξ = m * Real.pi * ξ + n * Real.pi * ξ := by
      rw [hk₁]; push_cast; ring
    have h2 : (k₂ : ℝ) * Real.pi * ξ = m * Real.pi * ξ - n * Real.pi * ξ := by
      rw [hk₂]; push_cast; ring
    rw [h1, h2, Real.cos_add, Real.cos_sub, cosFun, cosFun]
    ring
  simp_rw [hprod]
  have i1 : IntervalIntegrable (fun ξ : ℝ => Real.cos ((k₁ : ℝ) * Real.pi * ξ)) volume 0 1 :=
    (by fun_prop : Continuous fun ξ : ℝ => Real.cos ((k₁ : ℝ) * Real.pi * ξ)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun ξ : ℝ => Real.cos ((k₂ : ℝ) * Real.pi * ξ)) volume 0 1 :=
    (by fun_prop : Continuous fun ξ : ℝ => Real.cos ((k₂ : ℝ) * Real.pi * ξ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
    integral_cos_int_mul_pi, integral_cos_int_mul_pi]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hmn : m = n
  · subst hmn
    by_cases hm : m = 0
    · subst hm; simp [cosNorm, hk₁, hk₂]; norm_num
    · have : k₁ ≠ 0 := by rw [hk₁]; exact_mod_cast (by omega : m + m ≠ 0)
      simp [cosNorm, hm, this, hk₂, hsq]
  · have h1 : k₁ ≠ 0 := by rw [hk₁]; exact_mod_cast (by omega : m + n ≠ 0)
    have h2 : k₂ ≠ 0 := by rw [hk₂]; exact sub_ne_zero.2 (by exact_mod_cast hmn)
    simp [h1, h2, hmn]

/-! ### Classes in `L²(0, 1)` -/

/-- `eₙ` as a bounded continuous function on `ℝ`. -/
def cosBCF (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cosFun n) (continuous_cosFun n) (Real.sqrt 2)
    fun ξ => by rw [Real.norm_eq_abs]; exact abs_cosFun_le n ξ

/-- `cosBCF n` is `eₙ`. -/
@[simp] theorem cosBCF_apply (n : ℕ) (ξ : ℝ) : cosBCF n ξ = cosFun n ξ := rfl

/-- `‖eₙ‖_∞ ≤ √2`. -/
theorem norm_cosBCF_le (n : ℕ) : ‖cosBCF n‖ ≤ Real.sqrt 2 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (Real.sqrt_nonneg 2) _

/-- The class in `L²(0, 1)` of a bounded continuous function on `ℝ`. -/
abbrev toL2 : (ℝ →ᵇ ℝ) →L[ℝ] L2 ℝ 1 := BoundedContinuousFunction.toLp 2 (μI 1) ℝ

/-- `toL2 f` is the class of `f`. -/
theorem coeFn_toL2 (f : ℝ →ᵇ ℝ) : (toL2 f : ℝ → ℝ) =ᵐ[μI 1] f :=
  BoundedContinuousFunction.coeFn_toLp 2 (μI 1) ℝ f

/-- Bounded continuous functions that agree on `(0, 1]` have the same class. -/
theorem toL2_eq_of_eqOn {f g : ℝ →ᵇ ℝ} (h : EqOn f g (Ioc 0 1)) : toL2 f = toL2 g :=
  Lp.ext ((coeFn_toL2 f).trans (EventuallyEq.trans
    (ae_restrict_of_forall_mem measurableSet_Ioc h) (coeFn_toL2 g).symm))

/-- The inner product of `L²(0, 1)`: `⟪f, g⟫ = ∫₀¹ f g`. -/
theorem inner_eq_integral (f g : L2 ℝ 1) :
    ⟪f, g⟫_ℝ = ∫ ξ in (0 : ℝ)..1, f ξ * g ξ := by
  rw [MeasureTheory.L2.inner_def, intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- Two functions continuous on `[0, 1]` and a.e. equal on `(0, 1]` agree on `[0, 1]`. -/
theorem eqOn_Icc_of_ae_eq {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (h : f =ᵐ[μI 1] g) : EqOn f g (Icc 0 1) := by
  refine Measure.eqOn_Icc_of_ae_eq volume zero_ne_one ?_ hf hg
  rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- The class of `eₙ` in `L²(0, 1)`. -/
def cosL2 (n : ℕ) : L2 ℝ 1 := toL2 (cosBCF n)

/-- `⟪[f], [g]⟫ = ∫₀¹ f g` for bounded continuous `f`, `g`. -/
theorem inner_toL2 (f g : ℝ →ᵇ ℝ) : ⟪toL2 f, toL2 g⟫_ℝ = ∫ ξ in (0 : ℝ)..1, f ξ * g ξ := by
  rw [inner_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 f, coeFn_toL2 g] with ξ h1 h2
  rw [h1, h2]

/-- The classes of the `eₙ` are orthonormal in `L²(0, 1)`. -/
theorem orthonormal_cosL2 : Orthonormal ℝ cosL2 := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [cosL2, cosL2, inner_toL2]
  exact integral_cosFun_mul_cosFun m n

/-! ### Completeness -/

/-- The unnormalised cosines `cos(nπξ)` on `[0, 1]`. -/
def cosCM (n : ℕ) : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun ξ => Real.cos (n * Real.pi * ξ), by fun_prop⟩

/-- `cos(mπξ) cos(nπξ) = (cos((m + n)πξ) + cos((m - n)πξ)) / 2`. -/
theorem cosCM_mul_mem (m n : ℕ) : cosCM m * cosCM n ∈ Submodule.span ℝ (range cosCM) := by
  have key : ∀ m n : ℕ, n ≤ m →
      cosCM m * cosCM n = (1 / 2 : ℝ) • cosCM (m + n) + (1 / 2 : ℝ) • cosCM (m - n) := by
    intro m n hnm
    ext ξ
    simp only [cosCM, ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.coe_mk, smul_eq_mul]
    rw [Nat.cast_add, Nat.cast_sub hnm]
    have h1 : ((m : ℝ) + n) * Real.pi * ξ = m * Real.pi * ξ + n * Real.pi * ξ := by ring
    have h2 : ((m : ℝ) - n) * Real.pi * ξ = m * Real.pi * ξ - n * Real.pi * ξ := by ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  have mem : ∀ k, cosCM k ∈ Submodule.span ℝ (range cosCM) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  rcases le_total n m with h | h
  · rw [key m n h]
    exact add_mem (Submodule.smul_mem _ _ (mem _)) (Submodule.smul_mem _ _ (mem _))
  · rw [mul_comm, key n m h]
    exact add_mem (Submodule.smul_mem _ _ (mem _)) (Submodule.smul_mem _ _ (mem _))

/-- The span of the cosines is a subalgebra of `C([0, 1], ℝ)`. -/
def cosSubalgebra : Subalgebra ℝ C(Icc (0 : ℝ) 1, ℝ) :=
  (Submodule.span ℝ (range cosCM)).toSubalgebra
    (by
      have h : cosCM 0 = 1 := by ext ξ; simp [cosCM]
      rw [← h]; exact Submodule.subset_span ⟨0, rfl⟩)
    (fun x y hx hy => by
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
      exact cosCM_mul_mem m n)

/-- `cos(πξ)` separates the points of `[0, 1]`. -/
theorem cosSubalgebra_separatesPoints : cosSubalgebra.SeparatesPoints := by
  intro x y hxy
  refine ⟨cosCM 1, ⟨cosCM 1, Submodule.subset_span ⟨1, rfl⟩, rfl⟩, fun h => hxy ?_⟩
  have hx : Real.pi * x ∈ Icc 0 Real.pi :=
    ⟨by have := x.2.1; positivity, by nlinarith [x.2.2, Real.pi_pos]⟩
  have hy : Real.pi * y ∈ Icc 0 Real.pi :=
    ⟨by have := y.2.1; positivity, by nlinarith [y.2.2, Real.pi_pos]⟩
  have h' : Real.cos (Real.pi * x) = Real.cos (Real.pi * y) := by
    simpa [cosCM] using h
  exact Subtype.ext (mul_left_cancel₀ Real.pi_ne_zero (Real.injOn_cos hx hy h'))

/-- The projection `ℝ → [0, 1]`. -/
def projI : C(ℝ, Icc (0 : ℝ) 1) := ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

/-- A continuous function on `[0, 1]`, extended constantly to `ℝ`, as a class in `L²(0, 1)`. -/
def extendL2 : C(Icc (0 : ℝ) 1, ℝ) →L[ℝ] L2 ℝ 1 :=
  toL2.comp ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ projI).comp
    (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) 1) ℝ
      ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

/-- `extendL2 s = [f]` when `f` extends `s`. -/
theorem extendL2_eq_of_eqOn (s : C(Icc (0 : ℝ) 1, ℝ)) (f : ℝ →ᵇ ℝ)
    (h : ∀ ξ (hξ : ξ ∈ Icc (0 : ℝ) 1), s ⟨ξ, hξ⟩ = f ξ) : extendL2 s = toL2 f := by
  refine toL2_eq_of_eqOn fun ξ hξ => ?_
  have hξ' : ξ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hξ
  show s (projIcc 0 1 zero_le_one ξ) = f ξ
  rw [projIcc_of_mem _ hξ']
  exact h ξ hξ'

/-- `extendL2 (cos(nπ·)) = eₙ / cosNorm n`. -/
theorem extendL2_cosCM (n : ℕ) : extendL2 (cosCM n) = (cosNorm n)⁻¹ • cosL2 n := by
  rw [cosL2, ← map_smul]
  refine extendL2_eq_of_eqOn _ _ fun ξ _ => ?_
  simp only [cosCM, ContinuousMap.coe_mk, BoundedContinuousFunction.coe_smul, cosBCF_apply,
    cosFun, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (cosNorm_pos n).ne', one_mul]

/-- The span of the `eₙ` is dense in `L²(0, 1)`. -/
theorem dense_span_cosL2 : ⊤ ≤ (Submodule.span ℝ (range cosL2)).topologicalClosure := by
  set M := (Submodule.span ℝ (range cosL2)).topologicalClosure
  have hM : IsClosed (M : Set (L2 ℝ 1)) := Submodule.isClosed_topologicalClosure _
  have h1 : MapsTo extendL2 (cosSubalgebra : Set C(Icc (0 : ℝ) 1, ℝ)) (M : Set (L2 ℝ 1)) := by
    intro s hs
    have hs' : s ∈ Submodule.span ℝ (range cosCM) := hs
    refine Submodule.le_topologicalClosure _ ?_
    have hmap : Submodule.map (extendL2 : C(Icc (0 : ℝ) 1, ℝ) →ₗ[ℝ] L2 ℝ 1)
        (Submodule.span ℝ (range cosCM)) ≤ Submodule.span ℝ (range cosL2) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨n, rfl⟩
      rw [ContinuousLinearMap.coe_coe, extendL2_cosCM]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
    exact hmap (Submodule.mem_map_of_mem hs')
  have h2 : ∀ s, extendL2 s ∈ M := by
    intro s
    have hs : s ∈ closure (cosSubalgebra : Set C(Icc (0 : ℝ) 1, ℝ)) := by
      rw [← Subalgebra.topologicalClosure_coe,
        ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
          cosSubalgebra_separatesPoints]
      trivial
    exact hM.closure_subset (map_mem_closure extendL2.continuous hs h1)
  have h3 : range toL2 ⊆ (M : Set (L2 ℝ 1)) := by
    rintro _ ⟨g, rfl⟩
    rw [← extendL2_eq_of_eqOn (g.toContinuousMap.restrict (Icc (0 : ℝ) 1)) g fun _ _ => rfl]
    exact h2 _
  intro x _
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ (μI 1) ℝ
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  exact hM.closure_subset_iff.2 h3 (hd x)

/-- **The cosine basis of `L²(0, 1)`**: `e₀ = 1`, `eₙ(ξ) = √2 cos(nπξ)`, the normalised
eigenfunctions of the Neumann Laplacian (`ex:intro-pde`, `app:boundary-heat-informative`). -/
def cosBasis : HilbertBasis ℕ ℝ (L2 ℝ 1) := HilbertBasis.mk orthonormal_cosL2 dense_span_cosL2

/-- The `n`-th vector of the cosine basis is the class of `eₙ`. -/
theorem cosBasis_apply (n : ℕ) : cosBasis n = cosL2 n := by
  rw [cosBasis, HilbertBasis.coe_mk]

/-- `cosBasis n` is the class of `eₙ`. -/
theorem coeFn_cosBasis (n : ℕ) : (cosBasis n : ℝ → ℝ) =ᵐ[μI 1] cosFun n := by
  rw [cosBasis_apply]; exact coeFn_toL2 _

/-- The coordinates in the cosine basis: `⟪eₙ, f⟫ = ∫₀¹ eₙ f`. -/
theorem inner_cosBasis (n : ℕ) (f : L2 ℝ 1) :
    ⟪cosBasis n, f⟫_ℝ = ∫ ξ in (0 : ℝ)..1, cosFun n ξ * f ξ := by
  rw [inner_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cosBasis n] with ξ h
  rw [h]

/-- The coordinates of the class of `f ∈ L²(0, 1)`: `⟪eₙ, [f]⟫ = ∫₀¹ eₙ f`. -/
theorem inner_cosBasis_toLp (n : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 (μI 1)) :
    ⟪cosBasis n, hf.toLp f⟫_ℝ = ∫ ξ in (0 : ℝ)..1, cosFun n ξ * f ξ := by
  rw [inner_cosBasis, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ξ h
  rw [h]

/-! ### Absolutely convergent cosine series -/

/-- `∑ₙ aₙ eₙ` converges in sup norm when `∑ |aₙ| < ∞`. -/
theorem summable_smul_cosBCF {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    Summable fun n => a n • cosBCF n :=
  Summable.of_norm_bounded (ha.mul_right (Real.sqrt 2)) fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_cosBCF_le n) (abs_nonneg _)

/-- The cosine series `ξ ↦ ∑ₙ aₙ eₙ(ξ)` as a bounded continuous function (`∑ |aₙ| < ∞`). -/
def cosSeries (a : ℕ → ℝ) : ℝ →ᵇ ℝ := ∑' n, a n • cosBCF n

/-- The cosine series converges at every point. -/
theorem hasSum_cosSeries_apply {a : ℕ → ℝ} (ha : Summable fun n => |a n|) (ξ : ℝ) :
    HasSum (fun n => a n * cosFun n ξ) (cosSeries a ξ) := by
  simpa [cosSeries] using
    (summable_smul_cosBCF ha).hasSum.mapL (BoundedContinuousFunction.evalCLM ℝ ξ)

/-- The class of the cosine series is the `L²` sum `∑ₙ aₙ eₙ`. -/
theorem hasSum_cosBasis_cosSeries {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    HasSum (fun n => a n • cosBasis n) (toL2 (cosSeries a)) := by
  simpa [cosBasis_apply, cosL2, cosSeries] using (summable_smul_cosBCF ha).hasSum.mapL toL2

/-- If the coordinates of `x` are absolutely summable, `x` is the class of its cosine series. -/
theorem toL2_cosSeries {x : L2 ℝ 1} (hx : Summable fun n => |⟪cosBasis n, x⟫_ℝ|) :
    toL2 (cosSeries fun n => ⟪cosBasis n, x⟫_ℝ) = x := by
  refine (hasSum_cosBasis_cosSeries hx).unique ?_
  simpa [HilbertBasis.repr_apply_apply] using cosBasis.hasSum_repr x

/-- **Point evaluation**: if `∑ₙ |⟪eₙ, x⟫| < ∞` and `f` is a representative of `x` continuous on
`[0, 1]`, then `∑ₙ eₙ(ξ) ⟪eₙ, x⟫ = f(ξ)` for every `ξ ∈ [0, 1]`. -/
theorem hasSum_cosFun_mul_inner {x : L2 ℝ 1} (hx : Summable fun n => |⟪cosBasis n, x⟫_ℝ|)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (hxf : (x : ℝ → ℝ) =ᵐ[μI 1] f) {ξ : ℝ}
    (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n => cosFun n ξ * ⟪cosBasis n, x⟫_ℝ) (f ξ) := by
  set S := cosSeries fun n => ⟪cosBasis n, x⟫_ℝ
  have h1 : ((toL2 S : L2 ℝ 1) : ℝ → ℝ) =ᵐ[μI 1] f := by rw [toL2_cosSeries hx]; exact hxf
  have heq := eqOn_Icc_of_ae_eq S.continuous.continuousOn hf ((coeFn_toL2 S).symm.trans h1)
  rw [← heq hξ]
  simpa [mul_comm] using hasSum_cosSeries_apply hx ξ

/-- `∑ₙ (λₙ aₙ)² < ∞ ⇒ ∑ₙ (n + 1) |aₙ| < ∞` (Cauchy–Schwarz against `∑ 1/n²`). -/
theorem summable_succ_mul_abs {a : ℕ → ℝ} (h : Summable fun n => (cosEig n * a n) ^ 2) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * |a n| := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  refine ((h.comp_injective (add_left_injective 1)).add hs).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  simp only [Function.comp_apply]
  set m : ℝ := ((n + 1 : ℕ) : ℝ) with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast Nat.succ_pos n
  have hm0 : m ≠ 0 := by positivity
  set b := |a (n + 1)| with hb
  have hb0 : 0 ≤ b := abs_nonneg _
  have key := two_mul_le_add_sq (m ^ 2 * b) m⁻¹
  have e1 : 2 * (m ^ 2 * b) * m⁻¹ = 2 * m * b := by field_simp
  have e2 : (cosEig (n + 1) * a (n + 1)) ^ 2 = Real.pi ^ 4 * (m ^ 2 * b) ^ 2 := by
    rw [hb, hm, cosEig, mul_pow (_ : ℝ) |a (n + 1)|, sq_abs]
    ring
  have hpi : 1 ≤ Real.pi ^ 4 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have e3 : (m⁻¹) ^ 2 = (m ^ 2)⁻¹ := inv_pow m 2
  have hsq : 0 ≤ (m ^ 2 * b) ^ 2 := sq_nonneg _
  rw [e2]
  calc (m + 1) * b ≤ 2 * m * b := by nlinarith
    _ ≤ (m ^ 2 * b) ^ 2 + (m⁻¹) ^ 2 := by rw [← e1]; exact key
    _ ≤ Real.pi ^ 4 * (m ^ 2 * b) ^ 2 + (m ^ 2)⁻¹ := by rw [e3]; nlinarith

/-- `∑ₙ (λₙ aₙ)² < ∞ ⇒ ∑ₙ |aₙ| < ∞`. -/
theorem summable_abs_of_summable_sq {a : ℕ → ℝ} (h : Summable fun n => (cosEig n * a n) ^ 2) :
    Summable fun n => |a n| :=
  (summable_succ_mul_abs h).of_nonneg_of_le (fun _ => abs_nonneg _) fun n => by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith [abs_nonneg (a n)]

/-- Termwise differentiation of the cosine series when `∑ (n + 1) |aₙ| < ∞`. -/
theorem hasDerivAt_tsum_cosFun {a : ℕ → ℝ} (ha : Summable fun n : ℕ => ((n : ℝ) + 1) * |a n|)
    (ξ : ℝ) :
    HasDerivAt (fun ξ => ∑' n, a n * cosFun n ξ) (∑' n, a n * cosDeriv n ξ) ξ := by
  refine hasDerivAt_tsum (y₀ := 0) (ha.mul_left (Real.sqrt 2 * Real.pi))
    (fun n y => (hasDerivAt_cosFun n y).const_mul (a n)) (fun n y => ?_) ?_ ξ
  · rw [Real.norm_eq_abs, abs_mul]
    have h := abs_cosDeriv_le n y
    have : (0 : ℝ) ≤ Real.sqrt 2 * Real.pi := by positivity
    calc |a n| * |cosDeriv n y| ≤ |a n| * (Real.sqrt 2 * Real.pi * n) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ Real.sqrt 2 * Real.pi * (((n : ℝ) + 1) * |a n|) := by
          nlinarith [abs_nonneg (a n)]
  · refine Summable.of_norm_bounded (ha.mul_left (Real.sqrt 2)) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h := abs_cosFun_le n 0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    calc |a n| * |cosFun n 0| ≤ |a n| * Real.sqrt 2 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ Real.sqrt 2 * (((n : ℝ) + 1) * |a n|) := by
        have h2 : |a n| ≤ ((n : ℝ) + 1) * |a n| := by nlinarith [abs_nonneg (a n)]
        nlinarith [Real.sqrt_nonneg 2]

/-- The differentiated cosine series is continuous when `∑ (n + 1) |aₙ| < ∞`. -/
theorem continuous_tsum_cosDeriv {a : ℕ → ℝ} (ha : Summable fun n : ℕ => ((n : ℝ) + 1) * |a n|) :
    Continuous fun ξ => ∑' n, a n * cosDeriv n ξ := by
  refine continuous_tsum (fun n => (continuous_cosDeriv n).const_mul (a n))
    (ha.mul_left (Real.sqrt 2 * Real.pi)) fun n y => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have h := abs_cosDeriv_le n y
  calc |a n| * |cosDeriv n y| ≤ |a n| * (Real.sqrt 2 * Real.pi * n) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ Real.sqrt 2 * Real.pi * (((n : ℝ) + 1) * |a n|) := by
        have : (0 : ℝ) ≤ Real.sqrt 2 * Real.pi := by positivity
        nlinarith [abs_nonneg (a n)]

end CosineBasis

end DataDrivenControl
