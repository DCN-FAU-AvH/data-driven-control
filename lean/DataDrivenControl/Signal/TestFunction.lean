module

public import DataDrivenControl.Signal.Basic

/-!
# Test functions and derivative moments

Distributions enter only through test functions.

Paper: the derivative moments `⟨Dᵏ ū, φ⟩ = (-1)ᵏ ∫ ū φ⁽ᵏ⁾` before `def:PE`
(`sections/informativity.tex`), and the tools used by `app:pe-necessity`,
`app:window-pe-necessity`, `app:finite-pe-sufficiency`, `app:infinite-pe-insufficient`,
`app:harmonic-pe` and `app:willems-gramian`.

## Conventions

* A test function on `I = (0, T)` is a real function `φ : ℝ → ℝ` with `IsTestFunction T φ`:
  `φ` is smooth and `tsupport φ ⊆ Ioo 0 T`.  We use this predicate rather than Mathlib's
  bundled `TestFunction`, because derivatives (`deriv`, `iteratedDeriv`), translates and products
  are then plain functions.  `testFunctions T` is the same space as a submodule of `ℝ → ℝ`.
* `derivMoment k u φ = (-1)ᵏ ∫ φ⁽ᵏ⁾ • u` is the paper's `⟨Dᵏ u, φ⟩`.  The integral is over all
  of `ℝ`; for a test function on `(0, T)` it equals the integral over `I`
  (`IsTestFunction.derivMoment_eq_setIntegral`).  No regularity of `u` is needed.
* `polyDerivMoment p u φ = ⟨p(D) u, φ⟩ = ∑ₖ pₖ ⟨Dᵏ u, φ⟩` for a real polynomial `p`.
* A relation "`… = 0` in `𝒟'(I)`" is stated as `∀ φ, IsTestFunction T φ → … = 0`.

## Main statements

* `IsTestFunction.deriv`, `IsTestFunction.iteratedDeriv`, `IsTestFunction.comp_sub`
  (translates), `IsTestFunction.mul_left` (products with smooth functions);
* `derivMoment_succ`, `derivMoment_comp_add` (translation), `inner_derivMoment`,
  `ContinuousLinearMap.map_derivMoment`;
* `derivMoment_succ_of_hasDerivAt`: `Dᵏ⁺¹ u = Dᵏ u'` for `u` differentiable on `(0, T)`;
* the fundamental lemma on an interval, `ae_eq_zero_of_integral_smul_eq_zero`, and its
  continuous version `eqOn_zero_of_integral_smul_eq_zero`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Polynomial
open scoped ContDiff InnerProductSpace

noncomputable section

set_option autoImplicit false

namespace DataDrivenControl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Test functions on `(0, T)` -/

/-- `φ ∈ 𝒟(I)` for `I = (0, T)`: a smooth real function whose closed support lies in
`Ioo 0 T` (the paper's test functions, Sec. 3.3). -/
structure IsTestFunction (T : ℝ) (φ : ℝ → ℝ) : Prop where
  /-- Test functions are smooth. -/
  contDiff : ContDiff ℝ ∞ φ
  /-- The closed support of a test function lies in `(0, T)`. -/
  tsupport_subset : tsupport φ ⊆ Ioo 0 T

namespace IsTestFunction

variable {T T' : ℝ} {φ ψ : ℝ → ℝ}

/-- Test functions have compact support. -/
theorem hasCompactSupport (hφ : IsTestFunction T φ) : HasCompactSupport φ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport φ)
    (hφ.tsupport_subset.trans Ioo_subset_Icc_self)

theorem continuous (hφ : IsTestFunction T φ) : Continuous φ :=
  hφ.contDiff.continuous

theorem differentiable (hφ : IsTestFunction T φ) : Differentiable ℝ φ :=
  hφ.contDiff.differentiable (by simp)

/-- A test function vanishes outside `(0, T)`. -/
theorem apply_eq_zero (hφ : IsTestFunction T φ) {t : ℝ} (ht : t ∉ Ioo 0 T) : φ t = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => ht (hφ.tsupport_subset h)

theorem integrable (hφ : IsTestFunction T φ) : Integrable φ :=
  hφ.continuous.integrable_of_hasCompactSupport hφ.hasCompactSupport

theorem zero : IsTestFunction T 0 :=
  ⟨contDiff_const, by simp⟩

theorem add (hφ : IsTestFunction T φ) (hψ : IsTestFunction T ψ) : IsTestFunction T (φ + ψ) :=
  ⟨hφ.contDiff.add hψ.contDiff,
    (tsupport_add φ ψ).trans (union_subset hφ.tsupport_subset hψ.tsupport_subset)⟩

theorem neg (hφ : IsTestFunction T φ) : IsTestFunction T (-φ) :=
  ⟨hφ.contDiff.neg, (tsupport_neg φ).symm ▸ hφ.tsupport_subset⟩

theorem sub (hφ : IsTestFunction T φ) (hψ : IsTestFunction T ψ) : IsTestFunction T (φ - ψ) := by
  rw [sub_eq_add_neg]; exact hφ.add hψ.neg

theorem const_smul (hφ : IsTestFunction T φ) (c : ℝ) : IsTestFunction T (c • φ) :=
  ⟨hφ.contDiff.const_smul c, (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.tsupport_subset⟩

theorem sum {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℝ} (h : ∀ i ∈ s, IsTestFunction T (φ i)) :
    IsTestFunction T (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The derivative of a test function is a test function. -/
protected theorem deriv (hφ : IsTestFunction T φ) : IsTestFunction T (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.1 hφ.contDiff).2, (tsupport_deriv_subset).trans hφ.tsupport_subset⟩

/-- Iterated derivatives of a test function are test functions. -/
protected theorem iteratedDeriv (hφ : IsTestFunction T φ) (k : ℕ) :
    IsTestFunction T (iteratedDeriv k φ) := by
  induction k with
  | zero => simpa using hφ
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- The product of a test function with a smooth function is a test function. -/
theorem mul_left (hφ : IsTestFunction T φ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsTestFunction T (fun t => g t * φ t) :=
  ⟨hg.mul hφ.contDiff, (tsupport_mul_subset_right).trans hφ.tsupport_subset⟩

/-- Translates: if `φ ∈ 𝒟(0, T)`, `0 ≤ s` and `T + s ≤ T'`, then `φ (· - s) ∈ 𝒟(0, T')`
(used to test a relation on `(0, T + T')` on windows, `app:window-pe-necessity`). -/
theorem comp_sub (hφ : IsTestFunction T φ) {s : ℝ} (hs : 0 ≤ s) (hsT : T + s ≤ T') :
    IsTestFunction T' (fun t => φ (t - s)) := by
  refine ⟨hφ.contDiff.comp (contDiff_id.sub contDiff_const), ?_⟩
  intro t ht
  have h1 := tsupport_comp_subset_preimage φ (f := fun t : ℝ => t - s)
    (by fun_prop) ht
  have h2 := hφ.tsupport_subset h1
  simp only [mem_Ioo] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem mono (hφ : IsTestFunction T φ) (hT : T ≤ T') : IsTestFunction T' φ :=
  ⟨hφ.contDiff, hφ.tsupport_subset.trans (Ioo_subset_Ioo_right hT)⟩

/-- A test function times a signal integrable on the window is integrable on `ℝ`. -/
theorem integrable_smul (hφ : IsTestFunction T φ) {u : ℝ → E} (hu : Integrable u (μI T)) :
    Integrable (fun t => φ t • u t) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.hasCompactSupport
  have h1 : IntegrableOn (fun t => φ t • u t) (Ioc 0 T) :=
    hu.bdd_smul C hφ.continuous.aestronglyMeasurable (ae_of_all _ hC)
  refine h1.integrable_of_forall_notMem_eq_zero fun t ht => ?_
  rw [hφ.apply_eq_zero fun h => ht (Ioo_subset_Ioc_self h), zero_smul]

/-- The integral of a test function against a signal is the integral over the window. -/
theorem integral_smul_eq_setIntegral (hφ : IsTestFunction T φ) (u : ℝ → E) :
    ∫ t, φ t • u t = ∫ t, φ t • u t ∂(μI T) := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
  rw [hφ.apply_eq_zero fun h => ht (Ioo_subset_Ioc_self h), zero_smul]

end IsTestFunction

/-- There is a nonnegative test function with integral `1` on any nonempty interval. -/
theorem exists_isTestFunction_integral_eq_one {T : ℝ} (hT : 0 < T) :
    ∃ φ, IsTestFunction T φ ∧ (∀ t, 0 ≤ φ t) ∧ ∫ t, φ t = 1 := by
  let f : ContDiffBump (T / 2) := ⟨T / 8, T / 4, by positivity, by linarith⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed, ?_⟩, f.nonneg_normed, f.integral_normed⟩
  rw [f.tsupport_normed_eq, Real.closedBall_eq_Icc]
  intro t ht
  simp only [mem_Icc, f] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- There is a nonzero test function on any nonempty interval. -/
theorem exists_isTestFunction_ne_zero {T : ℝ} (hT : 0 < T) :
    ∃ φ, IsTestFunction T φ ∧ φ ≠ 0 := by
  obtain ⟨φ, hφ, -, h1⟩ := exists_isTestFunction_integral_eq_one hT
  refine ⟨φ, hφ, fun h => ?_⟩
  simp [h] at h1

/-- The test functions on `(0, T)`, as a real vector space (`𝒟(I)`). -/
def testFunctions (T : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {φ | IsTestFunction T φ}
  zero_mem' := IsTestFunction.zero
  add_mem' := fun ha hb => IsTestFunction.add ha hb
  smul_mem' := fun c _ ha => IsTestFunction.const_smul ha c

@[simp] theorem mem_testFunctions {T : ℝ} {φ : ℝ → ℝ} :
    φ ∈ testFunctions T ↔ IsTestFunction T φ :=
  Iff.rfl

/-! ### Derivative moments -/

/-- The derivative moment `⟨Dᵏ u, φ⟩ = (-1)ᵏ ∫ φ⁽ᵏ⁾ u` (Sec. 3.3, before `def:PE`).  For a test
function `φ` on `(0, T)` the integral is over the window `I` (see
`IsTestFunction.derivMoment_eq_setIntegral`); no regularity of `u` is needed. -/
def derivMoment (k : ℕ) (u : ℝ → E) (φ : ℝ → ℝ) : E :=
  (-1 : ℝ) ^ k • ∫ t, iteratedDeriv k φ t • u t

/-- `⟨p(D) u, φ⟩ = ∑ₖ pₖ ⟨Dᵏ u, φ⟩` for a real polynomial `p`. -/
def polyDerivMoment (p : ℝ[X]) (u : ℝ → E) (φ : ℝ → ℝ) : E :=
  p.sum fun k a => a • derivMoment k u φ

section derivMoment

variable {T : ℝ} {k : ℕ} {u v : ℝ → E} {φ ψ : ℝ → ℝ}

@[simp] theorem derivMoment_zero (u : ℝ → E) (φ : ℝ → ℝ) :
    derivMoment 0 u φ = ∫ t, φ t • u t := by
  simp [derivMoment]

/-- `⟨Dᵏ⁺¹ u, φ⟩ = -⟨Dᵏ u, φ'⟩`. -/
theorem derivMoment_succ (k : ℕ) (u : ℝ → E) (φ : ℝ → ℝ) :
    derivMoment (k + 1) u φ = -derivMoment k u (deriv φ) := by
  simp only [derivMoment, iteratedDeriv_succ', pow_succ, mul_neg_one, neg_smul]

theorem derivMoment_eq_derivMoment_zero (k : ℕ) (u : ℝ → E) (φ : ℝ → ℝ) :
    derivMoment k u φ = (-1 : ℝ) ^ k • derivMoment 0 u (iteratedDeriv k φ) := by
  simp [derivMoment]

theorem IsTestFunction.derivMoment_eq_setIntegral (hφ : IsTestFunction T φ) (k : ℕ)
    (u : ℝ → E) :
    derivMoment k u φ = (-1 : ℝ) ^ k • ∫ t, iteratedDeriv k φ t • u t ∂(μI T) := by
  rw [derivMoment, (hφ.iteratedDeriv k).integral_smul_eq_setIntegral]

theorem IsTestFunction.integrable_iteratedDeriv_smul (hφ : IsTestFunction T φ)
    (hu : Integrable u (μI T)) (k : ℕ) :
    Integrable (fun t => iteratedDeriv k φ t • u t) :=
  (hφ.iteratedDeriv k).integrable_smul hu

/-- Derivative moments are additive in the signal. -/
theorem derivMoment_add (hφ : IsTestFunction T φ) (hu : Integrable u (μI T))
    (hv : Integrable v (μI T)) (k : ℕ) :
    derivMoment k (fun t => u t + v t) φ = derivMoment k u φ + derivMoment k v φ := by
  simp only [derivMoment, smul_add]
  rw [integral_add (hφ.integrable_iteratedDeriv_smul hu k)
    (hφ.integrable_iteratedDeriv_smul hv k), smul_add]

theorem derivMoment_sub (hφ : IsTestFunction T φ) (hu : Integrable u (μI T))
    (hv : Integrable v (μI T)) (k : ℕ) :
    derivMoment k (fun t => u t - v t) φ = derivMoment k u φ - derivMoment k v φ := by
  simp only [derivMoment, smul_sub]
  rw [integral_sub (hφ.integrable_iteratedDeriv_smul hu k)
    (hφ.integrable_iteratedDeriv_smul hv k), smul_sub]

theorem derivMoment_neg (k : ℕ) (u : ℝ → E) (φ : ℝ → ℝ) :
    derivMoment k (fun t => -u t) φ = -derivMoment k u φ := by
  simp [derivMoment, integral_neg]

theorem derivMoment_smul (k : ℕ) (c : ℝ) (u : ℝ → E) (φ : ℝ → ℝ) :
    derivMoment k (fun t => c • u t) φ = c • derivMoment k u φ := by
  simp only [derivMoment, smul_comm _ c, integral_smul]

theorem derivMoment_finset_sum {ι : Type*} (s : Finset ι) {u : ι → ℝ → E}
    (hφ : IsTestFunction T φ) (hu : ∀ i ∈ s, Integrable (u i) (μI T)) (k : ℕ) :
    derivMoment k (fun t => ∑ i ∈ s, u i t) φ = ∑ i ∈ s, derivMoment k (u i) φ := by
  simp only [derivMoment, Finset.smul_sum]
  rw [integral_finsetSum _ fun i hi => hφ.integrable_iteratedDeriv_smul (hu i hi) k,
    Finset.smul_sum]

/-- Derivative moments are additive in the test function. -/
theorem derivMoment_add_right (hφ : IsTestFunction T φ) (hψ : IsTestFunction T ψ)
    (hu : Integrable u (μI T)) (k : ℕ) :
    derivMoment k u (φ + ψ) = derivMoment k u φ + derivMoment k u ψ := by
  have h : iteratedDeriv k (φ + ψ) = fun t => iteratedDeriv k φ t + iteratedDeriv k ψ t := by
    funext t
    exact iteratedDeriv_add (hφ.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
      (hψ.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
  simp only [derivMoment, h, add_smul]
  rw [integral_add (hφ.integrable_iteratedDeriv_smul hu k)
    (hψ.integrable_iteratedDeriv_smul hu k), smul_add]

theorem derivMoment_smul_right (hφ : IsTestFunction T φ) (c : ℝ) (k : ℕ) (u : ℝ → E) :
    derivMoment k u (c • φ) = c • derivMoment k u φ := by
  have _h := hφ
  simp only [derivMoment, iteratedDeriv_const_smul_field, smul_eq_mul, mul_smul, integral_smul]
  rw [smul_comm]

/-- Bounded operators pass through derivative moments. -/
theorem _root_.ContinuousLinearMap.map_derivMoment [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) (hφ : IsTestFunction T φ) (hu : Integrable u (μI T)) (k : ℕ) :
    L (derivMoment k u φ) = derivMoment k (fun t => L (u t)) φ := by
  simp only [derivMoment, map_smul]
  rw [← L.integral_comp_comm (hφ.integrable_iteratedDeriv_smul hu k)]
  simp only [map_smul]

/-- `⟪ζ, ⟨Dᵏ u, φ⟩⟫ = ⟨Dᵏ ⟪ζ, u⟫, φ⟩`. -/
theorem inner_derivMoment {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {u : ℝ → H} (ζ : H) (hφ : IsTestFunction T φ) (hu : Integrable u (μI T))
    (k : ℕ) :
    ⟪ζ, derivMoment k u φ⟫_ℝ = derivMoment k (fun t => ⟪ζ, u t⟫_ℝ) φ := by
  have := (innerSL ℝ ζ).map_derivMoment hφ hu k
  simpa only [innerSL_apply_apply] using this

/-- Translation: `⟨Dᵏ u(· + s), φ⟩ = ⟨Dᵏ u, φ(· - s)⟩`. -/
theorem derivMoment_comp_add (k : ℕ) (u : ℝ → E) (φ : ℝ → ℝ) (s : ℝ) :
    derivMoment k (fun t => u (t + s)) φ = derivMoment k u (fun t => φ (t - s)) := by
  simp only [derivMoment, iteratedDeriv_comp_sub_const]
  congr 1
  rw [← integral_add_right_eq_self (fun t => iteratedDeriv k φ (t - s) • u t) s]
  simp

/-- A test function with nonempty support is supported in some `Ioo a b` with
`0 < a < b < T`. -/
theorem IsTestFunction.exists_Ioo (hφ : IsTestFunction T φ)
    (hne : (tsupport φ).Nonempty) :
    ∃ a b, 0 < a ∧ a < b ∧ b < T ∧ tsupport φ ⊆ Ioo a b := by
  have hK : IsCompact (tsupport φ) := hφ.hasCompactSupport
  have h1 := hφ.tsupport_subset (hK.sInf_mem hne)
  have h2 := hφ.tsupport_subset (hK.sSup_mem hne)
  refine ⟨sInf (tsupport φ) / 2, (sSup (tsupport φ) + T) / 2, by linarith [h1.1], ?_,
    by linarith [h2.2], fun t ht => ⟨?_, ?_⟩⟩
  · linarith [h1.1, h2.2, csInf_le hK.bddBelow (hK.sSup_mem hne)]
  · linarith [h1.1, csInf_le hK.bddBelow ht]
  · linarith [h2.2, le_csSup hK.bddAbove ht]

/-- Integration by parts against a test function. -/
private theorem IsTestFunction.integral_deriv_smul_of_hasDerivAt [CompleteSpace E]
    (hφ : IsTestFunction T φ) {u u' : ℝ → E} (hu : ∀ t ∈ Ioo 0 T, HasDerivAt u (u' t) t)
    (hu' : ContinuousOn u' (Ioo 0 T)) :
    ∫ t, deriv φ t • u t = -∫ t, φ t • u' t := by
  rcases (tsupport φ).eq_empty_or_nonempty with h | hne
  · have : φ = 0 := tsupport_eq_empty_iff.1 h
    subst this
    simp
  obtain ⟨a, b, ha, hab, hb, hsub⟩ := hφ.exists_Ioo hne
  have hφ0 : ∀ t ∉ Ioo a b, φ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hsub h)
  have hφ'0 : ∀ t ∉ Ioo a b, deriv φ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hsub (tsupport_deriv_subset h))
  have hab' : uIcc a b ⊆ Ioo 0 T := by
    rw [uIcc_of_le hab.le]
    exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have e1 : ∫ t, deriv φ t • u t = ∫ t in a..b, deriv φ t • u t := by
    rw [intervalIntegral.integral_of_le hab.le]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [hφ'0 t fun h => ht (Ioo_subset_Ioc_self h), zero_smul]
  have e2 : ∫ t, φ t • u' t = ∫ t in a..b, φ t • u' t := by
    rw [intervalIntegral.integral_of_le hab.le]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [hφ0 t fun h => ht (Ioo_subset_Ioc_self h), zero_smul]
  have ibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := a) (b := b)
    (u := φ) (u' := deriv φ) (v := u) (v' := u')
    (fun t _ => (hφ.differentiable t).hasDerivAt) (fun t ht => hu t (hab' ht))
    ((hφ.deriv).continuous.intervalIntegrable a b)
    ((hu'.mono hab').intervalIntegrable)
  rw [hφ0 a (fun h => lt_irrefl a h.1), hφ0 b (fun h => lt_irrefl b h.2)] at ibp
  rw [e1, e2, ibp]
  simp

/-- Integration by parts: for `u` differentiable on `(0, T)` with continuous derivative `u'`,
`⟨Dᵏ⁺¹ u, φ⟩ = ⟨Dᵏ u', φ⟩`. -/
theorem derivMoment_succ_of_hasDerivAt [CompleteSpace E] (hφ : IsTestFunction T φ)
    {u u' : ℝ → E} (hu : ∀ t ∈ Ioo 0 T, HasDerivAt u (u' t) t)
    (hu' : ContinuousOn u' (Ioo 0 T)) (k : ℕ) :
    derivMoment (k + 1) u φ = derivMoment k u' φ := by
  have := (hφ.iteratedDeriv k).integral_deriv_smul_of_hasDerivAt hu hu'
  simp only [derivMoment, iteratedDeriv_succ, this, pow_succ, mul_neg_one, neg_smul, smul_neg,
    neg_neg]

/-- For a signal with continuous classical derivatives `v 0 = u, v 1, …, v k` on `(0, T)`,
`⟨Dᵏ u, φ⟩ = ∫ φ • v k` (the remark on regular inputs after `def:PE`). -/
theorem derivMoment_eq_integral_of_hasDerivAt [CompleteSpace E] (hφ : IsTestFunction T φ)
    {v : ℕ → ℝ → E} (k : ℕ) (hv : ∀ j < k, ∀ t ∈ Ioo 0 T, HasDerivAt (v j) (v (j + 1) t) t)
    (hcont : ∀ j ≤ k, ContinuousOn (v j) (Ioo 0 T)) :
    derivMoment k (v 0) φ = ∫ t, φ t • v k t := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [derivMoment_succ_of_hasDerivAt hφ (hv 0 (Nat.succ_pos k)) (hcont 1 (by omega)) k]
    exact ih (v := fun j => v (j + 1)) (fun j hj t ht => hv (j + 1) (by omega) t ht)
      (fun j hj => hcont (j + 1) (by omega))

end derivMoment

/-! ### Polynomials in `D` -/

section polyDerivMoment

variable {T : ℝ} {u v : ℝ → E} {φ : ℝ → ℝ}

theorem polyDerivMoment_eq_sum_range (p : ℝ[X]) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment p u φ =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • derivMoment k u φ := by
  rw [polyDerivMoment, Polynomial.sum_over_range]
  intro n
  simp

@[simp] theorem polyDerivMoment_zero (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment 0 u φ = 0 := by
  simp [polyDerivMoment]

@[simp] theorem polyDerivMoment_C (a : ℝ) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment (C a) u φ = a • ∫ t, φ t • u t := by
  rw [polyDerivMoment, sum_C_index (by simp), derivMoment_zero]

@[simp] theorem polyDerivMoment_monomial (k : ℕ) (a : ℝ) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment (monomial k a) u φ = a • derivMoment k u φ := by
  rw [polyDerivMoment, sum_monomial_index _ _ (by simp)]

theorem polyDerivMoment_add_left (p q : ℝ[X]) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment (p + q) u φ = polyDerivMoment p u φ + polyDerivMoment q u φ := by
  rw [polyDerivMoment, sum_add_index _ _ _ (by simp) (by simp [add_smul])]
  rfl

theorem polyDerivMoment_C_mul (a : ℝ) (p : ℝ[X]) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment (C a * p) u φ = a • polyDerivMoment p u φ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, polyDerivMoment_add_left, polyDerivMoment_add_left, hp, hq,
      smul_add]
  | monomial n b => rw [C_mul_monomial, polyDerivMoment_monomial, polyDerivMoment_monomial,
      mul_smul]

/-- `⟨(X p)(D) u, φ⟩ = -⟨p(D) u, φ'⟩`. -/
theorem polyDerivMoment_X_mul (p : ℝ[X]) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment (X * p) u φ = -polyDerivMoment p u (deriv φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, polyDerivMoment_add_left, polyDerivMoment_add_left, hp, hq,
      neg_add]
  | monomial n b => rw [X_mul_monomial, polyDerivMoment_monomial, polyDerivMoment_monomial,
      derivMoment_succ, smul_neg]

theorem polyDerivMoment_add (p : ℝ[X]) (hφ : IsTestFunction T φ) (hu : Integrable u (μI T))
    (hv : Integrable v (μI T)) :
    polyDerivMoment p (fun t => u t + v t) φ = polyDerivMoment p u φ + polyDerivMoment p v φ := by
  simp only [polyDerivMoment, Polynomial.sum_def, derivMoment_add hφ hu hv, smul_add,
    Finset.sum_add_distrib]

theorem polyDerivMoment_smul (p : ℝ[X]) (c : ℝ) (u : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment p (fun t => c • u t) φ = c • polyDerivMoment p u φ := by
  simp only [polyDerivMoment, Polynomial.sum_def, derivMoment_smul, smul_comm _ c,
    Finset.smul_sum]

theorem _root_.ContinuousLinearMap.map_polyDerivMoment [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) (p : ℝ[X]) (hφ : IsTestFunction T φ) (hu : Integrable u (μI T)) :
    L (polyDerivMoment p u φ) = polyDerivMoment p (fun t => L (u t)) φ := by
  simp only [polyDerivMoment, Polynomial.sum_def, map_sum, map_smul, L.map_derivMoment hφ hu]

end polyDerivMoment

/-! ### The fundamental lemma of the calculus of variations on `(0, T)` -/

section fundamental

variable [CompleteSpace E] {T : ℝ} {u v : ℝ → E}

/-- A signal that is locally integrable on `(0, T)` and orthogonal to every test function vanishes
a.e. on the window. -/
theorem ae_eq_zero_of_integral_smul_eq_zero' (hu : LocallyIntegrableOn u (Ioo 0 T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, φ t • u t = 0) :
    ∀ᵐ t ∂(μI T), u t = 0 := by
  have h1 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hu
    (fun g hg _ hgs => h g ⟨hg, hgs⟩)
  have h2 : μI T = volume.restrict (Ioo 0 T) := (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [h2, ae_restrict_iff' measurableSet_Ioo]
  exact h1

/-- The fundamental lemma on the window: a signal integrable on `I` and orthogonal to every
test function vanishes a.e. on `I` ("`u = 0` in `𝒟'(I)` implies `u = 0` in `L²`"). -/
theorem ae_eq_zero_of_integral_smul_eq_zero (hu : Integrable u (μI T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, φ t • u t = 0) :
    ∀ᵐ t ∂(μI T), u t = 0 :=
  ae_eq_zero_of_integral_smul_eq_zero'
    ((IntegrableOn.mono_set (hu : IntegrableOn u (Ioc 0 T) volume) Ioo_subset_Ioc_self).locallyIntegrableOn)
    h

theorem ae_eq_of_integral_smul_eq (hu : Integrable u (μI T)) (hv : Integrable v (μI T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, φ t • u t = ∫ t, φ t • v t) :
    u =ᵐ[μI T] v := by
  have := ae_eq_zero_of_integral_smul_eq_zero (u := fun t => u t - v t) (hu.sub hv) fun φ hφ => by
    simp only [smul_sub]
    rw [integral_sub (hφ.integrable_smul hu) (hφ.integrable_smul hv), h φ hφ, sub_self]
  filter_upwards [this] with t ht using sub_eq_zero.1 ht

/-- The fundamental lemma for signals continuous on `(0, T)`: they vanish everywhere there. -/
theorem eqOn_zero_of_integral_smul_eq_zero (hu : ContinuousOn u (Ioo 0 T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, φ t • u t = 0) :
    ∀ t ∈ Ioo 0 T, u t = 0 := by
  have h1 := ae_eq_zero_of_integral_smul_eq_zero' (hu.locallyIntegrableOn measurableSet_Ioo) h
  have h2 : μI T = volume.restrict (Ioo 0 T) := (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  rw [h2] at h1
  intro t ht
  exact Measure.eqOn_of_ae_eq (f := u) (g := 0) h1 hu continuousOn_const
    (by rw [isOpen_Ioo.interior_eq]; exact subset_closure) ht

end fundamental

end DataDrivenControl
