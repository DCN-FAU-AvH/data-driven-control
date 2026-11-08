module

public import Mathlib
public import DataDrivenControl.Analysis.CosineBasis
public import DataDrivenControl.Signal.WeakDerivative
public import DataDrivenControl.Examples.Heat.Modal

/-!
# The boundary-controlled heat equation on `L²(0, 1)`: the dictionary

Paper: `ex:intro-pde` (`introduction.tex`), `app:boundary-heat-informative`
(`appendix_proofs.tex`).

The ties of the modal objects (cosine basis `eₙ`, `λₙ = -(nπ)²`, `bₙ = -eₙ(0)`, `cₙ = eₙ(ξ₀)`) to
the PDE `∂ₜx = ∂_ξξ x`, `∂_ξ x(t, 0) = u(t)`, `∂_ξ x(t, 1) = 0`, `y(t) = x(t, ξ₀)` on
`X = L²(0, 1)`, in function language.

## Main declarations

* `HasH2 φ φ' φ''` (`φ ∈ H²(0, 1)`, two `HasWeakDeriv` layers) and `IsNeumannH2 φ φ' φ''`
  (`φ'(0) = φ'(1) = 0`).
* `integral_cosFun_mul_deriv2`: `∫₀¹ eₙ φ'' = λₙ ∫₀¹ eₙ φ - eₙ(0) φ'(0) + eₙ(1) φ'(1)`;
  `inner_cosBasis_neumann_control`: **the weak form of the Neumann control**
  `⟪eₙ, φ''⟫ = λₙ ⟪eₙ, φ⟫ + bₙ φ'(0)` when `φ'(1) = 0`.
* **The generator of `heatSemigroup` is the Neumann Laplacian**: `mem_generator_domain_iff`
  (`D(A) = H²_N(0, 1)`), `generator_ae_eq` (`A φ = φ''`), `mem_graph_generator_iff`.
* `hasSum_cosFun_mul_inner_of_isNeumannH2`: `∑ₙ eₙ(ξ) ⟪eₙ, φ⟫ = φ(ξ)` on `[0, 1]`, hence
  `hasSum_obsCoeff_mul_inner` (`∑ₙ cₙ φₙ = φ(ξ₀)`) and `hasSum_ctrlCoeff_mul_inner`
  (`∑ₙ bₙ ηₙ = -η(0)`).

## Proof of `D(A) ⊆ H²_N(0, 1)`

For `x ∈ D(A)` the coordinates satisfy `∑ (λₙ xₙ)² < ∞`, so `∑ (n + 1) |xₙ| < ∞`
(`summable_succ_mul_abs`).  Then `φ = ∑ xₙ eₙ` and `φ' = ∑ xₙ eₙ'` converge uniformly and may be
differentiated termwise, and `φ'' = A x ∈ L²` satisfies `∫₀ᵗ φ'' = ⟪1_{(0, t]}, A x⟫ =
∑ₙ ⟪1_{(0, t]}, eₙ⟫ λₙ xₙ = ∑ₙ xₙ eₙ'(t) = φ'(t)` (Parseval, `eₙ'' = λₙ eₙ`, `eₙ'(0) = 0`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace BoundaryHeat

namespace PDE

open CosineBasis

/-! ### `H²(0, 1)` and integration by parts -/

/-- **`φ ∈ H²(0, 1)`** with first and second derivatives `φ'` and `φ''`, in the integral form
of `HasWeakDeriv`: `φ` and `φ'` are absolutely continuous on `[0, 1]`, `φ(t) = φ(0) + ∫₀ᵗ φ'`,
`φ'(t) = φ'(0) + ∫₀ᵗ φ''`, and `φ'' ∈ L²(0, 1)`. -/
structure HasH2 (φ φ' φ'' : ℝ → ℝ) : Prop where
  /-- `φ ∈ H¹(0, 1)` with weak derivative `φ'`. -/
  hasWeakDeriv : HasWeakDeriv 1 φ φ'
  /-- `φ' ∈ H¹(0, 1)` with weak derivative `φ'' ∈ L²(0, 1)`. -/
  hasWeakDeriv_deriv : HasWeakDeriv 1 φ' φ''

/-- **The Neumann `H²` class** `H²_N(0, 1)`: `φ ∈ H²(0, 1)` with `φ'(0) = φ'(1) = 0`, the domain
of the Neumann Laplacian. -/
structure IsNeumannH2 (φ φ' φ'' : ℝ → ℝ) : Prop extends HasH2 φ φ' φ'' where
  /-- The Neumann condition at `0`. -/
  deriv_zero : φ' 0 = 0
  /-- The Neumann condition at `1`. -/
  deriv_one : φ' 1 = 0

/-- `φ ∈ L²(0, 1)`. -/
theorem HasH2.memLp {φ φ' φ'' : ℝ → ℝ} (h : HasH2 φ φ' φ'') : MemLp φ 2 (μI 1) :=
  h.hasWeakDeriv.memLp

/-- `φ'' ∈ L²(0, 1)`. -/
theorem HasH2.memLp_deriv2 {φ φ' φ'' : ℝ → ℝ} (h : HasH2 φ φ' φ'') : MemLp φ'' 2 (μI 1) :=
  h.hasWeakDeriv_deriv.memLp_deriv

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

/-- **Green's formula for the eigenfunctions**: for `φ ∈ H²(0, 1)`,
`∫₀¹ eₙ φ'' = λₙ ∫₀¹ eₙ φ - eₙ(0) φ'(0) + eₙ(1) φ'(1)` (no boundary conditions on `φ`; the
terms with `φ` vanish because `eₙ'(0) = eₙ'(1) = 0`). -/
theorem integral_cosFun_mul_deriv2 {φ φ' φ'' : ℝ → ℝ} (h : HasH2 φ φ' φ'') (n : ℕ) :
    ∫ t in (0 : ℝ)..1, cosFun n t * φ'' t =
      cosEig n * (∫ t in (0 : ℝ)..1, cosFun n t * φ t) - cosFun n 0 * φ' 0 +
        cosFun n 1 * φ' 1 := by
  have h1 := integral_mul_deriv h.hasWeakDeriv_deriv (hasDerivAt_cosFun n)
    (continuous_cosDeriv n)
  have h2 := integral_mul_deriv h.hasWeakDeriv (hasDerivAt_cosDeriv n)
    ((continuous_cosFun n).const_mul (cosEig n))
  simp only [cosDeriv_zero, cosDeriv_one, zero_mul, sub_zero, zero_sub] at h2
  have h3 : ∫ t in (0 : ℝ)..1, cosEig n * cosFun n t * φ t =
      cosEig n * ∫ t in (0 : ℝ)..1, cosFun n t * φ t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [h1, h2, h3]
  ring

/-- The coordinates of a class with representative `f`: `⟪eₙ, x⟫ = ∫₀¹ eₙ f`. -/
theorem inner_cosBasis_of_ae_eq {x : L2 ℝ 1} {f : ℝ → ℝ} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] f)
    (n : ℕ) : ⟪cosBasis n, x⟫_ℝ = ∫ t in (0 : ℝ)..1, cosFun n t * f t := by
  rw [inner_cosBasis, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [hx] with t h
  rw [h]

/-- Green's formula in `L²(0, 1)`: `⟪eₙ, φ''⟫ = λₙ ⟪eₙ, φ⟫ - eₙ(0) φ'(0) + eₙ(1) φ'(1)`. -/
theorem inner_cosBasis_deriv2 {φ φ' φ'' : ℝ → ℝ} (h : HasH2 φ φ' φ'') {x y : L2 ℝ 1}
    (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) (hy : (y : ℝ → ℝ) =ᵐ[μI 1] φ'') (n : ℕ) :
    ⟪cosBasis n, y⟫_ℝ = cosEig n * ⟪cosBasis n, x⟫_ℝ - cosFun n 0 * φ' 0 + cosFun n 1 * φ' 1 := by
  rw [inner_cosBasis_of_ae_eq hx, inner_cosBasis_of_ae_eq hy, integral_cosFun_mul_deriv2 h]

/-- **`B` is the Neumann boundary control at `0`** (`ex:intro-pde`,
`app:boundary-heat-informative`).  For `φ ∈ H²(0, 1)` with `φ'(1) = 0`,
`⟪eₙ, φ''⟫ = λₙ ⟪eₙ, φ⟫ + bₙ φ'(0)` with `bₙ = -eₙ(0)` (`ctrlCoeff`).  Applied to a solution
`x(t, ·)` of `∂ₜx = ∂_ξξ x` with `∂_ξ x(t, 0) = u(t)`, `∂_ξ x(t, 1) = 0`, this is the modal
equation `ẋₙ = λₙ xₙ + bₙ u` of `ẋ = A x + B u`, i.e. the boundary condition `∂_ξ x(t, 0) = u(t)`
is the control operator `B` with `B⋆ eₙ = bₙ`. -/
theorem inner_cosBasis_neumann_control {φ φ' φ'' : ℝ → ℝ} (h : HasH2 φ φ' φ'')
    (h1 : φ' 1 = 0) {x y : L2 ℝ 1} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ)
    (hy : (y : ℝ → ℝ) =ᵐ[μI 1] φ'') (n : ℕ) :
    ⟪cosBasis n, y⟫_ℝ = eig n * ⟪cosBasis n, x⟫_ℝ + ctrlCoeff n * φ' 0 := by
  rw [inner_cosBasis_deriv2 h hx hy, h1, ctrlCoeff_eq_neg_cosFun, eig_eq_cosEig]
  ring

/-- For `φ ∈ H²_N(0, 1)`: `⟪eₙ, φ''⟫ = λₙ ⟪eₙ, φ⟫`. -/
theorem inner_cosBasis_deriv2_of_isNeumannH2 {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'')
    {x y : L2 ℝ 1} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) (hy : (y : ℝ → ℝ) =ᵐ[μI 1] φ'') (n : ℕ) :
    ⟪cosBasis n, y⟫_ℝ = eig n * ⟪cosBasis n, x⟫_ℝ := by
  rw [inner_cosBasis_deriv2 h.toHasH2 hx hy, h.deriv_zero, h.deriv_one, eig_eq_cosEig]
  ring

/-! ### The generator is the Neumann Laplacian -/

/-- The heat semigroup on `L²(0, 1)`: the diagonal semigroup of the cosine basis with
`λₙ = -(nπ)²`. -/
abbrev heatSemigroup : C0Semigroup ℝ (L2 ℝ 1) := diagSemigroup cosBasis eig bddAbove_eig

/-- **`H²_N(0, 1) ⊆ D(A)`**. -/
theorem mem_generator_domain_of_isNeumannH2 {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'')
    {x : L2 ℝ 1} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) : x ∈ heatSemigroup.generator.domain := by
  rw [mem_generator_domain_diag_iff]
  refine (Diagonal.summable_inner_sq cosBasis (h.memLp_deriv2.toLp φ'')).congr fun n => ?_
  rw [inner_cosBasis_deriv2_of_isNeumannH2 h hx h.memLp_deriv2.coeFn_toLp n]

/-- **`A φ = φ''`** on `H²_N(0, 1)`. -/
theorem generator_ae_eq {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') {x : L2 ℝ 1}
    (hx : x ∈ heatSemigroup.generator.domain) (hxφ : (x : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSemigroup.generator ⟨x, hx⟩ : ℝ → ℝ) =ᵐ[μI 1] φ'' := by
  have hy : heatSemigroup.generator ⟨x, hx⟩ = h.memLp_deriv2.toLp φ'' := by
    refine Diagonal.ext_inner cosBasis fun n => ?_
    rw [inner_generator_diag,
      inner_cosBasis_deriv2_of_isNeumannH2 h hxφ h.memLp_deriv2.coeFn_toLp n]
  rw [hy]
  exact h.memLp_deriv2.coeFn_toLp

/-- `∫₀ᵗ f` for `f ∈ L²(0, 1)` and `t ∈ [0, 1]`, as an inner product with `1_{(0, t]}`. -/
theorem inner_indicator_eq_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (f : L2 ℝ 1) :
    ⟪indicatorConstLp 2 (measurableSet_Ioc (a := 0) (b := t)) (measure_ne_top (μI 1) _)
      (1 : ℝ), f⟫_ℝ = ∫ s in (0 : ℝ)..t, f s := by
  rw [L2.inner_indicatorConstLp_one, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioc_right ht.2), intervalIntegral.integral_of_le ht.1]

/-- Representatives agree on `(0, t]` for `t ≤ 1`. -/
theorem intervalIntegral_congr_of_ae_eq {f g : ℝ → ℝ} (h : f =ᵐ[μI 1] g) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ∫ s in (0 : ℝ)..t, f s = ∫ s in (0 : ℝ)..t, g s := by
  refine intervalIntegral.integral_congr_ae ?_
  have h' : ∀ᵐ s, s ∈ Ioc (0 : ℝ) 1 → f s = g s := (ae_restrict_iff' measurableSet_Ioc).1 h
  filter_upwards [h'] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  exact hs (Ioc_subset_Ioc_right ht.2 hsI)

/-- **`D(A) ⊆ H²_N(0, 1)`**: every `x ∈ D(A)` has a representative `φ ∈ H²_N(0, 1)` with
`A x = φ''`. -/
theorem exists_isNeumannH2_of_mem_domain {x : L2 ℝ 1} (hx : x ∈ heatSemigroup.generator.domain) :
    ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (x : ℝ → ℝ) =ᵐ[μI 1] φ ∧
      (heatSemigroup.generator ⟨x, hx⟩ : ℝ → ℝ) =ᵐ[μI 1] φ'' := by
  set a : ℕ → ℝ := fun n => ⟪cosBasis n, x⟫_ℝ with ha_def
  have hs : Summable fun n => (cosEig n * a n) ^ 2 :=
    (mem_generator_domain_diag_iff cosBasis eig bddAbove_eig x).1 hx
  have ha := summable_succ_mul_abs hs
  set y := heatSemigroup.generator ⟨x, hx⟩ with hy_def
  have hyn : ∀ n, ⟪cosBasis n, y⟫_ℝ = cosEig n * a n := fun n =>
    inner_generator_diag cosBasis eig bddAbove_eig ⟨x, hx⟩ n
  refine ⟨fun ξ => ∑' n, a n * cosFun n ξ, fun ξ => ∑' n, a n * cosDeriv n ξ, y,
    ⟨⟨HasWeakDeriv.of_hasDerivAt (hasDerivAt_tsum_cosFun ha) (continuous_tsum_cosDeriv ha),
      ⟨Lp.memLp y, fun t ht => ?_⟩⟩, by simp, by simp⟩, ?_, EventuallyEq.rfl⟩
  · -- `φ'(t) = φ'(0) + ∫₀ᵗ A x`
    simp only [cosDeriv_zero, mul_zero, tsum_zero, zero_add]
    rw [← inner_indicator_eq_integral ht]
    refine (HasSum.tsum_eq ?_).symm.symm
    convert cosBasis.hasSum_inner_mul_inner _ y using 1
    funext n
    rw [hyn, inner_indicator_eq_integral ht,
      intervalIntegral_congr_of_ae_eq (coeFn_cosBasis n) ht]
    have hftc : ∫ s in (0 : ℝ)..t, cosEig n * cosFun n s = cosDeriv n t - cosDeriv n 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_cosDeriv n s)
        (((continuous_cosFun n).const_mul _).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, cosDeriv_zero, sub_zero] at hftc
    rw [← hftc]
    ring
  · -- `x` is the class of `φ`
    have h1 := toL2_cosSeries (summable_abs_of_summable_sq hs)
    have h2 : (cosSeries a : ℝ → ℝ) = fun ξ => ∑' n, a n * cosFun n ξ :=
      funext fun ξ => (hasSum_cosSeries_apply (summable_abs_of_summable_sq hs) ξ).tsum_eq.symm
    rw [← h2]
    conv_lhs => rw [← h1]
    exact coeFn_toL2 _

/-- **`D(A) = H²_N(0, 1)`**: the domain of the generator of the heat semigroup on `L²(0, 1)` is
the set of classes of the Neumann `H²` functions. -/
theorem mem_generator_domain_iff (x : L2 ℝ 1) :
    x ∈ heatSemigroup.generator.domain ↔
      ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (x : ℝ → ℝ) =ᵐ[μI 1] φ :=
  ⟨fun hx => let ⟨φ, φ', φ'', h, hφ, _⟩ := exists_isNeumannH2_of_mem_domain hx
      ⟨φ, φ', φ'', h, hφ⟩,
    fun ⟨_, _, _, h, hφ⟩ => mem_generator_domain_of_isNeumannH2 h hφ⟩

/-- **The generator is the Neumann Laplacian**: its graph is `{([φ], [φ'']) : φ ∈ H²_N(0, 1)}`. -/
theorem mem_graph_generator_iff (p : L2 ℝ 1 × L2 ℝ 1) :
    p ∈ heatSemigroup.generator.graph ↔
      ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
        (p.2 : ℝ → ℝ) =ᵐ[μI 1] φ'' := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨⟨x, hx⟩, h1, h2⟩
    obtain ⟨φ, φ', φ'', h, hφ, hφ''⟩ := exists_isNeumannH2_of_mem_domain hx
    refine ⟨φ, φ', φ'', h, ?_, ?_⟩
    · rw [← h1]; exact hφ
    · rw [← h2]; exact hφ''
  · rintro ⟨φ, φ', φ'', h, h1, h2⟩
    have hx := mem_generator_domain_of_isNeumannH2 h h1
    refine ⟨⟨p.1, hx⟩, rfl, Lp.ext ?_⟩
    exact (generator_ae_eq h hx h1).trans h2.symm

/-! ### Point evaluation and boundary trace -/

/-- **Point evaluation on `H²_N(0, 1)`**: `∑ₙ eₙ(ξ) ⟪eₙ, φ⟫ = φ(ξ)` for `ξ ∈ [0, 1]`. -/
theorem hasSum_cosFun_mul_inner_of_isNeumannH2 {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'')
    {x : L2 ℝ 1} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) {ξ : ℝ} (hξ : ξ ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n => cosFun n ξ * ⟪cosBasis n, x⟫_ℝ) (φ ξ) := by
  have hs : Summable fun n => (cosEig n * ⟪cosBasis n, x⟫_ℝ) ^ 2 :=
    (mem_generator_domain_diag_iff cosBasis eig bddAbove_eig x).1
      (mem_generator_domain_of_isNeumannH2 h hx)
  exact hasSum_cosFun_mul_inner (summable_abs_of_summable_sq hs) h.hasWeakDeriv.continuousOn hx hξ

/-- **`C` is point evaluation at `ξ₀`** in modal form: `∑ₙ cₙ ⟪eₙ, φ⟫ = φ(ξ₀)` on
`H²_N(0, 1)`. -/
theorem hasSum_obsCoeff_mul_inner {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') {x : L2 ℝ 1}
    (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n => obsCoeff ξ₀ n * ⟪cosBasis n, x⟫_ℝ) (φ ξ₀) := by
  simpa only [obsCoeff_eq_cosFun] using hasSum_cosFun_mul_inner_of_isNeumannH2 h hx hξ₀

/-- **`B⋆` is minus the trace at `0`** in modal form: `∑ₙ bₙ ⟪eₙ, η⟫ = -η(0)` on
`H²_N(0, 1)`. -/
theorem hasSum_ctrlCoeff_mul_inner {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'')
    {x : L2 ℝ 1} (hx : (x : ℝ → ℝ) =ᵐ[μI 1] φ) :
    HasSum (fun n => ctrlCoeff n * ⟪cosBasis n, x⟫_ℝ) (-φ 0) := by
  have := (hasSum_cosFun_mul_inner_of_isNeumannH2 h hx ⟨le_rfl, zero_le_one⟩).neg
  simpa only [ctrlCoeff_eq_neg_cosFun, neg_mul] using this

end PDE

end BoundaryHeat

end DataDrivenControl
