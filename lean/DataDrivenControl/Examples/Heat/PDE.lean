module

public import Mathlib
public import DataDrivenControl.Analysis.CosineBasis
public import DataDrivenControl.Signal.WeakDerivative
public import DataDrivenControl.Examples.BoundaryHeat

/-!
# The boundary-controlled heat equation on `L²(0, 1)`: the dictionary

Paper: `ex:intro-pde` (`introduction.tex`), `ex:boundary-heat-informative`
(`informativity.tex`), `app:boundary-heat-informative` (`appendix_proofs.tex`).

`Examples/BoundaryHeat` proves the paper's claims for the modal model on any Hilbert space `X`
with a Hilbert basis `e`.  This file instantiates it with `X = L²(0, 1) = L2 ℝ 1` and the cosine
basis `e = cosBasis` (`Analysis/CosineBasis`), and states its ties to the PDE
`∂ₜx = ∂_ξξ x`, `∂_ξ x(t, 0) = u(t)`, `∂_ξ x(t, 1) = 0`, `y(t) = x(t, ξ₀)` in function language.

## Main declarations

* `obsCoeff_eq_cosFun`, `ctrlCoeff_eq_neg_cosFun`, `eig_eq_cosEig`: the modal numbers of
  `Examples/Heat/Kernel` are `cₙ = eₙ(ξ₀)`, `bₙ = -eₙ(0)` and `λₙ = -(nπ)²`.
* `HasH2 φ φ' φ''` (`φ ∈ H²(0, 1)`, two `HasWeakDeriv` layers) and `IsNeumannH2 φ φ' φ''`
  (`φ'(0) = φ'(1) = 0`).
* `integral_cosFun_mul_deriv2`: `∫₀¹ eₙ φ'' = λₙ ∫₀¹ eₙ φ - eₙ(0) φ'(0) + eₙ(1) φ'(1)`;
  `inner_cosBasis_neumann_control`: **the weak form of the Neumann control**
  `⟪eₙ, φ''⟫ = λₙ ⟪eₙ, φ⟫ + bₙ φ'(0)` when `φ'(1) = 0`.
* **The generator is the Neumann Laplacian**: `mem_generator_domain_iff`
  (`D(A) = H²_N(0, 1)`), `generator_ae_eq` (`A φ = φ''`), `mem_graph_generator_iff`.
* `hasSum_cosFun_mul_inner_of_isNeumannH2`: `∑ₙ eₙ(ξ) ⟪eₙ, φ⟫ = φ(ξ)` on `[0, 1]`, hence
  `hasSum_obsCoeff_mul_inner` (`∑ₙ cₙ φₙ = φ(ξ₀)`) and `hasSum_ctrlCoeff_mul_inner`
  (`∑ₙ bₙ ηₙ = -η(0)`).
* `heatSystemL2 hξ₀ = heatSystem cosBasis hξ₀` and its ties: `heatSystemL2_A_graph`,
  `heatSystemL2_A_adjoint`, `heatSystemL2_C` (`C w = φ(ξ₀)`), `heatSystemL2_Bstar`
  (`B⋆η = -η(0)`), and `exists_boundaryHeat_L2`, **`ex:boundary-heat-informative` on
  `L²(0, 1)`**.

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

/-! ### The modal numbers -/

/-- `λₙ = -(nπ)²` are the eigenvalues of the cosine basis. -/
theorem eig_eq_cosEig : eig = cosEig := rfl

/-- `cₙ = eₙ(ξ₀)`: the observation coefficients are the values of the eigenfunctions at `ξ₀`. -/
theorem obsCoeff_eq_cosFun (ξ₀ : ℝ) (n : ℕ) : obsCoeff ξ₀ n = cosFun n ξ₀ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [obsCoeff]
  · rw [cosFun_of_ne_zero hn]
    simp [obsCoeff, hn]

/-- `bₙ = -eₙ(0)`: the control coefficients are minus the values of the eigenfunctions at `0`. -/
theorem ctrlCoeff_eq_neg_cosFun (n : ℕ) : ctrlCoeff n = -cosFun n 0 := by
  rw [cosFun_apply_zero, ctrlCoeff, cosNorm]
  split_ifs <;> rfl

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

/-! ### The heat system on `L²(0, 1)` -/

variable {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1)

/-- **The boundary-controlled heat system on `L²(0, 1)`** (`ex:intro-pde`): `heatSystem` with
the cosine basis. -/
abbrev heatSystemL2 : System ℝ (heatData hξ₀).W (L2 ℝ 1) (heatData hξ₀).V ℝ :=
  heatSystem cosBasis hξ₀

/-- The state-space semigroup is the heat semigroup of the cosine basis. -/
theorem heatSystemL2_SX : (heatSystemL2 hξ₀).SX = heatSemigroup := rfl

/-- **The generator is the Neumann Laplacian** (`ex:intro-pde`): the graph of `A` is
`{([φ], [φ'']) : φ ∈ H²_N(0, 1)}`. -/
theorem heatSystemL2_A_graph (p : L2 ℝ 1 × L2 ℝ 1) :
    p ∈ (heatSystemL2 hξ₀).A.graph ↔
      ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
        (p.2 : ℝ → ℝ) =ᵐ[μI 1] φ'' :=
  mem_graph_generator_iff p

/-- `D(A) = H²_N(0, 1)`. -/
theorem heatSystemL2_A_domain (x : L2 ℝ 1) :
    x ∈ (heatSystemL2 hξ₀).A.domain ↔
      ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (x : ℝ → ℝ) =ᵐ[μI 1] φ :=
  mem_generator_domain_iff x

/-- `A φ = φ''` on `H²_N(0, 1)`. -/
theorem heatSystemL2_A_apply {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') {x : L2 ℝ 1}
    (hx : x ∈ (heatSystemL2 hξ₀).A.domain) (hxφ : (x : ℝ → ℝ) =ᵐ[μI 1] φ) :
    ((heatSystemL2 hξ₀).A ⟨x, hx⟩ : ℝ → ℝ) =ᵐ[μI 1] φ'' :=
  generator_ae_eq h hx hxφ

/-- `A⋆ = A`: the Neumann Laplacian is self-adjoint. -/
theorem heatSystemL2_A_adjoint : (heatSystemL2 hξ₀).A.adjoint = (heatSystemL2 hξ₀).A :=
  generator_adjoint_diag cosBasis eig bddAbove_eig

/-- `D(A⋆) = H²_N(0, 1)`. -/
theorem heatSystemL2_A_adjoint_domain (η : L2 ℝ 1) :
    η ∈ (heatSystemL2 hξ₀).A.adjoint.domain ↔
      ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (η : ℝ → ℝ) =ᵐ[μI 1] φ := by
  rw [heatSystemL2_A_adjoint]
  exact heatSystemL2_A_domain hξ₀ η

/-- Every `φ ∈ H²_N(0, 1)` is the state `ι_W w` of some `w ∈ W` (`D(A) ⊆ W`). -/
theorem exists_heatSystemL2_ιW_ae_eq {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') :
    ∃ w : (heatData hξ₀).W, ((heatSystemL2 hξ₀).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ := by
  obtain ⟨w, hw⟩ := (heatData hξ₀).exists_ιW_eq cosBasis
    (mem_generator_domain_of_isNeumannH2 h h.memLp.coeFn_toLp)
  refine ⟨w, ?_⟩
  rw [ControlData.sys_ιW, hw]
  exact h.memLp.coeFn_toLp

/-- **`C` is point evaluation at `ξ₀`** (`ex:intro-pde`, `y(t) = x(t, ξ₀)`): if the state
`ι_W w ∈ L²(0, 1)` of `w ∈ W` is the class of `φ ∈ H²_N(0, 1)`, then `C w = φ(ξ₀)`. -/
theorem heatSystemL2_C {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') (w : (heatData hξ₀).W)
    (hw : ((heatSystemL2 hξ₀).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystemL2 hξ₀).C w = φ ξ₀ :=
  (hasSum_heatSystem_C cosBasis hξ₀ w (mem_generator_domain_of_isNeumannH2 h hw)).unique
    (hasSum_obsCoeff_mul_inner h hw (Ioo_subset_Icc_self hξ₀))

/-- **`B⋆` is minus the trace at `0`** (`app:boundary-heat-informative`, `B⋆φ = -φ(0)`): for
`η ∈ D(A⋆) = H²_N(0, 1)` the class of `φ`, `B⋆ η = -φ(0)`. -/
theorem heatSystemL2_Bstar {φ φ' φ'' : ℝ → ℝ} (h : IsNeumannH2 φ φ' φ'') {η : L2 ℝ 1}
    (hη : η ∈ (heatSystemL2 hξ₀).A.adjoint.domain) (hηφ : (η : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystemL2 hξ₀).Bstar ⟨η, hη⟩ = -φ 0 :=
  (hasSum_heatSystem_Bstar cosBasis hξ₀ hη).unique (hasSum_ctrlCoeff_mul_inner h hηφ)

include hξ₀ in
/-- **`ex:boundary-heat-informative` on `L²(0, 1)`** (`ex:intro-pde`): there are spaces
`W ↪ L²(0, 1) ↪ V` and a system on them whose generator is the Neumann Laplacian
(`D(A) = H²_N(0, 1)`, `A φ = φ''`, `A⋆ = A`), whose `B⋆` is minus the trace at `0` (`B` is the
Neumann control `∂_ξ x(t, 0) = u(t)`, see `inner_cosBasis_neumann_control`) and whose `C` is the
point evaluation at `ξ₀` on `H²_N(0, 1) ⊆ W`, such that `hyp:H1`, `hyp:H2` and `hyp:compat` hold
while `B` and `C` are unbounded on `L²(0, 1)`; `ū` is harmonically persistently exciting, `(A, B)`
is approximately controllable in every positive time, and `(ū, x̄)` is informative in `U × W` for
every `x̄₀ ∈ W` and window informative for every `x̄₀ ∈ L²(0, 1)`. -/
theorem exists_boundaryHeat_L2 :
    ∃ (W V : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W) (_ : CompleteSpace W)
      (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ W (L2 ℝ 1) V ℝ),
      sys.SX = diagSemigroup cosBasis eig bddAbove_eig ∧
      (∀ p : L2 ℝ 1 × L2 ℝ 1, p ∈ sys.A.graph ↔
        ∃ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
          (p.2 : ℝ → ℝ) =ᵐ[μI 1] φ'') ∧
      sys.A.adjoint = sys.A ∧
      (∀ (η : L2 ℝ 1) (hη : η ∈ sys.A.adjoint.domain) (φ φ' φ'' : ℝ → ℝ),
        IsNeumannH2 φ φ' φ'' → (η : ℝ → ℝ) =ᵐ[μI 1] φ → sys.Bstar ⟨η, hη⟩ = -φ 0) ∧
      (∀ φ φ' φ'' : ℝ → ℝ, IsNeumannH2 φ φ' φ'' → ∃ w : W, (sys.ιW w : ℝ → ℝ) =ᵐ[μI 1] φ) ∧
      (∀ (w : W) (φ φ' φ'' : ℝ → ℝ), IsNeumannH2 φ φ' φ'' →
        (sys.ιW w : ℝ → ℝ) =ᵐ[μI 1] φ → sys.C w = φ ξ₀) ∧
      (∀ T, sys.H1 T) ∧ (∀ T, sys.H2 T) ∧ sys.Compat ∧
      sys.B 1 ∉ Set.range sys.ιV ∧
      (¬ ∃ K : ℝ, ∀ w : W, sys.ιW w ∈ sys.A.domain → ‖sys.C w‖ ≤ K * ‖sys.ιW w‖) ∧
      heatInput.IsHarmonicPE ∧
      (∀ T > 0, sys.ApproxControllable T) ∧
      (∀ T > 0, ∀ w₀ : W, Informative T heatInput (sys.mildW w₀ heatInput)) ∧
      (∀ T > 0, ∀ T' > 0, ∀ x₀ : L2 ℝ 1,
        WindowInformative T T' heatInput (sys.mild x₀ heatInput)) :=
  ⟨(heatData hξ₀).W, (heatData hξ₀).V, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, heatSystemL2 hξ₀, heatSystemL2_SX hξ₀,
    heatSystemL2_A_graph hξ₀, heatSystemL2_A_adjoint hξ₀,
    fun _ hη _ _ _ h hηφ => heatSystemL2_Bstar hξ₀ h hη hηφ,
    fun _ _ _ h => exists_heatSystemL2_ιW_ae_eq hξ₀ h,
    fun w _ _ _ h hw => heatSystemL2_C hξ₀ h w hw,
    heatSystem_H1 cosBasis hξ₀, heatSystem_H2 cosBasis hξ₀, heatSystem_compat cosBasis hξ₀,
    heatSystem_B_not_mem_range cosBasis hξ₀, heatSystem_C_unbounded cosBasis hξ₀,
    isHarmonicPE_heatInput,
    fun _ hT => heatSystem_approxControllable cosBasis hξ₀ hT,
    fun _ hT w₀ => heatSystem_informative cosBasis hξ₀ hT w₀,
    fun _ hT _ hT' x₀ => heatSystem_windowInformative cosBasis hξ₀ hT hT' x₀⟩

end PDE

end BoundaryHeat

end DataDrivenControl
