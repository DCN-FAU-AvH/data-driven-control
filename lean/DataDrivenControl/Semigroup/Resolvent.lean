module

public import DataDrivenControl.Semigroup.Generator

/-!
# Resolvents

References: Pazy §1.5, Engel–Nagel II.1.

Complex spectra of *real* systems go through `Analysis/Complexification` (a complexified
semigroup is a `C0Semigroup ℂ X_ℂ`); everything here is generic over `𝕜`.

## Main declarations

* `IsResolvent A μ R`: `R ∈ L(E)` maps into `D(A)` and inverts `μ - A` on both sides;
  `resolventSet A`, `resolvent A μ` (junk `0` off the resolvent set) for `A : E →ₗ.[𝕜] E`;
  `IsResolvent.unique`, `resolvent_eq`, `isResolvent_resolvent`, `resolvent_mem_domain`,
  `sub_resolvent`, `resolvent_sub`.
* `resolvent_sub_resolvent`: the resolvent identity; `isOpen_resolventSet`,
  `differentiableOn_resolvent` (holomorphy, `𝕜 = ℂ`), both from the Neumann-series formula
  `R(ν) = (1 + (ν - μ) R(μ))⁻¹ R(μ)` (`isResolvent_of_isUnit`, `resolvent_eq_inverse_mul`).
* `C0Semigroup.rescale S μ`: the rescaled semigroup `e^{-μ t} S t`, with generator `A - μ`
  (`mem_rescale_generator_domain_iff`, `rescale_generator_apply`); it gives
  `C0Semigroup.sub_generator_integral_exp_smul`:
  `(μ - A) ∫₀ᵗ e^{-μ s} S s x ds = x - e^{-μ t} S t x` for every `μ`.
* `C0Semigroup.mem_resolventSet`, `C0Semigroup.resolvent_eq_integral(_real)`: the Laplace
  transform `(μ - A)⁻¹ x = ∫₀^∞ e^{-μ t} S t x dt` for `Re μ > ω`.
* `C0Semigroup.integral_exp_smul_eq(_real)`: the finite-time Laplace identity
  `∫₀ᵗ e^{-μ s} S s x ds = R(μ) x - e^{-μ t} S t R(μ) x` (`app:control-realization`).
* `C0Semigroup.Consistent.resolvent`: consistent semigroups have consistent resolvents;
  `C0Semigroup.resolvent_real_apply`: `R(μ)` commutes with `S t`.

The Laplace-transform results (`C0Semigroup.exists_isResolvent_laplace`) use closedness of the
generator for `(μ - A) R y = y` (limit of the finite-time identity as `t → ∞`) and the
eigenvector characterisation `eigen_iff` for injectivity of `μ - A`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace DataDrivenControl

section LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `R` is the (bounded) resolvent of `A` at `μ`: it maps into `D(A)`, `(μ - A) R y = y` for
all `y`, and `R (μ - A) x = x` for `x ∈ D(A)`. -/
def IsResolvent (A : E →ₗ.[𝕜] E) (μ : 𝕜) (R : E →L[𝕜] E) : Prop :=
  (∀ y : E, ∃ h : R y ∈ A.domain, μ • R y - A ⟨R y, h⟩ = y) ∧
    ∀ x : A.domain, R (μ • (x : E) - A x) = x

/-- The **resolvent set** `ρ(A)`: the `μ` for which `μ - A : D(A) → E` is bijective with bounded
inverse. -/
def resolventSet (A : E →ₗ.[𝕜] E) : Set 𝕜 := {μ | ∃ R : E →L[𝕜] E, IsResolvent A μ R}

open scoped Classical in
/-- The **resolvent** `(μ - A)⁻¹` (junk `0` for `μ ∉ ρ(A)`). -/
def resolvent (A : E →ₗ.[𝕜] E) (μ : 𝕜) : E →L[𝕜] E :=
  if h : ∃ R : E →L[𝕜] E, IsResolvent A μ R then h.choose else 0

variable {A : E →ₗ.[𝕜] E} {μ ν : 𝕜}

theorem IsResolvent.unique {R R' : E →L[𝕜] E} (hR : IsResolvent A μ R)
    (hR' : IsResolvent A μ R') : R = R' := by
  ext y
  obtain ⟨h, hy⟩ := hR'.1 y
  have := hR.2 ⟨R' y, h⟩
  simp only at this
  rw [hy] at this
  exact this

theorem isResolvent_resolvent (h : μ ∈ resolventSet A) : IsResolvent A μ (resolvent A μ) := by
  have h' : ∃ R : E →L[𝕜] E, IsResolvent A μ R := h
  rw [resolvent, dite_eq_left h']; exact h'.choose_spec

theorem resolvent_eq {R : E →L[𝕜] E} (hR : IsResolvent A μ R) : resolvent A μ = R :=
  (isResolvent_resolvent ⟨R, hR⟩).unique hR

theorem resolvent_mem_domain (h : μ ∈ resolventSet A) (y : E) : resolvent A μ y ∈ A.domain :=
  ((isResolvent_resolvent h).1 y).1

/-- `(μ - A) (μ - A)⁻¹ y = y`. -/
theorem sub_resolvent (h : μ ∈ resolventSet A) (y : E) :
    μ • resolvent A μ y - A ⟨resolvent A μ y, resolvent_mem_domain h y⟩ = y :=
  ((isResolvent_resolvent h).1 y).2

/-- `(μ - A)⁻¹ (μ - A) x = x` for `x ∈ D(A)`. -/
theorem resolvent_sub (h : μ ∈ resolventSet A) (x : A.domain) :
    resolvent A μ (μ • (x : E) - A x) = x :=
  (isResolvent_resolvent h).2 x

/-- The **resolvent identity** `R(μ) - R(ν) = (ν - μ) R(μ) R(ν)`. -/
theorem resolvent_sub_resolvent (hμ : μ ∈ resolventSet A) (hν : ν ∈ resolventSet A) :
    resolvent A μ - resolvent A ν = (ν - μ) • (resolvent A μ).comp (resolvent A ν) := by
  ext y
  have ha := resolvent_mem_domain hν y
  have h1 := resolvent_sub hμ ⟨resolvent A ν y, ha⟩
  have h2 := sub_resolvent hν y
  simp only at h1
  have key : μ • resolvent A ν y - A ⟨resolvent A ν y, ha⟩ = (μ - ν) • resolvent A ν y + y :=
    calc μ • resolvent A ν y - A ⟨resolvent A ν y, ha⟩
        = (μ - ν) • resolvent A ν y + (ν • resolvent A ν y - A ⟨resolvent A ν y, ha⟩) := by
          rw [sub_smul]; abel
      _ = (μ - ν) • resolvent A ν y + y := by rw [h2]
  rw [key, map_add, map_smul] at h1
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← h1]
  rw [← neg_sub μ ν, neg_smul]; abel

/-- Resolvents at two points commute. -/
theorem resolvent_comm (hμ : μ ∈ resolventSet A) (hν : ν ∈ resolventSet A) :
    (resolvent A μ).comp (resolvent A ν) = (resolvent A ν).comp (resolvent A μ) := by
  rcases eq_or_ne μ ν with rfl | hne
  · rfl
  have h1 := resolvent_sub_resolvent hμ hν
  have h2 := resolvent_sub_resolvent hν hμ
  have h3 : (ν - μ) • (resolvent A μ).comp (resolvent A ν) =
      (ν - μ) • (resolvent A ν).comp (resolvent A μ) := by
    rw [← h1, ← neg_sub μ ν, neg_smul, ← h2, neg_sub]
  exact smul_right_injective _ (sub_ne_zero.2 hne.symm) h3

/-- **Neumann series** around a point of the resolvent set: if `μ ∈ ρ(A)` and
`1 + (ν - μ) R(μ)` is invertible, then `(1 + (ν - μ) R(μ))⁻¹ R(μ)` is the resolvent at `ν`. -/
theorem isResolvent_of_isUnit (hμ : μ ∈ resolventSet A)
    (hU : IsUnit ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ)) :
    IsResolvent A ν
      (Ring.inverse ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ) * resolvent A μ) := by
  obtain ⟨u, hu⟩ := hU
  set R := resolvent A μ with hR
  have hcomm : Commute R (u : E →L[𝕜] E) := by
    rw [hu]; exact (Commute.one_right R).add_right ((Commute.refl R).smul_right _)
  have hcomm' : Commute R (↑u⁻¹ : E →L[𝕜] E) := hcomm.units_inv_right
  have hu_apply : ∀ z, (u : E →L[𝕜] E) z = z + (ν - μ) • R z := fun z => by
    rw [hu]; rfl
  have hinv : ∀ z, (u : E →L[𝕜] E) ((↑u⁻¹ : E →L[𝕜] E) z) = z := fun z => by
    rw [← mul_apply_eq_comp, u.mul_inv, one_apply_eq_self]
  have hinv' : ∀ z, (↑u⁻¹ : E →L[𝕜] E) ((u : E →L[𝕜] E) z) = z := fun z => by
    rw [← mul_apply_eq_comp, u.inv_mul, one_apply_eq_self]
  rw [← hu, Ring.inverse_unit]
  constructor
  · intro y
    have e : ((↑u⁻¹ : E →L[𝕜] E) * R) y = R ((↑u⁻¹ : E →L[𝕜] E) y) := by
      rw [← hcomm'.eq]; rfl
    rw [e]
    set z := (↑u⁻¹ : E →L[𝕜] E) y
    refine ⟨resolvent_mem_domain hμ z, ?_⟩
    have h1 := sub_resolvent hμ z
    calc ν • R z - A ⟨R z, resolvent_mem_domain hμ z⟩
        = (μ • R z - A ⟨R z, resolvent_mem_domain hμ z⟩) + (ν - μ) • R z := by
          rw [sub_smul]; abel
      _ = (u : E →L[𝕜] E) z := by rw [h1, hu_apply]
      _ = y := hinv y
  · intro x
    have h1 := resolvent_sub hμ x
    have e : ν • (x : E) - A x = (μ • (x : E) - A x) + (ν - μ) • (x : E) := by
      rw [sub_smul]; abel
    show (↑u⁻¹ : E →L[𝕜] E) (R (ν • (x : E) - A x)) = x
    rw [e, map_add, h1, map_smul, ← hu_apply, hinv']

/-- `ν ∈ ρ(A)` if `μ ∈ ρ(A)` and `1 + (ν - μ) R(μ)` is invertible. -/
theorem mem_resolventSet_of_isUnit (hμ : μ ∈ resolventSet A)
    (hU : IsUnit ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ)) : ν ∈ resolventSet A :=
  ⟨_, isResolvent_of_isUnit hμ hU⟩

/-- The Neumann-series formula `R(ν) = (1 + (ν - μ) R(μ))⁻¹ R(μ)`. -/
theorem resolvent_eq_inverse_mul (hμ : μ ∈ resolventSet A)
    (hU : IsUnit ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ)) :
    resolvent A ν =
      Ring.inverse ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ) * resolvent A μ :=
  resolvent_eq (isResolvent_of_isUnit hμ hU)

/-- `1 + (ν - μ) R(μ)` is invertible for `ν` near `μ` (on a Banach space). -/
theorem eventually_isUnit_one_add_smul_resolvent [CompleteSpace E] (μ : 𝕜) :
    ∀ᶠ ν in 𝓝 μ, IsUnit ((1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ) := by
  have hc : Continuous fun ν : 𝕜 => (1 : E →L[𝕜] E) + (ν - μ) • resolvent A μ := by fun_prop
  refine (hc.isOpen_preimage _ Units.isOpen).mem_nhds ?_
  simp

/-- The resolvent set is open. -/
theorem isOpen_resolventSet [CompleteSpace E] (A : E →ₗ.[𝕜] E) : IsOpen (resolventSet A) := by
  refine isOpen_iff_mem_nhds.2 fun μ hμ => ?_
  filter_upwards [eventually_isUnit_one_add_smul_resolvent (A := A) μ] with ν hν
  exact mem_resolventSet_of_isUnit hμ hν

/-- The resolvent is holomorphic on the resolvent set (complex scalars). -/
theorem differentiableOn_resolvent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (A : F →ₗ.[ℂ] F) : DifferentiableOn ℂ (resolvent A) (resolventSet A) := by
  intro μ hμ
  refine DifferentiableAt.differentiableWithinAt ?_
  have hg : DifferentiableAt ℂ
      (fun ν : ℂ => Ring.inverse ((1 : F →L[ℂ] F) + (ν - μ) • resolvent A μ) * resolvent A μ)
      μ := by
    have h1 : DifferentiableAt ℂ (fun ν : ℂ => (1 : F →L[ℂ] F) + (ν - μ) • resolvent A μ) μ := by
      fun_prop
    have h2 : DifferentiableAt ℂ (@Ring.inverse (F →L[ℂ] F) _)
        ((1 : F →L[ℂ] F) + (μ - μ) • resolvent A μ) :=
      differentiableAt_inverse (by simp)
    exact (h2.comp μ h1).mul_const _
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [eventually_isUnit_one_add_smul_resolvent (A := A) μ] with ν hν
  exact resolvent_eq_inverse_mul hμ hν

end LinearPMap

/-! ### Exponentials in `𝕜` -/

/-- `e^r` as an element of `𝕜`: `(e^r : 𝕜) = exp (r : 𝕜)`. -/
theorem ofReal_exp_eq_exp_rclike {𝕜 : Type*} [RCLike 𝕜] (r : ℝ) :
    ((Real.exp r : ℝ) : 𝕜) = NormedSpace.exp ((r : ℝ) : 𝕜) := by
  rw [Real.exp_eq_exp_ℝ, ← RCLike.algebraMap_eq_ofReal, NormedSpace.algebraMap_exp_comm,
    RCLike.algebraMap_eq_ofReal]

/-- `‖exp z‖ = e^{Re z}` for `z : 𝕜`. -/
theorem norm_exp_rclike {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    ‖NormedSpace.exp z‖ = Real.exp (RCLike.re z) := by
  have h1 : ((‖NormedSpace.exp z‖ ^ 2 : ℝ) : 𝕜) = ((Real.exp (RCLike.re z) ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_pow, ← RCLike.mul_conj, ← RCLike.star_def, NormedSpace.star_exp,
      ← NormedSpace.exp_add, RCLike.star_def, RCLike.add_conj, ← Real.exp_nat_mul,
      ofReal_exp_eq_exp_rclike]
    push_cast; ring_nf
  have h2 := RCLike.ofReal_inj.1 h1
  exact (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).1 h2

/-- `e^{c t} → 0` as `t → ∞` for `c < 0`. -/
private theorem tendsto_exp_mul_atTop {c : ℝ} (hc : c < 0) :
    Tendsto (fun t => Real.exp (c * t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hc tendsto_id)

namespace C0Semigroup

/-! ### The rescaled semigroup and the finite-time Laplace identity -/

section Rescale

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (S : C0Semigroup 𝕜 E)

/-- The **rescaled semigroup** `t ↦ e^{-μ t} S t`; its generator is `A - μ`
(`rescale_generator_apply`). -/
def rescale (μ : 𝕜) : C0Semigroup 𝕜 E where
  toFun t := NormedSpace.exp (-(((t : ℝ) : 𝕜) * μ)) • S t
  map_zero' := by simp
  map_add' s t := by
    rw [S.map_add, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      ← NormedSpace.exp_add]
    congr 2
    push_cast; ring
  continuous_apply' x := by
    show Continuous fun t : ℝ≥0 => NormedSpace.exp (-(((t : ℝ) : 𝕜) * μ)) • S t x
    exact (NormedSpace.exp_continuous.comp (by fun_prop)).smul (S.continuous_apply x)

theorem rescale_apply (μ : 𝕜) (t : ℝ≥0) :
    S.rescale μ t = NormedSpace.exp (-(((t : ℝ) : 𝕜) * μ)) • S t := rfl

/-- `(S.rescale μ).real t x = e^{-μ t} S t x` for `t ≥ 0`. -/
theorem rescale_real_apply (μ : 𝕜) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    (S.rescale μ).real t x = NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x := by
  simp only [real, rescale_apply, Real.coe_toNNReal _ ht, _root_.smul_apply]

theorem rescale_rescale (μ ν : 𝕜) : (S.rescale μ).rescale ν = S.rescale (μ + ν) := by
  ext t x
  simp only [rescale_apply, _root_.smul_apply, smul_smul, ← NormedSpace.exp_add]
  congr 2; ring

@[simp] theorem rescale_zero : S.rescale 0 = S := by
  ext t x
  simp [rescale_apply]

/-- `h⁻¹ (e^{-μ h} - 1) → -μ` as `h → 0⁺`. -/
private theorem tendsto_slope_exp (μ : 𝕜) :
    Tendsto (fun h : ℝ => h⁻¹ • (NormedSpace.exp (-((h : 𝕜) * μ)) - 1)) (𝓝[>] 0) (𝓝 (-μ)) := by
  have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-μ) (0 : ℝ)).tendsto_slope_zero_right
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul] at this
  refine this.congr fun h => ?_
  rw [RCLike.real_smul_eq_coe_mul (K := 𝕜) h (-μ), mul_neg]

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- If `h⁻¹ (S h x - x) → y`, then the difference quotients of the rescaled semigroup tend to
`y - μ x`. -/
theorem tendsto_diffQuot_rescale (μ : 𝕜) {x y : E}
    (h : Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y)) :
    Tendsto ((S.rescale μ).diffQuot x) (𝓝[>] 0) (𝓝 (y - μ • x)) := by
  have he : Tendsto (fun h : ℝ => NormedSpace.exp (-((h : 𝕜) * μ))) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun h : ℝ => NormedSpace.exp (-((h : 𝕜) * μ)) :=
      NormedSpace.exp_continuous.comp (by fun_prop)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim := (he.smul h).add ((tendsto_slope_exp μ).smul_const x)
  rw [one_smul, neg_smul, ← sub_eq_add_neg] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun h hh => ?_)
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  simp only [diffQuot, S.rescale_real_apply μ hh']
  set e := NormedSpace.exp (-((h : 𝕜) * μ))
  calc e • (h⁻¹ • (S.real h x - x)) + (h⁻¹ • (e - 1)) • x
      = h⁻¹ • (e • (S.real h x - x)) + h⁻¹ • (e • x - x) := by
        rw [smul_comm e h⁻¹, smul_assoc, sub_smul, one_smul]
    _ = h⁻¹ • (e • S.real h x - x) := by
        rw [← smul_add, smul_sub]; congr 1; abel

/-- The rescaled semigroup has the same generator domain. -/
theorem mem_rescale_generator_domain_iff (μ : 𝕜) {x : E} :
    x ∈ (S.rescale μ).generator.domain ↔ x ∈ S.generator.domain := by
  constructor
  · rintro ⟨y, hy⟩
    have := (S.rescale μ).tendsto_diffQuot_rescale (-μ) hy
    rw [rescale_rescale, add_neg_cancel, rescale_zero] at this
    exact ⟨_, this⟩
  · rintro ⟨y, hy⟩
    exact ⟨_, S.tendsto_diffQuot_rescale μ hy⟩

/-- The generator of the rescaled semigroup is `A - μ`. -/
theorem rescale_generator_apply (μ : 𝕜) {x : E} (hx : x ∈ S.generator.domain) :
    (S.rescale μ).generator ⟨x, (S.mem_rescale_generator_domain_iff μ).2 hx⟩ =
      S.generator ⟨x, hx⟩ - μ • x :=
  (S.rescale μ).generator_apply_eq _ (S.tendsto_diffQuot_rescale μ (S.tendsto_generator ⟨x, hx⟩))

omit [IsScalarTower ℝ 𝕜 E] in
/-- `∫₀ᵗ e^{-μ s} S s x ds` is the orbit integral of the rescaled semigroup. -/
theorem integral_exp_smul_eq_integral_rescale (μ : 𝕜) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x =
      ∫ s in (0 : ℝ)..t, (S.rescale μ).real s x := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  exact (S.rescale_real_apply μ hs.1 x).symm

/-- `∫₀ᵗ e^{-μ s} S s x ds ∈ D(A)`. -/
theorem integral_exp_smul_mem_domain (μ : 𝕜) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x) ∈
      S.generator.domain := by
  rw [S.integral_exp_smul_eq_integral_rescale μ x ht, ← S.mem_rescale_generator_domain_iff μ]
  exact (S.rescale μ).integral_mem_generator_domain x ht

/-- The finite-time Laplace identity before inverting `μ - A` (`app:control-realization`):
`(μ - A) ∫₀ᵗ e^{-μ s} S s x ds = x - e^{-μ t} S t x`, for every `μ`. -/
theorem sub_generator_integral_exp_smul [CompleteSpace E] (μ : 𝕜) (x : E) {t : ℝ}
    (ht : 0 ≤ t) :
    μ • (∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x) -
        S.generator ⟨_, S.integral_exp_smul_mem_domain μ x ht⟩ =
      x - NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x := by
  have hI := S.integral_exp_smul_eq_integral_rescale μ x ht
  have key := (S.rescale μ).generator_integral x ht
  have hdom := S.integral_exp_smul_mem_domain μ x ht
  have e : (⟨∫ s in (0 : ℝ)..t, (S.rescale μ).real s x,
      (S.rescale μ).integral_mem_generator_domain x ht⟩ : (S.rescale μ).generator.domain) =
      ⟨_, (S.mem_rescale_generator_domain_iff μ).2 hdom⟩ := Subtype.ext hI.symm
  rw [e, S.rescale_generator_apply μ hdom, S.rescale_real_apply μ ht] at key
  rw [← neg_sub, key]
  abel

/-- `A ∫₀ᵗ e^{-μ s} S s x ds = μ ∫₀ᵗ e^{-μ s} S s x ds - x + e^{-μ t} S t x`. -/
theorem generator_integral_exp_smul [CompleteSpace E] (μ : 𝕜) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    S.generator ⟨_, S.integral_exp_smul_mem_domain μ x ht⟩ =
      μ • (∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x) - x +
        NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x := by
  rw [← sub_sub_cancel (μ • (∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x))
    (S.generator ⟨_, S.integral_exp_smul_mem_domain μ x ht⟩),
    S.sub_generator_integral_exp_smul μ x ht]
  abel

/-- Resolvents commute with the semigroup: `R(μ) S t x = S t R(μ) x`. -/
theorem resolvent_real_apply {μ : 𝕜} (hμ : μ ∈ resolventSet S.generator) (t : ℝ) (x : E) :
    resolvent S.generator μ (S.real t x) = S.real t (resolvent S.generator μ x) := by
  have hd := S.real_mem_generator_domain (resolvent_mem_domain hμ x) t
  have h := resolvent_sub hμ ⟨_, hd⟩
  simp only at h
  rw [S.generator_real_apply (resolvent_mem_domain hμ x) t, ← map_smul, ← map_sub,
    sub_resolvent hμ x] at h
  exact h

/-! ### The Laplace transform of the semigroup -/

variable {M ω : ℝ}

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `‖e^{-μ t} S t x‖ ≤ M e^{(ω - Re μ) t} ‖x‖` for `t ≥ 0`. -/
theorem norm_exp_smul_real_apply_le (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t)) (μ : 𝕜)
    {t : ℝ} (ht : 0 ≤ t) (x : E) :
    ‖NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x‖ ≤
      M * Real.exp ((ω - RCLike.re μ) * t) * ‖x‖ := by
  rw [norm_smul, norm_exp_rclike]
  have h1 : ‖S.real t x‖ ≤ M * Real.exp (ω * t) * ‖x‖ := by
    refine ((S.real t).le_opNorm x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have := hS t.toNNReal
    rw [Real.coe_toNNReal _ ht] at this
    exact this
  have hre : RCLike.re (-((t : 𝕜) * μ)) = -(t * RCLike.re μ) := by
    rw [map_neg, RCLike.re_ofReal_mul]
  calc Real.exp (RCLike.re (-((t : 𝕜) * μ))) * ‖S.real t x‖
      ≤ Real.exp (-(t * RCLike.re μ)) * (M * Real.exp (ω * t) * ‖x‖) := by
        rw [hre]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = M * Real.exp ((ω - RCLike.re μ) * t) * ‖x‖ := by
        rw [show (ω - RCLike.re μ) * t = -(t * RCLike.re μ) + ω * t by ring, Real.exp_add]; ring

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Integrability of `t ↦ e^{-μ t} S t x` on `(0, ∞)` for `Re μ > ω`. -/
theorem integrableOn_exp_smul_real_apply (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t))
    {μ : 𝕜} (hμ : ω < RCLike.re μ) (x : E) :
    IntegrableOn (fun t : ℝ => NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x) (Ioi 0) := by
  have hc : Continuous fun t : ℝ => NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x :=
    (NormedSpace.exp_continuous.comp (by fun_prop)).smul (S.continuous_real_apply x)
  refine Integrable.mono' (Integrable.mul_const (Integrable.const_mul
    (integrableOn_exp_mul_Ioi (sub_neg.2 hμ) 0) M) ‖x‖) hc.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  exact S.norm_exp_smul_real_apply_le hS μ (le_of_lt ht) x

/-- For `Re μ > ω`, the **Laplace transform** `x ↦ ∫₀^∞ e^{-μ t} S t x dt` is the resolvent of
`A` at `μ`, with norm at most `M / (Re μ - ω)` (Pazy Thm 1.5.3, Engel–Nagel II.1.10). -/
theorem exists_isResolvent_laplace [CompleteSpace E]
    (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t)) {μ : 𝕜} (hμ : ω < RCLike.re μ) :
    ∃ R : E →L[𝕜] E, IsResolvent S.generator μ R ∧
      (∀ x, R x = ∫ t in Ioi (0 : ℝ), NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x) ∧
      ‖R‖ ≤ M / (RCLike.re μ - ω) := by
  have hM : 0 ≤ M := by
    have h0 := (norm_nonneg (S 0)).trans (hS 0)
    simpa using h0
  have hd : 0 < RCLike.re μ - ω := sub_pos.2 hμ
  have hint := S.integrableOn_exp_smul_real_apply hS hμ
  let L : E →ₗ[𝕜] E :=
    { toFun := fun x => ∫ t in Ioi (0 : ℝ), NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x
      map_add' := fun x y => by
        rw [← integral_add (hint x) (hint y)]
        congr 1; funext t
        rw [map_add, smul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext t
        rw [map_smul]; exact smul_comm _ _ _ }
  have hbound : ∀ x, ‖L x‖ ≤ M / (RCLike.re μ - ω) * ‖x‖ := by
    intro x
    have h1 : ‖L x‖ ≤ ∫ t in Ioi (0 : ℝ), M * Real.exp ((ω - RCLike.re μ) * t) * ‖x‖ :=
      norm_integral_le_of_norm_le (Integrable.mul_const (Integrable.const_mul
        (integrableOn_exp_mul_Ioi (sub_neg.2 hμ) 0) M) ‖x‖)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
          S.norm_exp_smul_real_apply_le hS μ (le_of_lt ht) x))
    have h2 : ∫ t in Ioi (0 : ℝ), M * Real.exp ((ω - RCLike.re μ) * t) * ‖x‖ =
        M / (RCLike.re μ - ω) * ‖x‖ := by
      rw [integral_mul_const, integral_const_mul, integral_exp_mul_Ioi (sub_neg.2 hμ), mul_zero,
        Real.exp_zero, show -1 / (ω - RCLike.re μ) = 1 / (RCLike.re μ - ω) by
          rw [← neg_sub, div_neg, neg_div, neg_neg]]
      ring
    exact h1.trans h2.le
  let R := L.mkContinuous (M / (RCLike.re μ - ω)) hbound
  have hR : ∀ x, R x = ∫ t in Ioi (0 : ℝ), NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x :=
    fun x => rfl
  -- `(μ - A) R y = y`: let `t → ∞` in the finite-time identity; `A` is closed.
  have ha : ∀ y, ∃ h : R y ∈ S.generator.domain, μ • R y - S.generator ⟨R y, h⟩ = y := by
    intro y
    have hI : Tendsto (fun T : ℝ =>
        ∫ s in (0 : ℝ)..T, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s y) atTop (𝓝 (R y)) :=
      intervalIntegral_tendsto_integral_Ioi 0 (hint y) tendsto_id
    have htail : Tendsto (fun T : ℝ => NormedSpace.exp (-((T : 𝕜) * μ)) • S.real T y) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (by
        simpa using ((tendsto_exp_mul_atTop (sub_neg.2 hμ)).const_mul M).mul_const ‖y‖)
      filter_upwards [eventually_ge_atTop 0] with T hT
      exact S.norm_exp_smul_real_apply_le hS μ hT y
    have hAI : Tendsto (fun T : ℝ =>
        μ • (∫ s in (0 : ℝ)..T, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s y) - y +
          NormedSpace.exp (-((T : 𝕜) * μ)) • S.real T y) atTop (𝓝 (μ • R y - y)) := by
      simpa using ((hI.const_smul μ).sub_const y).add htail
    have hgraph : ((R y, μ • R y - y) : E × E) ∈ S.generator.graph := by
      refine S.generator_isClosed.mem_of_tendsto (hI.prodMk_nhds hAI) ?_
      filter_upwards [eventually_ge_atTop 0] with T hT
      rw [← S.generator_integral_exp_smul μ y hT]
      exact S.generator.mem_graph ⟨_, S.integral_exp_smul_mem_domain μ y hT⟩
    obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).1 hgraph
    dsimp only at hz1 hz2
    have hRy : R y ∈ S.generator.domain := hz1 ▸ z.2
    refine ⟨hRy, ?_⟩
    have e : S.generator ⟨R y, hRy⟩ = μ • R y - y := by
      rw [← hz2]; congr 1; exact Subtype.ext hz1.symm
    rw [e]; abel
  refine ⟨R, ⟨ha, fun x => ?_⟩, hR, L.mkContinuous_norm_le (div_nonneg hM hd.le) hbound⟩
  -- `R (μ - A) x = x`: `μ - A` is injective, since an eigenvector `A w = μ w` has
  -- `‖w‖ = ‖e^{-μ t} S t w‖ ≤ M e^{(ω - Re μ) t} ‖w‖ → 0`.
  obtain ⟨hz, hz'⟩ := ha (μ • (x : E) - S.generator x)
  set w : S.generator.domain := ⟨R (μ • (x : E) - S.generator x), hz⟩ - x with hw_def
  have hw : S.generator ⟨(w : E), w.2⟩ = μ • (w : E) := by
    rw [hw_def, LinearPMap.map_sub, Submodule.coe_sub, smul_sub]
    exact (sub_eq_sub_iff_sub_eq_sub.1 hz').symm
  have heig := (S.eigen_iff (w : E) μ).2 ⟨w.2, hw⟩
  have hbd : ∀ T : ℝ, 0 ≤ T → ‖(w : E)‖ ≤ M * Real.exp ((ω - RCLike.re μ) * T) * ‖(w : E)‖ := by
    intro T hT
    have e : NormedSpace.exp (-((T : 𝕜) * μ)) • S.real T (w : E) = (w : E) := by
      rw [real, heig, Real.coe_toNNReal _ hT, smul_smul, ← NormedSpace.exp_add, neg_add_cancel,
        NormedSpace.exp_zero, one_smul]
    calc ‖(w : E)‖ = ‖NormedSpace.exp (-((T : 𝕜) * μ)) • S.real T (w : E)‖ := by rw [e]
      _ ≤ _ := S.norm_exp_smul_real_apply_le hS μ hT _
  have hlim : Tendsto (fun T : ℝ => M * Real.exp ((ω - RCLike.re μ) * T) * ‖(w : E)‖) atTop
      (𝓝 0) := by
    simpa using ((tendsto_exp_mul_atTop (sub_neg.2 hμ)).const_mul M).mul_const ‖(w : E)‖
  have hw0 : ‖(w : E)‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact hbd T hT
  have : (w : E) = 0 := norm_le_zero_iff.1 hw0
  rw [hw_def, Submodule.coe_sub, sub_eq_zero] at this
  exact this

end Rescale

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

variable (S : C0Semigroup 𝕜 E)

/-- Every `μ` with `Re μ > ω` is in the resolvent set, if `‖S t‖ ≤ M e^{ω t}`. -/
theorem mem_resolventSet {M ω : ℝ} (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t)) {μ : 𝕜}
    (hμ : ω < RCLike.re μ) : μ ∈ resolventSet S.generator :=
  let ⟨R, hR, _⟩ := S.exists_isResolvent_laplace hS hμ
  ⟨R, hR⟩

/-- The resolvent as a **Laplace transform**: `(μ - A)⁻¹ x = ∫₀^∞ e^{-μ t} S t x dt` for
`Re μ > ω` (for `𝕜 = ℂ`, `NormedSpace.exp = Complex.exp` by `Complex.exp_eq_exp_ℂ`). -/
theorem resolvent_eq_integral {M ω : ℝ} (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t))
    {μ : 𝕜} (hμ : ω < RCLike.re μ) (x : E) :
    resolvent S.generator μ x = ∫ t in Ioi (0 : ℝ), NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t x := by
  obtain ⟨R, hR, hRx, -⟩ := S.exists_isResolvent_laplace hS hμ
  rw [resolvent_eq hR, hRx]

/-- The Laplace transform formula for real `μ > ω`. -/
theorem resolvent_eq_integral_real {M ω : ℝ} (hS : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t))
    {μ : ℝ} (hμ : ω < μ) (x : E) :
    resolvent S.generator (μ : 𝕜) x = ∫ t in Ioi (0 : ℝ), Real.exp (-(t * μ)) • S.real t x := by
  rw [S.resolvent_eq_integral hS (by rwa [RCLike.ofReal_re]) x]
  congr 1; funext t
  rw [real_exp_smul (𝕜 := 𝕜)]
  push_cast; rfl

/-- The **finite-time Laplace identity** (`app:control-realization`): for `μ ∈ ρ(A)` and
`t ≥ 0`, `∫₀ᵗ e^{-μ s} S s x ds = R(μ) x - e^{-μ t} S t R(μ) x`. -/
theorem integral_exp_smul_eq {μ : 𝕜} (hμ : μ ∈ resolventSet S.generator) {t : ℝ} (ht : 0 ≤ t)
    (x : E) :
    ∫ s in (0 : ℝ)..t, NormedSpace.exp (-((s : 𝕜) * μ)) • S.real s x =
      resolvent S.generator μ x -
        NormedSpace.exp (-((t : 𝕜) * μ)) • S.real t (resolvent S.generator μ x) := by
  have h1 := resolvent_sub hμ ⟨_, S.integral_exp_smul_mem_domain μ x ht⟩
  simp only at h1
  rw [S.sub_generator_integral_exp_smul μ x ht, map_sub, map_smul,
    S.resolvent_real_apply hμ] at h1
  exact h1.symm

/-- The finite-time Laplace identity for real `μ`. -/
theorem integral_exp_smul_eq_real {μ : ℝ} (hμ : (μ : 𝕜) ∈ resolventSet S.generator) {t : ℝ}
    (ht : 0 ≤ t) (x : E) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(s * μ)) • S.real s x =
      resolvent S.generator (μ : 𝕜) x -
        Real.exp (-(t * μ)) • S.real t (resolvent S.generator (μ : 𝕜) x) := by
  have e : ∀ (s : ℝ) (v : E),
      Real.exp (-(s * μ)) • v = NormedSpace.exp (-((s : 𝕜) * (μ : 𝕜))) • v := fun s v => by
    rw [real_exp_smul (𝕜 := 𝕜)]; push_cast; rfl
  simp only [e]
  exact S.integral_exp_smul_eq hμ ht x

omit [CompleteSpace E] in
/-- Consistent semigroups have consistent resolvents: if `ι ∘ S' t = S t ∘ ι` then
`ι ∘ R(μ, A') = R(μ, A) ∘ ι` on the common resolvent set. -/
theorem Consistent.resolvent {ι : F →L[𝕜] E} {S' : C0Semigroup 𝕜 F} (h : Consistent ι S' S)
    {μ : 𝕜} (hμ' : μ ∈ resolventSet S'.generator) (hμ : μ ∈ resolventSet S.generator) (x : F) :
    ι (DataDrivenControl.resolvent S'.generator μ x) =
      DataDrivenControl.resolvent S.generator μ (ι x) := by
  set y := DataDrivenControl.resolvent S'.generator μ x
  have hy : y ∈ S'.generator.domain := resolvent_mem_domain hμ' x
  have hιy := h.mem_generator_domain S hy
  have key := resolvent_sub hμ ⟨ι y, hιy⟩
  simp only at key
  rw [h.generator_apply S hy, ← map_smul, ← map_sub] at key
  rw [← key, sub_resolvent hμ' x]

end C0Semigroup

end DataDrivenControl
