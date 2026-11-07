module

public import DataDrivenControl.Semigroup.Basic

/-!
# The generator of a C₀-semigroup

The scalar field is `𝕜` (`RCLike`); difference quotients and derivatives use the real scalar
action, so `E` also carries `[NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]` (automatic for `𝕜 = ℝ`
and for complex spaces).

## Main declarations

* `C0Semigroup.diffQuot S x h = h⁻¹ • (S h x - x)`;
* `C0Semigroup.generator S : E →ₗ.[𝕜] E` (Mathlib's `LinearPMap`): domain the `x` for which
  `diffQuot S x h` has a limit as `h → 0⁺`, value that limit (`tendsto_generator`,
  `generator_apply_eq`, `mem_generator_domain_of_tendsto`);
* `dense_generator_domain`, `generator_isClosed`;
* `mem_generator_domain_apply`, `generator_apply_apply`: `S t` preserves `D(A)` and commutes
  with `A`;
* `hasDerivAt_real_apply`, `hasDerivWithinAt_real_apply`: `d/dt S t x = S t (A x)`;
* `integral_mem_generator_domain`, `generator_integral`, `real_apply_sub_eq_integral`:
  `A ∫₀ᵗ S s x ds = S t x - x` and `S t x - x = ∫₀ᵗ S s (A x) ds`;
* `eigen_iff_real`, `eigen_iff`: `S t η = e^{μ t} η` for all `t` iff `A η = μ η`;
* `ext_of_generator`: a C₀-semigroup is determined by its generator;
* `Consistent.mem_generator_domain`, `Consistent.generator_apply`: consistent semigroups have
  consistent generators.

`dense_generator_domain`, `generator_isClosed`, `hasDerivAt_real_apply`, `generator_integral`,
`real_apply_sub_eq_integral` (for `0 ≤ t`) and `ext_of_generator` assume `[CompleteSpace E]`: on
incomplete spaces Bochner integrals vanish, uniform boundedness fails, and these statements
are false (see `Semigroup/Basic`).  Extra API:
`diffQuot_apply`, `tendsto_diffQuot_apply`, `real_mem_generator_domain`, `generator_real_apply`,
`hasDerivAt_integral_real_apply`, `tendsto_inv_smul_integral`, `diffQuot_integral`,
`tendsto_diffQuot_integral`, `real_exp_smul`, and `eq_real_apply_of_hasDerivWithinAt`
(uniqueness for the abstract Cauchy problem).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace DataDrivenControl

namespace C0Semigroup

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

variable (S : C0Semigroup 𝕜 E)

/-- The difference quotient `h⁻¹ • (S h x - x)`. -/
def diffQuot (x : E) (h : ℝ) : E := h⁻¹ • (S.real h x - x)

omit [IsScalarTower ℝ 𝕜 E] in
theorem diffQuot_add (x y : E) (h : ℝ) :
    S.diffQuot (x + y) h = S.diffQuot x h + S.diffQuot y h := by
  simp only [diffQuot, map_add, ← smul_add]
  congr 1; abel

theorem diffQuot_smul (c : 𝕜) (x : E) (h : ℝ) : S.diffQuot (c • x) h = c • S.diffQuot x h := by
  simp only [diffQuot, map_smul, ← smul_sub]
  exact smul_comm _ _ _

omit [IsScalarTower ℝ 𝕜 E] in
@[simp] theorem diffQuot_zero (h : ℝ) : S.diffQuot 0 h = 0 := by simp [diffQuot]

/-- The domain of the generator: the `x` whose difference quotients converge as `h → 0⁺`. -/
def generatorDomain : Submodule 𝕜 E where
  carrier := {x | ∃ y, Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y)}
  zero_mem' := ⟨0, tendsto_const_nhds.congr fun h => (S.diffQuot_zero h).symm⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, (ha.add hb).congr fun h => (S.diffQuot_add x y h).symm⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, (ha.const_smul c).congr fun h => (S.diffQuot_smul c x h).symm⟩

theorem tendsto_limUnder_diffQuot {x : E} (hx : x ∈ S.generatorDomain) :
    Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 (limUnder (𝓝[>] (0 : ℝ)) (S.diffQuot x))) :=
  tendsto_nhds_limUnder hx

/-- The **generator** `A` of `S`, a partially defined linear operator (`LinearPMap`):
`A x = lim_{h → 0⁺} h⁻¹ (S h x - x)` on the set of `x` where the limit exists. -/
def generator : E →ₗ.[𝕜] E where
  domain := S.generatorDomain
  toFun :=
    { toFun := fun x => limUnder (𝓝[>] (0 : ℝ)) (S.diffQuot x)
      map_add' := fun x y => by
        refine tendsto_nhds_unique (S.tendsto_limUnder_diffQuot (x + y).2) ?_
        exact ((S.tendsto_limUnder_diffQuot x.2).add (S.tendsto_limUnder_diffQuot y.2)).congr
          fun h => (S.diffQuot_add x y h).symm
      map_smul' := fun c x => by
        refine tendsto_nhds_unique (S.tendsto_limUnder_diffQuot (c • x).2) ?_
        exact ((S.tendsto_limUnder_diffQuot x.2).const_smul c).congr
          fun h => (S.diffQuot_smul c x h).symm }

theorem generator_domain : S.generator.domain = S.generatorDomain := rfl

theorem mem_generator_domain_iff {x : E} :
    x ∈ S.generator.domain ↔ ∃ y, Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y) := Iff.rfl

theorem mem_generator_domain_of_tendsto {x y : E} (h : Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y)) :
    x ∈ S.generator.domain := ⟨y, h⟩

/-- `h⁻¹ (S h x - x) → A x` as `h → 0⁺`. -/
theorem tendsto_generator (x : S.generator.domain) :
    Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 (S.generator x)) :=
  S.tendsto_limUnder_diffQuot x.2

/-- The generator is the limit of the difference quotients. -/
theorem generator_apply_eq {x : E} (hx : x ∈ S.generator.domain) {y : E}
    (h : Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y)) : S.generator ⟨x, hx⟩ = y :=
  tendsto_nhds_unique (S.tendsto_generator ⟨x, hx⟩) h

/-! ### Basic properties of the generator -/

/-- `s ↦ s - t` maps `𝓝[>] t` to `𝓝[>] 0`. -/
private theorem tendsto_sub_nhdsGT (t : ℝ) : Tendsto (fun s => s - t) (𝓝[>] t) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_id.sub continuous_const).tendsto' t 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun s hs => sub_pos.2 hs

/-- `S t` commutes with the difference quotients. -/
theorem diffQuot_apply (t : ℝ≥0) (x : E) (h : ℝ) :
    S.diffQuot (S t x) h = S t (S.diffQuot x h) := by
  rw [diffQuot, diffQuot, ContinuousLinearMap.map_smul_of_tower, map_sub, real,
    S.comm_apply h.toNNReal t x]

/-- `h⁻¹ (S h (S t x) - S t x) → S t (A x)`. -/
theorem tendsto_diffQuot_apply (x : S.generator.domain) (t : ℝ≥0) :
    Tendsto (S.diffQuot (S t x)) (𝓝[>] 0) (𝓝 (S t (S.generator x))) :=
  (((S t).continuous.tendsto _).comp (S.tendsto_generator x)).congr fun h =>
    (S.diffQuot_apply t x h).symm

/-- `S t` preserves the domain of the generator. -/
theorem mem_generator_domain_apply {x : E} (hx : x ∈ S.generator.domain) (t : ℝ≥0) :
    S t x ∈ S.generator.domain :=
  ⟨_, S.tendsto_diffQuot_apply ⟨x, hx⟩ t⟩

/-- `A (S t x) = S t (A x)` for `x ∈ D(A)`. -/
theorem generator_apply_apply {x : E} (hx : x ∈ S.generator.domain) (t : ℝ≥0) :
    S.generator ⟨S t x, S.mem_generator_domain_apply hx t⟩ = S t (S.generator ⟨x, hx⟩) :=
  S.generator_apply_eq _ (S.tendsto_diffQuot_apply ⟨x, hx⟩ t)

/-- Real-time version of `mem_generator_domain_apply`. -/
theorem real_mem_generator_domain {x : E} (hx : x ∈ S.generator.domain) (t : ℝ) :
    S.real t x ∈ S.generator.domain :=
  S.mem_generator_domain_apply hx _

/-- Real-time version of `generator_apply_apply`. -/
theorem generator_real_apply {x : E} (hx : x ∈ S.generator.domain) (t : ℝ) :
    S.generator ⟨S.real t x, S.real_mem_generator_domain hx t⟩ =
      S.real t (S.generator ⟨x, hx⟩) :=
  S.generator_apply_apply hx _

/-- The right derivative of `t ↦ S t x` at `t ≥ 0` is `S t (A x)` for `x ∈ D(A)`. -/
theorem hasDerivWithinAt_real_apply (x : S.generator.domain) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => S.real s x) (S.real t (S.generator x)) (Ici t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  refine (((S.real t).continuous.tendsto _).comp
    ((S.tendsto_generator x).comp (tendsto_sub_nhdsGT t))).congr'
    (eventually_nhdsWithin_of_forall fun s hs => ?_)
  have hs' : 0 ≤ s - t := (sub_pos.2 hs).le
  have e : S.real t (S.real (s - t) x) = S.real s x := by
    rw [← S.real_add_apply ht hs', add_sub_cancel]
  simp only [Function.comp_apply, slope_def_module, diffQuot,
    ContinuousLinearMap.map_smul_of_tower, map_sub, e]

/-! ### Integrals of orbits (Banach spaces) -/

omit [IsScalarTower ℝ 𝕜 E] in
/-- FTC for orbits: `d/du ∫₀ᵘ S s x ds = S u x`. -/
theorem hasDerivAt_integral_real_apply [CompleteSpace E] (x : E) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, S.real s x) (S.real t x) t :=
  ((S.continuous_real_apply x).integral_hasStrictDerivAt 0 t).hasDerivAt

omit [IsScalarTower ℝ 𝕜 E] in
/-- `h⁻¹ ∫₀ʰ S s y ds → y` as `h → 0⁺`. -/
theorem tendsto_inv_smul_integral [CompleteSpace E] (y : E) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ s in (0 : ℝ)..h, S.real s y) (𝓝[>] 0) (𝓝 y) := by
  simpa using (S.hasDerivAt_integral_real_apply y 0).tendsto_slope_zero_right

omit [IsScalarTower ℝ 𝕜 E] in
/-- The difference quotient of `∫₀ᵗ S s x ds`. -/
theorem diffQuot_integral [CompleteSpace E] (x : E) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    S.diffQuot (∫ s in (0 : ℝ)..t, S.real s x) h =
      h⁻¹ • ((∫ s in (0 : ℝ)..t + h, S.real s x) - ∫ s in (0 : ℝ)..t, S.real s x) -
        h⁻¹ • ∫ s in (0 : ℝ)..h, S.real s x := by
  have hint : ∀ a b, IntervalIntegrable (fun s => S.real s x) volume a b := fun a b =>
    (S.continuous_real_apply x).intervalIntegrable a b
  have e0 : (∫ s in (0 : ℝ)..t, S.real h (S.real s x)) = ∫ s in (0 : ℝ)..t, S.real (s + h) x := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by rw [uIcc_of_le ht] at hs; exact hs.1
    show S.real h (S.real s x) = S.real (s + h) x
    rw [S.real_comm_apply h s x, ← S.real_add_apply hs0 hh]
  have e1 : S.real h (∫ s in (0 : ℝ)..t, S.real s x) =
      (∫ s in (0 : ℝ)..t + h, S.real s x) - ∫ s in (0 : ℝ)..h, S.real s x := by
    calc S.real h (∫ s in (0 : ℝ)..t, S.real s x)
        = ∫ s in (0 : ℝ)..t, S.real h (S.real s x) :=
          ((S.real h).intervalIntegral_comp_comm (hint 0 t)).symm
      _ = ∫ s in (0 : ℝ)..t, S.real (s + h) x := e0
      _ = ∫ s in (0 : ℝ) + h..t + h, S.real s x :=
          intervalIntegral.integral_comp_add_right (fun s => S.real s x) h
      _ = (∫ s in (0 : ℝ)..t + h, S.real s x) - ∫ s in (0 : ℝ)..h, S.real s x := by
          rw [zero_add, intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [diffQuot, e1, ← smul_sub]
  congr 1
  abel

omit [IsScalarTower ℝ 𝕜 E] in
/-- `h⁻¹ (S h - 1) ∫₀ᵗ S s x ds → S t x - x`. -/
theorem tendsto_diffQuot_integral [CompleteSpace E] (x : E) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (S.diffQuot (∫ s in (0 : ℝ)..t, S.real s x)) (𝓝[>] 0) (𝓝 (S.real t x - x)) := by
  refine (((S.hasDerivAt_integral_real_apply x t).tendsto_slope_zero_right).sub
    (S.tendsto_inv_smul_integral x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (S.diffQuot_integral x ht (le_of_lt hh)).symm

/-- `∫₀ᵗ S s x ds ∈ D(A)` for every `x` and `t ≥ 0`. -/
theorem integral_mem_generator_domain (x : E) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, S.real s x) ∈ S.generator.domain := by
  by_cases hE : CompleteSpace E
  · exact ⟨_, S.tendsto_diffQuot_integral x ht⟩
  · rw [intervalIntegral.integral_of_le ht, integral_of_not_completeSpace hE]
    exact S.generator.domain.zero_mem

/-- `A ∫₀ᵗ S s x ds = S t x - x` (Banach space). -/
theorem generator_integral [CompleteSpace E] (x : E) {t : ℝ} (ht : 0 ≤ t) :
    S.generator ⟨∫ s in (0 : ℝ)..t, S.real s x, S.integral_mem_generator_domain x ht⟩ =
      S.real t x - x :=
  S.generator_apply_eq _ (S.tendsto_diffQuot_integral x ht)

/-- The generator is densely defined (Banach space): `t⁻¹ ∫₀ᵗ S s x ds → x`. -/
theorem dense_generator_domain [CompleteSpace E] : Dense (S.generator.domain : Set E) := fun x =>
  mem_closure_of_tendsto (S.tendsto_inv_smul_integral x)
    (eventually_nhdsWithin_of_forall fun _h hh =>
      S.generator.domain.smul_of_tower_mem _ (S.integral_mem_generator_domain x (le_of_lt hh)))

/-- `S t x - x = ∫₀ᵗ S s (A x) ds` for `x ∈ D(A)` and `t ≥ 0` (Banach space). -/
theorem real_apply_sub_eq_integral [CompleteSpace E] (x : S.generator.domain) (t : ℝ)
    (ht : 0 ≤ t) : S.real t x - x = ∫ s in (0 : ℝ)..t, S.real s (S.generator x) := by
  have hcont : Continuous fun s => S.real s x - x - ∫ r in (0 : ℝ)..s, S.real r (S.generator x) :=
    ((S.continuous_real_apply x).sub continuous_const).sub
      (continuous_iff_continuousAt.2 fun s => (S.hasDerivAt_integral_real_apply _ s).continuousAt)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt
      (fun s => S.real s x - x - ∫ r in (0 : ℝ)..s, S.real r (S.generator x)) 0 (Ici s) s := by
    intro s hs
    simpa using ((S.hasDerivWithinAt_real_apply x hs.1).sub_const (x : E)).fun_sub
      (S.hasDerivAt_integral_real_apply (S.generator x) s).hasDerivWithinAt
  have := constant_of_has_deriv_right_zero hcont.continuousOn hderiv t ⟨ht, le_rfl⟩
  simp only [real_zero, one_apply_eq_self, sub_self, intervalIntegral.integral_same] at this
  exact sub_eq_zero.1 this

/-- `d/dt S t x = S t (A x)` for `x ∈ D(A)` and `t > 0` (Banach space). -/
theorem hasDerivAt_real_apply [CompleteSpace E] (x : S.generator.domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => S.real s x) (S.real t (S.generator x)) t := by
  refine ((S.hasDerivAt_integral_real_apply (S.generator x) t).const_add
    (x : E)).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [← S.real_apply_sub_eq_integral x s hs.le]
  abel

/-- The generator is closed (Banach space).  Its graph is
`{(x, y) | ∀ h > 0, S h x - x = ∫₀ʰ S s y ds}`. -/
theorem generator_isClosed [CompleteSpace E] : S.generator.IsClosed := by
  have e : (S.generator.graph : Set (E × E)) =
      ⋂ h ∈ Ioi (0 : ℝ), {p | S.real h p.1 - p.1 = ∫ s in (0 : ℝ)..h, S.real s p.2} := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, mem_iInter, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨z, hzx, hzy⟩ h hh
      rw [← hzx, ← hzy]
      exact S.real_apply_sub_eq_integral z h hh.le
    · intro H
      have hlim : Tendsto (S.diffQuot x) (𝓝[>] 0) (𝓝 y) :=
        (S.tendsto_inv_smul_integral y).congr' (eventually_nhdsWithin_of_forall fun h hh => by
          rw [diffQuot, H h hh])
      exact ⟨⟨x, ⟨y, hlim⟩⟩, rfl, S.generator_apply_eq _ hlim⟩
  rw [LinearPMap.IsClosed, e]
  refine isClosed_biInter fun h _ => isClosed_eq ?_ ?_
  · exact ((S.real h).continuous.comp continuous_fst).sub continuous_fst
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (p : E × E) (s : ℝ) => S.real s p.2)
      (S.continuous_real_apply₂.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
      0 h

/-! ### Eigenvectors -/

/-- `e^{r} • v = exp (r : 𝕜) • v`. -/
theorem real_exp_smul (r : ℝ) (v : E) :
    Real.exp r • v = NormedSpace.exp ((r : ℝ) : 𝕜) • v := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), Real.exp_eq_exp_ℝ, ← RCLike.algebraMap_eq_ofReal,
    NormedSpace.algebraMap_exp_comm, RCLike.algebraMap_eq_ofReal]

/-- `u ↦ exp (u μ)` has derivative `exp (t μ) μ` (as a function of a real variable). -/
private theorem hasDerivAt_exp_mul (μ : 𝕜) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : 𝕜) * μ))
      (NormedSpace.exp ((t : 𝕜) * μ) * μ) t := by
  simpa [RCLike.real_smul_eq_coe_mul] using hasDerivAt_exp_smul_const (𝕂 := ℝ) μ t

/-- Eigenvectors with eigenvalue `μ : 𝕜` (for `𝕜 = ℂ`, `NormedSpace.exp = Complex.exp` by
`Complex.exp_eq_exp_ℂ`): `S t η = e^{μ t} η` for all `t ≥ 0` iff `η ∈ D(A)` and `A η = μ η`. -/
theorem eigen_iff (η : E) (μ : 𝕜) :
    (∀ t : ℝ≥0, S t η = NormedSpace.exp (((t : ℝ) : 𝕜) * μ) • η) ↔
      ∃ h : η ∈ S.generator.domain, S.generator ⟨η, h⟩ = μ • η := by
  constructor
  · intro H
    have hlim : Tendsto (S.diffQuot η) (𝓝[>] 0) (𝓝 (μ • η)) := by
      have := ((hasDerivAt_exp_mul μ 0).tendsto_slope_zero_right).smul_const η
      simp only [zero_add, RCLike.ofReal_zero, zero_mul, NormedSpace.exp_zero, one_mul] at this
      refine this.congr' (eventually_nhdsWithin_of_forall fun h hh => ?_)
      have hh' : (0 : ℝ) ≤ h := le_of_lt hh
      rw [diffQuot, real, H, Real.coe_toNNReal _ hh', smul_assoc, sub_smul, one_smul]
    exact ⟨⟨_, hlim⟩, S.generator_apply_eq _ hlim⟩
  · rintro ⟨hη, hA⟩ t
    -- `s ↦ e^{-sμ} S s η` has zero right derivative, hence is constant.
    set φ : ℝ → E := fun s => NormedSpace.exp ((s : 𝕜) * -μ) • S.real s η with hφ
    have hcont : ContinuousOn φ (Icc 0 t) :=
      (continuous_iff_continuousAt.2 fun s => ((hasDerivAt_exp_mul (-μ) s).continuousAt).smul
        (S.continuous_real_apply η).continuousAt).continuousOn
    have hderiv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt φ 0 (Ici s) s := by
      intro s hs
      have h1 := (hasDerivAt_exp_mul (-μ) s).hasDerivWithinAt (s := Ici s)
      have h2 := S.hasDerivWithinAt_real_apply ⟨η, hη⟩ hs.1
      have h3 := h1.fun_smul h2
      convert h3 using 1
      simp only [hA, map_smul, smul_smul]
      rw [← add_smul, ← mul_add, add_neg_cancel, mul_zero, zero_smul]
    have hconst := constant_of_has_deriv_right_zero hcont hderiv t ⟨t.2, le_rfl⟩
    simp only [hφ, RCLike.ofReal_zero, zero_mul, NormedSpace.exp_zero, real_zero, one_smul,
      one_apply_eq_self, real_coe] at hconst
    calc S t η = NormedSpace.exp (((t : ℝ) : 𝕜) * μ) •
          (NormedSpace.exp (((t : ℝ) : 𝕜) * -μ) • S t η) := by
          rw [smul_smul, ← NormedSpace.exp_add, mul_neg, add_neg_cancel, NormedSpace.exp_zero,
            one_smul]
      _ = NormedSpace.exp (((t : ℝ) : 𝕜) * μ) • η := by rw [hconst]

/-- Eigenvectors with real eigenvalue: `S t η = e^{μ t} η` for all `t ≥ 0` iff `η ∈ D(A)` and
`A η = μ η`. -/
theorem eigen_iff_real (η : E) (μ : ℝ) :
    (∀ t : ℝ≥0, S t η = Real.exp (μ * t) • η) ↔
      ∃ h : η ∈ S.generator.domain, S.generator ⟨η, h⟩ = μ • η := by
  have e1 : ∀ t : ℝ≥0, Real.exp (μ * t) • η = NormedSpace.exp (((t : ℝ) : 𝕜) * (μ : 𝕜)) • η :=
    fun t => by rw [real_exp_smul (𝕜 := 𝕜), RCLike.ofReal_mul, mul_comm]
  simp only [e1, RCLike.real_smul_eq_coe_smul (K := 𝕜) μ η]
  exact S.eigen_iff η μ

/-- **Uniqueness for the abstract Cauchy problem** (Banach space): a function `w`, continuous
on `[0, t]`, with values in `D(A)` and right derivative `A (w s)` on `[0, t)`, is
`w t = S t (w 0)`. -/
theorem eq_real_apply_of_hasDerivWithinAt [CompleteSpace E] {w : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn w (Icc 0 t)) (hdom : ∀ s ∈ Ico (0 : ℝ) t, w s ∈ S.generator.domain)
    (hderiv : ∀ s (hs : s ∈ Ico (0 : ℝ) t),
      HasDerivWithinAt w (S.generator ⟨w s, hdom s hs⟩) (Ici s) s) :
    w t = S.real t (w 0) := by
  obtain ⟨K, -, hK⟩ := S.exists_norm_real_le t
  have hφc : ContinuousOn (fun s => S.real (t - s) (w s)) (Icc 0 t) :=
    S.continuous_real_apply₂.comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).prodMk hcont)
  have hφd : ∀ s ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s => S.real (t - s) (w s)) 0 (Ici s) s := by
    intro s hs
    have hlim1 := hderiv s hs
    rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hlim1
    have hlim2 := (S.tendsto_generator ⟨w s, hdom s hs⟩).comp (tendsto_sub_nhdsGT s)
    have hlim : Tendsto (fun r => slope w s r - S.diffQuot (w s) (r - s)) (𝓝[>] s) (𝓝 0) := by
      simpa using hlim1.sub hlim2
    rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using hlim.norm.const_mul K)
    filter_upwards [Ioc_mem_nhdsGT hs.2] with r hr
    have h1 : S.real (t - s) (w s) = S.real (t - r) (S.real (r - s) (w s)) := by
      rw [← S.real_add_apply (by linarith [hr.2]) (by linarith [hr.1])]
      congr 2; ring
    have e : slope (fun s => S.real (t - s) (w s)) s r =
        S.real (t - r) (slope w s r - S.diffQuot (w s) (r - s)) := by
      simp only [slope_def_module, diffQuot]
      rw [h1, ← map_sub, ← ContinuousLinearMap.map_smul_of_tower, ← smul_sub]
      congr 2; abel
    rw [e]
    exact ((S.real (t - r)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK _ (by linarith [hr.1, hs.1])) (norm_nonneg _))
  have := constant_of_has_deriv_right_zero hφc hφd t ⟨ht, le_rfl⟩
  simpa using this

/-- A C₀-semigroup on a Banach space is determined by its generator. -/
theorem ext_of_generator [CompleteSpace E] {S' : C0Semigroup 𝕜 E}
    (h : S.generator = S'.generator) : S = S' := by
  obtain ⟨hdom, hval⟩ := LinearPMap.ext_iff.1 h
  have hdom' : ∀ {y : E}, y ∈ S'.generator.domain → y ∈ S.generator.domain := fun hy =>
    hdom ▸ hy
  refine C0Semigroup.ext fun t => ContinuousLinearMap.ext fun x => ?_
  -- equality on the dense set `D(A)`
  have key : ∀ x ∈ (S.generator.domain : Set E), S t x = S' t x := by
    intro x hx
    have hx' : x ∈ S'.generator.domain := hdom ▸ hx
    have := S.eq_real_apply_of_hasDerivWithinAt (w := fun s => S'.real s x) t.2
      (S'.continuous_real_apply x).continuousOn
      (fun s _ => hdom' (S'.real_mem_generator_domain hx' s))
      (fun s hs => by
        have h2 := S'.hasDerivWithinAt_real_apply ⟨x, hx'⟩ hs.1
        rwa [← S'.generator_real_apply hx' s, ← hval] at h2)
    simpa using this.symm
  exact congrFun (Continuous.ext_on S.dense_generator_domain (S t).continuous
    (S' t).continuous key) x

/-! ### Consistent semigroups have consistent generators -/

theorem Consistent.diffQuot {ι : F →L[𝕜] E} {S' : C0Semigroup 𝕜 F} (h : Consistent ι S' S)
    (x : F) (t : ℝ) : ι (S'.diffQuot x t) = S.diffQuot (ι x) t := by
  simp only [C0Semigroup.diffQuot, map_sub, h.real, ContinuousLinearMap.map_smul_of_tower]

theorem Consistent.mem_generator_domain {ι : F →L[𝕜] E} {S' : C0Semigroup 𝕜 F}
    (h : Consistent ι S' S) {x : F} (hx : x ∈ S'.generator.domain) :
    ι x ∈ S.generator.domain := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨ι y, ((ι.continuous.tendsto y).comp hy).congr fun t => h.diffQuot S x t⟩

theorem Consistent.generator_apply {ι : F →L[𝕜] E} {S' : C0Semigroup 𝕜 F}
    (h : Consistent ι S' S) {x : F} (hx : x ∈ S'.generator.domain) :
    S.generator ⟨ι x, h.mem_generator_domain S hx⟩ = ι (S'.generator ⟨x, hx⟩) := by
  refine S.generator_apply_eq _ ?_
  exact ((ι.continuous.tendsto _).comp (S'.tendsto_generator ⟨x, hx⟩)).congr
    fun t => h.diffQuot S x t

end C0Semigroup

end DataDrivenControl
