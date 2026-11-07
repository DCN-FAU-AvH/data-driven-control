module

public import DataDrivenControl.Semigroup.Generator

/-!
# The adjoint semigroup

On a Hilbert space `E` over `𝕜`, `t ↦ (S t)†` is a C₀-semigroup whose generator is `A†`
(Mathlib's `LinearPMap.adjoint`, notation `A†` under `open scoped LinearPMap`).

## Main declarations

* `continuous_adjoint_apply`: strong continuity of `t ↦ (S t)† η` (Pazy §1.10,
  Engel–Nagel I.5.14), used in the definition below.  Proof: on `D(A†)`,
  `‖(S t)† η - η‖ ≤ ‖A† η‖ M t` (`norm_adjoint_real_apply_sub_le`), and `D(A†)` is dense
  (test `ξ ⊥ D(A†)` against `(∫₀ʰ S s ds)† ξ ∈ D(A†)`);
* `C0Semigroup.adjoint S`, with `adjoint_apply : S.adjoint t = (S t)†`, `adjoint_real`,
  `inner_adjoint_apply`, `adjoint_adjoint`;
* `inner_real_apply_eq_add_integral`: `⟪η, S t x⟫ = ⟪η, x⟫ + ∫₀ᵗ ⟪A† η, S s x⟫ ds` for
  `η ∈ D(A†)` (the integrated form of `hasDerivAt_inner`, for every `x`);
* `adjoint_real_apply_sub_eq_integral`: `(S t)† η - η = ∫₀ᵗ (S s)† A† η ds` on `D(A†)`;
* `generator_adjoint : S.adjoint.generator = S.generator†`;
* `adjoint_mem_adjoint_domain`, `generator_adjoint_apply_adjoint`: `(S t)†` preserves `D(A†)`
  and commutes with `A†`;
* `hasDerivAt_inner`, `hasDerivWithinAt_inner`: `d/dt ⟪η, S t x⟫ = ⟪A† η, S t x⟫` for
  `η ∈ D(A†)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace C0Semigroup

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

variable (S : C0Semigroup 𝕜 E)

section Aux

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

omit [IsScalarTower ℝ 𝕜 E] in
private theorem inner_intervalIntegral_right_aux {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (c : E) :
    ⟪c, ∫ s in a..b, f s⟫_𝕜 = ∫ s in a..b, ⟪c, f s⟫_𝕜 :=
  ((innerSL 𝕜 c).intervalIntegral_comp_comm hf).symm

/-- `⟪η, S t x - x⟫ = ⟪A† η, ∫₀ᵗ S s x ds⟫` for `η ∈ D(A†)` and `t ≥ 0`. -/
theorem inner_real_apply_sub_eq_inner_integral {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ⟪η, S.real t x - x⟫_𝕜 =
      ⟪S.generator.adjoint ⟨η, hη⟩, ∫ s in (0 : ℝ)..t, S.real s x⟫_𝕜 := by
  rw [← S.generator_integral x ht]
  exact (LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain ⟨η, hη⟩
    ⟨_, S.integral_mem_generator_domain x ht⟩).symm

/-- `⟪η, S t x⟫ = ⟪η, x⟫ + ∫₀ᵗ ⟪A† η, S s x⟫ ds` for `η ∈ D(A†)` and `t ≥ 0`. -/
theorem inner_real_apply_eq_add_integral {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ⟪η, S.real t x⟫_𝕜 =
      ⟪η, x⟫_𝕜 + ∫ s in (0 : ℝ)..t, ⟪S.generator.adjoint ⟨η, hη⟩, S.real s x⟫_𝕜 := by
  rw [← inner_intervalIntegral_right_aux ((S.continuous_real_apply x).intervalIntegrable _ _),
    ← S.inner_real_apply_sub_eq_inner_integral hη x ht, inner_sub_right, add_sub_cancel]

/-- `‖(S t)† η - η‖ ≤ ‖A† η‖ M t` for `η ∈ D(A†)`, if `‖S s‖ ≤ M` for `s ≤ t`. -/
theorem norm_adjoint_real_apply_sub_le {η : E} (hη : η ∈ S.generator.adjoint.domain) {M t : ℝ}
    (hM0 : 0 ≤ M) (ht : 0 ≤ t) (hM : ∀ s, s ≤ t → ‖S.real s‖ ≤ M) :
    ‖ContinuousLinearMap.adjoint (S.real t) η - η‖ ≤
      ‖S.generator.adjoint ⟨η, hη⟩‖ * (M * t) := by
  set v := ContinuousLinearMap.adjoint (S.real t) η - η
  set C := ‖S.generator.adjoint ⟨η, hη⟩‖ * (M * t)
  have hC : 0 ≤ C := by positivity
  have h1 : ‖v‖ ^ 2 ≤ C * ‖v‖ := by
    have hvv : ⟪v, v⟫_𝕜 = ⟪S.generator.adjoint ⟨η, hη⟩, ∫ s in (0 : ℝ)..t, S.real s v⟫_𝕜 := by
      rw [← S.inner_real_apply_sub_eq_inner_integral hη v ht]
      conv_lhs => rw [show v = ContinuousLinearMap.adjoint (S.real t) η - η from rfl]
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, ← inner_sub_right]
    have hint : ‖∫ s in (0 : ℝ)..t, S.real s v‖ ≤ M * ‖v‖ * |t - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      rw [uIoc_of_le ht] at hs
      exact ((S.real s).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hM s hs.2) (norm_nonneg v))
    rw [sub_zero, abs_of_nonneg ht] at hint
    calc ‖v‖ ^ 2 = RCLike.re ⟪v, v⟫_𝕜 := norm_sq_eq_re_inner v
      _ ≤ ‖⟪v, v⟫_𝕜‖ := RCLike.re_le_norm _
      _ ≤ ‖S.generator.adjoint ⟨η, hη⟩‖ * ‖∫ s in (0 : ℝ)..t, S.real s v‖ := by
          rw [hvv]; exact norm_inner_le_norm _ _
      _ ≤ ‖S.generator.adjoint ⟨η, hη⟩‖ * (M * ‖v‖ * t) :=
          mul_le_mul_of_nonneg_left hint (norm_nonneg _)
      _ = C * ‖v‖ := by ring
  rcases (norm_nonneg v).eq_or_lt with h | h
  · rw [← h]; exact hC
  · nlinarith

/-- The bounded operator `x ↦ ∫₀ᵗ S s x ds`. -/
private theorem exists_integralCLM_aux (t : ℝ) :
    ∃ V : E →L[𝕜] E, ∀ x, V x = ∫ s in (0 : ℝ)..t, S.real s x := by
  refine ⟨LinearMap.mkContinuousOfExistsBound
    { toFun := fun x => ∫ s in (0 : ℝ)..t, S.real s x
      map_add' := fun x y => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((S.continuous_real_apply x).intervalIntegrable _ _)
          ((S.continuous_real_apply y).intervalIntegrable _ _)
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ } ?_, fun x => rfl⟩
  obtain ⟨M, -, hM⟩ := S.exists_norm_real_le |t|
  refine ⟨M * |t|, fun x => ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  calc ‖∫ s in (0 : ℝ)..t, S.real s x‖ ≤ M * ‖x‖ * |t - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
        refine ((S.real s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hM s ?_) (norm_nonneg x))
        rcases le_total 0 t with h | h
        · rw [uIoc_of_le h] at hs; exact hs.2.trans (le_abs_self t)
        · rw [uIoc_of_ge h] at hs; linarith [hs.1, hs.2, abs_nonneg t]
    _ = M * |t| * ‖x‖ := by rw [sub_zero]; ring

/-- `D(A†)` is dense: if `ξ ⊥ D(A†)`, test against `(∫₀ʰ S s ds)† ξ ∈ D(A†)`. -/
private theorem dense_adjoint_domain_aux : Dense (S.generator.adjoint.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro ξ hξ
  rw [Submodule.mem_orthogonal] at hξ
  have hg : ∀ h : ℝ, 0 ≤ h → ∫ s in (0 : ℝ)..h, ⟪ξ, S.real s ξ⟫_𝕜 = 0 := by
    intro h hh
    obtain ⟨V, hV⟩ := S.exists_integralCLM_aux h
    have hmem : ContinuousLinearMap.adjoint V ξ ∈ S.generator.adjoint.domain := by
      refine LinearPMap.mem_adjoint_domain_of_exists _
        ⟨ContinuousLinearMap.adjoint (S.real h) ξ - ξ, fun x => ?_⟩
      rw [ContinuousLinearMap.adjoint_inner_left, hV, ← S.real_apply_sub_eq_integral x h hh,
        inner_sub_left, ContinuousLinearMap.adjoint_inner_left, inner_sub_right]
    have := hξ _ hmem
    rwa [ContinuousLinearMap.adjoint_inner_left, hV,
      inner_intervalIntegral_right_aux ((S.continuous_real_apply ξ).intervalIntegrable _ _)] at this
  have hc : Continuous fun s : ℝ => ⟪ξ, S.real s ξ⟫_𝕜 :=
    continuous_const.inner (S.continuous_real_apply ξ)
  have hd := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, S.real_zero,
    one_apply_eq_self] at hd
  have h0 : Tendsto (fun t : ℝ => t⁻¹ • ∫ s in (0 : ℝ)..t, ⟪ξ, S.real s ξ⟫_𝕜) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hg t (le_of_lt ht), smul_zero])
  exact inner_self_eq_zero.1 (tendsto_nhds_unique hd h0)

/-- Strong continuity of `t ↦ (S t)† η` at `0`. -/
private theorem tendsto_adjoint_apply_zero_aux (η : E) :
    Tendsto (fun t : ℝ≥0 => ContinuousLinearMap.adjoint (S t) η) (𝓝 0) (𝓝 η) := by
  obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le 1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨η', hball, hη'⟩ := Metric.dense_iff.1 S.dense_adjoint_domain_aux η _ hδ
  set C := ‖S.generator.adjoint ⟨η', hη'⟩‖
  have h1 : ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ) < 1 :=
    (NNReal.continuous_coe.tendsto 0).eventually (eventually_lt_nhds (by simp))
  have h2 : ∀ᶠ t : ℝ≥0 in 𝓝 0, C * (M * t) < ε / 2 := by
    have : Tendsto (fun t : ℝ≥0 => C * (M * (t : ℝ))) (𝓝 0) (𝓝 (C * (M * ((0 : ℝ≥0) : ℝ)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul (NNReal.continuous_coe.tendsto 0))
    rw [NNReal.coe_zero, mul_zero, mul_zero] at this
    exact this.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [h1, h2] with t ht1 ht2
  rw [dist_eq_norm]
  have hb := S.norm_adjoint_real_apply_sub_le hη' hM0 t.coe_nonneg (fun s hs => hM s (hs.trans ht1.le))
  simp only [real_coe] at hb
  have hA : ‖ContinuousLinearMap.adjoint (S t) (η - η')‖ ≤ M * ‖η - η'‖ := by
    calc _ ≤ ‖ContinuousLinearMap.adjoint (S t)‖ * ‖η - η'‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖S t‖ * ‖η - η'‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ M * ‖η - η'‖ :=
          mul_le_mul_of_nonneg_right (by simpa using hM t ht1.le) (norm_nonneg _)
  have hdist : ‖η - η'‖ < ε / (2 * (M + 1)) := by
    rw [← dist_eq_norm, dist_comm]; exact hball
  have hdist' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M + 1))).1 hdist
  calc ‖ContinuousLinearMap.adjoint (S t) η - η‖ =
        ‖ContinuousLinearMap.adjoint (S t) (η - η') +
          (ContinuousLinearMap.adjoint (S t) η' - η') + (η' - η)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖ContinuousLinearMap.adjoint (S t) (η - η')‖ +
          ‖ContinuousLinearMap.adjoint (S t) η' - η'‖ + ‖η' - η‖ := norm_add₃_le
    _ ≤ M * ‖η - η'‖ + C * (M * t) + ‖η - η'‖ := by
        rw [norm_sub_rev η' η]; gcongr
    _ < ε := by nlinarith [norm_nonneg (η - η')]

end Aux

/-- Strong continuity of the adjoint semigroup on a Hilbert space (Pazy §1.10, Engel–Nagel
I.5.14).  The proof gives `E` its real structure and shows strong continuity at `0`: on `D(A†)`,
`‖(S t)† η - η‖ ≤ ‖A† η‖ M t`, and `D(A†)` is dense. -/
theorem continuous_adjoint_apply (η : E) :
    Continuous fun t => ContinuousLinearMap.adjoint (S t) η := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  refine continuous_of_tendsto (fun t => ContinuousLinearMap.adjoint (S t)) ?_ ?_
    S.tendsto_adjoint_apply_zero_aux η
  · rw [S.map_zero, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  · intro s t; rw [add_comm, S.map_add, ContinuousLinearMap.adjoint_comp]

/-- The **adjoint semigroup** `t ↦ (S t)†` on a Hilbert space. -/
def adjoint : C0Semigroup 𝕜 E where
  toFun t := ContinuousLinearMap.adjoint (S t)
  map_zero' := by rw [S.map_zero, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  map_add' s t := by rw [add_comm, S.map_add, ContinuousLinearMap.adjoint_comp]
  continuous_apply' := S.continuous_adjoint_apply

@[simp] theorem adjoint_apply (t : ℝ≥0) : S.adjoint t = ContinuousLinearMap.adjoint (S t) := rfl

@[simp] theorem adjoint_real (t : ℝ) : S.adjoint.real t = ContinuousLinearMap.adjoint (S.real t) :=
  rfl

theorem inner_adjoint_apply (t : ℝ≥0) (η x : E) : ⟪S.adjoint t η, x⟫_𝕜 = ⟪η, S t x⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem inner_adjoint_real_apply (t : ℝ) (η x : E) :
    ⟪S.adjoint.real t η, x⟫_𝕜 = ⟪η, S.real t x⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] theorem adjoint_adjoint : S.adjoint.adjoint = S := by
  ext t x
  simp [ContinuousLinearMap.adjoint_adjoint]

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- `(S t)† η - η = ∫₀ᵗ (S s)† A† η ds` for `η ∈ D(A†)` and `t ≥ 0`. -/
theorem adjoint_real_apply_sub_eq_integral {η : E} (hη : η ∈ S.generator.adjoint.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    S.adjoint.real t η - η =
      ∫ s in (0 : ℝ)..t, S.adjoint.real s (S.generator.adjoint ⟨η, hη⟩) := by
  refine ext_inner_left 𝕜 fun x => ?_
  rw [inner_intervalIntegral_right_aux ((S.adjoint.continuous_real_apply _).intervalIntegrable _ _)]
  simp only [adjoint_real, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_sub_left, ← inner_conj_symm, S.inner_real_apply_sub_eq_inner_integral hη x ht,
    inner_intervalIntegral_right_aux ((S.continuous_real_apply x).intervalIntegrable _ _),
    ← intervalIntegral.intervalIntegral_conj]
  simp_rw [inner_conj_symm]

/-- The difference quotients of the adjoint semigroup converge to `A† η` on `D(A†)`. -/
theorem tendsto_adjoint_diffQuot {η : E} (hη : η ∈ S.generator.adjoint.domain) :
    Tendsto (S.adjoint.diffQuot η) (𝓝[>] 0) (𝓝 (S.generator.adjoint ⟨η, hη⟩)) := by
  have hd := ((S.adjoint.continuous_real_apply (S.generator.adjoint ⟨η, hη⟩)).integral_hasStrictDerivAt
    0 0).hasDerivAt.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, S.adjoint.real_zero,
    one_apply_eq_self] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [diffQuot, S.adjoint_real_apply_sub_eq_integral hη (le_of_lt hh)]

/-- `D(A†)` is contained in the domain of the generator of the adjoint semigroup. -/
theorem mem_adjoint_generator_domain {η : E} (hη : η ∈ S.generator.adjoint.domain) :
    η ∈ S.adjoint.generator.domain :=
  S.adjoint.mem_generator_domain_of_tendsto (S.tendsto_adjoint_diffQuot hη)

/-- On `D(A†)`, the generator of the adjoint semigroup is `A†`. -/
theorem adjoint_generator_apply {η : E} (hη : η ∈ S.generator.adjoint.domain) :
    S.adjoint.generator ⟨η, S.mem_adjoint_generator_domain hη⟩ = S.generator.adjoint ⟨η, hη⟩ :=
  S.adjoint.generator_apply_eq _ (S.tendsto_adjoint_diffQuot hη)

/-- Difference quotients of `S†` and of `S` are adjoint. -/
theorem inner_adjoint_diffQuot (η x : E) (h : ℝ) :
    ⟪S.adjoint.diffQuot η h, x⟫_𝕜 = ⟪η, S.diffQuot x h⟫_𝕜 := by
  simp only [diffQuot, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_real_left,
    inner_smul_real_right, adjoint_real, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left]

/-- The generator of the adjoint semigroup is a restriction of `A†`. -/
theorem exists_mem_adjoint_domain_of_mem_adjoint_generator {η : E}
    (hη : η ∈ S.adjoint.generator.domain) :
    ∃ h : η ∈ S.generator.adjoint.domain,
      S.generator.adjoint ⟨η, h⟩ = S.adjoint.generator ⟨η, hη⟩ := by
  have key : ∀ x : S.generator.domain,
      ⟪S.adjoint.generator ⟨η, hη⟩, (x : E)⟫_𝕜 = ⟪η, S.generator x⟫_𝕜 := fun x =>
    tendsto_nhds_unique (((S.adjoint.tendsto_generator ⟨η, hη⟩).inner tendsto_const_nhds).congr
      fun h => S.inner_adjoint_diffQuot η x h) (tendsto_const_nhds.inner (S.tendsto_generator x))
  have hmem : η ∈ S.generator.adjoint.domain := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq S.dense_generator_domain ⟨η, hmem⟩ key⟩

/-- The generator of the adjoint semigroup is the adjoint `A†` of the generator. -/
theorem generator_adjoint : S.adjoint.generator = S.generator.adjoint := by
  refine LinearPMap.ext ?_ fun η h1 h2 => ?_
  · ext η
    exact ⟨fun h => (S.exists_mem_adjoint_domain_of_mem_adjoint_generator h).1,
      S.mem_adjoint_generator_domain⟩
  · exact S.adjoint_generator_apply h2

/-- `(S t)†` preserves `D(A†)`. -/
theorem adjoint_mem_adjoint_domain {η : E} (hη : η ∈ S.generator.adjoint.domain) (t : ℝ≥0) :
    S.adjoint t η ∈ S.generator.adjoint.domain := by
  rw [← generator_adjoint] at hη ⊢
  exact S.adjoint.mem_generator_domain_apply hη t

/-- `(S t)†` preserves `D(A†)` (real-time version). -/
theorem adjoint_real_mem_adjoint_domain {η : E} (hη : η ∈ S.generator.adjoint.domain) (t : ℝ) :
    S.adjoint.real t η ∈ S.generator.adjoint.domain :=
  S.adjoint_mem_adjoint_domain hη _

/-- `A† (S t)† η = (S t)† A† η` for `η ∈ D(A†)`. -/
theorem generator_adjoint_apply_adjoint {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (t : ℝ≥0) :
    S.generator.adjoint ⟨S.adjoint t η, S.adjoint_mem_adjoint_domain hη t⟩ =
      S.adjoint t (S.generator.adjoint ⟨η, hη⟩) := by
  rw [← S.adjoint_generator_apply hη, ← S.adjoint_generator_apply (S.adjoint_mem_adjoint_domain hη t)]
  exact S.adjoint.generator_apply_apply (S.mem_adjoint_generator_domain hη) t

/-- `d/dt ⟪η, S t x⟫ = ⟪A† η, S t x⟫` for `η ∈ D(A†)` and `t > 0`. -/
theorem hasDerivAt_inner {η : E} (hη : η ∈ S.generator.adjoint.domain) (x : E) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s => ⟪η, S.real s x⟫_𝕜) ⟪S.generator.adjoint ⟨η, hη⟩, S.real t x⟫_𝕜 t := by
  have h := S.adjoint.hasDerivAt_real_apply ⟨η, S.mem_adjoint_generator_domain hη⟩ ht
  rw [S.adjoint_generator_apply hη] at h
  have := h.inner 𝕜 (hasDerivAt_const t x)
  simpa only [inner_zero_right, zero_add, adjoint_real, ContinuousLinearMap.adjoint_inner_left]
    using this

/-- The right derivative of `t ↦ ⟪η, S t x⟫` at `t ≥ 0` is `⟪A† η, S t x⟫`, `η ∈ D(A†)`. -/
theorem hasDerivWithinAt_inner {η : E} (hη : η ∈ S.generator.adjoint.domain) (x : E) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ⟪η, S.real s x⟫_𝕜) ⟪S.generator.adjoint ⟨η, hη⟩, S.real t x⟫_𝕜
      (Ici t) t := by
  have h := S.adjoint.hasDerivWithinAt_real_apply ⟨η, S.mem_adjoint_generator_domain hη⟩ ht
  rw [S.adjoint_generator_apply hη] at h
  have := h.inner 𝕜 (hasDerivWithinAt_const t (Ici t) x)
  simpa only [inner_zero_right, zero_add, adjoint_real, ContinuousLinearMap.adjoint_inner_left]
    using this

/-- `D(A†)` is dense (the generator is closed and densely defined). -/
theorem dense_adjoint_domain : Dense (S.generator.adjoint.domain : Set E) := by
  rw [← generator_adjoint]; exact S.adjoint.dense_generator_domain

end C0Semigroup

end DataDrivenControl
