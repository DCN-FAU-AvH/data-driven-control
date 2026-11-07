module

public import Mathlib

/-!
# Bounded-below operators

A continuous linear map `T : E →L[𝕜] F` is *bounded below* (`IsBoundedBelow T`) if
`c * ‖x‖ ≤ ‖T x‖` for some `c > 0`.  The paper uses this notion for the graph operator `Γ`
(`eq:graph-operator`, Step 2 of `app:willems-gramian`), for the parametrisation `𝓜_T`
(`lem:io-parametrization`, `app:lqr-data-io`, `app:io-window-controllability`) and for the
observability map `𝓞_T` (`eq:io-state-recovery`).

Normed spaces (`E` complete where needed):
* `IsBoundedBelow.isClosedEmbedding`, `IsBoundedBelow.isClosed_range`: a bounded-below map is a
  homeomorphism onto its closed range; `IsBoundedBelow.equivRange` is that homeomorphism;
* `IsBoundedBelow.isClosed_map`, `IsBoundedBelow.map_topologicalClosure`: it maps closed
  subspaces to closed subspaces and commutes with closures of subspaces;
* constructors: `IsBoundedBelow.of_bound`, `IsBoundedBelow.of_norm_le` (`‖x‖ ≤ ‖T x‖`),
  `IsBoundedBelow.mono`, `IsBoundedBelow.comp`, `IsBoundedBelow.of_antilipschitzWith`;
* `isBoundedBelow_iff_exists_antilipschitzWith`,
  `IsBoundedBelow.of_injective_of_isClosed_range` (the converse, for Banach spaces),
  `isBoundedBelow_iff_injective` (finite dimensions).

Hilbert spaces:
* `IsBoundedBelow.adjoint_comp_self`: `T† ∘L T` is bounded below, and
  `IsBoundedBelow.adjointCompSelfEquiv` is `T† ∘L T` as a `ContinuousLinearEquiv`; with
  `IsBoundedBelow.adjointCompSelfEquiv_symm_adjoint_apply` this is `eq:io-state-recovery`,
  `x = (T† T)⁻¹ (T†) (T x)`;
* `IsBoundedBelow.adjoint_surjective`: `T†` is onto;
* `IsBoundedBelow.range_eq_orthogonal_ker_adjoint`: `range T = (ker T†)ᗮ`.
-/

@[expose] public section

open Function Set Topology
open scoped InnerProductSpace InnerProduct NNReal

noncomputable section

namespace DataDrivenControl

section Normed

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous linear map `T` is **bounded below** if `c * ‖x‖ ≤ ‖T x‖` for some `c > 0` and
all `x` (used for `Γ` in `eq:graph-operator`, for `𝓜_T` in `lem:io-parametrization` and for
`𝓞_T` under exact observability). -/
def IsBoundedBelow (T : E →L[𝕜] F) : Prop :=
  ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖

namespace IsBoundedBelow

variable {T : E →L[𝕜] F}

/-- Constructor from an explicit constant. -/
theorem of_bound {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ≤ ‖T x‖) : IsBoundedBelow T :=
  ⟨c, hc, h⟩

/-- `‖x‖ ≤ ‖T x‖` (constant `1`), the form in which `Γ` is bounded below. -/
theorem of_norm_le (h : ∀ x, ‖x‖ ≤ ‖T x‖) : IsBoundedBelow T :=
  ⟨1, one_pos, by simpa using h⟩

/-- If `T` is bounded below and `‖T x‖ ≤ ‖T' x‖` for all `x`, then `T'` is bounded below. -/
theorem mono {T' : E →L[𝕜] G} (hT : IsBoundedBelow T) (h : ∀ x, ‖T x‖ ≤ ‖T' x‖) :
    IsBoundedBelow T' := by
  obtain ⟨c, hc, hT⟩ := hT
  exact ⟨c, hc, fun x => (hT x).trans (h x)⟩

/-- The identity is bounded below. -/
theorem id : IsBoundedBelow (ContinuousLinearMap.id 𝕜 E) :=
  of_norm_le fun _ => le_rfl

/-- A composition of bounded-below maps is bounded below. -/
theorem comp {S : F →L[𝕜] G} (hS : IsBoundedBelow S) (hT : IsBoundedBelow T) :
    IsBoundedBelow (S ∘L T) := by
  obtain ⟨a, ha, hS⟩ := hS
  obtain ⟨b, hb, hT⟩ := hT
  refine ⟨a * b, mul_pos ha hb, fun x => ?_⟩
  calc a * b * ‖x‖ = a * (b * ‖x‖) := mul_assoc _ _ _
    _ ≤ a * ‖T x‖ := mul_le_mul_of_nonneg_left (hT x) ha.le
    _ ≤ ‖S (T x)‖ := hS (T x)

/-- A bounded-below map is anti-Lipschitz. -/
theorem exists_antilipschitzWith (hT : IsBoundedBelow T) : ∃ K, AntilipschitzWith K T := by
  obtain ⟨c, hc, h⟩ := hT
  refine ⟨⟨c⁻¹, inv_nonneg.2 hc.le⟩, T.antilipschitz_of_bound fun x => ?_⟩
  show ‖x‖ ≤ c⁻¹ * ‖T x‖
  rw [le_inv_mul_iff₀ hc]
  exact h x

/-- An anti-Lipschitz continuous linear map is bounded below. -/
theorem of_antilipschitzWith {K : ℝ≥0} (h : AntilipschitzWith K T) : IsBoundedBelow T := by
  refine ⟨((K : ℝ) + 1)⁻¹, by positivity, fun x => ?_⟩
  rw [inv_mul_le_iff₀ (by positivity)]
  calc ‖x‖ ≤ K * ‖T x‖ := T.bound_of_antilipschitz h x
    _ ≤ (K + 1) * ‖T x‖ := by gcongr; linarith

/-- A bounded-below map is injective. -/
theorem injective (hT : IsBoundedBelow T) : Injective T := by
  obtain ⟨K, hK⟩ := hT.exists_antilipschitzWith
  exact hK.injective

/-- A bounded-below map has trivial kernel. -/
theorem ker_eq_bot (hT : IsBoundedBelow T) : T.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr hT.injective

/-- A bounded-below map on a Banach space is a closed embedding: a homeomorphism onto its
closed range. -/
theorem isClosedEmbedding [CompleteSpace E] (hT : IsBoundedBelow T) : IsClosedEmbedding T := by
  obtain ⟨K, hK⟩ := hT.exists_antilipschitzWith
  exact hK.isClosedEmbedding T.uniformContinuous

/-- A bounded-below map on a Banach space has closed range. -/
theorem isClosed_range [CompleteSpace E] (hT : IsBoundedBelow T) : IsClosed (range T) :=
  hT.isClosedEmbedding.isClosed_range

/-- The range of a bounded-below map on a Banach space is a closed subspace. -/
theorem range_topologicalClosure [CompleteSpace E] (hT : IsBoundedBelow T) :
    T.range.topologicalClosure = T.range := by
  refine IsClosed.submodule_topologicalClosure_eq ?_
  rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  exact hT.isClosed_range

/-- A bounded-below map on a Banach space maps closed sets to closed sets. -/
theorem isClosed_image [CompleteSpace E] (hT : IsBoundedBelow T) {s : Set E} (hs : IsClosed s) :
    IsClosed (T '' s) :=
  hT.isClosedEmbedding.isClosedMap s hs

/-- A bounded-below map on a Banach space maps closed subspaces to closed subspaces. -/
theorem isClosed_map [CompleteSpace E] (hT : IsBoundedBelow T) {K : Submodule 𝕜 E}
    (hK : IsClosed (K : Set E)) : IsClosed (K.map (T : E →ₗ[𝕜] F) : Set F) := by
  simpa using hT.isClosed_image hK

/-- A bounded-below map on a Banach space commutes with closures of subspaces:
`T (closure K) = closure (T K)` (Step 2 of `app:willems-gramian`). -/
theorem map_topologicalClosure [CompleteSpace E] (hT : IsBoundedBelow T) (K : Submodule 𝕜 E) :
    K.topologicalClosure.map (T : E →ₗ[𝕜] F) = (K.map (T : E →ₗ[𝕜] F)).topologicalClosure := by
  refine SetLike.ext' ?_
  simp only [Submodule.map_coe, Submodule.topologicalClosure_coe, ContinuousLinearMap.coe_coe]
  exact (hT.isClosedEmbedding.closure_image_eq _).symm

/-- The homeomorphism of `E` onto the range of a bounded-below map (closed when `E` is
complete, `isClosed_range`). -/
def equivRange (hT : IsBoundedBelow T) : E ≃L[𝕜] T.range :=
  have hT' : ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖ := hT
  (LinearEquiv.ofInjective (T : E →ₗ[𝕜] F) hT.injective).toContinuousLinearEquivOfBounds
    ‖T‖ hT'.choose⁻¹ (fun x => T.le_opNorm x) (fun y => by
      obtain ⟨hc, h⟩ := hT'.choose_spec
      have hx : T ((LinearEquiv.ofInjective (T : E →ₗ[𝕜] F) hT.injective).symm y) = y :=
        LinearEquiv.ofInjective_symm_apply (f := (T : E →ₗ[𝕜] F)) y
      have hy : ‖y‖ = ‖(y : F)‖ := rfl
      rw [hy, ← hx, le_inv_mul_iff₀ hc]
      exact h _)

@[simp]
theorem coe_equivRange_apply (hT : IsBoundedBelow T) (x : E) :
    (hT.equivRange x : F) = T x :=
  rfl

@[simp]
theorem equivRange_symm_apply (hT : IsBoundedBelow T) (x : E) :
    hT.equivRange.symm ⟨T x, LinearMap.mem_range_self (T : E →ₗ[𝕜] F) x⟩ = x := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  rfl

/-- Conversely, an injective map with closed range between Banach spaces is bounded below. -/
theorem of_injective_of_isClosed_range [CompleteSpace E] [CompleteSpace F]
    (hinj : Injective T) (hcl : IsClosed (range T)) : IsBoundedBelow T := by
  obtain ⟨K, hK⟩ := T.antilipschitz_of_injective_of_isClosed_range hinj hcl
  exact of_antilipschitzWith hK

end IsBoundedBelow

/-- Bounded below is the same as anti-Lipschitz. -/
theorem isBoundedBelow_iff_exists_antilipschitzWith {T : E →L[𝕜] F} :
    IsBoundedBelow T ↔ ∃ K, AntilipschitzWith K T :=
  ⟨fun h => h.exists_antilipschitzWith, fun ⟨_, h⟩ => .of_antilipschitzWith h⟩

/-- In finite dimensions, a continuous linear map is bounded below iff it is injective. -/
theorem isBoundedBelow_iff_injective [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {T : E →L[𝕜] F} : IsBoundedBelow T ↔ Injective T := by
  refine ⟨fun h => h.injective, fun h => ?_⟩
  obtain ⟨K, -, hK⟩ := ((T : E →ₗ[𝕜] F).injective_iff_antilipschitz).1 h
  exact .of_antilipschitzWith hK

end Normed

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace IsBoundedBelow

variable {T : E →L[𝕜] F}

/-- If `c * ‖x‖ ≤ ‖T x‖`, then `T† ∘L T` is bounded below (with constant `c ^ 2`). -/
theorem adjoint_comp_self (hT : IsBoundedBelow T) :
    IsBoundedBelow (T† ∘L T) := by
  obtain ⟨c, hc, h⟩ := hT
  refine ⟨c ^ 2, by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 : ‖T x‖ ^ 2 ≤ ‖(T† ∘L T) x‖ * ‖x‖ := by
    rw [T.apply_norm_sq_eq_inner_adjoint_left x]
    exact re_inner_le_norm _ _
  have h2 : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := pow_le_pow_left₀ (by positivity) (h x) 2
  refine le_of_mul_le_mul_right ?_ hx'
  nlinarith

/-- `T† ∘L T` is bijective for bounded-below `T`. -/
theorem bijective_adjoint_comp_self (hT : IsBoundedBelow T) :
    Bijective (T† ∘L T) := by
  have hA := hT.adjoint_comp_self
  refine (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz _).2
    ⟨?_, hA.exists_antilipschitzWith⟩
  rw [Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  exact hA.ker_eq_bot

/-- `T† ∘L T` as a continuous linear equivalence, for bounded-below `T`
(the inverse `(𝓞_T† 𝓞_T)⁻¹` of `eq:io-state-recovery`). -/
def adjointCompSelfEquiv (hT : IsBoundedBelow T) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofBijective (T† ∘L T)
    (LinearMap.ker_eq_bot.mpr hT.bijective_adjoint_comp_self.1)
    (LinearMap.range_eq_top.mpr hT.bijective_adjoint_comp_self.2)

@[simp]
theorem coe_adjointCompSelfEquiv (hT : IsBoundedBelow T) :
    (hT.adjointCompSelfEquiv : E →L[𝕜] E) = T† ∘L T :=
  rfl

@[simp]
theorem adjointCompSelfEquiv_apply (hT : IsBoundedBelow T) (x : E) :
    hT.adjointCompSelfEquiv x = (T†) (T x) :=
  rfl

/-- State recovery (`eq:io-state-recovery`): `(T† T)⁻¹ (T†) (T x) = x`. -/
theorem adjointCompSelfEquiv_symm_adjoint_apply (hT : IsBoundedBelow T) (x : E) :
    hT.adjointCompSelfEquiv.symm ((T†) (T x)) = x := by
  rw [← adjointCompSelfEquiv_apply hT x, ContinuousLinearEquiv.symm_apply_apply]

/-- The adjoint of a bounded-below map is surjective (used for `𝓜_T†` in
`app:io-window-controllability`). -/
theorem adjoint_surjective (hT : IsBoundedBelow T) :
    Surjective (T†) := by
  intro y
  refine ⟨T (hT.adjointCompSelfEquiv.symm y), ?_⟩
  rw [← adjointCompSelfEquiv_apply hT, ContinuousLinearEquiv.apply_symm_apply]

/-- The adjoint of a bounded-below map has full range. -/
theorem range_adjoint (hT : IsBoundedBelow T) :
    (T†).range = ⊤ :=
  LinearMap.range_eq_top.mpr hT.adjoint_surjective

/-- The (closed) range of a bounded-below map is the orthogonal complement of the kernel of its
adjoint. -/
theorem range_eq_orthogonal_ker_adjoint (hT : IsBoundedBelow T) :
    T.range = (T†).kerᗮ := by
  rw [ContinuousLinearMap.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint,
    hT.range_topologicalClosure]

end IsBoundedBelow

end Hilbert

end DataDrivenControl
