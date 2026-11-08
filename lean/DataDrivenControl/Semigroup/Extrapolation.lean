module

public import DataDrivenControl.Semigroup.Inhomogeneous

/-!
# Extrapolation spaces (dual model)

Real Hilbert spaces.

`E₋₁` is realised as the Riesz copy of `D(A†)` with the graph norm (the *dual model*): the
graph of `A†` is a closed subspace of `WithLp 2 (E × E)`, hence a Hilbert space, and it *is*
the type `S.Extrap`.  An element `φ ∈ E₋₁` acts on `η ∈ D(A†)` through `⟪φ, graphVec η⟫`.

* `E ↪ E₋₁`, `x ↦ Riesz⁻¹(η ↦ ⟪x, η⟫)`, is `S.toExtrap`, the Hilbert adjoint of the first
  projection `fstG : E₋₁ → E` (`inner_toExtrap_graphVec`);
* `A₋₁ x = Riesz⁻¹(η ↦ ⟪x, A† η⟫)` is `S.genExtrap : E →L[ℝ] E₋₁`, the adjoint of the second
  projection (`inner_genExtrap_graphVec`);
* `denseRange_toExtrap`;
* `S.extrapSemigroup : C0Semigroup ℝ S.Extrap` extends `S` (`extrapSemigroup_toExtrap`,
  `consistent_extrapSemigroup`); it is used only to state the control convolution in `X₋₁`
  (`System.toExtrap_L`);
* `integral_eq_iff_weak`, `isWeakSol_iff_extrap`: `ẋ = A₋₁ x + f` in `E₋₁` (integral form)
  is exactly the weak formulation of Ball's theorem.

## Proof notes

* `D(A†)` is dense because `A` is closed and densely defined
  (`dense_adjoint_domain_of_isClosed`, from Mathlib's graph description of `A†`).
* `(S t)†` preserves `D(A†)` and commutes with `A†` (`adjoint_mem_adjoint_domain_aux`,
  `generator_adjoint_apply_adjoint_aux`, proved from `S t D(A) ⊆ D(A)`), so
  `(S t)† ⊕ (S t)†` restricts to a C₀-semigroup `S.extrapU` on the graph `E₋₁`; the extended
  semigroup is its Hilbert adjoint (`extrapSemigroup_eq_adjoint`).

For a system, `V₋₁ = sys.SV.Extrap`; `A ∈ L(X, V₋₁)` is `sys.SV.genExtrap ∘L sys.ιV`,
`B ∈ L(U, V₋₁)` is `sys.SV.toExtrap ∘L sys.B` and the graph operator of Section 4 is
`Γ (v, ξ) = (v, ξ, sys.SV.genExtrap (sys.ιWV ξ) + sys.SV.toExtrap (sys.B v), sys.C ξ)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

section Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The adjoint of a closed densely defined operator on a Hilbert space is densely defined. -/
theorem dense_adjoint_domain_of_isClosed {T : E →ₗ.[ℝ] E} (hc : T.IsClosed) :
    Dense (T.adjoint.domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  set G : Submodule ℝ (WithLp 2 (E × E)) :=
    T.graph.comap (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap with hGdef
  have hG : IsClosed (G : Set (WithLp 2 (E × E))) :=
    hc.preimage (WithLp.prod_continuous_ofLp 2 E E)
  have hmem : WithLp.toLp 2 ((0 : E), y) ∈ Gᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hdom : w.snd ∈ T.adjoint.domain := by
      refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨-w.fst, fun x => ?_⟩
      have := hw (WithLp.toLp 2 ((x : E), T x)) (by simp [hGdef])
      simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd] at this
      rw [inner_neg_left, real_inner_comm (x : E) w.fst, real_inner_comm (T x) w.snd]
      linarith
    simpa [real_inner_comm] using hy _ hdom
  rw [Submodule.orthogonal_orthogonal_eq_closure, hG.submodule_topologicalClosure_eq] at hmem
  exact T.graph_fst_eq_zero_snd (by simpa [hGdef] using hmem) rfl

/-- Interval integrals commute with inner products. -/
private theorem inner_intervalIntegral_aux {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {g : ℝ → F} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : F) :
    ⟪c, ∫ s in a..b, g s⟫_ℝ = ∫ s in a..b, ⟪c, g s⟫_ℝ :=
  ((innerSL ℝ c).intervalIntegral_comp_comm hg).symm

end Aux

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (S : C0Semigroup ℝ E)

/-- The graph of `A†` as a subspace of the Hilbert space `WithLp 2 (E × E)`. -/
def adjGraph : Submodule ℝ (WithLp 2 (E × E)) :=
  S.generator.adjoint.graph.comap (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

theorem isClosed_adjGraph : IsClosed (S.adjGraph : Set (WithLp 2 (E × E))) :=
  (S.generator.adjoint_isClosed S.dense_generator_domain).preimage
    (WithLp.prod_continuous_ofLp 2 E E)

/-- The **extrapolation space** `E₋₁` in the dual model: the graph of `A†` with the inner
product of `WithLp 2 (E × E)` (a Hilbert space), identified by Riesz with the dual of `D(A†)`
under the graph norm. -/
abbrev Extrap : Type _ := ↥S.adjGraph

instance : CompleteSpace S.Extrap := S.isClosed_adjGraph.isComplete.completeSpace_coe

/-- The graph vector `(η, A† η) ∈ E₋₁` of `η ∈ D(A†)`; `φ ∈ E₋₁` acts on `η` by
`⟪φ, graphVec η⟫`. -/
def graphVec : S.generator.adjoint.domain →ₗ[ℝ] S.Extrap :=
  LinearMap.codRestrict S.adjGraph
    ((WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap ∘ₗ
      (S.generator.adjoint.domain.subtype.prod S.generator.adjoint.toFun))
    fun η => (LinearPMap.mem_graph_iff S.generator.adjoint).2 ⟨η, rfl, rfl⟩

@[simp] theorem coe_graphVec (η : S.generator.adjoint.domain) :
    (S.graphVec η : WithLp 2 (E × E)) = WithLp.toLp 2 ((η : E), S.generator.adjoint η) := rfl

@[simp] theorem graphVec_fst (η : S.generator.adjoint.domain) :
    (WithLp.ofLp (S.graphVec η : WithLp 2 (E × E))).1 = η := rfl

@[simp] theorem graphVec_snd (η : S.generator.adjoint.domain) :
    (WithLp.ofLp (S.graphVec η : WithLp 2 (E × E))).2 = S.generator.adjoint η := rfl

/-- `graphVec` is onto: every element of `E₋₁` is the graph vector of some `η ∈ D(A†)`. -/
theorem graphVec_surjective : Function.Surjective S.graphVec := by
  rintro ⟨g, hg⟩
  obtain ⟨η, h1, h2⟩ := (LinearPMap.mem_graph_iff S.generator.adjoint).1 hg
  refine ⟨η, Subtype.ext ?_⟩
  rw [coe_graphVec]
  exact (WithLp.ext_iff 2).2 (Prod.ext h1 h2)

/-- The graph norm: `‖graphVec η‖² = ‖η‖² + ‖A† η‖²`. -/
theorem norm_graphVec_sq (η : S.generator.adjoint.domain) :
    ‖S.graphVec η‖ ^ 2 = ‖(η : E)‖ ^ 2 + ‖S.generator.adjoint η‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- The first projection `E₋₁ → E`, `(η, A† η) ↦ η`. -/
def fstG : S.Extrap →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E E).comp S.adjGraph.subtypeL

/-- The second projection `E₋₁ → E`, `(η, A† η) ↦ A† η`. -/
def sndG : S.Extrap →L[ℝ] E :=
  (WithLp.sndL 2 ℝ E E).comp S.adjGraph.subtypeL

/-- The embedding `E ↪ E₋₁`, `x ↦ Riesz⁻¹(η ↦ ⟪x, η⟫)`. -/
def toExtrap : E →L[ℝ] S.Extrap := ContinuousLinearMap.adjoint S.fstG

/-- The extension `A₋₁ ∈ L(E, E₋₁)` of the generator, `x ↦ Riesz⁻¹(η ↦ ⟪x, A† η⟫)`. -/
def genExtrap : E →L[ℝ] S.Extrap := ContinuousLinearMap.adjoint S.sndG

/-- The defining property of `E ↪ E₋₁`: `⟪x, η⟫` is the pairing of `x` with `η ∈ D(A†)`. -/
theorem inner_toExtrap_graphVec (x : E) (η : S.generator.adjoint.domain) :
    ⟪S.toExtrap x, S.graphVec η⟫_ℝ = ⟪x, (η : E)⟫_ℝ := by
  rw [toExtrap, ContinuousLinearMap.adjoint_inner_left]; rfl

/-- The defining property of `A₋₁`: `⟪A₋₁ x, η⟫ = ⟪x, A† η⟫` for `η ∈ D(A†)`. -/
theorem inner_genExtrap_graphVec (x : E) (η : S.generator.adjoint.domain) :
    ⟪S.genExtrap x, S.graphVec η⟫_ℝ = ⟪x, S.generator.adjoint η⟫_ℝ := by
  rw [genExtrap, ContinuousLinearMap.adjoint_inner_left]; rfl

/-- Elements of `E₋₁` are determined by their pairings with `D(A†)`. -/
theorem extrap_ext {φ ψ : S.Extrap}
    (h : ∀ η : S.generator.adjoint.domain, ⟪φ, S.graphVec η⟫_ℝ = ⟪ψ, S.graphVec η⟫_ℝ) :
    φ = ψ := by
  refine ext_inner_right ℝ fun g => ?_
  obtain ⟨η, rfl⟩ := S.graphVec_surjective g
  exact h η

/-! ### Basic properties of the embedding `E ↪ E₋₁` -/

@[simp] theorem fstG_graphVec (η : S.generator.adjoint.domain) : S.fstG (S.graphVec η) = η :=
  rfl

@[simp] theorem sndG_graphVec (η : S.generator.adjoint.domain) :
    S.sndG (S.graphVec η) = S.generator.adjoint η := rfl

/-- The first projection `E₋₁ → E` is injective (`A† 0 = 0`). -/
theorem fstG_injective : Function.Injective S.fstG := by
  refine (injective_iff_map_eq_zero S.fstG).2 fun g hg => ?_
  obtain ⟨η, rfl⟩ := S.graphVec_surjective g
  have hη : η = 0 := Subtype.ext hg
  rw [hη, map_zero]

/-- `⟪(η, A† η), x⟫ = ⟪η, x⟫` for `x ∈ E ↪ E₋₁` (weak-formulation orientation). -/
theorem inner_graphVec_toExtrap (η : S.generator.adjoint.domain) (x : E) :
    ⟪S.graphVec η, S.toExtrap x⟫_ℝ = ⟪(η : E), x⟫_ℝ := by
  rw [real_inner_comm, inner_toExtrap_graphVec, real_inner_comm]

/-- `⟪(η, A† η), A₋₁ x⟫ = ⟪A† η, x⟫` (weak-formulation orientation). -/
theorem inner_graphVec_genExtrap (η : S.generator.adjoint.domain) (x : E) :
    ⟪S.graphVec η, S.genExtrap x⟫_ℝ = ⟪S.generator.adjoint η, x⟫_ℝ := by
  rw [real_inner_comm, inner_genExtrap_graphVec, real_inner_comm]

/-- `E` is dense in `E₋₁`. -/
theorem denseRange_toExtrap : DenseRange S.toExtrap := by
  have h : S.toExtrap.rangeᗮ = ⊥ := by
    rw [toExtrap, ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_adjoint]
    exact LinearMap.ker_eq_bot.2 S.fstG_injective
  rw [← Submodule.topologicalClosure_eq_top_iff,
    ← Submodule.dense_iff_topologicalClosure_eq_top] at h
  have h2 : Dense (Set.range S.toExtrap) := by
    convert h using 1
    ext; simp
  exact h2

/-! ### The extended semigroup -/

private theorem adjoint_aux {η : E} (hη : η ∈ S.generator.adjoint.domain) (t : ℝ≥0) :
    ∃ h : S.adjoint t η ∈ S.generator.adjoint.domain,
      S.generator.adjoint ⟨S.adjoint t η, h⟩ = S.adjoint t (S.generator.adjoint ⟨η, hη⟩) := by
  have hd := S.dense_generator_domain
  have key : ∀ x : S.generator.domain,
      ⟪S.adjoint t (S.generator.adjoint ⟨η, hη⟩), (x : E)⟫_ℝ =
        ⟪S.adjoint t η, S.generator x⟫_ℝ := by
    intro x
    rw [inner_adjoint_apply, inner_adjoint_apply, ← S.generator_apply_apply x.2 t]
    exact LinearPMap.adjoint_isFormalAdjoint hd ⟨η, hη⟩ ⟨S t x, S.mem_generator_domain_apply x.2 t⟩
  have h : S.adjoint t η ∈ S.generator.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨h, LinearPMap.adjoint_apply_eq hd ⟨_, h⟩ key⟩

/-- `(S t)†` preserves `D(A†)`.  Same statement as `adjoint_mem_adjoint_domain`, proved directly
from `S t D(A) ⊆ D(A)` and `A S t = S t A` (without `generator_adjoint`). -/
theorem adjoint_mem_adjoint_domain_aux {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (t : ℝ≥0) : S.adjoint t η ∈ S.generator.adjoint.domain :=
  (S.adjoint_aux hη t).1

/-- `A† (S t)† η = (S t)† A† η` for `η ∈ D(A†)` (cf. `generator_adjoint_apply_adjoint`). -/
theorem generator_adjoint_apply_adjoint_aux {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (t : ℝ≥0) :
    S.generator.adjoint ⟨S.adjoint t η, S.adjoint_mem_adjoint_domain_aux hη t⟩ =
      S.adjoint t (S.generator.adjoint ⟨η, hη⟩) :=
  (S.adjoint_aux hη t).2

/-- `(S t)† ⊕ (S t)†` on `WithLp 2 (E × E)`. -/
def diagAdjoint (t : ℝ≥0) : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    ((S.adjoint t).prodMap (S.adjoint t)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

theorem diagAdjoint_apply (t : ℝ≥0) (g : WithLp 2 (E × E)) :
    S.diagAdjoint t g = WithLp.toLp 2 (S.adjoint t g.fst, S.adjoint t g.snd) := rfl

/-- `(S t)† ⊕ (S t)†` maps the graph vector of `η` to that of `(S t)† η`. -/
theorem diagAdjoint_graphVec (t : ℝ≥0) (η : S.generator.adjoint.domain) :
    S.diagAdjoint t (S.graphVec η) =
      (S.graphVec ⟨S.adjoint t η, S.adjoint_mem_adjoint_domain_aux η.2 t⟩ :
        WithLp 2 (E × E)) := by
  rw [diagAdjoint_apply, coe_graphVec, coe_graphVec, generator_adjoint_apply_adjoint_aux]
  rfl

/-- `(S t)† ⊕ (S t)†` preserves the graph of `A†`. -/
theorem diagAdjoint_mem (t : ℝ≥0) (g : S.Extrap) : S.diagAdjoint t g ∈ S.adjGraph := by
  obtain ⟨η, rfl⟩ := S.graphVec_surjective g
  rw [diagAdjoint_graphVec]
  exact Subtype.property _

/-- `(S t)† ⊕ (S t)†` restricted to the graph of `A†`, as an operator on `E₋₁`. -/
def extrapUOp (t : ℝ≥0) : S.Extrap →L[ℝ] S.Extrap :=
  ((S.diagAdjoint t).comp S.adjGraph.subtypeL).codRestrict S.adjGraph (S.diagAdjoint_mem t)

@[simp] theorem coe_extrapUOp (t : ℝ≥0) (g : S.Extrap) :
    (S.extrapUOp t g : WithLp 2 (E × E)) = S.diagAdjoint t g := rfl

theorem extrapUOp_graphVec (t : ℝ≥0) (η : S.generator.adjoint.domain) :
    S.extrapUOp t (S.graphVec η) =
      S.graphVec ⟨S.adjoint t η, S.adjoint_mem_adjoint_domain_aux η.2 t⟩ :=
  Subtype.ext (S.diagAdjoint_graphVec t η)

/-- The C₀-semigroup `(S t)† ⊕ (S t)†` on `E₋₁` (the graph of `A†`); the extended semigroup is
its adjoint (`extrapSemigroup_eq_adjoint`). -/
def extrapU : C0Semigroup ℝ S.Extrap where
  toFun := S.extrapUOp
  map_zero' := by
    ext g : 1
    apply Subtype.ext
    simp [diagAdjoint_apply]
    rfl
  map_add' s t := by
    ext g : 1
    apply Subtype.ext
    change S.diagAdjoint (s + t) g = S.diagAdjoint s (S.diagAdjoint t g)
    simp only [diagAdjoint_apply, S.adjoint.add_apply]
    rfl
  continuous_apply' g := by
    refine Continuous.subtype_mk ?_ _
    exact (WithLp.prod_continuous_toLp 2 E E).comp
      ((S.adjoint.continuous_apply _).prodMk (S.adjoint.continuous_apply _))

theorem extrapU_apply (t : ℝ≥0) : S.extrapU t = S.extrapUOp t := rfl

/-- The adjoint of `extrapU` extends `S`. -/
theorem extrapU_adjoint_toExtrap (t : ℝ≥0) (x : E) :
    S.extrapU.adjoint t (S.toExtrap x) = S.toExtrap (S t x) := by
  refine S.extrap_ext fun η => ?_
  rw [inner_adjoint_apply, extrapU_apply, extrapUOp_graphVec, inner_toExtrap_graphVec,
    inner_toExtrap_graphVec, real_inner_comm, inner_adjoint_apply, real_inner_comm]

-- `extrapSemigroup` is defined by choice from this existence theorem.
/-- The semigroup extends to `E₋₁` (uniquely, by density of `E`). -/
theorem exists_extrapSemigroup :
    ∃ T : C0Semigroup ℝ S.Extrap, ∀ (t : ℝ≥0) (x : E), T t (S.toExtrap x) = S.toExtrap (S t x) :=
  ⟨S.extrapU.adjoint, S.extrapU_adjoint_toExtrap⟩

/-- The **extended semigroup** on `E₋₁`. -/
def extrapSemigroup : C0Semigroup ℝ S.Extrap := S.exists_extrapSemigroup.choose

theorem extrapSemigroup_toExtrap (t : ℝ≥0) (x : E) :
    S.extrapSemigroup t (S.toExtrap x) = S.toExtrap (S t x) :=
  S.exists_extrapSemigroup.choose_spec t x

theorem consistent_extrapSemigroup : Consistent S.toExtrap S S.extrapSemigroup :=
  fun t x => (S.extrapSemigroup_toExtrap t x).symm

/-- The extended semigroup is the Hilbert adjoint of `(S t)† ⊕ (S t)†` on the graph of `A†`. -/
theorem extrapSemigroup_eq_adjoint : S.extrapSemigroup = S.extrapU.adjoint := by
  ext t : 1
  apply DFunLike.coe_injective
  refine S.denseRange_toExtrap.equalizer (map_continuous _) (map_continuous _)
    (funext fun x => ?_)
  simp only [Function.comp_apply, extrapSemigroup_toExtrap, extrapU_adjoint_toExtrap]

/-! ### Weak derivatives in `E₋₁` and Ball's weak formulation -/

/-- **`ẋ = A₋₁ x + f` in `E₋₁` is the weak formulation**: for `x ∈ C([0, τ]; E)` and
`f ∈ L¹(0, τ; E)`, the integral identity `x t = x 0 + ∫₀ᵗ (A₋₁ x + f)` in `E₋₁` holds iff
`⟪η, x t⟫ = ⟪η, x 0⟫ + ∫₀ᵗ (⟪A† η, x⟫ + ⟪η, f⟫)` for every `η ∈ D(A†)`. -/
theorem integral_eq_iff_weak {τ : ℝ} {x f : ℝ → E} (hx : ContinuousOn x (Icc 0 τ))
    (hf : IntegrableOn f (Ioc 0 τ)) :
    (∀ t ∈ Icc 0 τ, S.toExtrap (x t) =
        S.toExtrap (x 0) + ∫ s in (0 : ℝ)..t, (S.genExtrap (x s) + S.toExtrap (f s))) ↔
      ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain), ∀ t ∈ Icc 0 τ,
        ⟪η, x t⟫_ℝ = ⟪η, x 0⟫_ℝ +
          ∫ s in (0 : ℝ)..t, (⟪S.generator.adjoint ⟨η, hη⟩, x s⟫_ℝ + ⟪η, f s⟫_ℝ) := by
  -- Pairing the right-hand side with `(η, A† η)` gives the weak right-hand side.
  have key : ∀ t ∈ Icc 0 τ, ∀ η : S.generator.adjoint.domain,
      ⟪S.graphVec η, S.toExtrap (x 0) +
          ∫ s in (0 : ℝ)..t, (S.genExtrap (x s) + S.toExtrap (f s))⟫_ℝ =
        ⟪(η : E), x 0⟫_ℝ +
          ∫ s in (0 : ℝ)..t, (⟪S.generator.adjoint η, x s⟫_ℝ + ⟪(η : E), f s⟫_ℝ) := by
    intro t ht η
    have hint : IntervalIntegrable (fun s => S.genExtrap (x s) + S.toExtrap (f s)) volume 0 t := by
      refine IntervalIntegrable.add ?_ ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc ht.1
          (S.genExtrap.continuous.comp_continuousOn (hx.mono (Icc_subset_Icc_right ht.2)))
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
        exact S.toExtrap.integrable_comp (hf.mono_set (Ioc_subset_Ioc_right ht.2))
    rw [inner_add_right, inner_intervalIntegral_aux hint, inner_graphVec_toExtrap]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [inner_add_right, inner_graphVec_toExtrap, inner_graphVec_genExtrap]
  constructor
  · intro h η hη t ht
    rw [← key t ht ⟨η, hη⟩, ← h t ht, inner_graphVec_toExtrap]
  · intro h t ht
    refine S.extrap_ext fun η => ?_
    obtain ⟨η, hη⟩ := η
    rw [inner_toExtrap_graphVec, real_inner_comm (S.graphVec ⟨η, hη⟩), key t ht ⟨η, hη⟩,
      real_inner_comm η (x t), h η hη t ht]

/-- Weak solutions (Ball) are exactly the continuous solutions of `ẋ = A₋₁ x + f` in `E₋₁`
(integral form). -/
theorem isWeakSol_iff_extrap {τ : ℝ} {x₀ : E} {f x : ℝ → E} (hf : IntegrableOn f (Ioc 0 τ)) :
    S.IsWeakSol τ x₀ f x ↔
      ContinuousOn x (Icc 0 τ) ∧ x 0 = x₀ ∧
        ∀ t ∈ Icc 0 τ, S.toExtrap (x t) =
          S.toExtrap x₀ + ∫ s in (0 : ℝ)..t, (S.genExtrap (x s) + S.toExtrap (f s)) := by
  constructor
  · rintro ⟨hc, h0, hw⟩
    refine ⟨hc, h0, ?_⟩
    have := (S.integral_eq_iff_weak hc hf).2 (by rw [h0]; exact hw)
    rwa [h0] at this
  · rintro ⟨hc, h0, hi⟩
    refine ⟨hc, h0, ?_⟩
    have := (S.integral_eq_iff_weak hc hf).1 (by rw [h0]; exact hi)
    rwa [h0] at this

end C0Semigroup

end DataDrivenControl
