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
  projection (`inner_genExtrap_graphVec`); it extends `A` (`genExtrap_of_mem`);
* `toExtrap_injective`, `denseRange_toExtrap`;
* `S.extrapSemigroup : C0Semigroup ℝ S.Extrap` extends `S` (`extrapSemigroup_toExtrap`,
  `consistent_extrapSemigroup`); its generator has domain `range toExtrap` and acts as
  `A₋₁` (`mem_extrapSemigroup_generator_domain_iff`, `extrapSemigroup_generator_toExtrap`);
* `integral_eq_iff_weak`, `isWeakSol_iff_extrap`: `ẋ = A₋₁ x + f` in `E₋₁` (integral form)
  is exactly the weak formulation of Ball's theorem.

## Proof notes

* `D(A†)` is dense because `A` is closed and densely defined
  (`dense_adjoint_domain_of_isClosed`, from Mathlib's graph description of `A†`).
* `(S t)†` preserves `D(A†)` and commutes with `A†` (`adjoint_mem_adjoint_domain_aux`,
  `generator_adjoint_apply_adjoint_aux`, proved from `S t D(A) ⊆ D(A)`), so
  `(S t)† ⊕ (S t)†` restricts to a C₀-semigroup `S.extrapU` on the graph `E₋₁`; the extended
  semigroup is its Hilbert adjoint (`extrapSemigroup_eq_adjoint`), i.e.
  `⟪T t φ, (η, A† η)⟫ = ⟪S t φ₁, η⟫ + ⟪S t φ₂, A† η⟫` (`inner_extrapSemigroup_graphVec`).
* `E ⊆ D(A_{-1})`: `S h x - x = ∫₀ʰ A₋₁ S s x ds` in `E₋₁` (`toExtrap_real_apply_sub`).
* `D(A_{-1}) ⊆ E`: `∫₀ˢ T r φ dr` is the image of the explicit element
  `S.extrapIntegral s φ = ∫₀ˢ S r φ₁ dr + S s φ₂ - φ₂ ∈ E` (`toExtrap_extrapIntegral`), and
  `φ = ∫₀¹ T s φ ds - ∫₀¹ (T s φ - φ) ds = ∫₀¹ T s φ ds - ∫₀¹ ∫₀ˢ T r (A_{-1} φ) dr ds`.

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

theorem mem_adjGraph_iff (g : WithLp 2 (E × E)) :
    g ∈ S.adjGraph ↔ (WithLp.ofLp g) ∈ S.generator.adjoint.graph := Iff.rfl

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

/-- `D(A†)` is dense (from closedness of the generator, via the graph of `A†`). -/
theorem dense_generator_adjoint_domain : Dense (S.generator.adjoint.domain : Set E) :=
  dense_adjoint_domain_of_isClosed S.generator_isClosed

@[simp] theorem fstG_graphVec (η : S.generator.adjoint.domain) : S.fstG (S.graphVec η) = η :=
  rfl

@[simp] theorem sndG_graphVec (η : S.generator.adjoint.domain) :
    S.sndG (S.graphVec η) = S.generator.adjoint η := rfl

theorem fstG_apply (φ : S.Extrap) : S.fstG φ = (φ : WithLp 2 (E × E)).fst := rfl

theorem sndG_apply (φ : S.Extrap) : S.sndG φ = (φ : WithLp 2 (E × E)).snd := rfl

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

/-- `E ↪ E₋₁` is injective. -/
theorem toExtrap_injective : Function.Injective S.toExtrap := by
  refine (injective_iff_map_eq_zero S.toExtrap).2 fun x hx => ?_
  refine S.dense_generator_adjoint_domain.eq_zero_of_inner_left ℝ fun η hη => ?_
  rw [← S.inner_toExtrap_graphVec x ⟨η, hη⟩, hx, inner_zero_left]

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

/-- `A₋₁` extends `A`: `A₋₁ x = A x` (in `E₋₁`) for `x ∈ D(A)`. -/
theorem genExtrap_of_mem (x : S.generator.domain) :
    S.genExtrap x = S.toExtrap (S.generator x) := by
  refine S.extrap_ext fun η => ?_
  rw [inner_genExtrap_graphVec, inner_toExtrap_graphVec, real_inner_comm,
    LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain η x, real_inner_comm]

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

/-- The action of the extended semigroup on test vectors:
`⟪T t φ, (η, A† η)⟫ = ⟪S t φ₁, η⟫ + ⟪S t φ₂, A† η⟫` for `φ = (φ₁, φ₂) ∈ E₋₁`. -/
theorem inner_extrapSemigroup_graphVec (t : ℝ≥0) (φ : S.Extrap)
    (η : S.generator.adjoint.domain) :
    ⟪S.extrapSemigroup t φ, S.graphVec η⟫_ℝ =
      ⟪S t (S.fstG φ), (η : E)⟫_ℝ + ⟪S t (S.sndG φ), S.generator.adjoint η⟫_ℝ := by
  rw [extrapSemigroup_eq_adjoint, inner_adjoint_apply, extrapU_apply, extrapUOp_graphVec,
    Submodule.coe_inner, WithLp.prod_inner_apply, coe_graphVec,
    generator_adjoint_apply_adjoint_aux _ η.2]
  simp only [adjoint_apply, ContinuousLinearMap.adjoint_inner_right, fstG_apply,
    sndG_apply, WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- Real-time version of `inner_extrapSemigroup_graphVec`. -/
theorem inner_extrapSemigroup_real_graphVec (t : ℝ) (φ : S.Extrap)
    (η : S.generator.adjoint.domain) :
    ⟪S.extrapSemigroup.real t φ, S.graphVec η⟫_ℝ =
      ⟪S.real t (S.fstG φ), (η : E)⟫_ℝ + ⟪S.real t (S.sndG φ), S.generator.adjoint η⟫_ℝ :=
  S.inner_extrapSemigroup_graphVec _ φ η

/-- The weak derivative of an orbit: `⟪S s x - x, η⟫ = ∫₀ˢ ⟪S r x, A† η⟫ dr` for
`η ∈ D(A†)` and `s ≥ 0`. -/
theorem inner_real_apply_sub_eq_integral_inner (x : E) (η : S.generator.adjoint.domain)
    {s : ℝ} (hs : 0 ≤ s) :
    ⟪S.real s x - x, (η : E)⟫_ℝ = ∫ r in (0 : ℝ)..s, ⟪S.real r x, S.generator.adjoint η⟫_ℝ := by
  have hfa := LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain η
    ⟨_, S.integral_mem_generator_domain x hs⟩
  rw [← S.generator_integral x hs, real_inner_comm, ← hfa,
    inner_intervalIntegral_aux ((S.continuous_real_apply x).intervalIntegrable 0 s)]
  exact intervalIntegral.integral_congr fun r _ => real_inner_comm _ _

/-- `S s x - x = ∫₀ˢ A₋₁ S r x dr` in `E₋₁`, for every `x ∈ E` and `s ≥ 0`. -/
theorem toExtrap_real_apply_sub (x : E) {s : ℝ} (hs : 0 ≤ s) :
    S.toExtrap (S.real s x - x) = ∫ r in (0 : ℝ)..s, S.genExtrap (S.real r x) := by
  refine S.extrap_ext fun η => ?_
  have hint : IntervalIntegrable (fun r => S.genExtrap (S.real r x)) volume 0 s :=
    (S.genExtrap.continuous.comp (S.continuous_real_apply x)).intervalIntegrable 0 s
  rw [inner_toExtrap_graphVec, S.inner_real_apply_sub_eq_integral_inner x η hs,
    real_inner_comm (S.graphVec η), inner_intervalIntegral_aux hint]
  exact intervalIntegral.integral_congr fun r _ => by
    rw [inner_graphVec_genExtrap, real_inner_comm]

/-- The difference quotients of the extended semigroup at `x ∈ E` converge to `A₋₁ x`. -/
theorem tendsto_diffQuot_extrapSemigroup (x : E) :
    Tendsto (S.extrapSemigroup.diffQuot (S.toExtrap x)) (𝓝[>] 0) (𝓝 (S.genExtrap x)) := by
  have hc : Continuous fun r => S.genExtrap (S.real r x) :=
    S.genExtrap.continuous.comp (S.continuous_real_apply x)
  have hd := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, S.real_zero,
    one_apply_eq_self] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  rw [← S.consistent_extrapSemigroup.diffQuot S.extrapSemigroup x h, diffQuot, map_smul,
    S.toExtrap_real_apply_sub x hh.le]

/-- `E ⊆ D(A_{-1})` for the generator `A_{-1}` of the extended semigroup. -/
theorem toExtrap_mem_extrapSemigroup_generator_domain (x : E) :
    S.toExtrap x ∈ S.extrapSemigroup.generator.domain :=
  S.extrapSemigroup.mem_generator_domain_of_tendsto (S.tendsto_diffQuot_extrapSemigroup x)

/-- `∫₀ˢ S r φ₁ dr + S s φ₂ - φ₂ ∈ E` for `φ = (φ₁, φ₂) ∈ E₋₁`: its image in `E₋₁` is
`∫₀ˢ T r φ dr` (`toExtrap_extrapIntegral`). -/
def extrapIntegral (s : ℝ) (φ : S.Extrap) : E :=
  (∫ r in (0 : ℝ)..s, S.real r (S.fstG φ)) + (S.real s (S.sndG φ) - S.sndG φ)

theorem continuous_extrapIntegral (φ : S.Extrap) : Continuous fun s => S.extrapIntegral s φ :=
  (intervalIntegral.continuous_primitive
    (fun a b => (S.continuous_real_apply _).intervalIntegrable a b) 0).add
    ((S.continuous_real_apply _).sub continuous_const)

/-- Integrals of the extended semigroup lie in `E`: `∫₀ˢ T r φ dr = extrapIntegral s φ`. -/
theorem toExtrap_extrapIntegral (φ : S.Extrap) {s : ℝ} (hs : 0 ≤ s) :
    S.toExtrap (S.extrapIntegral s φ) = ∫ r in (0 : ℝ)..s, S.extrapSemigroup.real r φ := by
  refine S.extrap_ext fun η => ?_
  have h1 : IntervalIntegrable (fun r => S.real r (S.fstG φ)) volume 0 s :=
    (S.continuous_real_apply _).intervalIntegrable 0 s
  have h2 : IntervalIntegrable (fun r => S.extrapSemigroup.real r φ) volume 0 s :=
    (S.extrapSemigroup.continuous_real_apply φ).intervalIntegrable 0 s
  have h3 : IntervalIntegrable (fun r => ⟪(η : E), S.real r (S.fstG φ)⟫_ℝ) volume 0 s :=
    (continuous_const.inner (S.continuous_real_apply _)).intervalIntegrable 0 s
  have h4 : IntervalIntegrable (fun r => ⟪S.real r (S.sndG φ), S.generator.adjoint η⟫_ℝ)
      volume 0 s :=
    ((S.continuous_real_apply _).inner continuous_const).intervalIntegrable 0 s
  rw [inner_toExtrap_graphVec, extrapIntegral, inner_add_left,
    S.inner_real_apply_sub_eq_integral_inner _ η hs, real_inner_comm (η : E),
    inner_intervalIntegral_aux h1, real_inner_comm (S.graphVec η),
    inner_intervalIntegral_aux h2, ← intervalIntegral.integral_add h3 h4]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [real_inner_comm _ (S.graphVec η), inner_extrapSemigroup_real_graphVec,
    real_inner_comm (η : E)]

/-- The domain of the extended generator is (the image of) `E`. -/
theorem mem_extrapSemigroup_generator_domain_iff (φ : S.Extrap) :
    φ ∈ S.extrapSemigroup.generator.domain ↔ ∃ x : E, S.toExtrap x = φ := by
  refine ⟨fun hφ => ?_, ?_⟩
  · -- `φ = ∫₀¹ T s φ ds - ∫₀¹ (T s φ - φ) ds` and `T s φ - φ = ∫₀ˢ T r (A_{-1} φ) dr`.
    have h1 : EqOn (fun s => S.extrapSemigroup.real s φ - φ)
        (fun s => S.toExtrap (S.extrapIntegral s (S.extrapSemigroup.generator ⟨φ, hφ⟩)))
        (uIcc 0 1) := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact (S.extrapSemigroup.real_apply_sub_eq_integral ⟨φ, hφ⟩ s hs.1).trans
        (S.toExtrap_extrapIntegral _ hs.1).symm
    refine ⟨S.extrapIntegral 1 φ -
      ∫ s in (0 : ℝ)..1, S.extrapIntegral s (S.extrapSemigroup.generator ⟨φ, hφ⟩), ?_⟩
    rw [map_sub, S.toExtrap_extrapIntegral φ zero_le_one,
      ← S.toExtrap.intervalIntegral_comp_comm
        ((S.continuous_extrapIntegral _).intervalIntegrable 0 1),
      ← intervalIntegral.integral_congr h1,
      intervalIntegral.integral_sub
        ((S.extrapSemigroup.continuous_real_apply φ).intervalIntegrable 0 1)
        intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  · rintro ⟨x, rfl⟩
    exact S.toExtrap_mem_extrapSemigroup_generator_domain x

/-- The extended generator acts on `E` as `A₋₁`. -/
theorem extrapSemigroup_generator_toExtrap (x : E)
    (hx : S.toExtrap x ∈ S.extrapSemigroup.generator.domain) :
    S.extrapSemigroup.generator ⟨S.toExtrap x, hx⟩ = S.genExtrap x :=
  S.extrapSemigroup.generator_apply_eq hx (S.tendsto_diffQuot_extrapSemigroup x)

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
