module

public import DataDrivenControl.Semigroup.Generator

/-!
# The domain of the generator as a Hilbert space

Real Hilbert spaces.

For a C₀-semigroup `S` on a real Hilbert space `E` with generator `A`, the domain `D(A)` with
the graph norm `‖x‖²_{D(A)} = ‖x‖² + ‖A x‖²` is realised, as `C0Semigroup.Extrap` is, by the
graph of `A`: a closed subspace of `WithLp 2 (E × E)` (`generator_isClosed`), hence a Hilbert
space.  It is the type `S.Dom`.  The heat example takes `W = D(A_V)` and the
delay example takes `W = D(A)`.

## Main declarations

* `S.domGraph`, `isClosed_domGraph`, `S.Dom` (with its `CompleteSpace` instance);
* `S.domIncl : S.Dom →L[ℝ] E` (`(x, A x) ↦ x`) and `S.domGen : S.Dom →L[ℝ] E`
  (`(x, A x) ↦ A x`): `domIncl_mem`, `generator_domIncl`, `domIncl_injective`,
  `denseRange_domIncl`, `range_domIncl`, `norm_sq_dom` (`‖w‖² = ‖x‖² + ‖A x‖²`);
* `S.toDom : D(A) →ₗ[ℝ] S.Dom`, `x ↦ (x, A x)` (`domIncl_toDom`, `domGen_toDom`,
  `norm_toDom_sq`, `norm_toDom_le`);
* `S.domSemigroup : C0Semigroup ℝ S.Dom`, the restriction `S t ⊕ S t` of `S` to the graph
  (strongly continuous in the graph norm because `S t` commutes with `A`):
  `consistent_domSemigroup` (`Consistent S.domIncl S.domSemigroup S`).

## The part of a generator

`C0Semigroup.Consistent.exists_mem_generator_domain` and
`C0Semigroup.Consistent.mem_generator_domain_iff`: if `ι : F →L[𝕜] E` is injective and
`Consistent ι S' S` (Banach spaces), then `v ∈ D(A')` iff `ι v ∈ D(A)` and `A (ι v) ∈ range ι`,
and then `ι (A' v) = A (ι v)` (`Consistent.generator_apply` of `Semigroup/Generator`).  This
generalises `System.mem_AW_domain_of_ιW` (`Informativity/Analytic/Transfer`, the case `W ⊂ X`);
the proof uses `S t v - v = ∫₀ᵗ S s (A v) ds` instead of resolvents.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace C0Semigroup

/-! ### The part of a generator in a continuously embedded invariant subspace -/

section Part

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [CompleteSpace F]
  {S : C0Semigroup 𝕜 E} {S' : C0Semigroup 𝕜 F} {ι : F →L[𝕜] E}

/-- **The part of a generator.**  Let `ι : F →L[𝕜] E` be injective with `ι ∘ S' t = S t ∘ ι`.  If
`ι v ∈ D(A)` and `A (ι v) = ι g`, then `v ∈ D(A')` and `A' v = g`.  (Generalises
`System.mem_AW_domain_of_ιW`.) -/
theorem Consistent.exists_mem_generator_domain (h : Consistent ι S' S)
    (hι : Function.Injective ι) {v g : F} (hv : ι v ∈ S.generator.domain)
    (hA : S.generator ⟨ι v, hv⟩ = ι g) :
    ∃ hv' : v ∈ S'.generator.domain, S'.generator ⟨v, hv'⟩ = g := by
  -- `S' t v - v = ∫₀ᵗ S' s g ds`, read through the injective `ι`.
  have key : ∀ t : ℝ, 0 ≤ t → S'.real t v - v = ∫ s in (0 : ℝ)..t, S'.real s g := by
    intro t ht
    apply hι
    have hint : IntervalIntegrable (fun s => S'.real s g) volume 0 t :=
      (S'.continuous_real_apply g).intervalIntegrable 0 t
    calc ι (S'.real t v - v) = S.real t (ι v) - ι v := by rw [map_sub, h.real]
      _ = ∫ s in (0 : ℝ)..t, S.real s (S.generator ⟨ι v, hv⟩) :=
          S.real_apply_sub_eq_integral ⟨ι v, hv⟩ t ht
      _ = ∫ s in (0 : ℝ)..t, ι (S'.real s g) := by
          rw [hA]
          exact intervalIntegral.integral_congr fun s _ => (h.real s g).symm
      _ = ι (∫ s in (0 : ℝ)..t, S'.real s g) := ι.intervalIntegral_comp_comm hint
  have hlim : Tendsto (S'.diffQuot v) (𝓝[>] 0) (𝓝 g) :=
    (S'.tendsto_inv_smul_integral g).congr' (eventually_nhdsWithin_of_forall fun t ht => by
      rw [C0Semigroup.diffQuot, key t (le_of_lt ht)])
  exact ⟨S'.mem_generator_domain_of_tendsto hlim, S'.generator_apply_eq _ hlim⟩

/-- **The generator of a consistent semigroup is the part of `A`**: for injective `ι` with
`Consistent ι S' S`, `v ∈ D(A')` iff `ι v ∈ D(A)` and `A (ι v) ∈ range ι`; then
`ι (A' v) = A (ι v)` by `Consistent.generator_apply`. -/
theorem Consistent.mem_generator_domain_iff (h : Consistent ι S' S)
    (hι : Function.Injective ι) {v : F} :
    v ∈ S'.generator.domain ↔
      ∃ hv : ι v ∈ S.generator.domain, S.generator ⟨ι v, hv⟩ ∈ Set.range ι := by
  constructor
  · intro hv
    exact ⟨h.mem_generator_domain S hv, ⟨_, (h.generator_apply S hv).symm⟩⟩
  · rintro ⟨hv, g, hg⟩
    exact (h.exists_mem_generator_domain hι hv hg.symm).1

end Part

/-! ### `D(A)` with the graph norm -/

section Dom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (S : C0Semigroup ℝ E)

/-- The graph of the generator `A` as a subspace of the Hilbert space `WithLp 2 (E × E)`. -/
def domGraph : Submodule ℝ (WithLp 2 (E × E)) :=
  S.generator.graph.comap (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

/-- The graph of the generator is closed. -/
theorem isClosed_domGraph : IsClosed (S.domGraph : Set (WithLp 2 (E × E))) :=
  S.generator_isClosed.preimage (WithLp.prod_continuous_ofLp 2 E E)

/-- **`D(A)` with the graph norm**: the graph of `A` with the inner product of
`WithLp 2 (E × E)`, a Hilbert space; `‖(x, A x)‖² = ‖x‖² + ‖A x‖²` (`norm_sq_dom`). -/
abbrev Dom : Type _ := ↥S.domGraph

instance : CompleteSpace S.Dom := S.isClosed_domGraph.isComplete.completeSpace_coe

/-- The embedding `D(A) ↪ E`, `(x, A x) ↦ x`. -/
def domIncl : S.Dom →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E E).comp S.domGraph.subtypeL

/-- The generator as a bounded operator `D(A) → E`, `(x, A x) ↦ A x`. -/
def domGen : S.Dom →L[ℝ] E :=
  (WithLp.sndL 2 ℝ E E).comp S.domGraph.subtypeL

/-- The constructor `D(A) → S.Dom`, `x ↦ (x, A x)`. -/
def toDom : S.generator.domain →ₗ[ℝ] S.Dom :=
  LinearMap.codRestrict S.domGraph
    ((WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap ∘ₗ
      (S.generator.domain.subtype.prod S.generator.toFun))
    fun x => (LinearPMap.mem_graph_iff S.generator).2 ⟨x, rfl, rfl⟩

@[simp] theorem coe_toDom (x : S.generator.domain) :
    (S.toDom x : WithLp 2 (E × E)) = WithLp.toLp 2 ((x : E), S.generator x) := rfl

@[simp] theorem domIncl_toDom (x : S.generator.domain) : S.domIncl (S.toDom x) = x := rfl

@[simp] theorem domGen_toDom (x : S.generator.domain) :
    S.domGen (S.toDom x) = S.generator x := rfl

/-- `toDom` is onto: every element of `S.Dom` is `(x, A x)` for some `x ∈ D(A)`. -/
theorem toDom_surjective : Function.Surjective S.toDom := by
  rintro ⟨g, hg⟩
  obtain ⟨x, h1, h2⟩ := (LinearPMap.mem_graph_iff S.generator).1 hg
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_toDom]
  exact (WithLp.ext_iff 2).2 (Prod.ext h1 h2)

/-- `S.domIncl w ∈ D(A)`. -/
theorem domIncl_mem (w : S.Dom) : S.domIncl w ∈ S.generator.domain := by
  obtain ⟨x, rfl⟩ := S.toDom_surjective w
  exact x.2

/-- `A (domIncl w) = domGen w`. -/
theorem generator_domIncl (w : S.Dom) :
    S.generator ⟨S.domIncl w, S.domIncl_mem w⟩ = S.domGen w := by
  obtain ⟨x, rfl⟩ := S.toDom_surjective w
  rfl

/-- Elements of `S.Dom` are determined by their first component. -/
theorem dom_ext {w w' : S.Dom} (h : S.domIncl w = S.domIncl w') : w = w' := by
  obtain ⟨x, rfl⟩ := S.toDom_surjective w
  obtain ⟨x', rfl⟩ := S.toDom_surjective w'
  have hx : x = x' := Subtype.ext h
  rw [hx]

/-- `D(A) ↪ E` is injective. -/
theorem domIncl_injective : Function.Injective S.domIncl := fun _ _ h => S.dom_ext h

/-- The range of `D(A) ↪ E` is `D(A)`. -/
theorem range_domIncl : Set.range S.domIncl = (S.generator.domain : Set E) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact S.domIncl_mem w
  · intro hx
    exact ⟨S.toDom ⟨x, hx⟩, rfl⟩

/-- Every `x ∈ D(A)` is the image of an element of `S.Dom`. -/
theorem exists_domIncl_eq {x : E} (hx : x ∈ S.generator.domain) :
    ∃ w : S.Dom, S.domIncl w = x :=
  ⟨S.toDom ⟨x, hx⟩, rfl⟩

/-- `D(A)` is dense in `E`. -/
theorem denseRange_domIncl : DenseRange S.domIncl := by
  rw [DenseRange, range_domIncl]
  exact S.dense_generator_domain

/-- The graph norm: `‖w‖² = ‖x‖² + ‖A x‖²` for `w = (x, A x)`. -/
theorem norm_sq_dom (w : S.Dom) : ‖w‖ ^ 2 = ‖S.domIncl w‖ ^ 2 + ‖S.domGen w‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (w : WithLp 2 (E × E))

/-- `‖(x, A x)‖² = ‖x‖² + ‖A x‖²`. -/
theorem norm_toDom_sq (x : S.generator.domain) :
    ‖S.toDom x‖ ^ 2 = ‖(x : E)‖ ^ 2 + ‖S.generator x‖ ^ 2 :=
  S.norm_sq_dom _

/-- `‖(x, A x)‖ ≤ ‖x‖ + ‖A x‖`. -/
theorem norm_toDom_le (x : S.generator.domain) :
    ‖S.toDom x‖ ≤ ‖(x : E)‖ + ‖S.generator x‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [S.norm_toDom_sq x]
  nlinarith [mul_nonneg (norm_nonneg (x : E)) (norm_nonneg (S.generator x))]

/-! ### The restricted semigroup -/

/-- `S t ⊕ S t` on `WithLp 2 (E × E)`. -/
def domDiag (t : ℝ≥0) : WithLp 2 (E × E) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    ((S t).prodMap (S t)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

theorem domDiag_apply (t : ℝ≥0) (g : WithLp 2 (E × E)) :
    S.domDiag t g = WithLp.toLp 2 (S t g.fst, S t g.snd) := rfl

/-- `S t ⊕ S t` preserves the graph of `A` (`S t D(A) ⊆ D(A)`, `A S t = S t A`). -/
theorem domDiag_mem (t : ℝ≥0) (w : S.Dom) : S.domDiag t w ∈ S.domGraph := by
  obtain ⟨x, rfl⟩ := S.toDom_surjective w
  refine (LinearPMap.mem_graph_iff S.generator).2
    ⟨⟨S t x, S.mem_generator_domain_apply x.2 t⟩, rfl, ?_⟩
  exact S.generator_apply_apply x.2 t

/-- `S t ⊕ S t` restricted to the graph of `A`, as an operator on `D(A)`. -/
def domSemigroupOp (t : ℝ≥0) : S.Dom →L[ℝ] S.Dom :=
  ((S.domDiag t).comp S.domGraph.subtypeL).codRestrict S.domGraph (S.domDiag_mem t)

@[simp] theorem coe_domSemigroupOp (t : ℝ≥0) (w : S.Dom) :
    (S.domSemigroupOp t w : WithLp 2 (E × E)) = S.domDiag t w := rfl

/-- The **restricted semigroup** on `D(A)` with the graph norm: `(x, A x) ↦ (S t x, S t A x)`. -/
def domSemigroup : C0Semigroup ℝ S.Dom where
  toFun := S.domSemigroupOp
  map_zero' := by
    ext w : 1
    apply Subtype.ext
    simp [domDiag_apply]
    rfl
  map_add' s t := by
    ext w : 1
    apply Subtype.ext
    change S.domDiag (s + t) w = S.domDiag s (S.domDiag t w)
    simp only [domDiag_apply, S.add_apply]
    rfl
  continuous_apply' w := by
    refine Continuous.subtype_mk ?_ _
    exact (WithLp.prod_continuous_toLp 2 E E).comp
      ((S.continuous_apply _).prodMk (S.continuous_apply _))

@[simp] theorem domIncl_domSemigroup (t : ℝ≥0) (w : S.Dom) :
    S.domIncl (S.domSemigroup t w) = S t (S.domIncl w) := rfl

@[simp] theorem domGen_domSemigroup (t : ℝ≥0) (w : S.Dom) :
    S.domGen (S.domSemigroup t w) = S t (S.domGen w) := rfl

theorem domIncl_domSemigroup_real (t : ℝ) (w : S.Dom) :
    S.domIncl (S.domSemigroup.real t w) = S.real t (S.domIncl w) := rfl

/-- The restricted semigroup is consistent with `S` along `D(A) ↪ E`. -/
theorem consistent_domSemigroup : Consistent S.domIncl S.domSemigroup S := fun _ _ => rfl

end Dom

end C0Semigroup

end DataDrivenControl
