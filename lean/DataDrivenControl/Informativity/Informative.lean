module

public import DataDrivenControl.Signal.Gramian
public import DataDrivenControl.System.Mild

/-!
# Informative data

Paper: `def:hilbert-informative`, `eq:informative-span`, `lem:informative-gramian`
(`app:informative-gramian`), and the remark after it ("informativity in `U × W` implies
informativity in `U × X`").

## Main declarations

* `Informative T u x`: the pair `(ū, x̄)` is **informative in `U × H`** on the window
  `I = (0, T]` (`def:hilbert-informative`, `eq:informative-span`):
  `cspan ℝ (μI T) (t ↦ (ū t, x̄ t)) = ⊤` in `WithLp 2 (U × H)`.  The record is a pair of
  functions; square integrability (`(ū, x̄) ∈ L²(I; U × H)`) is a hypothesis of the lemmas that
  need it.  The ambient `H ↪ X` of the paper plays no role in the definition: `H` is any real
  inner product space (`U × W` with `H = W`, `U × X` with `H = X`).
* `informative_iff_annihilator`, `informative_iff`: the "equivalently" clause of
  `def:hilbert-informative` (only `(α, β) = 0` annihilates the record a.e.).
* `informative_iff_injective_gramian`: `lem:informative-gramian`, `(ū, x̄)` is informative iff
  the Gramian `𝒢(ū, x̄)` on `U × H` is injective.
* `Informative.mono`, `Informative.congr`: monotonicity in the window and invariance under a.e.
  equality.
* `Informative.map_of_denseRange`: informativity in `U × W` implies informativity in `U × X`
  for a continuous dense-range map `W → X` (the remark after `lem:informative-gramian`);
  `System.Informative.mild_of_mildW` is its instance for the record `(ū, x̄)` with `x̄₀ ∈ W`.

## Upstream results used

`cspan_eq_top_iff`, `cspan_pair_eq_top_iff`, `cspan_μI_mono`, `cspan_congr`
(`Signal/Span`); `gramian_injective_iff_cspan_eq_top` (`Signal/Gramian`);
`MemLp.of_fst_of_snd_prodLp` (Mathlib); `ContinuousLinearMap.adjoint_inner_left` and
`DenseRange` (Mathlib); `System.ιW_mildW` (`System/Mild`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option autoImplicit false

namespace DataDrivenControl

variable {U H X : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- **Informative data** (`def:hilbert-informative`, `eq:informative-span`): the pair
`(ū, x̄)` is *informative in `U × H`* on the window `(0, T]` if the record
`t ↦ (ū t, x̄ t)` spans `U × H` densely, `cspan (ū, x̄) = U × H` (closed span in
`WithLp 2 (U × H)`).  The paper assumes `(ū, x̄) ∈ L²(I; U × H)`; the lemmas
that need it take `MemLp` hypotheses. -/
def Informative (T : ℝ) (u : ℝ → U) (x : ℝ → H) : Prop :=
  cspan ℝ (μI T) (fun t => WithLp.toLp 2 (u t, x t)) = ⊤

variable {T : ℝ} {u : ℝ → U} {x : ℝ → H}

/-- Informativity is the triviality of the annihilator of the record. -/
theorem informative_iff_annihilator :
    Informative T u x ↔ annihilator ℝ (μI T) (fun t => WithLp.toLp 2 (u t, x t)) = ⊥ :=
  cspan_eq_top_iff

/-- The "equivalently" clause of `def:hilbert-informative`: `(ū, x̄)` is informative iff
`⟪α, ū t⟫ + ⟪β, x̄ t⟫ = 0` for a.e. `t ∈ I` forces `(α, β) = 0`. -/
theorem informative_iff :
    Informative T u x ↔
      ∀ (a : U) (b : H), (∀ᵐ t ∂(μI T), ⟪a, u t⟫_ℝ + ⟪b, x t⟫_ℝ = 0) → a = 0 ∧ b = 0 :=
  cspan_pair_eq_top_iff

/-- Use an informative record: an annihilator `(α, β)` of the record vanishes. -/
theorem Informative.eq_zero (h : Informative T u x) {a : U} {b : H}
    (hab : ∀ᵐ t ∂(μI T), ⟪a, u t⟫_ℝ + ⟪b, x t⟫_ℝ = 0) : a = 0 ∧ b = 0 :=
  informative_iff.1 h a b hab

/-- **Gramian characterisation of informative data** (`lem:informative-gramian`): a pair
`(ū, x̄) ∈ L²(I; U × H)` is informative in `U × H` iff its Gramian `𝒢(ū, x̄)` on `U × H` is
injective. -/
theorem informative_iff_injective_gramian [CompleteSpace U] [CompleteSpace H]
    (hu : MemLp u 2 (μI T)) (hx : MemLp x 2 (μI T)) :
    Informative T u x ↔
      Function.Injective (gramian ℝ (μI T) (fun t => WithLp.toLp 2 (u t, x t))) :=
  (gramian_injective_iff_cspan_eq_top (MemLp.of_fst_of_snd_prodLp ⟨hu, hx⟩)).symm

/-- Informativity on a window `(0, T]` gives informativity on every longer window. -/
theorem Informative.mono {T' : ℝ} (h : Informative T u x) (hT : T ≤ T') :
    Informative T' u x :=
  top_unique (h ▸ cspan_μI_mono hT)

/-- Informativity only depends on the record almost everywhere on the window. -/
theorem Informative.congr {u' : ℝ → U} {x' : ℝ → H} (h : Informative T u x)
    (hu : u =ᵐ[μI T] u') (hx : x =ᵐ[μI T] x') : Informative T u' x' := by
  have hp : (fun t => WithLp.toLp 2 (u t, x t)) =ᵐ[μI T] fun t => WithLp.toLp 2 (u' t, x' t) :=
    hu.mp (hx.mono fun t hxt hut => by simp only [hut, hxt])
  unfold Informative at h ⊢
  rwa [← cspan_congr hp]

/-- **Informativity in `U × W` implies informativity in `U × X`** (remark after
`lem:informative-gramian`): if `ι : H → X` is continuous with dense range (e.g. the dense
embedding `W ↪ X`) and `(ū, x̄)` is informative in `U × H`, then `(ū, ι ∘ x̄)` is informative in
`U × X`.  Only the density of the range is used. -/
theorem Informative.map_of_denseRange [CompleteSpace H] [CompleteSpace X] {ι : H →L[ℝ] X}
    (hι : DenseRange ι) (h : Informative T u x) : Informative T u (fun t => ι (x t)) := by
  rw [informative_iff] at h ⊢
  intro a b hab
  have hab' : ∀ᵐ t ∂(μI T), ⟪a, u t⟫_ℝ + ⟪(ContinuousLinearMap.adjoint ι) b, x t⟫_ℝ = 0 :=
    hab.mono fun t ht => by rwa [ContinuousLinearMap.adjoint_inner_left]
  obtain ⟨ha, hb⟩ := h a _ hab'
  refine ⟨ha, ?_⟩
  have hperp : ∀ w : H, ⟪b, ι w⟫_ℝ = 0 := fun w => by
    rw [← ContinuousLinearMap.adjoint_inner_left, hb, inner_zero_left]
  have hcl : ∀ y ∈ closure (Set.range ι), ⟪b, y⟫_ℝ = 0 := by
    intro y hy
    have hc : IsClosed {y : X | ⟪b, y⟫_ℝ = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    exact hc.closure_subset_iff.2 (by rintro _ ⟨w, rfl⟩; exact hperp w) hy
  exact inner_self_eq_zero.1 (hcl b (hι.closure_range ▸ Set.mem_univ b))

namespace System

variable {W V Y : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [CompleteSpace U] [CompleteSpace X]

/-- The remark after `lem:informative-gramian` for a record: if the record `(ū, x̄)` generated by
`(x̄₀, ū)` with `x̄₀ ∈ W` is informative in `U × W` (state `sys.mildW x̄₀ ū`), it is informative
in `U × X` (state `sys.mild (ιW x̄₀) ū`). -/
theorem Informative.mild_of_mildW (sys : System U W X V Y) {w₀ : W}
    (h : Informative T u (sys.mildW w₀ u)) : Informative T u (sys.mild (sys.ιW w₀) u) := by
  have := h.map_of_denseRange sys.ιW_denseRange
  simpa only [ιW_mildW] using this

end System

end DataDrivenControl
