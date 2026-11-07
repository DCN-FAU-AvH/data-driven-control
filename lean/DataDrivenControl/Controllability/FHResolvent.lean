module

public import DataDrivenControl.Controllability.FHObservation
public import DataDrivenControl.Semigroup.CompactResolvent
public import DataDrivenControl.Informativity.Analytic.Transfer

/-!
# Fattorini–Hautus, step FH3: the unobservable subspace and one resolvent of `A⋆`

Paper: `prop:fattorini-hautus` (cited from Boyer, Thm III.3.7; proved here).

## Main declarations (namespace `DataDrivenControl.FH`)

* `FH.unobsC sys = (FH.unobs sys)_ℂ ⊆ X_ℂ`, closed (`isClosed_unobsC`).
* `FH.exists_real_resolvent`: a real `μ₀ ∈ ρ(A)` beyond the growth bound with
  `R(μ₀, A)† N ⊆ N`.
* `FH.resolvent_adjoint_complexify_eq` / `FH.adjoint_resolvent_adjoint_complexify`: for real
  `μ₀ ∈ ρ(A)`, `K = R(μ₀, A⋆) = (R(μ₀, A)†)_ℂ` and `K† = R(μ₀, A_ℂ)`; `FH.resolvent_mem_unobsC`:
  `K N_ℂ ⊆ N_ℂ`.
* `FH.eq_zero_of_resolvent_eq_smul` (**no eigenvectors in `N_ℂ`**): under the Hautus condition,
  if `R(z, A⋆) ξ = ν ξ` with `ν ≠ 0` and `ξ ∈ N_ℂ`, then `ξ = 0`.  (`ξ` is an eigenvector of
  `A⋆` with eigenvalue `z - ν⁻¹`, and `B⋆ ξ = 0` by `FH.bstar_eq_zero_of_mem_unobs`.)
* `FH.injective_resolvent`: resolvents are injective.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace FH

open _root_.DataDrivenControl.System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The complexified unobservable subspace `N_ℂ = N + i N ⊆ X_ℂ`. -/
abbrev unobsC (sys : System U W X V Y) : Submodule ℂ (Complexification X) :=
  (unobs sys).complexify

variable {sys : System U W X V Y}

/-- `N_ℂ` is closed (`N` is). -/
theorem isClosed_unobsC : IsClosed (unobsC sys : Set (Complexification X)) :=
  Submodule.isClosed_complexify_iff.2 isClosed_unobs

/-- Resolvents are injective: `R(μ) x = 0` gives `x = (μ - A) R(μ) x = 0`. -/
theorem injective_resolvent {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : E →ₗ.[𝕜] E} {μ : 𝕜} (hμ : μ ∈ resolventSet A) : Function.Injective (resolvent A μ) := by
  intro x y hxy
  have hx := sub_resolvent hμ x
  have hy := sub_resolvent hμ y
  rw [← hx, ← hy]
  simp only [hxy]

/-- A real point `μ₀ ∈ ρ(A)` beyond the growth bound of `S`, at which `R(μ₀, A)†` leaves `N`
invariant (`adjoint_resolvent_mem_unobs`). -/
theorem exists_real_resolvent {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    ∃ μ₀ : ℝ, μ₀ ∈ resolventSet sys.A ∧
      ∀ η ∈ unobs sys, ContinuousLinearMap.adjoint (resolvent sys.A μ₀) η ∈ unobs sys := by
  obtain ⟨M, ω, -, hS⟩ := sys.SX.exists_norm_le_exp
  have hω : ω < max ω 0 + 1 := by linarith [le_max_left ω 0]
  refine ⟨max ω 0 + 1, ?_, fun η hη => adjoint_resolvent_mem_unobs hH1 hT hS hω hη⟩
  have := sys.SX.mem_resolventSet (𝕜 := ℝ) hS (μ := max ω 0 + 1) (by simpa using hω)
  simpa using this

/-- `μ₀ ∈ ρ(A†)` and `R(μ₀, A†) = R(μ₀, A)†` for real `μ₀ ∈ ρ(A)`. -/
theorem resolvent_adjoint_real {μ₀ : ℝ} (hμ₀ : μ₀ ∈ resolventSet sys.A) :
    μ₀ ∈ resolventSet sys.A.adjoint ∧
      resolvent sys.A.adjoint μ₀ = ContinuousLinearMap.adjoint (resolvent sys.A μ₀) := by
  have h1 := mem_resolventSet_adjoint sys.SX.dense_generator_domain hμ₀
  have h2 := resolvent_adjoint sys.SX.dense_generator_domain hμ₀
  simp only [conj_trivial] at h1 h2
  exact ⟨h1, h2⟩

/-- `K = R(μ₀, A⋆) = (R(μ₀, A)†)_ℂ` for real `μ₀ ∈ ρ(A)`. -/
theorem resolvent_adjoint_complexify_eq {μ₀ : ℝ} (hμ₀ : μ₀ ∈ resolventSet sys.A) :
    resolvent sys.A.adjoint.complexify (μ₀ : ℂ) =
      (ContinuousLinearMap.adjoint (resolvent sys.A μ₀)).complexify := by
  obtain ⟨h1, h2⟩ := resolvent_adjoint_real hμ₀
  rw [resolvent_complexify_ofReal h1, h2]

/-- `(μ₀ : ℂ) ∈ ρ(A⋆)` for real `μ₀ ∈ ρ(A)`. -/
theorem ofReal_mem_resolventSet_adjoint_complexify {μ₀ : ℝ} (hμ₀ : μ₀ ∈ resolventSet sys.A) :
    (μ₀ : ℂ) ∈ resolventSet sys.A.adjoint.complexify :=
  ofReal_mem_resolventSet_complexify (resolvent_adjoint_real hμ₀).1

/-- `K† = R(μ₀, A_ℂ)` for `K = R(μ₀, A⋆)`, real `μ₀ ∈ ρ(A)`. -/
theorem adjoint_resolvent_adjoint_complexify {μ₀ : ℝ} (hμ₀ : μ₀ ∈ resolventSet sys.A) :
    ContinuousLinearMap.adjoint (resolvent sys.A.adjoint.complexify (μ₀ : ℂ)) =
      resolvent sys.A.complexify (μ₀ : ℂ) := by
  rw [resolvent_adjoint_complexify_eq hμ₀, ContinuousLinearMap.adjoint_complexify,
    ContinuousLinearMap.adjoint_adjoint, resolvent_complexify_ofReal hμ₀]

/-- **`N_ℂ` is invariant under `K = R(μ₀, A⋆)`** when `R(μ₀, A)† N ⊆ N`. -/
theorem resolvent_mem_unobsC {μ₀ : ℝ} (hμ₀ : μ₀ ∈ resolventSet sys.A)
    (hinv : ∀ η ∈ unobs sys, ContinuousLinearMap.adjoint (resolvent sys.A μ₀) η ∈ unobs sys)
    {ξ : Complexification X} (hξ : ξ ∈ unobsC sys) :
    resolvent sys.A.adjoint.complexify (μ₀ : ℂ) ξ ∈ unobsC sys := by
  rw [resolvent_adjoint_complexify_eq hμ₀]
  exact ⟨hinv _ hξ.1, hinv _ hξ.2⟩

/-- **No eigenvectors in `N_ℂ`** (`prop:fattorini-hautus`, proof): under `hyp:H1` and the Hautus
condition, if `R(z, A⋆) ξ = ν ξ` with `ν ≠ 0` and `ξ ∈ N_ℂ`, then `ξ = 0`.  Indeed `ξ ∈ D(A⋆)`
with `A⋆ ξ = (z - ν⁻¹) ξ`, so `Re ξ, Im ξ` and their images under `A†` lie in `N`, and
`B⋆ ξ = 0` (`bstar_eq_zero_of_mem_unobs`). -/
theorem eq_zero_of_resolvent_eq_smul {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hH : sys.HautusCondition) {z : ℂ} (hz : z ∈ resolventSet sys.A.adjoint.complexify)
    {ν : ℂ} (hν : ν ≠ 0) {ξ : Complexification X} (hξ : ξ ∈ unobsC sys)
    (heq : resolvent sys.A.adjoint.complexify z ξ = ν • ξ) : ξ = 0 := by
  obtain ⟨hD, hAξ⟩ := mem_domain_of_resolvent_eq_smul hz hν heq
  have hre : sys.A.adjoint ⟨ξ.re, (Submodule.mem_complexify.1 hD).1⟩ ∈ unobs sys := by
    have h := congrArg Complexification.re hAξ
    rw [LinearPMap.complexify_apply_re, Complexification.smul_re] at h
    rw [h]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hξ.1) (Submodule.smul_mem _ _ hξ.2)
  have him : sys.A.adjoint ⟨ξ.im, (Submodule.mem_complexify.1 hD).2⟩ ∈ unobs sys := by
    have h := congrArg Complexification.im hAξ
    rw [LinearPMap.complexify_apply_im, Complexification.smul_im] at h
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hξ.2) (Submodule.smul_mem _ _ hξ.1)
  refine hH (z - ν⁻¹) ξ ⟨hD, hAξ, ?_⟩
  apply Complexification.ext
  · rw [LinearPMap.complexify_apply_re]
    exact bstar_eq_zero_of_mem_unobs hH1 hT _ hξ.1 hre
  · rw [LinearPMap.complexify_apply_im]
    exact bstar_eq_zero_of_mem_unobs hH1 hT _ hξ.2 him

end FH

end DataDrivenControl
