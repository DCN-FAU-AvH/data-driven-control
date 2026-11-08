module

public import DataDrivenControl.System.Mild

/-!
# Controllability and observability

Paper: `def:controllability`, `def:observability`.

## Main declarations

* `System.reachable T x₀`: the reachable set `ℛ_T(x₀) = {x(T; x₀, u) : u ∈ L²(0, T; U)}`;
  `reachable_zero_eq_range`: `ℛ_T(0) = im L_T`.
* `System.ExactlyControllable T` (`ℛ_T(0) = X`), `System.ApproxControllable T`
  (`ℛ_T(0)` dense in `X`); `approxControllable_iff`: no nonzero `η ∈ X` annihilates `im L_T`.
* `System.ApproxObservable T` (`ker 𝓞_T = 0`), `System.ExactlyObservable T`
  (`‖𝓞_T x‖ ≥ c_T ‖x‖`); `ExactlyObservable.approxObservable`, `ExactlyObservable.mono`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-- The set `ℛ_T(x₀)` of states reachable at time `T` from `x₀` (`def:controllability`). -/
def reachable (T : ℝ) (x₀ : X) : Set X :=
  {x | ∃ u : ℝ → U, MemLp u 2 (μI T) ∧ sys.mild x₀ u T = x}

/-- `(A, B)` is **exactly controllable in time `T`**: `ℛ_T(0) = X` (`def:controllability`). -/
def ExactlyControllable (T : ℝ) : Prop := sys.reachable T 0 = Set.univ

/-- `(A, B)` is **approximately controllable in time `T`**: `ℛ_T(0)` is dense in `X`
(`def:controllability`). -/
def ApproxControllable (T : ℝ) : Prop := Dense (sys.reachable T 0)

/-- `(A, C)` is **approximately observable in time `T`**: `ker 𝓞_T = {0}`
(`def:observability`). -/
def ApproxObservable (T : ℝ) : Prop := LinearMap.ker (sys.𝓞 T : X →ₗ[ℝ] L2 Y T) = ⊥

/-- `(A, C)` is **exactly observable in time `T`**: `‖𝓞_T x‖ ≥ c_T ‖x‖` for some `c_T > 0`
(`def:observability`). -/
def ExactlyObservable (T : ℝ) : Prop := ∃ c > 0, ∀ x : X, c * ‖x‖ ≤ ‖sys.𝓞 T x‖

variable {sys}

/-- `ℛ_T(0) = im L_T` (`def:controllability`). -/
theorem reachable_zero_eq_range {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    sys.reachable T 0 = Set.range (sys.ιW.comp (sys.Lop T)) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨hu.toLp u, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, Lop_apply hH1 hT, mild_zero_left]
    rw [L_congr_ae hu.coeFn_toLp]
  · rintro ⟨u, rfl⟩
    refine ⟨u, Lp.memLp u, ?_⟩
    simp only [ContinuousLinearMap.comp_apply, Lop_apply hH1 hT, mild_zero_left]

/-- Approximate controllability in time `T` iff no nonzero `η ∈ X` is orthogonal to `im L_T`. -/
theorem approxControllable_iff {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    sys.ApproxControllable T ↔
      ∀ η : X, (∀ u : L2 U T, ⟪η, sys.ιW (sys.Lop T u)⟫_ℝ = 0) → η = 0 := by
  rw [ApproxControllable, reachable_zero_eq_range hH1 hT]
  change DenseRange (sys.ιW.comp (sys.Lop T)) ↔ _
  rw [denseRange_iff_adjoint_eq_zero]
  refine forall_congr' fun η => imp_congr_left ?_
  constructor
  · intro h u
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left, h,
      inner_zero_left]
  · intro h
    have := h (ContinuousLinearMap.adjoint (sys.ιW.comp (sys.Lop T)) η)
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_zero] at this
    exact this

theorem ExactlyControllable.approxControllable {T : ℝ} (h : sys.ExactlyControllable T) :
    sys.ApproxControllable T := by
  rw [ApproxControllable, h]; exact dense_univ

theorem approxObservable_iff {T : ℝ} :
    sys.ApproxObservable T ↔ ∀ x : X, sys.𝓞 T x = 0 → x = 0 := by
  rw [ApproxObservable, LinearMap.ker_eq_bot']; simp

theorem ExactlyObservable.approxObservable {T : ℝ} (h : sys.ExactlyObservable T) :
    sys.ApproxObservable T := by
  rw [approxObservable_iff]
  intro x hx
  obtain ⟨c, hc, hcx⟩ := h
  have := hcx x
  rw [hx, norm_zero] at this
  exact norm_eq_zero.1 (le_antisymm (nonpos_of_mul_nonpos_right this hc) (norm_nonneg x))

/-- Exact observability in time `ρ` gives it in every time `τ ≥ ρ`, with the same constant
(`app:lqr-data-io`, Step 1). -/
theorem ExactlyObservable.mono {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {ρ τ : ℝ} (hρτ : ρ ≤ τ)
    (h : sys.ExactlyObservable ρ) : sys.ExactlyObservable τ := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun x => (h x).trans ?_⟩
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (𝓞_restrict hH2 hT hρτ x)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
    (eLpNorm_mono_measure _ (Measure.restrict_mono (Ioc_subset_Ioc_right hρτ) le_rfl))

end System

end DataDrivenControl
