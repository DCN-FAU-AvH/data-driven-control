module

public import DataDrivenControl.Controllability.FHResolvent

/-!
# Fattorini–Hautus, steps FH4–FH5: the Fattorini–Hautus theorem

Paper: `prop:fattorini-hautus` (cited from Boyer, Thm III.3.7, and Badra–Takahashi, Thm 1.3;
**proved here**).

## The root-vector hypothesis

`System.FattoriniHautusHypotheses.completeRootVectors` asks for completeness of the root vectors
of the generator `A` on `X_ℂ` (Badra–Takahashi's (H2)).  Boyer's statement names `A⋆` instead,
which does not suffice: there is an analytic, compact-resolvent system with complete root
vectors of `A⋆`, satisfying the Hautus condition, which is not approximately controllable
(sketch in the README, *The cited theorems, now proved*).  For all bounded `B` at once,
completeness for `A` is also necessary.

## Main declarations

* `FH.unobsC_eq_bot`: under `hyp:H1`, the Hautus condition, a compact resolvent of `A⋆` and
  complete root vectors of `A`, the complexified unobservable subspace `N_ℂ` is `0`: it is a
  closed subspace invariant under the compact `K = R(μ₀, A⋆)`, without eigenvectors of `K` for
  nonzero eigenvalues (`FH.eq_zero_of_resolvent_eq_smul`), so the Fredholm alternative puts it
  orthogonal to all root vectors of `K† = R(μ₀, A_ℂ)`
  (`eq_bot_of_dense_iSup_maxGenEigenspace_adjoint`), which are complete.
* `System.fattoriniHautusProperty_of_hypotheses`: **the Fattorini–Hautus theorem**: under
  `FattoriniHautusHypotheses T`, `(A, B)` is approximately controllable in time `T'` iff the
  Hautus condition holds, for every `T' > 0`.
* `System.fattoriniHautusTheorem : sys.FattoriniHautusTheorem`, the same in the `Prop` form of
  `Controllability/FattoriniHautus`, for every system.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

namespace FH

open _root_.DataDrivenControl.System

variable {sys : System U W X V Y}

/-- **`N_ℂ = 0`** (`prop:fattorini-hautus`, proof, step 4): under `hyp:H1`, the Hautus
condition, a compact resolvent of `A⋆` and complete root vectors of `A` (on `X_ℂ`), the
complexified unobservable subspace vanishes. -/
theorem unobsC_eq_bot {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hH : sys.HautusCondition)
    (hcomp : ∃ μ ∈ resolventSet sys.A.adjoint.complexify,
      IsCompactOperator (resolvent sys.A.adjoint.complexify μ))
    (hcompl : ∃ μ ∈ resolventSet sys.A.complexify,
      Dense (((⨆ ν : ℂ, Module.End.maxGenEigenspace
        ((resolvent sys.A.complexify μ : Complexification X →L[ℂ] Complexification X) :
          Module.End ℂ (Complexification X)) ν : Submodule ℂ (Complexification X))) :
        Set (Complexification X))) :
    unobsC sys = ⊥ := by
  obtain ⟨μ₀, hμ₀, hinv⟩ := exists_real_resolvent hH1 hT
  have hz := ofReal_mem_resolventSet_adjoint_complexify hμ₀
  have hμ₀c : (μ₀ : ℂ) ∈ resolventSet sys.A.complexify :=
    ofReal_mem_resolventSet_complexify hμ₀
  obtain ⟨μ, hμ, hK⟩ := hcomp
  obtain ⟨μc, hμc, hd⟩ := hcompl
  refine eq_bot_of_dense_iSup_maxGenEigenspace_adjoint (isCompactOperator_resolvent hμ hz hK)
    ?_ isClosed_unobsC (fun x hx => resolvent_mem_unobsC hμ₀ hinv hx)
    (fun ν hν x hx heq => eq_zero_of_resolvent_eq_smul hH1 hT hH hz hν hx heq) ?_
  · rw [adjoint_resolvent_adjoint_complexify hμ₀]
    exact injective_resolvent hμ₀c
  · rw [adjoint_resolvent_adjoint_complexify hμ₀]
    exact dense_iSup_maxGenEigenspace_resolvent hμc hμ₀c hd

end FH

namespace System

variable {sys : System U W X V Y}

/-- **The Fattorini–Hautus theorem** (`prop:fattorini-hautus`, Boyer Thm III.3.7 with the
root-vector hypothesis on `A`, Badra–Takahashi Thm 1.3): under `FattoriniHautusHypotheses T`,
for every `T' > 0`, `(A, B)` is approximately controllable in time `T'` iff
`ker B⋆ ∩ ker (A⋆ - λ) = {0}` for every `λ ∈ ℂ`.

Proof: the easy direction is `hautusCondition_of_approxControllable`.  Conversely, a state
`η ⊥ ℛ_{T'}(0)` lies in the unobservable subspace `N` (FH1, `FH.mem_unobs_of_forall`), and
`N_ℂ = 0` (`FH.unobsC_eq_bot`). -/
theorem fattoriniHautusProperty_of_hypotheses {T : ℝ} (h : sys.FattoriniHautusHypotheses T)
    {T' : ℝ} (hT' : 0 < T') : sys.FattoriniHautusProperty T' := by
  have hH1' := h.H1.of_pos sys h.pos T'
  refine ⟨hautusCondition_of_approxControllable hH1' hT', fun hH => ?_⟩
  rw [approxControllable_iff hH1' hT']
  intro η hη
  have hN := FH.mem_unobs_of_forall h.H1 h.pos h.analytic hT' hη
  have hbot := FH.unobsC_eq_bot h.H1 h.pos hH h.compactResolvent h.completeRootVectors
  have hC : (η : Complexification X) ∈ FH.unobsC sys := Submodule.ofReal_mem_complexify.2 hN
  rw [hbot, Submodule.mem_bot] at hC
  exact Complexification.ofReal_injective (hC.trans (by ext <;> simp))

variable (sys) in
/-- **The Fattorini–Hautus theorem** (`prop:fattorini-hautus`) in the `Prop` form
`sys.FattoriniHautusTheorem` of `Controllability/FattoriniHautus`: proved for every system.  The
theorems of Section 5 that take `FattoriniHautusProperty` as a hypothesis can obtain it from
`FattoriniHautusHypotheses` through this theorem. -/
theorem fattoriniHautusTheorem : sys.FattoriniHautusTheorem :=
  fun _ h _ hT' => fattoriniHautusProperty_of_hypotheses h hT'

end System

end DataDrivenControl
