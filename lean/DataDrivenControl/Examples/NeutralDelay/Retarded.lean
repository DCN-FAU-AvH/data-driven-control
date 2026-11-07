module

public import DataDrivenControl.Examples.NeutralDelay.Semigroup

/-!
# Consistency of the neutral and the retarded delay systems

With `M = 0` (no neutral point delays, `Mₖ = 0`, and `M_d = 0`) the neutral equation of
`NeutralDelay/Solution` is the retarded equation of `Delay/Solution`:

* `Equation.isSolOn_of_retarded`: the continuous solutions of the retarded equation
  (`Delay.Equation.IsSolOn`) solve the neutral equation in its a.e. form;
* `Equation.semigroup_eq_of_M_eq_zero`: the neutral delay semigroup
  `S(t) (r, ψ) = (x(t) - M x_t, x_t)` is the retarded one, `Delay.Equation.semigroup`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace NeutralDelay

open Delay (State state_ext traj traj_ae_congr)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Equation

variable {h : ℝ} (d : Equation h E)

/-- With `Mₖ = 0` and `M_d = 0` the neutral term vanishes. -/
theorem M_eval_eq_zero (hM : ∀ k, d.Mp k = 0) (hMd : d.Md = 0) (z : ℝ → E) (s : ℝ) :
    d.M.eval z s = 0 := by
  simp [DelayOp.eval, M, hM, hMd]

/-- With `M = 0`, solutions of the retarded equation solve the neutral equation. -/
theorem isSolOn_of_retarded (hM : ∀ k, d.Mp k = 0) (hMd : d.Md = 0) {τ : ℝ} {r : E}
    {ψ f x : ℝ → E} (hx : d.toEquation.IsSolOn τ r ψ f x) : d.IsSolOn τ r ψ f x := by
  refine ⟨memLp_μI_of_continuousOn hx.1, ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_⟩
  rw [d.M_eval_eq_zero hM hMd, zero_add, hx.2 t (Ioc_subset_Icc_self ht)]
  rfl

/-- **Consistency with the retarded delay system**: with `M = 0` the neutral delay semigroup is
the retarded delay semigroup `Delay.Equation.semigroup`. -/
theorem semigroup_eq_of_M_eq_zero (hM : ∀ k, d.Mp k = 0) (hMd : d.Md = 0) :
    d.semigroup = d.toEquation.semigroup := by
  ext1 t
  ext1 v
  have ht : (0 : ℝ) ≤ t := t.2
  have hr := d.toEquation.isSolOn_sol (r := v.fst) (Lp.memLp v.snd)
    (Delay.Equation.integrableOn_zero_forcing t)
  have hx : d.orbit v =ᵐ[μI t] d.toEquation.orbit v :=
    (d.isSolOn_orbit v ht).ae_eq ht (Lp.memLp v.snd) (integrableOn_zero_forcing t)
      (d.isSolOn_of_retarded hM hMd hr)
  have htr : d.trajOf v =ᵐ[μI (h + t)] d.toEquation.trajOf v :=
    traj_ae_congr_right _ hx
  rw [semigroup_apply, Delay.Equation.semigroup_apply]
  refine state_ext ?_ ?_
  · rw [stateAt_fst, Delay.Equation.stateAt_fst, fstAt, d.prim_congr hx ⟨ht, le_rfl⟩,
      Delay.Equation.orbit, hr.2 t ⟨ht, le_rfl⟩]
    rfl
  · rw [stateAt_snd, Delay.Equation.stateAt_snd]
    exact window_congr_ae htr ht (by linarith)

end Equation

end NeutralDelay

end DataDrivenControl
