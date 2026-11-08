module

public import DataDrivenControl.LQR.ValueOperator

/-!
# Dynamic programming along an optimal trajectory

Step R4 of the proof of `thm:lqr-riccati` (Pritchard–Salamon Thm 2.7) through the value
operator.

Let `u` satisfy the first-order condition of the full problem `J_0(ιWV x₀, ·)` (for instance
its minimiser) and let `x(t) = x(t; x₀, u)`, `y = 𝓞_V x₀ + 𝓕_T u`.  Bellman's principle is
proved through first-order conditions, which avoids comparing costs:

* `System.foc_lqTail_cut`: the cut-off control `cut t u` satisfies the first-order condition of
  the tail problem started at `(t, x(t))` (cocycle identities `tailState`, `tailOutput`,
  causality `cut_𝓕_cut`, and `R̃ cut t = cut t R̃`);
* `System.Pop_lqTail_mildW`: the value operator applied to the optimal state is the costate,
  `Pop_t (x(t)) = S_V(T - t)† 𝔾 x(T) + c_t† y` for `t ∈ [0, T]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace System

open Riccati

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {sys : System U W X V Y}

/-- `(b_t)† = cut t ∘ (ιWV ∘ L_T)†`. -/
theorem adjoint_tailB_apply (T t : ℝ) (v : V) :
    ((sys.tailB T t)†) v = cut T t (((sys.ιWV ∘L sys.Lop T)†) v) := by
  rw [tailB, ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.adjoint_comp, adjoint_cut]
  rfl

/-- `(d_t)† = cut t ∘ 𝓕_T†`. -/
theorem adjoint_tailD_apply (T t : ℝ) (y : L2 Y T) :
    ((sys.tailD T t)†) y = cut T t (((sys.𝓕 T)†) y) := by
  rw [tailD, ContinuousLinearMap.adjoint_comp, adjoint_cut]
  rfl

/-- Causality, adjoint form: `cut t 𝓕† (cut t y) = cut t 𝓕† y`. -/
theorem cut_adjoint_𝓕_cut {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (y : L2 Y T) : cut T t (((sys.𝓕 T)†) (cut T t y)) = cut T t (((sys.𝓕 T)†) y) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_cut_left, ContinuousLinearMap.adjoint_inner_left, inner_cut_left,
    cut_𝓕_cut hH1 hT ht, inner_cut_left, ContinuousLinearMap.adjoint_inner_left]

/-- The tail output map only sees the cut-off signal: `c_t† (cut t y) = c_t† y`. -/
theorem adjoint_tailC_cut {T t : ℝ} (ht : 0 ≤ t) (y : L2 Y T) :
    ((sys.tailC T t)†) (cut T t y) = ((sys.tailC T t)†) y := by
  refine ext_inner_right ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    inner_cut_left, tailC_apply, cut_shR ht]

/-- The first-order expression of the full problem:
`K_0 u + M_0 x₀ = (ιWV L_T)† 𝔾 x(T) + 𝓕_T† y + R̃ u`. -/
theorem K_add_M_lqTail_zero {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (wts : LQRWeights U V)
    (x₀ : W) (u : L2 U T) :
    (sys.lqTail wts T 0).K u + (sys.lqTail wts T 0).M (sys.ιWV x₀) =
      ((sys.ιWV ∘L sys.Lop T)†) (gOp wts (sys.ιWV (sys.mildW x₀ u T))) +
        ((sys.𝓕 T)†) (sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u) + rOp wts T u := by
  have hs := tailState hH1 hT x₀ u (t := 0) ⟨le_rfl, hT.le⟩
  rw [mildW_zero_time] at hs
  rw [LQ.K_add_M]
  simp only [lqTail]
  rw [hs, tailB_zero, tailC_zero, tailD_zero]

/-- **Bellman's principle via first-order conditions** (`R4`): if `u` satisfies the first-order
condition of the full problem from `x₀`, then `cut t u` satisfies the first-order condition of
the tail problem started at `(t, x(t))`, `t ∈ [0, T]`. -/
theorem foc_lqTail_cut {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) (x₀ : W) {u : L2 U T}
    (hu : (sys.lqTail wts T 0).K u + (sys.lqTail wts T 0).M (sys.ιWV x₀) = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (sys.lqTail wts T t).K (cut T t u) +
      (sys.lqTail wts T t).M (sys.ιWV (sys.mildW x₀ u t)) = 0 := by
  have hb : sys.tailB T t (cut T t u) = sys.tailB T t u := by
    rw [tailB_apply, tailB_apply, cut_idem ht.1]
  have hd : sys.tailD T t (cut T t u) = sys.tailD T t u := by
    rw [tailD_apply, tailD_apply, cut_idem ht.1]
  rw [K_add_M_lqTail_zero hH1 hT] at hu
  rw [LQ.K_add_M]
  simp only [lqTail]
  rw [hb, hd, tailState hH1 hT x₀ u ht, tailOutput hH1 hH2 hT x₀ u ht, adjoint_tailB_apply,
    adjoint_tailD_apply, cut_adjoint_𝓕_cut hH1 hT ht, ← cut_rOp wts ht.1, ← map_add, ← map_add,
    hu, map_zero]

/-- **The value operator along an optimal trajectory is the costate** (`R4`): for
`t ∈ [0, T]`, `Pop_t (x(t)) = S_V(T - t)† 𝔾 x(T) + c_t† y`, where `y = 𝓞_V x₀ + 𝓕_T u`. -/
theorem Pop_lqTail_mildW {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) (x₀ : W) {u : L2 U T}
    (hu : (sys.lqTail wts T 0).K u + (sys.lqTail wts T 0).M (sys.ιWV x₀) = 0) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (sys.lqTail wts T t).Pop (sys.ιWV (sys.mildW x₀ u t)) =
      ((sys.tailA T t)†) (gOp wts (sys.ιWV (sys.mildW x₀ u T))) +
        ((sys.tailC T t)†) (sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u) := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  have hb : sys.tailB T t (cut T t u) = sys.tailB T t u := by
    rw [tailB_apply, tailB_apply, cut_idem ht.1]
  have hd : sys.tailD T t (cut T t u) = sys.tailD T t u := by
    rw [tailD_apply, tailD_apply, cut_idem ht.1]
  rw [(hwf t).Pop_eq_of_foc (foc_lqTail_cut hH1 hH2 hT wts x₀ hu ht)]
  simp only [lqTail]
  rw [hb, hd, tailState hH1 hT x₀ u ht, tailOutput hH1 hH2 hT x₀ u ht, adjoint_tailC_cut ht.1]

end System

end DataDrivenControl
