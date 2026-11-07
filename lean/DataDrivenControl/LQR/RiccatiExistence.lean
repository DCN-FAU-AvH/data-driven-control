module

public import DataDrivenControl.LQR.DynamicProgramming
public import DataDrivenControl.LQR.Feedback
public import DataDrivenControl.LQR.InputStateOutput

/-!
# Existence of the Riccati operator (`thm:lqr-riccati`)

Step R6 of the proof of the cited theorem
`thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7) in the form recorded by
`System.RiccatiTheorem`.

## Main declarations

* `System.bStarP_riccatiP`: `B^⋆ P(t) x = B† Pop_t x`;
* `System.feedback_ae`: the optimal control is the feedback `u(t) = -R⁻¹ B^⋆ P(t) x(t)` a.e.
  (`eq:lqr-feedback`), from the first-order condition, the costate identity
  `Pop_lqTail_mildW` (`R4`) and the adjoint formula `coeFn_adjoint_input` (`R5`);
* `System.riccatiSolution_of_pos` (`T > 0`, value-operator route) and
  `System.riccatiSolution_of_nonpos` (`T ≤ 0`, `P ≡ G`);
* `System.nonempty_riccatiSolution`: **`hyp:H1` and `hyp:H2` suffice** (no `hyp:compat`);
* `System.riccatiTheorem`: `sys.RiccatiTheorem wts T` for every system, weights and horizon;
* `System.lqr_data_riccati_of_H1_H2`: `thm:lqr-data`, second part, with `thm:lqr-riccati` now
  proved (no Riccati hypothesis, no `hyp:compat`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option autoImplicit false

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

/-- `B^⋆ P(t) x = B† Pop_t x` for the Riccati family `riccatiP`. -/
theorem bStarP_riccatiP (wts : LQRWeights U V) (T t : ℝ) (x : W) :
    sys.bStarP (sys.riccatiP wts T t) x = (sys.B†) ((sys.lqTail wts T t).Pop (sys.ιWV x)) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_bStarP, riccatiP_apply, ContinuousLinearMap.adjoint_inner_left]

/-- **The feedback law** `eq:lqr-feedback` (`R5`): the optimal control
`u = uopt_0 (ιWV x₀)` satisfies `u(t) = -R⁻¹ B^⋆ P(t) x(t)` for a.e. `t ∈ (0, T)`. -/
theorem feedback_ae {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) (x₀ : W) :
    ∀ᵐ t ∂(μI T), (sys.lqTail wts T 0).uopt (sys.ιWV x₀) t =
      -wts.Rinv (sys.bStarP (sys.riccatiP wts T t)
        (sys.mildW x₀ ((sys.lqTail wts T 0).uopt (sys.ιWV x₀)) t)) := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  set u := (sys.lqTail wts T 0).uopt (sys.ιWV x₀) with hu_def
  have hfoc := (hwf 0).foc (sys.ιWV x₀)
  set y := sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u
  set z := gOp wts (sys.ιWV (sys.mildW x₀ u T))
  set lam := ((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y with hlam
  have h0 : lam + rOp wts T u = 0 := by
    rw [← hfoc, K_add_M_lqTail_zero hH1 hT]
  have hr : rOp wts T u = -lam := eq_neg_of_add_eq_zero_right h0
  have hR : Ring.inverse wts.R * wts.R = 1 := Ring.inverse_mul_cancel _ wts.isUnit_R
  filter_upwards [coeFn_rOp wts u, coeFn_adjoint_input hH1 hH2 hT z y, Lp.coeFn_neg lam,
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 ht
  have key : wts.R (u t) = -(sys.B†) ((sys.lqTail wts T t).Pop (sys.ιWV (sys.mildW x₀ u t))) := by
    rw [← h1, hr, h3, Pi.neg_apply, h2,
      Pop_lqTail_mildW hH1 hH2 hT wts x₀ (hfoc ▸ rfl) (Ioc_subset_Icc_self ht)]
  rw [bStarP_riccatiP, ← map_neg, ← key, LQRWeights.Rinv]
  exact (DFunLike.congr_fun hR (u t)).symm

/-- **`thm:lqr-riccati` for `T > 0`** (value-operator route): under `hyp:H1` and `hyp:H2`,
`P(t) = ⟪Pop_t ·, ·⟫` is a `RiccatiSolution`. -/
def riccatiSolution_of_pos {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) : sys.RiccatiSolution wts T where
  P := sys.riccatiP wts T
  symm t _ v w := riccatiP_symm wts T t v w
  nonneg t _ v := riccatiP_nonneg wts T t v
  continuousOn v := continuousOn_riccatiP wts T v
  terminal := riccatiP_terminal wts hT.le
  optimal x₀ := by
    obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
    refine ⟨(sys.lqTail wts T 0).uopt (sys.ιWV x₀), ?_, feedback_ae hH1 hH2 hT wts x₀, ?_⟩
    · refine isMinOn_univ_iff.2 fun v => ?_
      rw [lqrCost_eq_cost hH1 hH2 hT, lqrCost_eq_cost hH1 hH2 hT]
      exact isMinOn_univ_iff.1 ((hwf 0).isMinOn_cost _) v
    · rw [lqrCost_eq_cost hH1 hH2 hT, (hwf 0).cost_uopt]
      rfl

/-- **`thm:lqr-riccati` for `T ≤ 0`**: the control interval is empty,
the cost is `G x₀ x₀` for every input, and `P ≡ G` is a `RiccatiSolution`. -/
def riccatiSolution_of_nonpos {T : ℝ} (hT : T ≤ 0) (wts : LQRWeights U V) :
    sys.RiccatiSolution wts T where
  P _ := wts.G
  symm _ _ := wts.G_symm
  nonneg _ _ := wts.G_nonneg
  continuousOn _ := continuousOn_const
  terminal := rfl
  optimal x₀ := by
    have hI : Ioc (0 : ℝ) T = ∅ := Ioc_eq_empty (not_lt.2 hT)
    have hcost : ∀ u : ℝ → U, sys.lqrCost wts T x₀ u = wts.G (sys.ιWV x₀) (sys.ιWV x₀) := by
      intro u
      simp [lqrCost, mildW, sys.SW.real_of_nonpos hT, L_of_nonpos hT, hI]
    refine ⟨0, isMinOn_univ_iff.2 fun v => by rw [hcost, hcost], ?_, hcost _⟩
    simp [μI, hI]

/-- `hyp:H1` and `hyp:H2` give a `RiccatiSolution` at every horizon; `hyp:compat` is not
needed. -/
theorem nonempty_riccatiSolution {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (wts : LQRWeights U V) : Nonempty (sys.RiccatiSolution wts T) := by
  rcases le_or_gt T 0 with hT | hT
  · exact ⟨riccatiSolution_of_nonpos hT wts⟩
  · exact ⟨riccatiSolution_of_pos hH1 hH2 hT wts⟩

variable (sys) in
/-- **`thm:lqr-riccati`** (Pritchard–Salamon, Thm 2.7), in the form `System.RiccatiTheorem`
used by the paper: under `hyp:H1`, `hyp:H2` and `hyp:compat` there is a `RiccatiSolution`.
(`hyp:compat` is not used; see `nonempty_riccatiSolution`.) -/
theorem riccatiTheorem (wts : LQRWeights U V) (T : ℝ) : sys.RiccatiTheorem wts T :=
  fun hH1 hH2 _ => nonempty_riccatiSolution hH1 hH2 wts

/-- `thm:lqr-data`, second part, with `thm:lqr-riccati` proved: under `hyp:H1` and `hyp:H2`
(no Riccati hypothesis, no `hyp:compat`), there is a Riccati operator `P` such that every
minimiser of the data-driven problem is the feedback `u⋆(t) = -R⁻¹ B^⋆ P(t) x⋆(t)` with minimal
value `⟨x₀, P(0) x₀⟩_{V,V'}`. -/
theorem lqr_data_riccati_of_H1_H2 {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {w₀ : W} {ū : ℝ → U} (hū : MemLp ū 2 (μI T))
    {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) (x₀ : W) :
    ∃ ric : sys.RiccatiSolution wts T, ∀ p : Traj U W Y,
      p ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ →
      IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀) p →
      (∀ᵐ t ∂(μI T), p.1 t = -wts.Rinv (sys.bStarP (ric.P t) (p.2.1 t))) ∧
        sys.trajCost wts T p = ric.P 0 (sys.ιWV x₀) (sys.ιWV x₀) := by
  obtain ⟨ric⟩ := nonempty_riccatiSolution hH1 hH2 (sys := sys) wts
  exact ⟨ric, fun p hp hmin => lqr_data_riccati hH1 hT wts hū hxd hinf ric x₀ hp hmin⟩

end System

end DataDrivenControl
