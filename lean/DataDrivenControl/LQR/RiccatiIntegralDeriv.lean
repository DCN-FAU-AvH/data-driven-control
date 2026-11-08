module

public import Mathlib
public import DataDrivenControl.LQR.RiccatiEquation
public import DataDrivenControl.LQR.RiccatiExistence

/-!
# The value along the free motion has a right derivative (`thm:lqr-riccati`)

The analytic core of the existence part of `thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7) in
the integral form `System.IsRiccatiIntegralSolution` (`LQR/RiccatiEquation`); the equation
itself is derived in `LQR/RiccatiIntegral`.  `hyp:compat` is not used.

## Main declarations

* `System.cut_tailC`: `cut σ (c_τ ξ) = c_σ (S(σ - τ) ξ)` (the free output of a later tail);
* `System.cost_lqTail_eq_of_cut`: for a control that vanishes before `σ`,
  `J_τ(ξ, u) = J_σ(S(σ - τ) ξ, u) + ‖c_τ ξ‖² - ‖c_σ S(σ - τ) ξ‖²`;
* `System.exists_costate_uopt`: the optimal tail control from `(τ, ξ)`, `ξ ∈ V`, is
  `1_(τ,T] (-R⁻¹ B† p)` with a continuous costate `p` and `p(τ) = Pop_τ ξ` (first-order
  condition and the adjoint formula `coeFn_adjoint_input`); `System.cut_uopt_lqTail`;
* `System.reducedValue wts T σ η = P(σ)(η, η) - ‖c_σ η‖²`, with the two-sided bound
  `⟪R̃ v, v⟫ ≤ F(σ) - F(τ) ≤ ⟪K_τ v, v⟫` along the free motion (`inner_rOp_le_reducedValue_sub`,
  `reducedValue_sub_le`, `v = 1_(τ,σ] w`) and `⟪K_τ v, v⟫ - ⟪R̃ v, v⟫ = O((σ - τ)²)`
  (`exists_inner_K_le`);
* `System.hasDerivWithinAt_reducedValue`: `σ ↦ P(σ)(S(σ - τ) ξ, S(σ - τ) ξ) - ‖c_σ S(σ - τ) ξ‖²`
  has right derivative `⟪R⁻¹ B^⋆P(τ) ξ, B^⋆P(τ) ξ⟫` at `τ ∈ [0, T)`, for every `ξ ∈ V`.

## Proof

Let `w` be the optimal tail control from `(τ, ξ)` and `v = 1_(τ,σ] w`.  Completing the square
(`LQ.WF.cost_eq`) around `w`, with the competitors `cut σ w` (upper bound) and the optimal tail
control from `(σ, S(σ - τ) ξ)` (lower bound), and the splitting `cost_lqTail_eq_of_cut`, give
`⟪R̃ v, v⟫ ≤ F(σ) - F(τ) ≤ ⟪K_τ v, v⟫`.  By `exists_costate_uopt`, `w = -R⁻¹ B† p` on `(τ, T]`
with `p` continuous, so `⟪R̃ v, v⟫ = ∫_τ^σ ⟪R w, w⟫` has right derivative
`⟪R w(τ), w(τ)⟫ = ⟪R⁻¹ B† Pop_τ ξ, B† Pop_τ ξ⟫`, and `w` is bounded.  Then
`⟪K_τ v, v⟫ - ⟪R̃ v, v⟫ = ⟪𝔾 b_τ v, b_τ v⟫ + ‖d_τ v‖² = O((σ - τ)²)`: `‖b_τ v‖_V = O(σ - τ)`
because `B ∈ L(U, V)`; the output of `v` after `σ` is the free output of a state of `V`-norm
`O(σ - τ)` (`hyp:H2`), and on `(τ, σ]` it is bounded by `‖v‖_{L²} = O(√(σ - τ))` (`hyp:H1`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Asymptotics
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Riccati

/-! ### Cut-off algebra -/

section CutAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {T : ℝ}

/-- `cut β f - cut γ f = 1_(β,γ] f` for `0 ≤ β ≤ γ`. -/
theorem coeFn_cut_sub_cut {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (f : L2 E T) :
    ⇑(cut T β f - cut T γ f) =ᵐ[μI T] (Ioc β γ).indicator ⇑f := by
  have hγ : 0 ≤ γ := hβ.trans hβγ
  filter_upwards [Lp.coeFn_sub (cut T β f) (cut T γ f), coeFn_cut hβ f, coeFn_cut hγ f,
    ae_restrict_mem measurableSet_Ioc] with r h1 h2 h3 hr
  rw [h1, Pi.sub_apply, h2, h3]
  by_cases hr1 : r ≤ β
  · rw [indicator_of_notMem (show r ∉ Ioc β T from fun h => by linarith [h.1]),
      indicator_of_notMem (show r ∉ Ioc γ T from fun h => by linarith [h.1]),
      indicator_of_notMem (show r ∉ Ioc β γ from fun h => by linarith [h.1]), sub_zero]
  by_cases hr2 : r ≤ γ
  · rw [indicator_of_mem (show r ∈ Ioc β T from ⟨not_le.1 hr1, hr.2⟩),
      indicator_of_notMem (show r ∉ Ioc γ T from fun h => by linarith [h.1]),
      indicator_of_mem (show r ∈ Ioc β γ from ⟨not_le.1 hr1, hr2⟩), sub_zero]
  · rw [indicator_of_mem (show r ∈ Ioc β T from ⟨not_le.1 hr1, hr.2⟩),
      indicator_of_mem (show r ∈ Ioc γ T from ⟨not_le.1 hr2, hr.2⟩),
      indicator_of_notMem (show r ∉ Ioc β γ from fun h => hr2 h.2), sub_self]

/-- If `f = 1_(τ,T] ψ`, then `f - cut σ f = 1_(τ,σ] ψ` for `0 ≤ τ ≤ σ`. -/
theorem coeFn_sub_cut_of_ae {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) {f : L2 E T} {ψ : ℝ → E}
    (hf : ⇑f =ᵐ[μI T] (Ioc τ T).indicator ψ) :
    ⇑(f - cut T σ f) =ᵐ[μI T] (Ioc τ σ).indicator ψ := by
  filter_upwards [Lp.coeFn_sub f (cut T σ f), coeFn_cut (hτ.trans hτσ) f, hf,
    ae_restrict_mem measurableSet_Ioc] with r h1 h2 h3 hr
  rw [h1, Pi.sub_apply, h2, h3]
  by_cases hr1 : r ≤ τ
  · rw [indicator_of_notMem (show r ∉ Ioc τ T from fun h => by linarith [h.1]),
      indicator_of_notMem (show r ∉ Ioc σ T from fun h => by linarith [h.1]),
      indicator_of_notMem (show r ∉ Ioc τ σ from fun h => by linarith [h.1]), sub_zero]
  by_cases hr2 : r ≤ σ
  · rw [indicator_of_mem (show r ∈ Ioc τ T from ⟨not_le.1 hr1, hr.2⟩),
      indicator_of_notMem (show r ∉ Ioc σ T from fun h => by linarith [h.1]),
      indicator_of_mem (show r ∈ Ioc τ σ from ⟨not_le.1 hr1, hr2⟩), sub_zero]
  · rw [indicator_of_mem (show r ∈ Ioc σ T from ⟨not_le.1 hr2, hr.2⟩), h3, sub_self,
      indicator_of_notMem (show r ∉ Ioc τ σ from fun h => hr2 h.2)]

/-- Orthogonality: `⟪f - cut σ f, g⟫ = 0` if `cut σ g = g`. -/
theorem inner_sub_cut_eq_zero {σ : ℝ} (f g : L2 E T) (hg : cut T σ g = g) :
    ⟪f - cut T σ f, g⟫_ℝ = 0 := by
  rw [inner_sub_left, inner_cut_left, hg, sub_self]

/-- The right shift is a contraction, pointwise. -/
theorem norm_shR_apply_le {s : ℝ} (f : L2 E T) : ‖shR T s f‖ ≤ ‖f‖ := by
  have h2 := (shR (E := E) T s).le_opNorm f
  have h3 := norm_shR_le (E := E) T s
  calc ‖shR T s f‖ ≤ ‖shR (E := E) T s‖ * ‖f‖ := h2
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-- Pythagoras for the cut-off: `‖f‖² = ‖f - cut σ f‖² + ‖cut σ f‖²`. -/
theorem norm_sq_eq_sub_cut {σ : ℝ} (hσ : 0 ≤ σ) (f : L2 E T) :
    ‖f‖ ^ 2 = ‖f - cut T σ f‖ ^ 2 + ‖cut T σ f‖ ^ 2 := by
  have h := inner_sub_cut_eq_zero f (cut T σ f) (cut_idem hσ f)
  conv_lhs => rw [show f = (f - cut T σ f) + cut T σ f by abel]
  rw [norm_add_sq_real, h]
  ring

end CutAlgebra

section RMonotone

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {T : ℝ}

/-- The input penalty of a piece is at most the full penalty:
`⟪R̃ 1_(β,γ] e, 1_(β,γ] e⟫ ≤ ⟪R̃ e, e⟫` (`R ≥ 0` pointwise). -/
theorem inner_rOp_cut_sub_cut_le (wts : LQRWeights U V) {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (e : L2 U T) :
    ⟪rOp wts T (cut T β e - cut T γ e), cut T β e - cut T γ e⟫_ℝ ≤ ⟪rOp wts T e, e⟫_ℝ := by
  obtain ⟨ε, hε, hR⟩ := wts.R_coercive
  have hnn : ∀ a : U, 0 ≤ ⟪wts.R a, a⟫_ℝ := fun a => by
    rw [real_inner_comm]; exact le_trans (by positivity) (hR a)
  have hint : Integrable (fun t => ⟪wts.R (e t), e t⟫_ℝ) (μI T) :=
    (L2.integrable_inner (rOp wts T e) e).congr (by
      filter_upwards [coeFn_rOp wts e] with t ht
      rw [ht])
  rw [inner_rOp, inner_rOp]
  have hae : (fun t => ⟪wts.R ((cut T β e - cut T γ e) t), (cut T β e - cut T γ e) t⟫_ℝ)
      =ᵐ[μI T] (Ioc β γ).indicator fun t => ⟪wts.R (e t), e t⟫_ℝ := by
    filter_upwards [coeFn_cut_sub_cut hβ hβγ e] with t ht
    rw [ht]
    by_cases h : t ∈ Ioc β γ
    · simp only [indicator_of_mem h]
    · simp only [indicator_of_notMem h, map_zero, inner_zero_left]
  rw [integral_congr_ae hae]
  refine integral_mono_ae (hint.indicator measurableSet_Ioc) hint
    (Eventually.of_forall fun t => ?_)
  by_cases h : t ∈ Ioc β γ
  · simp only [indicator_of_mem h, le_refl]
  · simp only [indicator_of_notMem h]; exact hnn (e t)

end RMonotone

end Riccati

namespace System

open Riccati

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {sys : System U W X V Y}

/-- `B^⋆ P(t) x = B† Pop_t x` for the value operator, for every `x ∈ V`. -/
theorem bStarPV_riccatiP (wts : LQRWeights U V) (T t : ℝ) (x : V) :
    sys.bStarPV (sys.riccatiP wts T t) x = (sys.B†) ((sys.lqTail wts T t).Pop x) :=
  ext_inner_right ℝ fun u => by
    rw [inner_bStarPV, riccatiP_apply, ContinuousLinearMap.adjoint_inner_left]

/-! ### The free output and the cost of a later tail -/

/-- The free output of the tail from `τ`, seen after `σ ≥ τ`, is the free output of the tail
from `σ` started at `S(σ - τ) ξ`: `cut σ (c_τ ξ) = c_σ (S_V(σ - τ) ξ)`.  Checked on `W`, then
extended by density. -/
theorem cut_tailC {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (ξ : V) : cut T σ (sys.tailC T τ ξ) = sys.tailC T σ (sys.SV.real (σ - τ) ξ) := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  have key : (fun ξ : V => cut T σ (sys.tailC T τ ξ)) =
      fun ξ : V => sys.tailC T σ (sys.SV.real (σ - τ) ξ) := by
    refine (denseRange_ιWV (sys := sys)).equalizer
      ((cut T σ).continuous.comp (sys.tailC T τ).continuous)
      ((sys.tailC T σ).continuous.comp (sys.SV.real (σ - τ)).continuous) (funext fun w => ?_)
    simp only [Function.comp_apply]
    rw [← ιWV_SW]
    refine Lp.ext ?_
    have hA := ae_sub_of_ae (t := τ) (𝓞V_ae_eq hH2 hT (τ := T) w)
    have hB := ae_sub_of_ae (t := σ) (𝓞V_ae_eq hH2 hT (τ := T) (sys.SW.real (σ - τ) w))
    filter_upwards [coeFn_cut hσ (sys.tailC T τ (sys.ιWV w)),
      coeFn_shR (T := T) (s := τ) (sys.𝓞V T (sys.ιWV w)),
      coeFn_shR (T := T) (s := σ) (sys.𝓞V T (sys.ιWV (sys.SW.real (σ - τ) w))),
      ae_restrict_of_ae hA, ae_restrict_of_ae hB, ae_restrict_mem measurableSet_Ioc]
      with r h1 h2 h3 h4 h5 hr
    rw [h1, tailC_apply, tailC_apply, h3]
    by_cases hrσ : σ < r
    · have hm1 : r - τ ∈ Ioc 0 T := ⟨by linarith, by linarith [hr.2]⟩
      have hm2 : r - σ ∈ Ioc 0 T := ⟨by linarith, by linarith [hr.2]⟩
      rw [indicator_of_mem (show r ∈ Ioc σ T from ⟨hrσ, hr.2⟩), h2, indicator_of_mem hm1,
        indicator_of_mem hm2, h4 hm1, h5 hm2,
        ← sys.SW.real_add_apply hm2.1.le (sub_nonneg.2 hτσ), sub_add_sub_cancel]
    · rw [indicator_of_notMem (show r ∉ Ioc σ T from fun h => hrσ h.1),
        indicator_of_notMem (show r - σ ∉ Ioc 0 T from fun h => hrσ (by linarith [h.1]))]
  exact congrFun key ξ

/-- **Splitting the tail cost** at `σ ≥ τ`: for a control that vanishes before `σ`,
`J_τ(ξ, u) = J_σ(S(σ - τ) ξ, u) + (‖c_τ ξ‖² - ‖c_σ S(σ - τ) ξ‖²)`; the last term is the output
cost of the free motion on `(τ, σ]`. -/
theorem cost_lqTail_eq_of_cut {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T) (ξ : V)
    {u : L2 U T} (hu : cut T σ u = u) :
    (sys.lqTail wts T τ).cost ξ u = (sys.lqTail wts T σ).cost (sys.SV.real (σ - τ) ξ) u +
      (‖sys.tailC T τ ξ‖ ^ 2 - ‖sys.tailC T σ (sys.SV.real (σ - τ) ξ)‖ ^ 2) := by
  have hσ : 0 ≤ σ := hτ.trans hτσ
  have hcu : cut T τ u = u := by rw [← hu, cut_cut hτ hσ, max_eq_right hτσ]
  have hA : sys.tailA T τ ξ = sys.tailA T σ (sys.SV.real (σ - τ) ξ) := by
    rw [tailA_apply, tailA_apply, ← sys.SV.real_add_apply (by linarith) (by linarith),
      sub_add_sub_cancel]
  have hB : sys.tailB T τ u = sys.tailB T σ u := by rw [tailB_apply, tailB_apply, hcu, hu]
  have hD : sys.tailD T τ u = sys.tailD T σ u := by rw [tailD_apply, tailD_apply, hcu, hu]
  have hcf : cut T σ (sys.tailC T τ ξ) = sys.tailC T σ (sys.SV.real (σ - τ) ξ) :=
    cut_tailC hH2 hT hτ hτσ ξ
  have hg : cut T σ (sys.tailC T σ (sys.SV.real (σ - τ) ξ) + sys.tailD T σ u) =
      sys.tailC T σ (sys.SV.real (σ - τ) ξ) + sys.tailD T σ u := by
    rw [map_add, tailC_apply, cut_shR hσ, tailD_apply, cut_𝓕_cut hH1 hT ⟨hσ, hσT⟩]
  have hsplit : sys.tailC T τ ξ + sys.tailD T τ u =
      (sys.tailC T τ ξ - cut T σ (sys.tailC T τ ξ)) +
        (sys.tailC T σ (sys.SV.real (σ - τ) ξ) + sys.tailD T σ u) := by
    rw [hD, hcf]; abel
  have hnorm : ‖sys.tailC T τ ξ + sys.tailD T τ u‖ ^ 2 = ‖sys.tailC T τ ξ‖ ^ 2 -
      ‖sys.tailC T σ (sys.SV.real (σ - τ) ξ)‖ ^ 2 +
      ‖sys.tailC T σ (sys.SV.real (σ - τ) ξ) + sys.tailD T σ u‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, inner_sub_cut_eq_zero _ _ hg,
      norm_sq_eq_sub_cut hσ (sys.tailC T τ ξ), hcf]
    ring
  simp only [LQ.cost, lqTail]
  rw [hA, hB, hnorm]
  ring

/-! ### The optimal tail control -/

/-- **The optimal tail control from `(τ, ξ)`**, `ξ ∈ V`: it vanishes before `τ` and equals
`-R⁻¹ B† p` on `(τ, T]` for a continuous costate path `p` with `p(τ) = Pop_τ ξ`.  First-order
condition, the adjoint formula `coeFn_adjoint_input` (`R5`) and `Pop_eq_of_foc`. -/
theorem exists_costate_uopt {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ : ℝ} (hτ : τ ∈ Icc 0 T) (ξ : V) :
    ∃ p : ℝ → V, Continuous p ∧ p τ = (sys.lqTail wts T τ).Pop ξ ∧
      ⇑((sys.lqTail wts T τ).uopt ξ) =ᵐ[μI T]
        (Ioc τ T).indicator fun s => -wts.Rinv ((sys.B†) (p s)) := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  have hfoc := (hwf τ).foc ξ
  set w := (sys.lqTail wts T τ).uopt ξ with hw
  refine ⟨fun s => ((sys.tailA T s)†) (gOp wts (sys.tailA T τ ξ + sys.tailB T τ w)) +
      ((sys.tailC T s)†) (sys.tailC T τ ξ + sys.tailD T τ w),
    continuous_costate T _ _, ((hwf τ).Pop_eq_of_foc hfoc).symm, ?_⟩
  have h0 := hfoc
  rw [LQ.K_add_M] at h0
  simp only [lqTail] at h0
  rw [adjoint_tailB_apply, adjoint_tailD_apply, ← map_add] at h0
  generalize gOp wts (sys.tailA T τ ξ + sys.tailB T τ w) = z at h0 ⊢
  generalize sys.tailC T τ ξ + sys.tailD T τ w = y at h0 ⊢
  have hr : rOp wts T w = -cut T τ (((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y) :=
    eq_neg_of_add_eq_zero_right h0
  filter_upwards [coeFn_rOp wts w,
    coeFn_cut hτ.1 (((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y),
    coeFn_adjoint_input hH1 hH2 hT z y,
    Lp.coeFn_neg (cut T τ (((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y))] with s h1 h2 h3 h4
  have key : wts.R (w s) = -(Ioc τ T).indicator
      (fun s => (sys.B†) (((sys.tailA T s)†) z + ((sys.tailC T s)†) y)) s := by
    rw [← h1, hr, h4, Pi.neg_apply, h2]
    by_cases hs : s ∈ Ioc τ T
    · rw [indicator_of_mem hs, indicator_of_mem hs, h3]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [← wts.Rinv_R (w s), key]
  by_cases hs : s ∈ Ioc τ T
  · simp only [indicator_of_mem hs, map_neg]
  · simp only [indicator_of_notMem hs, neg_zero, map_zero]

/-- The optimal tail control from `τ` vanishes before `τ`. -/
theorem cut_uopt_lqTail {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ : ℝ} (hτ : τ ∈ Icc 0 T) (ξ : V) :
    cut T τ ((sys.lqTail wts T τ).uopt ξ) = (sys.lqTail wts T τ).uopt ξ := by
  obtain ⟨p, -, -, hp⟩ := exists_costate_uopt hH1 hH2 hT wts hτ ξ
  refine Lp.ext ?_
  filter_upwards [coeFn_cut hτ.1 ((sys.lqTail wts T τ).uopt ξ), hp] with s h1 h2
  rw [h1]
  by_cases hs : s ∈ Ioc τ T
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, h2, indicator_of_notMem hs]

/-! ### Increments of the value along the free motion -/

variable (sys) in
/-- The value of the tail problem from `(σ, η)` minus the output cost of the free motion:
`P(σ)(η, η) - ‖c_σ η‖²`. -/
def reducedValue (wts : LQRWeights U V) (T σ : ℝ) (η : V) : ℝ :=
  sys.riccatiP wts T σ η η - ‖sys.tailC T σ η‖ ^ 2

/-- **Upper bound for the increment**: with `w` the optimal tail control from `(τ, ξ)` and the
competitor `cut σ w`, the increment of the reduced value from `τ` to `σ` along the free motion is
at most `⟪K_τ v, v⟫`, `v = w - cut σ w`. -/
theorem reducedValue_sub_le {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T) (ξ : V) :
    sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ) - sys.reducedValue wts T τ ξ ≤
      ⟪(sys.lqTail wts T τ).K ((sys.lqTail wts T τ).uopt ξ -
          cut T σ ((sys.lqTail wts T τ).uopt ξ)),
        (sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)⟫_ℝ := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  have hσ : 0 ≤ σ := hτ.trans hτσ
  have h1 : sys.riccatiP wts T σ (sys.SV.real (σ - τ) ξ) (sys.SV.real (σ - τ) ξ) ≤
      (sys.lqTail wts T σ).cost (sys.SV.real (σ - τ) ξ)
        (cut T σ ((sys.lqTail wts T τ).uopt ξ)) := by
    rw [riccatiP_apply, ← (hwf σ).cost_uopt]
    exact isMinOn_univ_iff.1 ((hwf σ).isMinOn_cost _) _
  have h2 := cost_lqTail_eq_of_cut hH1 hH2 hT wts hτ hτσ hσT ξ
    (cut_idem hσ ((sys.lqTail wts T τ).uopt ξ))
  have h3 := (hwf τ).cost_eq ξ (cut T σ ((sys.lqTail wts T τ).uopt ξ))
  set w := (sys.lqTail wts T τ).uopt ξ with hw
  have h4 : ⟪(sys.lqTail wts T τ).K (cut T σ w - w), cut T σ w - w⟫_ℝ =
      ⟪(sys.lqTail wts T τ).K (w - cut T σ w), w - cut T σ w⟫_ℝ := by
    rw [show cut T σ w - w = -(w - cut T σ w) by abel, map_neg, inner_neg_neg]
  have h5 : sys.riccatiP wts T τ ξ ξ = ⟪(sys.lqTail wts T τ).Pop ξ, ξ⟫_ℝ :=
    riccatiP_apply wts T τ ξ ξ
  unfold reducedValue
  linarith

/-- **Lower bound for the increment**: the increment of the reduced value from `τ` to `σ` along
the free motion is at least the input penalty `⟪R̃ v, v⟫` of `v = w - cut σ w`. -/
theorem inner_rOp_le_reducedValue_sub {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) (hσT : σ ≤ T) (ξ : V) :
    ⟪rOp wts T ((sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)),
        (sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)⟫_ℝ ≤
      sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ) - sys.reducedValue wts T τ ξ := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  have hσ : 0 ≤ σ := hτ.trans hτσ
  have hw := cut_uopt_lqTail hH1 hH2 hT wts ⟨hτ, hτσ.trans hσT⟩ ξ
  have hw' := cut_uopt_lqTail hH1 hH2 hT wts ⟨hσ, hσT⟩ (sys.SV.real (σ - τ) ξ)
  have h1 : sys.riccatiP wts T σ (sys.SV.real (σ - τ) ξ) (sys.SV.real (σ - τ) ξ) =
      (sys.lqTail wts T σ).cost (sys.SV.real (σ - τ) ξ)
        ((sys.lqTail wts T σ).uopt (sys.SV.real (σ - τ) ξ)) :=
    ((hwf σ).cost_uopt _).symm
  have h2 := cost_lqTail_eq_of_cut hH1 hH2 hT wts hτ hτσ hσT ξ hw'
  have h3 := (hwf τ).cost_eq ξ ((sys.lqTail wts T σ).uopt (sys.SV.real (σ - τ) ξ))
  have h5 : sys.riccatiP wts T τ ξ ξ = ⟪(sys.lqTail wts T τ).Pop ξ, ξ⟫_ℝ :=
    riccatiP_apply wts T τ ξ ξ
  set w := (sys.lqTail wts T τ).uopt ξ with hwdef
  set w' := (sys.lqTail wts T σ).uopt (sys.SV.real (σ - τ) ξ) with hw'def
  have hτw' : cut T τ w' = w' := by rw [← hw', cut_cut hτ hσ, max_eq_right hτσ]
  have hPi : cut T τ (w' - w) - cut T σ (w' - w) = -(w - cut T σ w) := by
    rw [map_sub, map_sub, hτw', hw, hw']; abel
  have hKR : ∀ e, ⟪rOp wts T e, e⟫_ℝ ≤ ⟪(sys.lqTail wts T τ).K e, e⟫_ℝ := fun e => by
    have h := LQ.inner_K_self (p := sys.lqTail wts T τ) e
    have hg := (hwf τ).g_nonneg ((sys.lqTail wts T τ).b e)
    have hd := sq_nonneg ‖(sys.lqTail wts T τ).d e‖
    have hr : (sys.lqTail wts T τ).r = rOp wts T := rfl
    rw [hr] at h
    linarith
  have h4 : ⟪rOp wts T (w - cut T σ w), w - cut T σ w⟫_ℝ ≤
      ⟪(sys.lqTail wts T τ).K (w' - w), w' - w⟫_ℝ :=
    calc ⟪rOp wts T (w - cut T σ w), w - cut T σ w⟫_ℝ
        = ⟪rOp wts T (cut T τ (w' - w) - cut T σ (w' - w)),
            cut T τ (w' - w) - cut T σ (w' - w)⟫_ℝ := by rw [hPi, map_neg, inner_neg_neg]
      _ ≤ ⟪rOp wts T (w' - w), w' - w⟫_ℝ := inner_rOp_cut_sub_cut_le wts hτ hτσ _
      _ ≤ _ := hKR _
  unfold reducedValue
  linarith

/-- **The excess of the upper bound is `O((σ - τ)²)`**: the optimal tail control from `(τ, ξ)`
is bounded, so its piece `v = 1_(τ,σ] w` moves the state by `O(σ - τ)` in `V` (`B ∈ L(U, V)`)
and the output by `O(σ - τ)` in `L²` (`hyp:H2` after `σ`, `hyp:H1` on `(τ, σ]`). -/
theorem exists_inner_K_le {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ : ℝ} (hτ : τ ∈ Icc 0 T) (ξ : V) :
    ∃ C, ∀ σ ∈ Icc τ T,
      ⟪(sys.lqTail wts T τ).K ((sys.lqTail wts T τ).uopt ξ -
          cut T σ ((sys.lqTail wts T τ).uopt ξ)),
        (sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)⟫_ℝ ≤
      ⟪rOp wts T ((sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)),
        (sys.lqTail wts T τ).uopt ξ - cut T σ ((sys.lqTail wts T τ).uopt ξ)⟫_ℝ +
        C * (σ - τ) ^ 2 := by
  obtain ⟨p, hpc, -, hp⟩ := exists_costate_uopt hH1 hH2 hT wts hτ ξ
  have hw := cut_uopt_lqTail hH1 hH2 hT wts hτ ξ
  set w := (sys.lqTail wts T τ).uopt ξ with hwdef
  set ψ : ℝ → U := fun s => -wts.Rinv ((sys.B†) (p s)) with hψ
  have hψc : Continuous ψ := (wts.Rinv.continuous.comp ((sys.B†).continuous.comp hpc)).neg
  obtain ⟨Ψ₀, hΨ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hψc.continuousOn (s := Icc 0 T))
  set Ψ := max Ψ₀ 0 with hΨdef
  have hΨ : ∀ s ∈ Icc 0 T, ‖ψ s‖ ≤ Ψ := fun s hs => (hΨ₀ s hs).trans (le_max_left _ _)
  have hΨ0 : 0 ≤ Ψ := le_max_right _ _
  have hwb : ∀ᵐ r ∂(μI T), ‖w r‖ ≤ Ψ := by
    filter_upwards [hp, ae_restrict_mem measurableSet_Ioc] with r h1 hr
    rw [h1]
    by_cases h : r ∈ Ioc τ T
    · rw [indicator_of_mem h]; exact hΨ r (Ioc_subset_Icc_self hr)
    · rw [indicator_of_notMem h, norm_zero]; exact hΨ0
  obtain ⟨M, hM0, hM⟩ := sys.SV.exists_norm_real_le T
  obtain ⟨b, hb⟩ := exists_norm_L_le hH1 hT T
  refine ⟨‖gOp wts‖ * (M * ‖sys.B‖ * Ψ) ^ 2 +
    (‖sys.𝓞V T‖ * (M * ‖sys.B‖ * Ψ) + ‖sys.C‖ * max b 0 * Ψ) ^ 2, fun σ hσ => ?_⟩
  have hσ0 : 0 ≤ σ := hτ.1.trans hσ.1
  have hστ : 0 ≤ σ - τ := sub_nonneg.2 hσ.1
  obtain ⟨v, hv⟩ : ∃ v : L2 U T, v = w - cut T σ w := ⟨_, rfl⟩
  rw [← hv]
  have hv' : v = cut T τ w - cut T σ w := by rw [hv, hw]
  have hvae : ⇑v =ᵐ[μI T] (Ioc τ σ).indicator ψ := by
    rw [hv]; exact coeFn_sub_cut_of_ae hτ.1 hσ.1 hp
  have hcv : cut T τ v = v := by
    rw [hv, map_sub, hw, cut_cut hτ.1 hσ0, max_eq_right hσ.1]
  have hcσv : cut T σ v = 0 := by rw [hv, map_sub, cut_idem hσ0, sub_self]
  have hvn : ‖v‖ ≤ √(σ - τ) * Ψ := by
    rw [hv']; exact norm_cut_sub_cut_le hτ.1 hσ.1 hΨ0 hwb
  -- the state reached by `v` stays `O(σ - τ)` in `V`
  have hstate : ∀ ρ ∈ Icc σ T,
      ‖sys.ιWV (sys.L ρ v)‖ ≤ (σ - τ) * (M * ‖sys.B‖ * Ψ) := by
    intro ρ hρ
    rw [ιWV_L hH1 hT (memLp_μI_of_le (Lp.memLp _) hρ.2), convV]
    have hpt : (fun r => sys.SV.real (ρ - r) (sys.B (v r))) =ᵐ[μI ρ]
        (Ioc τ σ).indicator fun r => sys.SV.real (ρ - r) (sys.B (ψ r)) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hρ.2) hvae]
        with r hr
      rw [hr]
      by_cases h : r ∈ Ioc τ σ
      · simp only [indicator_of_mem h]
      · simp only [indicator_of_notMem h, map_zero]
    rw [integral_congr_ae hpt, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_eq_left hτ.1,
      min_eq_left hρ.1]
    refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖sys.B‖ * Ψ) (by simp)
      fun r hr => ?_).trans_eq ?_
    · have hr0 : r ∈ Icc 0 T := ⟨hτ.1.trans hr.1.le, hr.2.trans hσ.2⟩
      calc ‖sys.SV.real (ρ - r) (sys.B (ψ r))‖ ≤ M * (‖sys.B‖ * ‖ψ r‖) :=
            ((sys.SV.real (ρ - r)).le_opNorm _).trans (mul_le_mul
              (hM _ (by linarith [hρ.2, hr.1, hτ.1])) (sys.B.le_opNorm _) (norm_nonneg _) hM0)
        _ ≤ M * (‖sys.B‖ * Ψ) := by gcongr; exact hΨ r hr0
        _ = M * ‖sys.B‖ * Ψ := by ring
    · rw [Real.volume_real_Ioc_of_le hσ.1, mul_comm]
  have hB : ‖sys.tailB T τ v‖ ≤ (σ - τ) * (M * ‖sys.B‖ * Ψ) := by
    rw [tailB_apply, hcv, Lop_apply hH1 hT]; exact hstate T ⟨hσ.2, le_rfl⟩
  have hD : ‖sys.tailD T τ v‖ ≤
      (σ - τ) * (‖sys.𝓞V T‖ * (M * ‖sys.B‖ * Ψ) + ‖sys.C‖ * max b 0 * Ψ) := by
    rw [tailD_apply, hcv, needle_output hH1 hH2 hT ⟨hτ.1, hτ.2⟩ ⟨hσ0, hσ.2⟩ hcv hcσv]
    have h1 : ‖sys.tailC T σ (sys.ιWV (sys.L σ v))‖ ≤
        ‖sys.𝓞V T‖ * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) := by
      rw [tailC_apply]
      calc ‖shR T σ (sys.𝓞V T (sys.ιWV (sys.L σ v)))‖
          ≤ ‖sys.𝓞V T (sys.ιWV (sys.L σ v))‖ :=
            norm_shR_apply_le _
        _ ≤ ‖sys.𝓞V T‖ * ‖sys.ιWV (sys.L σ v)‖ := (sys.𝓞V T).le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hstate σ ⟨le_rfl, hσ.2⟩) (norm_nonneg (sys.𝓞V T))
    have hpt : ∀ᵐ r ∂(μI T), ‖sys.𝓕 T v r‖ ≤
        ‖sys.C‖ * (max b 0 * (√(σ - τ) * Ψ)) := by
      filter_upwards [𝓕_ae_eq hH1 hT v, ae_restrict_mem measurableSet_Ioc]
        with r h1 h2
      rw [h1]
      refine (sys.C.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      calc ‖sys.L r v‖ ≤ b * ‖v‖ :=
            hb v r (Ioc_subset_Icc_self h2)
        _ ≤ max b 0 * ‖v‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max b 0 * (√(σ - τ) * Ψ) := mul_le_mul_of_nonneg_left hvn (le_max_right _ _)
    have h2 : ‖cut T τ (sys.𝓕 T v) - cut T σ (sys.𝓕 T v)‖ ≤
        (σ - τ) * (‖sys.C‖ * max b 0 * Ψ) := by
      have hK0 : 0 ≤ ‖sys.C‖ * (max b 0 * (√(σ - τ) * Ψ)) :=
        mul_nonneg (norm_nonneg _) (mul_nonneg (le_max_right _ _)
          (mul_nonneg (Real.sqrt_nonneg _) hΨ0))
      refine (norm_cut_sub_cut_le hτ.1 hσ.1 hK0 hpt).trans_eq ?_
      have hs : √(σ - τ) * √(σ - τ) = σ - τ := Real.mul_self_sqrt hστ
      calc √(σ - τ) * (‖sys.C‖ * (max b 0 * (√(σ - τ) * Ψ)))
          = ‖sys.C‖ * max b 0 * Ψ * (√(σ - τ) * √(σ - τ)) := by ring
        _ = _ := by rw [hs]; ring
    calc _ ≤ ‖sys.tailC T σ (sys.ιWV (sys.L σ v))‖ +
          ‖cut T τ (sys.𝓕 T v) - cut T σ (sys.𝓕 T v)‖ :=
          norm_add_le _ _
      _ ≤ ‖sys.𝓞V T‖ * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) + (σ - τ) * (‖sys.C‖ * max b 0 * Ψ) :=
          add_le_add h1 h2
      _ = _ := by ring
  have hE : ⟪gOp wts (sys.tailB T τ v), sys.tailB T τ v⟫_ℝ ≤
      ‖gOp wts‖ * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) ^ 2 := by
    calc ⟪gOp wts (sys.tailB T τ v), sys.tailB T τ v⟫_ℝ
        ≤ ‖gOp wts (sys.tailB T τ v)‖ * ‖sys.tailB T τ v‖ :=
          real_inner_le_norm _ _
      _ ≤ ‖gOp wts‖ * ‖sys.tailB T τ v‖ * ‖sys.tailB T τ v‖ := by
          gcongr; exact (gOp wts).le_opNorm _
      _ ≤ ‖gOp wts‖ * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) := by
          gcongr
      _ = _ := by ring
  have hD2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hid : ‖gOp wts‖ * ((σ - τ) * (M * ‖sys.B‖ * Ψ)) ^ 2 +
      ((σ - τ) * (‖sys.𝓞V T‖ * (M * ‖sys.B‖ * Ψ) + ‖sys.C‖ * max b 0 * Ψ)) ^ 2 =
      (‖gOp wts‖ * (M * ‖sys.B‖ * Ψ) ^ 2 +
        (‖sys.𝓞V T‖ * (M * ‖sys.B‖ * Ψ) + ‖sys.C‖ * max b 0 * Ψ) ^ 2) * (σ - τ) ^ 2 := by
    ring
  rw [LQ.inner_K_self]
  simp only [lqTail]
  linarith

/-- **The right derivative of the reduced value along the free motion**: for `τ ∈ [0, T)` and
`ξ ∈ V`, `σ ↦ P(σ)(S(σ - τ) ξ, S(σ - τ) ξ) - ‖c_σ S(σ - τ) ξ‖²` has right derivative
`⟪R⁻¹ B^⋆P(τ) ξ, B^⋆P(τ) ξ⟫` at `τ`. -/
theorem hasDerivWithinAt_reducedValue {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {τ : ℝ} (hτ : τ ∈ Ico 0 T) (ξ : V) :
    HasDerivWithinAt (fun σ => sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ))
      ⟪wts.Rinv ((sys.B†) ((sys.lqTail wts T τ).Pop ξ)),
        (sys.B†) ((sys.lqTail wts T τ).Pop ξ)⟫_ℝ (Ici τ) τ := by
  have hτ' : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.le⟩
  obtain ⟨p, hpc, hpτ, hp⟩ := exists_costate_uopt hH1 hH2 hT wts hτ' ξ
  obtain ⟨C, hC⟩ := exists_inner_K_le hH1 hH2 hT wts hτ' ξ
  set w := (sys.lqTail wts T τ).uopt ξ with hwdef
  set ψ : ℝ → U := fun s => -wts.Rinv ((sys.B†) (p s)) with hψ
  have hψc : Continuous ψ := (wts.Rinv.continuous.comp ((sys.B†).continuous.comp hpc)).neg
  have hgc : Continuous fun s => ⟪wts.R (ψ s), ψ s⟫_ℝ := (wts.R.continuous.comp hψc).inner hψc
  have hgτ : ⟪wts.R (ψ τ), ψ τ⟫_ℝ = ⟪wts.Rinv ((sys.B†) ((sys.lqTail wts T τ).Pop ξ)),
      (sys.B†) ((sys.lqTail wts T τ).Pop ξ)⟫_ℝ := by
    rw [hψ]
    simp only [map_neg, inner_neg_neg, wts.R_Rinv, hpτ]
    rw [real_inner_comm]
  -- the input penalty of `v = 1_(τ,σ] w` is `∫_τ^σ ⟪R ψ, ψ⟫`
  have hL : ∀ σ ∈ Icc τ T, ⟪rOp wts T (w - cut T σ w), w - cut T σ w⟫_ℝ =
      ∫ s in τ..σ, ⟪wts.R (ψ s), ψ s⟫_ℝ := by
    intro σ hσ
    have hae : (fun s => ⟪wts.R ((w - cut T σ w) s), (w - cut T σ w) s⟫_ℝ) =ᵐ[μI T]
        (Ioc τ σ).indicator fun s => ⟪wts.R (ψ s), ψ s⟫_ℝ := by
      filter_upwards [coeFn_sub_cut_of_ae hτ.1 hσ.1 hp] with s hs
      rw [hs]
      by_cases h : s ∈ Ioc τ σ
      · simp only [indicator_of_mem h]
      · simp only [indicator_of_notMem h, map_zero, inner_zero_left]
    rw [inner_rOp, intervalIntegral.integral_of_le hσ.1, integral_congr_ae hae,
      integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Ioc_inter_Ioc, max_eq_left hτ.1, min_eq_left hσ.2]
  have hfτ : sys.reducedValue wts T τ (sys.SV.real (τ - τ) ξ) = sys.reducedValue wts T τ ξ := by
    rw [sub_self, sys.SV.real_zero, one_apply_eq_self]
  -- the remainder is `O((σ - τ)²)`
  have hbd : ∀ σ ∈ Icc τ T,
      0 ≤ sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ) - sys.reducedValue wts T τ ξ -
        ∫ s in τ..σ, ⟪wts.R (ψ s), ψ s⟫_ℝ ∧
      sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ) - sys.reducedValue wts T τ ξ -
        ∫ s in τ..σ, ⟪wts.R (ψ s), ψ s⟫_ℝ ≤ C * (σ - τ) ^ 2 := by
    intro σ hσ
    have h1 := inner_rOp_le_reducedValue_sub hH1 hH2 hT wts hτ.1 hσ.1 hσ.2 ξ
    have h2 := reducedValue_sub_le hH1 hH2 hT wts hτ.1 hσ.1 hσ.2 ξ
    have h3 := hC σ hσ
    have h4 := hL σ hσ
    constructor <;> linarith
  have he : HasDerivWithinAt (fun σ => sys.reducedValue wts T σ (sys.SV.real (σ - τ) ξ) -
      sys.reducedValue wts T τ ξ - ∫ s in τ..σ, ⟪wts.R (ψ s), ψ s⟫_ℝ) 0 (Ici τ) τ := by
    rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
    intro c hc
    have hδ : 0 < min (T - τ) (c / (|C| + 1)) := lt_min (sub_pos.2 hτ.2) (by positivity)
    filter_upwards [Ico_mem_nhdsGE (show τ < τ + min (T - τ) (c / (|C| + 1)) by linarith)]
      with σ hσ
    have hσ1 : σ - τ ≤ T - τ := by linarith [hσ.2, min_le_left (T - τ) (c / (|C| + 1))]
    have hσ2 : σ - τ ≤ c / (|C| + 1) := by
      linarith [hσ.2, min_le_right (T - τ) (c / (|C| + 1))]
    have hστ : 0 ≤ σ - τ := sub_nonneg.2 hσ.1
    obtain ⟨hlo, hhi⟩ := hbd σ ⟨hσ.1, by linarith⟩
    rw [hfτ, sub_self, intervalIntegral.integral_same, sub_zero, smul_zero, sub_zero,
      sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlo, abs_of_nonneg hστ]
    calc _ ≤ C * (σ - τ) ^ 2 := hhi
      _ ≤ (|C| + 1) * (σ - τ) * (σ - τ) := by
          rw [sq, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (by linarith [le_abs_self C]) hστ) hστ
      _ ≤ (|C| + 1) * (c / (|C| + 1)) * (σ - τ) := by gcongr
      _ = c * (σ - τ) := by field_simp
  have hLd : HasDerivWithinAt (fun σ => ∫ s in τ..σ, ⟪wts.R (ψ s), ψ s⟫_ℝ)
      ⟪wts.R (ψ τ), ψ τ⟫_ℝ (Ici τ) τ :=
    (hgc.integral_hasStrictDerivAt τ τ).hasDerivAt.hasDerivWithinAt
  have h := (he.add hLd).add_const (sys.reducedValue wts T τ ξ)
  rw [zero_add, hgτ] at h
  refine h.congr (fun σ _ => ?_) ?_ <;> simp only [Pi.add_apply] <;> ring

end System

end DataDrivenControl
