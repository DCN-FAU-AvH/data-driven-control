module

public import Mathlib
public import DataDrivenControl.LQR.RiccatiIntegralDeriv

/-!
# The value operator solves the integral Riccati equation (`thm:lqr-riccati`)

Paper: `thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7), in full: under `hyp:H1` and `hyp:H2`
the integral Riccati equation (`System.IsRiccatiIntegralSolution`, `LQR/RiccatiEquation`) has a
unique strongly continuous, self-adjoint, nonnegative solution on `I = [0, T]`; it is the value
operator `System.riccatiP`, and it gives the optimal feedback and the minimal cost
(`System.RiccatiSolution`).  `hyp:compat` is not used.

## Main declarations

* `System.riccatiP_self_eq`: the quadratic integral Riccati equation for every `x ∈ V`;
* `System.inner_tailC_eq_integral`: the output term as an `L²` inner product;
* `System.isRiccatiIntegralSolution_riccatiP`: **existence**, `riccatiP` solves the equation;
  `System.isRiccatiIntegralSolution_of_nonpos` (`T ≤ 0`, `P ≡ G`);
* `System.IsRiccatiIntegralSolution.eqOn_riccatiP`: every solution is `riccatiP` on `[0, T]`;
* `System.IsRiccatiIntegralSolution.toRiccatiSolution`: every solution of the equation is a
  `RiccatiSolution` (feedback `eq:lqr-feedback` and optimal cost);
* `System.riccatiIntegralTheorem`: **`thm:lqr-riccati` in full**, at every horizon, from
  `hyp:H1` and `hyp:H2`; `System.riccatiIntegralTheorem_of_pos` (`T > 0`) names `riccatiP` and
  adds the unique optimal control.

## Proof of existence

Fix `t`, `x ∈ V` and the free motion `z(τ) = S_V(τ - t) x`, and let
`F(τ) = P(τ)(z(τ), z(τ)) - ‖c_τ z(τ)‖²` (`reducedValue`), where `c_τ` is the free output of the
tail problem from `τ`.  Then `F(T) = G(z(T), z(T))` and `F(t) = P(t)(x, x) - ‖c_t x‖²`, `F` is
continuous, and it has the continuous right derivative `⟪R⁻¹ B^⋆P(τ) z(τ), B^⋆P(τ) z(τ)⟫`
(`hasDerivWithinAt_reducedValue`, `LQR/RiccatiIntegralDeriv`).  The fundamental theorem of
calculus with right derivatives (`integral_eq_sub_of_hasDeriv_right_of_le`) gives the quadratic
equation for every `x ∈ V`, with no density argument, and polarisation gives the equation.
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

/-! ### The integral Riccati equation for the value operator -/

/-- **The quadratic integral Riccati equation** for the value operator, for every `x ∈ V`:
`P(t)(x, x) = G(S(T - t) x, S(T - t) x) + ‖c_t x‖² - ∫ₜᵀ ⟪R⁻¹ B^⋆P(s) S(s - t) x,
B^⋆P(s) S(s - t) x⟫ ds`. -/
theorem riccatiP_self_eq {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) {t : ℝ} (ht : t ∈ Icc 0 T) (x : V) :
    sys.riccatiP wts T t x x = wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) x) +
      ‖sys.tailC T t x‖ ^ 2 -
      ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)),
        sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)⟫_ℝ := by
  have hz : Continuous fun τ : ℝ => sys.SV.real (τ - t) x :=
    (sys.SV.continuous_real_apply x).comp (continuous_id.sub continuous_const)
  have hFc : ContinuousOn (fun τ => sys.reducedValue wts T τ (sys.SV.real (τ - t) x))
      (Icc t T) := by
    have h1 := ContinuousOn.inner (𝕜 := ℝ)
      ((scont_Pop_lqTail (sys := sys) wts T).continuousOn_apply hz.continuousOn) hz.continuousOn
    have h2 := ((scont_tailC (sys := sys) T).continuousOn_apply hz.continuousOn).norm.pow 2
    exact (h1.sub h2).mono (Icc_subset_Icc_left ht.1)
  have hderiv : ∀ τ ∈ Ioo t T,
      HasDerivWithinAt (fun τ => sys.reducedValue wts T τ (sys.SV.real (τ - t) x))
        ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T τ) (sys.SV.real (τ - t) x)),
          sys.bStarPV (sys.riccatiP wts T τ) (sys.SV.real (τ - t) x)⟫_ℝ (Ioi τ) τ := by
    intro τ hτ
    have h := hasDerivWithinAt_reducedValue hH1 hH2 hT wts ⟨ht.1.trans hτ.1.le, hτ.2⟩
      (sys.SV.real (τ - t) x)
    rw [bStarPV_riccatiP]
    refine (h.congr (fun σ hσ => ?_) ?_).mono Ioi_subset_Ici_self
    · rw [← sys.SV.real_add_apply (sub_nonneg.2 hσ) (sub_nonneg.2 hτ.1.le), sub_add_sub_cancel]
    · rw [sub_self, sys.SV.real_zero, one_apply_eq_self]
  have hint := intervalIntegrable_inner_bStarPV (sys := sys) ht
    (continuousOn_riccatiP (sys := sys) wts T) wts x x
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.2 hFc hderiv hint]
  simp only [reducedValue, sub_self, sys.SV.real_zero, one_apply_eq_self,
    riccatiP_terminal wts hT.le, tailC_self, zero_apply, norm_zero]
  ring

/-- The output term as an `L²` inner product: `⟪c_t x, c_t y⟫ = ∫ₜᵀ ⟪(𝓞_V x)(s - t),
(𝓞_V y)(s - t)⟫ ds`. -/
theorem inner_tailC_eq_integral {T t : ℝ} (ht : t ∈ Icc 0 T) (x y : V) :
    ⟪sys.tailC T t x, sys.tailC T t y⟫_ℝ =
      ∫ s in t..T, ⟪sys.𝓞V T x (s - t), sys.𝓞V T y (s - t)⟫_ℝ := by
  rw [L2.inner_def, intervalIntegral.integral_of_le ht.2]
  have hae : (fun r => ⟪sys.tailC T t x r, sys.tailC T t y r⟫_ℝ) =ᵐ[μI T]
      (Ioc t T).indicator fun r => ⟪sys.𝓞V T x (r - t), sys.𝓞V T y (r - t)⟫_ℝ := by
    filter_upwards [coeFn_shR (T := T) (s := t) (sys.𝓞V T x),
      coeFn_shR (T := T) (s := t) (sys.𝓞V T y), ae_restrict_mem measurableSet_Ioc]
      with r h1 h2 hr
    rw [tailC_apply, tailC_apply, h1, h2]
    by_cases hrt : t < r
    · have hm : r - t ∈ Ioc 0 T := ⟨by linarith, by linarith [hr.2, ht.1]⟩
      rw [indicator_of_mem hm, indicator_of_mem hm,
        indicator_of_mem (show r ∈ Ioc t T from ⟨hrt, hr.2⟩)]
    · have hm : r - t ∉ Ioc 0 T := fun h => hrt (by linarith [h.1])
      rw [indicator_of_notMem hm, indicator_of_notMem hm,
        indicator_of_notMem (show r ∉ Ioc t T from fun h => hrt h.1), inner_zero_left]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_eq_left ht.1, min_self]

/-- Polarisation: two "quadratic" functions that agree on the diagonal agree. -/
private theorem eq_of_polarization {f g : V → V → ℝ}
    (hf : ∀ x y, f (x + y) (x + y) - f (x - y) (x - y) = 4 * f x y)
    (hg : ∀ x y, g (x + y) (x + y) - g (x - y) (x - y) = 4 * g x y)
    (h : ∀ x, f x x = g x x) (x y : V) : f x y = g x y := by
  have h1 := hf x y
  have h2 := hg x y
  rw [h, h] at h1
  linarith

/-- **Existence for `thm:lqr-riccati`**: under `hyp:H1` and `hyp:H2` the value operator
`riccatiP` solves the integral Riccati equation on `[0, T]`.  `hyp:compat` is not needed. -/
theorem isRiccatiIntegralSolution_riccatiP {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (hT : 0 < T) (wts : LQRWeights U V) :
    sys.IsRiccatiIntegralSolution wts T (sys.riccatiP wts T) where
  symm t _ x y := riccatiP_symm wts T t x y
  continuousOn x := continuousOn_riccatiP wts T x
  eq_integral t ht x y := by
    have hint : ∀ z z' : V, IntervalIntegrable
        (fun s => ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) z)),
          sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) z')⟫_ℝ) volume t T :=
      fun z z' => intervalIntegrable_inner_bStarPV ht (continuousOn_riccatiP wts T) wts z z'
    have hf : ∀ x y : V, sys.riccatiP wts T t (x + y) (x + y) -
        sys.riccatiP wts T t (x - y) (x - y) = 4 * sys.riccatiP wts T t x y := by
      intro x y
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [riccatiP_symm wts T t y x]
      ring
    have hg : ∀ x y : V,
        (wts.G (sys.SV.real (T - t) (x + y)) (sys.SV.real (T - t) (x + y)) +
          ⟪sys.tailC T t (x + y), sys.tailC T t (x + y)⟫_ℝ -
          ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s)
            (sys.SV.real (s - t) (x + y))),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x + y))⟫_ℝ) -
        (wts.G (sys.SV.real (T - t) (x - y)) (sys.SV.real (T - t) (x - y)) +
          ⟪sys.tailC T t (x - y), sys.tailC T t (x - y)⟫_ℝ -
          ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s)
            (sys.SV.real (s - t) (x - y))),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x - y))⟫_ℝ) =
        4 * (wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) y) +
          ⟪sys.tailC T t x, sys.tailC T t y⟫_ℝ -
          ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) y)⟫_ℝ) := by
      intro x y
      have hG : wts.G (sys.SV.real (T - t) (x + y)) (sys.SV.real (T - t) (x + y)) -
          wts.G (sys.SV.real (T - t) (x - y)) (sys.SV.real (T - t) (x - y)) =
          4 * wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) y) := by
        simp only [map_add, map_sub, add_apply, sub_apply]
        rw [wts.G_symm (sys.SV.real (T - t) y) (sys.SV.real (T - t) x)]
        ring
      have hc : ⟪sys.tailC T t (x + y), sys.tailC T t (x + y)⟫_ℝ -
          ⟪sys.tailC T t (x - y), sys.tailC T t (x - y)⟫_ℝ =
          4 * ⟪sys.tailC T t x, sys.tailC T t y⟫_ℝ := by
        simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
          inner_sub_right]
        rw [real_inner_comm (sys.tailC T t x) (sys.tailC T t y)]
        ring
      have hpt : ∀ s,
          ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x + y))),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x + y))⟫_ℝ -
          ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x - y))),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) (x - y))⟫_ℝ =
          4 * ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) y)⟫_ℝ := by
        intro s
        simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
          inner_sub_right]
        rw [wts.inner_Rinv_comm
            (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) y))
            (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)),
          real_inner_comm (wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)))
            (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) y))]
        ring
      have hI := intervalIntegral.integral_sub (hint (x + y) (x + y)) (hint (x - y) (x - y))
      rw [intervalIntegral.integral_congr (fun s _ => hpt s),
        intervalIntegral.integral_const_mul] at hI
      linarith
    have hdiag : ∀ z : V, sys.riccatiP wts T t z z =
        wts.G (sys.SV.real (T - t) z) (sys.SV.real (T - t) z) +
          ⟪sys.tailC T t z, sys.tailC T t z⟫_ℝ -
          ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) z)),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) z)⟫_ℝ := fun z => by
      rw [real_inner_self_eq_norm_sq]; exact riccatiP_self_eq hH1 hH2 hT wts ht z
    have key := eq_of_polarization (f := fun x y => sys.riccatiP wts T t x y)
      (g := fun x y => wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) y) +
          ⟪sys.tailC T t x, sys.tailC T t y⟫_ℝ -
          ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) x)),
            sys.bStarPV (sys.riccatiP wts T s) (sys.SV.real (s - t) y)⟫_ℝ) hf hg hdiag x y
    rw [key, inner_tailC_eq_integral ht, intervalIntegral.integral_sub
      (intervalIntegrable_inner_𝓞V ht x y) (hint x y)]
    ring

/-! ### `thm:lqr-riccati` in full -/

/-- For `T ≤ 0`, `P ≡ G` solves the integral Riccati equation (on `[0, T] ⊆ {0}`). -/
theorem isRiccatiIntegralSolution_of_nonpos {T : ℝ} (hT : T ≤ 0) (wts : LQRWeights U V) :
    sys.IsRiccatiIntegralSolution wts T (fun _ => wts.G) where
  symm _ _ := wts.G_symm
  continuousOn _ := continuousOn_const
  eq_integral t ht x y := by
    have htT : t = T := le_antisymm ht.2 (by linarith [ht.1])
    subst htT
    simp

/-- Every solution of the integral Riccati equation is the value operator on `[0, T]`. -/
theorem IsRiccatiIntegralSolution.eqOn_riccatiP {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (hT : 0 < T) {wts : LQRWeights U V} {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    (h : sys.IsRiccatiIntegralSolution wts T P) : EqOn P (sys.riccatiP wts T) (Icc 0 T) :=
  h.eqOn (isRiccatiIntegralSolution_riccatiP hH1 hH2 hT wts)

/-- **Every solution of the integral Riccati equation is a `RiccatiSolution`** (under `hyp:H1`,
`hyp:H2`): it is nonnegative, and it gives the optimal feedback `u(t) = -R⁻¹ B^⋆P(t) x(t)` and
the minimal cost `⟨x₀, P(0) x₀⟩` (`eq:lqr-feedback`). -/
def IsRiccatiIntegralSolution.toRiccatiSolution {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (hT : 0 < T) {wts : LQRWeights U V} {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    (h : sys.IsRiccatiIntegralSolution wts T P) : sys.RiccatiSolution wts T where
  P := P
  symm := h.symm
  nonneg t ht v := by
    rw [h.eqOn_riccatiP hH1 hH2 hT ht]; exact riccatiP_nonneg wts T t v
  continuousOn := h.continuousOn
  terminal := h.terminal hT.le
  optimal x₀ := by
    obtain ⟨u, hmin, hfb, hcost⟩ := (riccatiSolution_of_pos hH1 hH2 hT wts).optimal x₀
    refine ⟨u, hmin, ?_, ?_⟩
    · filter_upwards [hfb, ae_restrict_mem measurableSet_Ioc] with t h1 h2
      rw [h.eqOn_riccatiP hH1 hH2 hT (Ioc_subset_Icc_self h2)]
      exact h1
    · rw [h.eqOn_riccatiP hH1 hH2 hT ⟨le_rfl, hT.le⟩]
      exact hcost

/-- **`thm:lqr-riccati`** (Pritchard–Salamon, Thm 2.7), in full, at every horizon, under
`hyp:H1` and `hyp:H2` (`hyp:compat` is not needed): the integral Riccati equation has a solution
`P` that is self-adjoint, nonnegative and strongly continuous on `I = [0, T]`, with `P(T) = G`,
and that gives the optimal feedback `u_F(t) = -R⁻¹ B^⋆P(t) x(t)` and the minimal cost
`⟨x₀, P(0) x₀⟩` for every `x₀ ∈ W` (a `RiccatiSolution`); every solution of the equation agrees
with it on `I`. -/
theorem riccatiIntegralTheorem {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (wts : LQRWeights U V) :
    ∃ ric : sys.RiccatiSolution wts T, sys.IsRiccatiIntegralSolution wts T ric.P ∧
      ∀ P : ℝ → V →L[ℝ] V →L[ℝ] ℝ, sys.IsRiccatiIntegralSolution wts T P →
        EqOn P ric.P (Icc 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · have h := isRiccatiIntegralSolution_of_nonpos (sys := sys) hT wts
    exact ⟨riccatiSolution_of_nonpos hT wts, h, fun P hP => hP.eqOn h⟩
  · have h := isRiccatiIntegralSolution_riccatiP hH1 hH2 hT wts
    exact ⟨riccatiSolution_of_pos hH1 hH2 hT wts, h, fun P hP => hP.eqOn h⟩

/-- **`thm:lqr-riccati`** for `T > 0`, with the value operator named: `riccatiP` solves the
integral Riccati equation, is nonnegative, and is its only solution on `I = [0, T]`; for every
`x₀ ∈ W` the problem `eq:lqr-cost` has a unique optimal control, which is the feedback
`u_F(t) = -R⁻¹ B^⋆P(t) x(t)`, with minimal cost `⟨x₀, P(0) x₀⟩` (`eq:lqr-feedback`). -/
theorem riccatiIntegralTheorem_of_pos {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) :
    sys.IsRiccatiIntegralSolution wts T (sys.riccatiP wts T) ∧
      (∀ t ∈ Icc 0 T, ∀ v : V, 0 ≤ sys.riccatiP wts T t v v) ∧
      (∀ P : ℝ → V →L[ℝ] V →L[ℝ] ℝ, sys.IsRiccatiIntegralSolution wts T P →
        EqOn P (sys.riccatiP wts T) (Icc 0 T)) ∧
      ∀ x₀ : W, ∃! u : L2 U T, IsMinOn (fun v : L2 U T => sys.lqrCost wts T x₀ v) univ u ∧
        (∀ᵐ t ∂(μI T), u t = -wts.Rinv (sys.bStarP (sys.riccatiP wts T t) (sys.mildW x₀ u t))) ∧
        sys.lqrCost wts T x₀ u = sys.riccatiP wts T 0 (sys.ιWV x₀) (sys.ιWV x₀) := by
  refine ⟨isRiccatiIntegralSolution_riccatiP hH1 hH2 hT wts,
    fun t _ v => riccatiP_nonneg wts T t v, fun P hP => hP.eqOn_riccatiP hH1 hH2 hT,
    fun x₀ => ?_⟩
  obtain ⟨u, hmin, hfb, hcost⟩ := (riccatiSolution_of_pos hH1 hH2 hT wts).optimal x₀
  exact ⟨u, ⟨hmin, hfb, hcost⟩, fun v hv =>
    (existsUnique_isMinOn_lqrCost hH1 hT wts x₀).unique hv.1 hmin⟩

end System

end DataDrivenControl
