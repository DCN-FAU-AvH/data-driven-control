module

public import Mathlib
public import DataDrivenControl.LQR.TailOperators

/-!
# The integral Riccati equation and the uniqueness of its solution

Paper: `thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7): the integral operator Riccati equation
associated with `eq:lqr-cost`, with terminal condition `P(T) = G`, and the uniqueness of its
strongly continuous self-adjoint solution.  The paper cites the theorem and never writes the
equation down.  Existence (for the value operator `System.riccatiP`) is in
`LQR/RiccatiIntegral`.

## The equation

The equation is the open-loop (Curtain–Pritchard, Pritchard–Salamon) form
`P(t) = S(T - t)^⋆ G S(T - t) + ∫ₜᵀ S(s - t)^⋆ (C^⋆C - P(s) B R⁻¹ B^⋆ P(s)) S(s - t) ds`.
With `P(t)`, `G` bounded bilinear forms on `V`, `𝓞_V x = C S(·) x` the free output on `V`
(`System.𝓞V`) and `B^⋆ P x` the Riesz representer of `v ↦ P(x, B v)` (`System.bStarPV`), it
reads, for `x, y ∈ V` and `t ∈ [0, T]`,

`P(t)(x, y) = G(S_V(T - t) x, S_V(T - t) y)`
`  + ∫ₜᵀ (⟪(𝓞_V x)(s - t), (𝓞_V y)(s - t)⟫ - ⟪R⁻¹ B^⋆P(s) S_V(s - t) x, B^⋆P(s) S_V(s - t) y⟫) ds`.

At `t = T` it gives the terminal condition `P(T) = G` (`IsRiccatiIntegralSolution.terminal`).

## Main declarations

* `LQRWeights.R_Rinv`, `LQRWeights.Rinv_R`, `LQRWeights.inner_Rinv_comm`: `R⁻¹` is the inverse
  of `R` and is symmetric;
* `System.bStarPV P : V →L[ℝ] U`: `B^⋆ P x` for `x ∈ V` (`bStarP_eq_bStarPV`: on `W` it is
  `System.bStarP`), with `‖B^⋆ P x‖ ≤ ‖B‖ ‖P‖ ‖x‖`;
* `System.IsRiccatiIntegralSolution wts T P`: `P` is symmetric and strongly continuous on
  `[0, T]` and solves the integral Riccati equation there;
* `Riccati.exists_opNorm_bound_of_continuousOn` (Banach–Steinhaus): a strongly continuous family
  is uniformly bounded on a compact set;
* `System.IsRiccatiIntegralSolution.eqOn`: **uniqueness**, two solutions agree on `[0, T]`.  No
  hypothesis on the system is needed.

## Proof of uniqueness

`Δ = P₁ - P₂` satisfies `Δ(t)(x, y) = ∫ₜᵀ (⟪R⁻¹ a₂, b₂⟫ - ⟪R⁻¹ a₁, b₁⟫)` with
`aᵢ = B^⋆Pᵢ(s) S(s - t) x`, `bᵢ = B^⋆Pᵢ(s) S(s - t) y`, and
`⟪R⁻¹ a₁, b₁⟫ - ⟪R⁻¹ a₂, b₂⟫ = ⟪R⁻¹ (a₁ - a₂), b₁⟫ + ⟪R⁻¹ a₂, b₁ - b₂⟫`, so the integrand is at
most `K ‖Δ(s)‖ ‖x‖ ‖y‖`.  The bounds on `‖Pᵢ(s)‖` come from Banach–Steinhaus.  Iterating gives
`‖Δ(t)‖ ≤ D Kⁿ (T - t)ⁿ / n!` for every `n`, which avoids any measurability question about
`s ↦ ‖Δ(s)‖`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct Nat

noncomputable section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace LQRWeights

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `R R⁻¹ = 1`. -/
theorem R_Rinv (wts : LQRWeights U V) (u : U) : wts.R (wts.Rinv u) = u := by
  have h : wts.R * wts.Rinv = 1 := Ring.mul_inverse_cancel _ wts.isUnit_R
  exact DFunLike.congr_fun h u

/-- `R⁻¹ R = 1`. -/
theorem Rinv_R (wts : LQRWeights U V) (u : U) : wts.Rinv (wts.R u) = u := by
  have h : wts.Rinv * wts.R = 1 := Ring.inverse_mul_cancel _ wts.isUnit_R
  exact DFunLike.congr_fun h u

/-- `R⁻¹` is symmetric. -/
theorem inner_Rinv_comm (wts : LQRWeights U V) (a b : U) :
    ⟪wts.Rinv a, b⟫_ℝ = ⟪a, wts.Rinv b⟫_ℝ := by
  conv_lhs => rw [← wts.R_Rinv b]
  have h := wts.R_isSymmetric (wts.Rinv a) (wts.Rinv b)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, R_Rinv]

end LQRWeights

namespace Riccati

/-- **Banach–Steinhaus** on a compact set of times: a family of operators that is strongly
continuous on a compact set `S` is uniformly bounded on `S`. -/
theorem exists_opNorm_bound_of_continuousOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set ℝ}
    (hS : IsCompact S) {A : ℝ → E →L[ℝ] F} (hA : ∀ e, ContinuousOn (fun s => A s e) S) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ S, ‖A s‖ ≤ C := by
  have h : ∀ e, ∃ C, ∀ i : S, ‖A i e‖ ≤ C := fun e => by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hA e)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i : S => A i) h
  exact ⟨max C 0, le_max_right _ _, fun s hs => (hC ⟨s, hs⟩).trans (le_max_left _ _)⟩

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

/-! ### `B^⋆ P x` for `x ∈ V` -/

variable (sys) in
/-- `B^⋆ P x ∈ U` for a bounded bilinear form `P` on `V` and `x ∈ V`: the Riesz representer of
`v ↦ P(x, B v)`, i.e. `⟪B^⋆ P x, v⟫_U = P(x, B v)` (`inner_bStarPV`).  It is bounded in `x ∈ V`
because `B ∈ L(U, V)`; on `W` it is `System.bStarP` (`bStarP_eq_bStarPV`). -/
def bStarPV (P : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] U :=
  (sys.B†) ∘L InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) P

/-- The defining property of `B^⋆ P x`. -/
theorem inner_bStarPV (P : V →L[ℝ] V →L[ℝ] ℝ) (x : V) (u : U) :
    ⟪sys.bStarPV P x, u⟫_ℝ = P x (sys.B u) := by
  rw [bStarPV, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    InnerProductSpace.continuousLinearMapOfBilin_apply]

/-- On `W`, `bStarPV` is `bStarP`. -/
theorem bStarP_eq_bStarPV (P : V →L[ℝ] V →L[ℝ] ℝ) (x : W) :
    sys.bStarP P x = sys.bStarPV P (sys.ιWV x) :=
  ext_inner_right ℝ fun u => by rw [inner_bStarP, inner_bStarPV]

/-- `B^⋆ P x = B† (Riesz representer of P x)`. -/
theorem bStarPV_apply (P : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    sys.bStarPV P x = (sys.B†) ((InnerProductSpace.toDual ℝ V).symm (P x)) :=
  ext_inner_right ℝ fun u => by
    rw [inner_bStarPV, ContinuousLinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply]

/-- `B^⋆ P x` is linear in `P`. -/
theorem bStarPV_sub (P Q : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    sys.bStarPV (P - Q) x = sys.bStarPV P x - sys.bStarPV Q x :=
  ext_inner_right ℝ fun u => by
    rw [inner_sub_left, inner_bStarPV, inner_bStarPV, inner_bStarPV,
      sub_apply, sub_apply]

/-- `‖B^⋆ P x‖ ≤ ‖B‖ ‖P‖ ‖x‖`. -/
theorem norm_bStarPV_apply_le (P : V →L[ℝ] V →L[ℝ] ℝ) (x : V) :
    ‖sys.bStarPV P x‖ ≤ ‖sys.B‖ * ‖P‖ * ‖x‖ := by
  rw [bStarPV_apply]
  calc ‖(sys.B†) ((InnerProductSpace.toDual ℝ V).symm (P x))‖
      ≤ ‖sys.B†‖ * ‖(InnerProductSpace.toDual ℝ V).symm (P x)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖sys.B‖ * ‖P x‖ := by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    _ ≤ ‖sys.B‖ * (‖P‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖sys.B‖ * ‖P‖ * ‖x‖ := by ring

/-! ### The integral Riccati equation -/

variable (sys) in
/-- **The integral Riccati equation** of `thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7):
`P : ℝ → L(V, V')`, as bounded bilinear forms on `V`, is symmetric and strongly continuous on
`I = [0, T]` and satisfies, for `t ∈ I` and `x, y ∈ V`,
`P(t)(x, y) = G(S_V(T - t) x, S_V(T - t) y) + ∫ₜᵀ (⟪(𝓞_V x)(s - t), (𝓞_V y)(s - t)⟫
  - ⟪R⁻¹ B^⋆P(s) S_V(s - t) x, B^⋆P(s) S_V(s - t) y⟫) ds`,
the open-loop form `P(t) = S^⋆ G S + ∫ S^⋆ (C^⋆C - P B R⁻¹ B^⋆ P) S`.  Here `𝓞_V x = C S(·) x`
on `(0, T]` (`System.𝓞V`).  At `t = T` it gives `P(T) = G` (`terminal`). -/
structure IsRiccatiIntegralSolution (wts : LQRWeights U V) (T : ℝ)
    (P : ℝ → V →L[ℝ] V →L[ℝ] ℝ) : Prop where
  /-- `P(t)` is self-adjoint on `I`. -/
  symm : ∀ t ∈ Icc 0 T, ∀ x y : V, P t x y = P t y x
  /-- `P` is strongly continuous on `I`: `t ↦ P(t) x ∈ V'` is continuous for every `x ∈ V`. -/
  continuousOn : ∀ x : V, ContinuousOn (fun t => P t x) (Icc 0 T)
  /-- The integral Riccati equation on `I`. -/
  eq_integral : ∀ t ∈ Icc 0 T, ∀ x y : V,
    P t x y = wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) y) +
      ∫ s in t..T, (⟪sys.𝓞V T x (s - t), sys.𝓞V T y (s - t)⟫_ℝ -
        ⟪wts.Rinv (sys.bStarPV (P s) (sys.SV.real (s - t) x)),
          sys.bStarPV (P s) (sys.SV.real (s - t) y)⟫_ℝ)

/-- The terminal condition `P(T) = G` is part of the integral equation. -/
theorem IsRiccatiIntegralSolution.terminal {wts : LQRWeights U V} {T : ℝ}
    {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ} (h : sys.IsRiccatiIntegralSolution wts T P) (hT : 0 ≤ T) :
    P T = wts.G := by
  ext x y
  rw [h.eq_integral T ⟨hT, le_rfl⟩ x y, intervalIntegral.integral_same, add_zero, sub_self,
    sys.SV.real_zero]
  rfl

/-- The output term of the equation is integrable on `[t, T]`. -/
theorem intervalIntegrable_inner_𝓞V {T t : ℝ} (ht : t ∈ Icc 0 T) (x y : V) :
    IntervalIntegrable (fun s => ⟪sys.𝓞V T x (s - t), sys.𝓞V T y (s - t)⟫_ℝ) volume t T := by
  have h0 : IntervalIntegrable (fun σ => ⟪sys.𝓞V T x σ, sys.𝓞V T y σ⟫_ℝ) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (ht.1.trans ht.2)).2 (L2.integrable_inner _ _)
  have h1 : IntervalIntegrable (fun σ => ⟪sys.𝓞V T x σ, sys.𝓞V T y σ⟫_ℝ) volume 0 (T - t) := by
    refine h0.mono_set ?_
    rw [uIcc_of_le (by linarith [ht.2] : (0 : ℝ) ≤ T - t), uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl (by linarith [ht.1])
  simpa using h1.comp_sub_right t

/-- The quadratic term of the equation is continuous on `[t, T]` for a strongly continuous
`P` (uniformly bounded by Banach–Steinhaus). -/
theorem continuousOn_inner_bStarPV {T t : ℝ} (ht : 0 ≤ t) {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    (hP : ∀ x, ContinuousOn (fun s => P s x) (Icc 0 T)) (wts : LQRWeights U V) (x y : V) :
    ContinuousOn (fun s => ⟪wts.Rinv (sys.bStarPV (P s) (sys.SV.real (s - t) x)),
      sys.bStarPV (P s) (sys.SV.real (s - t) y)⟫_ℝ) (Icc t T) := by
  obtain ⟨C, -, hC⟩ := exists_opNorm_bound_of_continuousOn isCompact_Icc hP
  have hsub : Icc t T ⊆ Icc 0 T := Icc_subset_Icc_left ht
  have key : ∀ z : V,
      ContinuousOn (fun s => sys.bStarPV (P s) (sys.SV.real (s - t) z)) (Icc t T) := by
    intro z
    have h1 : ContinuousOn (fun s => P s (sys.SV.real (s - t) z)) (Icc t T) :=
      continuousOn_apply_of_bounded (fun e => (hP e).mono hsub) (fun s hs => hC s (hsub hs))
        ((sys.SV.continuous_real_apply z).comp (continuous_id.sub continuous_const)).continuousOn
    simp only [bStarPV_apply]
    exact (sys.B†).continuous.comp_continuousOn
      ((InnerProductSpace.toDual ℝ V).symm.continuous.comp_continuousOn h1)
  exact (wts.Rinv.continuous.comp_continuousOn (key x)).inner (key y)

/-- The quadratic term of the equation is integrable on `[t, T]`. -/
theorem intervalIntegrable_inner_bStarPV {T t : ℝ} (ht : t ∈ Icc 0 T)
    {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ} (hP : ∀ x, ContinuousOn (fun s => P s x) (Icc 0 T))
    (wts : LQRWeights U V) (x y : V) :
    IntervalIntegrable (fun s => ⟪wts.Rinv (sys.bStarPV (P s) (sys.SV.real (s - t) x)),
      sys.bStarPV (P s) (sys.SV.real (s - t) y)⟫_ℝ) volume t T :=
  (continuousOn_inner_bStarPV ht.1 hP wts x y).intervalIntegrable_of_Icc ht.2

/-- The integral equation with the two integrals separated. -/
theorem IsRiccatiIntegralSolution.eq_sub {wts : LQRWeights U V} {T : ℝ}
    {P : ℝ → V →L[ℝ] V →L[ℝ] ℝ} (h : sys.IsRiccatiIntegralSolution wts T P) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x y : V) :
    P t x y = wts.G (sys.SV.real (T - t) x) (sys.SV.real (T - t) y) +
      (∫ s in t..T, ⟪sys.𝓞V T x (s - t), sys.𝓞V T y (s - t)⟫_ℝ) -
      ∫ s in t..T, ⟪wts.Rinv (sys.bStarPV (P s) (sys.SV.real (s - t) x)),
        sys.bStarPV (P s) (sys.SV.real (s - t) y)⟫_ℝ := by
  rw [h.eq_integral t ht x y, intervalIntegral.integral_sub (intervalIntegrable_inner_𝓞V ht x y)
    (intervalIntegrable_inner_bStarPV ht h.continuousOn wts x y), add_sub_assoc]

/-! ### Uniqueness -/

/-- `∫ₜᵀ (T - s)ⁿ ds = (T - t)ⁿ⁺¹ / (n + 1)`. -/
private theorem integral_sub_pow (t T : ℝ) (n : ℕ) :
    ∫ s in t..T, (T - s) ^ n = (T - t) ^ (n + 1) / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun s => s ^ n), sub_self, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero]

/-- **Uniqueness of the solution of the integral Riccati equation** (`thm:lqr-riccati`): two
solutions agree on `I = [0, T]`.  No hypothesis on the system is needed. -/
theorem IsRiccatiIntegralSolution.eqOn {wts : LQRWeights U V} {T : ℝ}
    {P₁ P₂ : ℝ → V →L[ℝ] V →L[ℝ] ℝ} (h₁ : sys.IsRiccatiIntegralSolution wts T P₁)
    (h₂ : sys.IsRiccatiIntegralSolution wts T P₂) : EqOn P₁ P₂ (Icc 0 T) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_opNorm_bound_of_continuousOn isCompact_Icc h₁.continuousOn
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_opNorm_bound_of_continuousOn isCompact_Icc h₂.continuousOn
  obtain ⟨M, hM, hSM⟩ := sys.SV.exists_norm_real_le T
  set K := ‖wts.Rinv‖ * ‖sys.B‖ ^ 2 * M ^ 2 * (C₁ + C₂) with hK
  have hK0 : 0 ≤ K := by positivity
  set D := C₁ + C₂ with hD
  have hD0 : 0 ≤ D := by positivity
  -- the integrand of `P₁ - P₂`
  set d : ℝ → V → V → ℝ → ℝ := fun t x y s =>
    ⟪wts.Rinv (sys.bStarPV (P₂ s) (sys.SV.real (s - t) x)),
        sys.bStarPV (P₂ s) (sys.SV.real (s - t) y)⟫_ℝ -
      ⟪wts.Rinv (sys.bStarPV (P₁ s) (sys.SV.real (s - t) x)),
        sys.bStarPV (P₁ s) (sys.SV.real (s - t) y)⟫_ℝ with hd
  have hdiff : ∀ t ∈ Icc 0 T, ∀ x y : V, P₁ t x y - P₂ t x y = ∫ s in t..T, d t x y s := by
    intro t ht x y
    rw [h₁.eq_sub ht x y, h₂.eq_sub ht x y, hd,
      intervalIntegral.integral_sub (intervalIntegrable_inner_bStarPV ht h₂.continuousOn wts x y)
        (intervalIntegrable_inner_bStarPV ht h₁.continuousOn wts x y)]
    ring
  -- the pointwise bound `|d s| ≤ K ‖Δ(s)‖ ‖x‖ ‖y‖`
  have hpt : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc t T, ∀ x y : V,
      ‖d t x y s‖ ≤ K * ‖P₁ s - P₂ s‖ * (‖x‖ * ‖y‖) := by
    intro t ht s hs x y
    have hs0 : s ∈ Icc 0 T := ⟨ht.1.trans hs.1, hs.2⟩
    have hS : ∀ z : V, ‖sys.SV.real (s - t) z‖ ≤ M * ‖z‖ := fun z =>
      ((sys.SV.real (s - t)).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right (hSM _ (by linarith [hs.2, ht.1])) (norm_nonneg _))
    set Δ := P₁ s - P₂ s
    set a₁ := sys.bStarPV (P₁ s) (sys.SV.real (s - t) x)
    set a₂ := sys.bStarPV (P₂ s) (sys.SV.real (s - t) x)
    set b₁ := sys.bStarPV (P₁ s) (sys.SV.real (s - t) y)
    set b₂ := sys.bStarPV (P₂ s) (sys.SV.real (s - t) y)
    have hbound : ∀ (Q : V →L[ℝ] V →L[ℝ] ℝ) (c : ℝ), ‖Q‖ ≤ c → ∀ z : V,
        ‖sys.bStarPV Q (sys.SV.real (s - t) z)‖ ≤ ‖sys.B‖ * c * (M * ‖z‖) := by
      intro Q c hQ z
      calc ‖sys.bStarPV Q (sys.SV.real (s - t) z)‖
          ≤ ‖sys.B‖ * ‖Q‖ * ‖sys.SV.real (s - t) z‖ := norm_bStarPV_apply_le _ _
        _ ≤ ‖sys.B‖ * c * (M * ‖z‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (hS z) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (by have := norm_nonneg Q; linarith))
    have e1 : ‖a₁ - a₂‖ ≤ ‖sys.B‖ * ‖Δ‖ * (M * ‖x‖) := by
      rw [← bStarPV_sub]; exact hbound Δ ‖Δ‖ le_rfl x
    have e2 : ‖b₁‖ ≤ ‖sys.B‖ * C₁ * (M * ‖y‖) := hbound _ _ (hb₁ s hs0) y
    have e3 : ‖a₂‖ ≤ ‖sys.B‖ * C₂ * (M * ‖x‖) := hbound _ _ (hb₂ s hs0) x
    have e4 : ‖b₁ - b₂‖ ≤ ‖sys.B‖ * ‖Δ‖ * (M * ‖y‖) := by
      rw [← bStarPV_sub]; exact hbound Δ ‖Δ‖ le_rfl y
    have hsplit : d t x y s = -(⟪wts.Rinv (a₁ - a₂), b₁⟫_ℝ + ⟪wts.Rinv a₂, b₁ - b₂⟫_ℝ) := by
      simp only [hd, map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [hsplit, norm_neg]
    calc ‖⟪wts.Rinv (a₁ - a₂), b₁⟫_ℝ + ⟪wts.Rinv a₂, b₁ - b₂⟫_ℝ‖
        ≤ ‖⟪wts.Rinv (a₁ - a₂), b₁⟫_ℝ‖ + ‖⟪wts.Rinv a₂, b₁ - b₂⟫_ℝ‖ := norm_add_le _ _
      _ ≤ ‖wts.Rinv (a₁ - a₂)‖ * ‖b₁‖ + ‖wts.Rinv a₂‖ * ‖b₁ - b₂‖ :=
          add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖wts.Rinv‖ * ‖a₁ - a₂‖ * ‖b₁‖ + ‖wts.Rinv‖ * ‖a₂‖ * ‖b₁ - b₂‖ := by
          gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖wts.Rinv‖ * (‖sys.B‖ * ‖Δ‖ * (M * ‖x‖)) * (‖sys.B‖ * C₁ * (M * ‖y‖)) +
          ‖wts.Rinv‖ * (‖sys.B‖ * C₂ * (M * ‖x‖)) * (‖sys.B‖ * ‖Δ‖ * (M * ‖y‖)) := by
          gcongr
      _ = K * ‖Δ‖ * (‖x‖ * ‖y‖) := by rw [hK]; ring
  -- iteration: `‖Δ(t)‖ ≤ D Kⁿ (T - t)ⁿ / n!`
  have hind : ∀ n : ℕ, ∀ t ∈ Icc 0 T, ‖P₁ t - P₂ t‖ ≤ D * (K ^ n * (T - t) ^ n / n !) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, hD]
      exact (norm_sub_le _ _).trans (add_le_add (hb₁ t ht) (hb₂ t ht))
    | succ n ih =>
      intro t ht
      have hTt : 0 ≤ T - t := by linarith [ht.2]
      refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun x y => ?_
      rw [sub_apply, sub_apply, hdiff t ht x y]
      set c := K * (D * (K ^ n / n !)) * (‖x‖ * ‖y‖) with hc
      have hg : IntervalIntegrable (fun s => c * (T - s) ^ n) volume t T :=
        (continuous_const.mul ((continuous_const.sub continuous_id).pow n)).intervalIntegrable _ _
      calc ‖∫ s in t..T, d t x y s‖ ≤ ∫ s in t..T, c * (T - s) ^ n := by
            refine intervalIntegral.norm_integral_le_of_norm_le ht.2
              (Eventually.of_forall fun s hs => ?_) hg
            have hs' : s ∈ Icc t T := Ioc_subset_Icc_self hs
            have hs0 : s ∈ Icc 0 T := ⟨ht.1.trans hs'.1, hs'.2⟩
            calc ‖d t x y s‖ ≤ K * ‖P₁ s - P₂ s‖ * (‖x‖ * ‖y‖) := hpt t ht s hs' x y
              _ ≤ K * (D * (K ^ n * (T - s) ^ n / n !)) * (‖x‖ * ‖y‖) := by
                  gcongr; exact ih s hs0
              _ = c * (T - s) ^ n := by rw [hc]; ring
        _ = c * ((T - t) ^ (n + 1) / (n + 1)) := by
            rw [intervalIntegral.integral_const_mul, integral_sub_pow]
        _ = D * (K ^ (n + 1) * (T - t) ^ (n + 1) / (n + 1)!) * ‖x‖ * ‖y‖ := by
            rw [hc, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
            field_simp
            ring
  intro t ht
  have hlim := (FloorSemiring.tendsto_pow_div_factorial_atTop (K * (T - t))).const_mul D
  rw [mul_zero] at hlim
  have hle : ‖P₁ t - P₂ t‖ ≤ 0 :=
    ge_of_tendsto' hlim fun n => by rw [mul_pow]; exact hind n t ht
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end System

end DataDrivenControl
