module

public import DataDrivenControl.LQR.ValueOperator

/-!
# The adjoint of the input map (needle variations)

Step R5 of the proof of `thm:lqr-riccati`, the analytic core
of the feedback identity `eq:lqr-feedback`.  It replaces Pritchard–Salamon, Lemma 2.5, and
needs neither `hyp:compat` nor a Fubini argument against the unbounded `C`.

For `z ∈ V` and `y ∈ L²(0, T; Y)`, the adjoint of the input map
`u ↦ (ιWV L_T u, 𝓕_T u) ∈ V × L²(0, T; Y)` is pointwise
`((ιWV ∘ L_T)† z + 𝓕_T† y)(t) = B† (S_V(T - t)† z + c_t† y)` for a.e. `t ∈ (0, T)`, where
`c_t = shR t ∘ 𝓞_V` is the free output of the tail problem started at `t`
(`System.coeFn_adjoint_input`).

## Proof (needle variations)

* `System.needle_state`, `System.needle_output`: for an input `h` supported in `(β, γ]`,
  `ιWV L_T h = S_V(T - γ) ιWV L_γ h` and `𝓕_T h = c_γ (ιWV L_γ h) + (cut β - cut γ) 𝓕_T h`
  (the cocycle identities of `LQR/TailOperators`);
* `System.norm_L_step_sub_le`: `ιWV L_γ 1_(β,γ] u₀ = (γ - β) B u₀ + o(γ - β)`;
  `System.exists_norm_cut_𝓕_step_le`: the output on `(β, γ]` is `O(γ - β)` (`hyp:H1`);
* `System.hasDerivWithinAt_needle`: `γ ↦ ⟪λ, 1_(0,γ] u₀⟫` has right derivative `⟪p β, B u₀⟫`,
  `p t = S_V(T - t)† z + c_t† y` (continuous: `System.continuous_costate`);
* the fundamental theorem of calculus (`constant_of_has_deriv_right_zero`) and Lebesgue
  differentiation (`Riccati.ae_eq_zero_of_integral_Ioc`) give the a.e. identity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Riccati

/-! ### Generic tools -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An integrable function on `(0, T]` whose integrals over all `(0, β]`, `β ∈ [0, T]`, vanish
is zero a.e. on `(0, T]` (Lebesgue differentiation, `LocallyIntegrable.ae_hasDerivAt_integral`). -/
theorem ae_eq_zero_of_integral_Ioc {T : ℝ} {f : ℝ → E} (hf : IntegrableOn f (Ioc 0 T))
    (h : ∀ β ∈ Icc 0 T, ∫ t in Ioc 0 β, f t = 0) : f =ᵐ[μI T] 0 := by
  set g := (Ioc 0 T).indicator f
  have hg : LocallyIntegrable g volume :=
    (hf.integrable_indicator measurableSet_Ioc).locallyIntegrable
  have hprim : ∀ x ∈ Icc 0 T, ∫ t in (0 : ℝ)..x, g t = 0 := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.1, setIntegral_indicator measurableSet_Ioc,
      Ioc_inter_Ioc, max_self, min_eq_left hx.2]
    exact h x hx
  have hT : ∀ᵐ x ∂volume, x ≠ T := by simp [ae_iff, measure_singleton]
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, hT] with x hx hxT hxI
  have hx' := hx 0
  have hloc : (fun x => ∫ t in (0 : ℝ)..x, g t) =ᶠ[𝓝 x] fun _ => (0 : E) := by
    filter_upwards [Ioo_mem_nhds hxI.1 (lt_of_le_of_ne hxI.2 hxT)] with y hy
    exact hprim y ⟨hy.1.le, hy.2.le⟩
  have h0 := (hasDerivAt_const x (0 : E)).congr_of_eventuallyEq hloc
  have := hx'.unique h0
  simpa [g, indicator_of_mem hxI] using this

end Generic

section Steps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The constant signal `u₀` in `L²(0, T; E)`. -/
def constL2 (T : ℝ) (u₀ : E) : L2 E T := (memLp_const u₀).toLp _

/-- A representative of the constant signal. -/
theorem coeFn_constL2 (T : ℝ) (u₀ : E) : ⇑(constL2 T u₀) =ᵐ[μI T] fun _ => u₀ :=
  (memLp_const u₀).coeFn_toLp

/-- The step `cut β (const u₀) - cut γ (const u₀)` is `1_(β,γ] u₀`. -/
theorem coeFn_step {T β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (u₀ : E) :
    ⇑(cut T β (constL2 T u₀) - cut T γ (constL2 T u₀)) =ᵐ[μI T]
      (Ioc β γ).indicator fun _ => u₀ := by
  filter_upwards [Lp.coeFn_sub (cut T β (constL2 T u₀)) (cut T γ (constL2 T u₀)),
    coeFn_cut hβ (constL2 T u₀), coeFn_cut (hβ.trans hβγ) (constL2 T u₀),
    coeFn_constL2 (E := E) T u₀, ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 h4 ht
  rw [h1, Pi.sub_apply, h2, h3]
  by_cases ha : t ≤ β
  · rw [indicator_of_notMem (show t ∉ Ioc β T from fun h => by linarith [h.1]),
      indicator_of_notMem (show t ∉ Ioc γ T from fun h => by linarith [h.1]),
      indicator_of_notMem (show t ∉ Ioc β γ from fun h => by linarith [h.1]), sub_zero]
  by_cases hb : t ≤ γ
  · rw [indicator_of_mem (show t ∈ Ioc β T from ⟨not_le.1 ha, ht.2⟩),
      indicator_of_notMem (show t ∉ Ioc γ T from fun h => by linarith [h.1]),
      indicator_of_mem (show t ∈ Ioc β γ from ⟨not_le.1 ha, hb⟩), sub_zero, h4]
  · rw [indicator_of_mem (show t ∈ Ioc β T from ⟨not_le.1 ha, ht.2⟩),
      indicator_of_mem (show t ∈ Ioc γ T from ⟨not_le.1 hb, ht.2⟩),
      indicator_of_notMem (show t ∉ Ioc β γ from fun h => hb h.2), sub_self]

/-- Pairing with a step: `⟪f, 1_(0,β] u₀⟫ = ∫_(0,β] ⟪f t, u₀⟫`. -/
theorem inner_step {T β : ℝ} (hβ : β ∈ Icc 0 T) (f : L2 E T) (u₀ : E) :
    ⟪f, cut T 0 (constL2 T u₀) - cut T β (constL2 T u₀)⟫_ℝ = ∫ t in Ioc 0 β, ⟪f t, u₀⟫_ℝ := by
  rw [L2.inner_def]
  have hae : (fun t => ⟪f t, (cut T 0 (constL2 T u₀) - cut T β (constL2 T u₀)) t⟫_ℝ)
      =ᵐ[μI T] (Ioc 0 β).indicator fun t => ⟪f t, u₀⟫_ℝ := by
    filter_upwards [coeFn_step (T := T) le_rfl hβ.1 u₀] with t ht
    rw [ht]
    by_cases h : t ∈ Ioc 0 β
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, inner_zero_right]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_left hβ.2]

end Steps

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

/-! ### The costate path -/

/-- `S_V(T - t)†` is the adjoint semigroup at `T - t`. -/
theorem adjoint_tailA_apply (T t : ℝ) (z : V) :
    ((sys.tailA T t)†) z = sys.SV.adjoint.real (T - t) z := by
  rw [tailA, C0Semigroup.adjoint_real]

/-- `c_t† = 𝓞_V† ∘ windowL T T t`. -/
theorem adjoint_tailC_apply (T t : ℝ) (y : L2 Y T) :
    ((sys.tailC T t)†) y = ((sys.𝓞V T)†) (windowL T T t y) := by
  rw [tailC, ContinuousLinearMap.adjoint_comp, adjoint_shR]
  rfl

/-- The costate path `t ↦ S_V(T - t)† z + c_t† y` is continuous on `ℝ`. -/
theorem continuous_costate (T : ℝ) (z : V) (y : L2 Y T) :
    Continuous fun t => ((sys.tailA T t)†) z + ((sys.tailC T t)†) y := by
  simp only [adjoint_tailA_apply, adjoint_tailC_apply]
  exact ((sys.SV.adjoint.continuous_real_apply z).comp (continuous_const.sub continuous_id)).add
    (((sys.𝓞V T)†).continuous.comp (continuous_windowL T T y))

/-! ### Needle variations -/

/-- Terminal state of an input supported in `(0, γ]`: `ιWV L_T h = S_V(T - γ) ιWV L_γ h`. -/
theorem needle_state {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {γ : ℝ} (hγ : γ ∈ Icc 0 T)
    {h : L2 U T} (hh : cut T γ h = 0) :
    sys.ιWV (sys.Lop T h) = sys.tailA T γ (sys.ιWV (sys.L γ h)) := by
  have := tailState hH1 hT 0 h hγ
  simp only [mildW, map_zero, zero_add] at this
  rw [tailB_apply, hh, map_zero, map_zero, add_zero] at this
  rw [Lop_apply hH1 hT, this]

/-- Output of an input supported in `(β, γ]`:
`𝓕_T h = c_γ (ιWV L_γ h) + (cut β - cut γ) 𝓕_T h`. -/
theorem needle_output {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) {β γ : ℝ}
    (hβ : β ∈ Icc 0 T) (hγ : γ ∈ Icc 0 T) {h : L2 U T} (hhβ : cut T β h = h)
    (hhγ : cut T γ h = 0) :
    sys.𝓕 T h =
      sys.tailC T γ (sys.ιWV (sys.L γ h)) + (cut T β (sys.𝓕 T h) - cut T γ (sys.𝓕 T h)) := by
  have h1 := tailOutput hH1 hH2 hT 0 h hγ
  simp only [mildW, map_zero, zero_add] at h1
  rw [tailD_apply, hhγ, map_zero, add_zero] at h1
  have h2 := cut_𝓕_cut hH1 hT hβ h
  rw [hhβ] at h2
  rw [h1, h2]
  abel

/-- The state reached by a short step: `‖ιWV L_γ 1_(β,γ] u₀ - (γ - β) B u₀‖ ≤ (γ - β) ε` if
`‖S_V(σ) B u₀ - B u₀‖ ≤ ε` for `σ ∈ [0, γ - β]`. -/
theorem norm_L_step_sub_le {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {β γ : ℝ} (hβ : 0 ≤ β)
    (hβγ : β ≤ γ) (hγT : γ ≤ T) (u₀ : U) {h : L2 U T}
    (hh : ⇑h =ᵐ[μI T] (Ioc β γ).indicator fun _ => u₀) {ε : ℝ}
    (hε : ∀ σ ∈ Icc 0 (γ - β), ‖sys.SV.real σ (sys.B u₀) - sys.B u₀‖ ≤ ε) :
    ‖sys.ιWV (sys.L γ h) - (γ - β) • sys.B u₀‖ ≤ (γ - β) * ε := by
  have hae : ∀ᵐ r ∂(μI γ), h r = (Ioc β γ).indicator (fun _ => u₀) r :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hγT) hh
  have hcont : Continuous fun r => sys.SV.real (γ - r) (sys.B u₀) :=
    (sys.SV.continuous_real_apply _).comp (continuous_const.sub continuous_id)
  have hconv : sys.ιWV (sys.L γ h) = ∫ r in Ioc β γ, sys.SV.real (γ - r) (sys.B u₀) := by
    rw [ιWV_L hH1 hT (memLp_μI_of_le (Lp.memLp h) hγT), convV]
    have hpt : (fun r => sys.SV.real (γ - r) (sys.B (h r))) =ᵐ[μI γ]
        (Ioc β γ).indicator fun r => sys.SV.real (γ - r) (sys.B u₀) := by
      filter_upwards [hae] with r hr
      rw [hr]
      by_cases hm : r ∈ Ioc β γ
      · simp only [indicator_of_mem hm]
      · simp only [indicator_of_notMem hm, map_zero]
    rw [integral_congr_ae hpt, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc, max_eq_left hβ, min_self]
  have hconst : (γ - β) • sys.B u₀ = ∫ _ in Ioc β γ, sys.B u₀ := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hβγ]
  rw [hconv, hconst, ← integral_sub (hcont.integrableOn_Ioc) (integrableOn_const (by simp))]
  refine (norm_setIntegral_le_of_norm_le_const (C := ε) (by simp) fun r hr => ?_).trans_eq ?_
  · exact hε _ ⟨by linarith [hr.2], by linarith [hr.1]⟩
  · rw [Real.volume_real_Ioc_of_le hβγ, mul_comm]

/-- The output of a short step is `O(γ - β)` on `(β, γ]`. -/
theorem exists_norm_cut_𝓕_step_le {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    ∃ K, 0 ≤ K ∧ ∀ (u₀ : U) {β γ : ℝ}, 0 ≤ β → β ≤ γ →
      ‖cut T β (sys.𝓕 T (cut T β (constL2 T u₀) - cut T γ (constL2 T u₀))) -
        cut T γ (sys.𝓕 T (cut T β (constL2 T u₀) - cut T γ (constL2 T u₀)))‖ ≤
        K * ‖u₀‖ * (γ - β) := by
  obtain ⟨b, hb⟩ := exists_norm_L_le hH1 hT T
  refine ⟨‖sys.C‖ * max b 0, by positivity, fun u₀ β γ hβ hβγ => ?_⟩
  set h := cut T β (constL2 T u₀) - cut T γ (constL2 T u₀)
  have hh : ‖h‖ ≤ √(γ - β) * ‖u₀‖ :=
    norm_cut_sub_cut_le hβ hβγ (norm_nonneg _) ((coeFn_constL2 T u₀).mono fun t ht => by rw [ht])
  have hpt : ∀ᵐ r ∂(μI T), ‖sys.𝓕 T h r‖ ≤ ‖sys.C‖ * (max b 0 * (√(γ - β) * ‖u₀‖)) := by
    filter_upwards [𝓕_ae_eq hH1 hT h, ae_restrict_mem measurableSet_Ioc] with r h1 h2
    rw [h1]
    refine (sys.C.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ‖sys.L r h‖ ≤ b * ‖h‖ := hb h r (Ioc_subset_Icc_self h2)
      _ ≤ max b 0 * ‖h‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max b 0 * (√(γ - β) * ‖u₀‖) := mul_le_mul_of_nonneg_left hh (le_max_right _ _)
  refine (norm_cut_sub_cut_le hβ hβγ (by positivity) hpt).trans_eq ?_
  have hs : √(γ - β) * √(γ - β) = γ - β := Real.mul_self_sqrt (by linarith)
  calc √(γ - β) * (‖sys.C‖ * (max b 0 * (√(γ - β) * ‖u₀‖)))
      = ‖sys.C‖ * max b 0 * ‖u₀‖ * (√(γ - β) * √(γ - β)) := by ring
    _ = _ := by rw [hs]

/-- **The needle derivative** (`R5`): with `λ = (ιWV ∘ L_T)† z + 𝓕_T† y` and the step inputs
`1_(0,γ] u₀`, `γ ↦ ⟪λ, 1_(0,γ] u₀⟫` has right derivative `⟪p β, B u₀⟫` at `β ∈ [0, T)`, where
`p t = S_V(T - t)† z + c_t† y` is the costate path. -/
theorem hasDerivWithinAt_needle {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) (z : V)
    (y : L2 Y T) (u₀ : U) {β : ℝ} (hβ : β ∈ Ico 0 T) :
    HasDerivWithinAt
      (fun γ => ⟪((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y,
        cut T 0 (constL2 T u₀) - cut T γ (constL2 T u₀)⟫_ℝ)
      ⟪((sys.tailA T β)†) z + ((sys.tailC T β)†) y, sys.B u₀⟫_ℝ (Ici β) β := by
  set κ := constL2 T u₀ with hκ
  set lam := ((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y with hlam
  set p : ℝ → V := fun t => ((sys.tailA T t)†) z + ((sys.tailC T t)†) y with hp
  have hpc : Continuous p := continuous_costate T z y
  set hs : ℝ → L2 U T := fun γ => cut T β κ - cut T γ κ with hs_def
  set E : ℝ → L2 Y T := fun γ => cut T β (sys.𝓕 T (hs γ)) - cut T γ (sys.𝓕 T (hs γ))
    with hE_def
  obtain ⟨K, hK, hKb⟩ := exists_norm_cut_𝓕_step_le hH1 hT (sys := sys)
  have key : ∀ γ ∈ Icc β T,
      ⟪lam, cut T 0 κ - cut T γ κ⟫_ℝ - ⟪lam, cut T 0 κ - cut T β κ⟫_ℝ =
        ⟪p γ, sys.ιWV (sys.L γ (hs γ))⟫_ℝ + ⟪y, E γ⟫_ℝ := by
    intro γ hγ
    have hβ' : β ∈ Icc 0 T := ⟨hβ.1, hβ.2.le⟩
    have hγ' : γ ∈ Icc 0 T := ⟨hβ.1.trans hγ.1, hγ.2⟩
    have hhβ : cut T β (hs γ) = hs γ := by
      simp only [hs_def, map_sub, cut_cut hβ.1 hβ.1, cut_cut hβ.1 hγ'.1, max_self,
        max_eq_right hγ.1]
    have hhγ : cut T γ (hs γ) = 0 := by
      simp only [hs_def, map_sub, cut_cut hγ'.1 hβ.1, cut_cut hγ'.1 hγ'.1, max_self,
        max_eq_left hγ.1, sub_self]
    have hcomp : (sys.ιWV ∘L sys.Lop T) (hs γ) = sys.ιWV (sys.Lop T (hs γ)) := rfl
    have hdiff : cut T 0 κ - cut T γ κ - (cut T 0 κ - cut T β κ) = hs γ := by
      simp only [hs_def]; abel
    rw [← inner_sub_right, hdiff, hlam, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, hcomp, needle_state hH1 hT hγ' hhγ,
      needle_output hH1 hH2 hT hβ' hγ' hhβ hhγ, inner_add_right]
    simp only [hp, hE_def, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
    ring
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set D := ‖p β‖ + 1 with hD
  have hDpos : 0 < D := by positivity
  set ε₁ := c / (3 * D) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  set r₁ := min 1 (c / (3 * (‖sys.B u₀‖ + 1))) with hr₁
  have hr₁pos : 0 < r₁ := lt_min one_pos (by positivity)
  set r₂ := c / (3 * (K * ‖u₀‖ + 1)) with hr₂
  have hr₂pos : 0 < r₂ := by positivity
  -- continuity of the costate at `β`
  have hE1 : ∀ᶠ γ in 𝓝[Ici β] β, ‖p γ - p β‖ < r₁ := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 (hpc.tendsto β)
    exact (this.eventually (gt_mem_nhds hr₁pos)).filter_mono nhdsWithin_le_nhds
  -- strong continuity of `S_V` at `0`
  obtain ⟨η, hη, hηb⟩ : ∃ η > 0, ∀ σ : ℝ, dist σ 0 < η →
      ‖sys.SV.real σ (sys.B u₀) - sys.B u₀‖ < ε₁ := by
    have h0 := (sys.SV.continuous_real_apply (sys.B u₀)).tendsto 0
    rw [sys.SV.real_zero, one_apply_eq_self,
      tendsto_iff_norm_sub_tendsto_zero] at h0
    exact Metric.eventually_nhds_iff.1 (h0.eventually (gt_mem_nhds hε₁pos))
  have hE2 : ∀ᶠ γ in 𝓝[Ici β] β, γ ∈ Ico β (β + η) := Ico_mem_nhdsGE (by linarith)
  -- strong continuity of the cut-off at `β`
  have hE3 : ∀ᶠ γ in 𝓝[Ici β] β, ‖cut T β y - cut T γ y‖ < r₂ := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 ((continuous_cut_apply T y).tendsto β)
    refine (this.eventually (gt_mem_nhds hr₂pos)).filter_mono nhdsWithin_le_nhds |>.mono ?_
    intro γ hγ
    rwa [norm_sub_rev]
  have hE0 : ∀ᶠ γ in 𝓝[Ici β] β, γ ∈ Ico β T := Ico_mem_nhdsGE hβ.2
  filter_upwards [hE0, hE1, hE2, hE3] with γ h0 h1 h2 h3
  have hγβ : 0 ≤ γ - β := by linarith [h0.1]
  have hγ' : γ ∈ Icc β T := ⟨h0.1, h0.2.le⟩
  rw [key γ hγ', smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hγβ]
  set w := sys.ιWV (sys.L γ (hs γ))
  -- the three error terms
  have hw : ‖w - (γ - β) • sys.B u₀‖ ≤ (γ - β) * ε₁ :=
    norm_L_step_sub_le hH1 hT hβ.1 h0.1 h0.2.le u₀ (coeFn_step hβ.1 h0.1 u₀)
      fun σ hσ => (hηb σ (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hσ.1]; linarith [hσ.2, h2.2])).le
  have hpγ : ‖p γ‖ ≤ D := by
    have := norm_le_norm_add_norm_sub' (p γ) (p β)
    have h1' : ‖p γ - p β‖ < 1 := h1.trans_le (min_le_left _ _)
    rw [hD]; linarith [norm_sub_rev (p γ) (p β)]
  have hpdiff : ‖p γ - p β‖ * ‖sys.B u₀‖ ≤ c / 3 := by
    have h1' : ‖p γ - p β‖ ≤ c / (3 * (‖sys.B u₀‖ + 1)) := (h1.trans_le (min_le_right _ _)).le
    calc ‖p γ - p β‖ * ‖sys.B u₀‖ ≤ c / (3 * (‖sys.B u₀‖ + 1)) * (‖sys.B u₀‖ + 1) :=
          mul_le_mul h1' (by linarith) (norm_nonneg _) (by positivity)
      _ = c / 3 := by field_simp
  have hEb : ‖E γ‖ ≤ K * ‖u₀‖ * (γ - β) := hKb u₀ hβ.1 h0.1
  have hyE : |⟪y, E γ⟫_ℝ| ≤ c / 3 * (γ - β) := by
    have hproj : ⟪y, E γ⟫_ℝ = ⟪cut T β y - cut T γ y, E γ⟫_ℝ :=
      inner_cut_sub_cut hβ.1 h0.1 y _
    rw [hproj]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖cut T β y - cut T γ y‖ * ‖E γ‖ ≤ r₂ * (K * ‖u₀‖ * (γ - β)) :=
          mul_le_mul h3.le hEb (norm_nonneg _) hr₂pos.le
      _ ≤ c / (3 * (K * ‖u₀‖ + 1)) * ((K * ‖u₀‖ + 1) * (γ - β)) := by
          rw [hr₂]
          exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = c / 3 * (γ - β) := by field_simp
  have hsplit : ⟪p γ, w⟫_ℝ + ⟪y, E γ⟫_ℝ - (γ - β) * ⟪p β, sys.B u₀⟫_ℝ =
      ⟪p γ, w - (γ - β) • sys.B u₀⟫_ℝ + (γ - β) * ⟪p γ - p β, sys.B u₀⟫_ℝ + ⟪y, E γ⟫_ℝ := by
    simp only [inner_sub_right, real_inner_smul_right, inner_sub_left]
    ring
  have hshow : ⟪p β, sys.B u₀⟫_ℝ = ⟪((sys.tailA T β)†) z + ((sys.tailC T β)†) y,
      sys.B u₀⟫_ℝ := rfl
  rw [← hshow, hsplit]
  have t1 : |⟪p γ, w - (γ - β) • sys.B u₀⟫_ℝ| ≤ c / 3 * (γ - β) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖p γ‖ * ‖w - (γ - β) • sys.B u₀‖ ≤ D * ((γ - β) * ε₁) :=
          mul_le_mul hpγ hw (norm_nonneg _) hDpos.le
      _ = c / 3 * (γ - β) := by rw [hε₁]; field_simp
  have t2 : |(γ - β) * ⟪p γ - p β, sys.B u₀⟫_ℝ| ≤ c / 3 * (γ - β) := by
    rw [abs_mul, abs_of_nonneg hγβ, mul_comm (c / 3)]
    exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans hpdiff) hγβ
  calc |⟪p γ, w - (γ - β) • sys.B u₀⟫_ℝ + (γ - β) * ⟪p γ - p β, sys.B u₀⟫_ℝ + ⟪y, E γ⟫_ℝ|
      ≤ |⟪p γ, w - (γ - β) • sys.B u₀⟫_ℝ| + |(γ - β) * ⟪p γ - p β, sys.B u₀⟫_ℝ| +
          |⟪y, E γ⟫_ℝ| := abs_add_three _ _ _
    _ ≤ c / 3 * (γ - β) + c / 3 * (γ - β) + c / 3 * (γ - β) := by linarith
    _ = c * (γ - β) := by ring

/-- **The adjoint of the input map** (`R5`; replaces Pritchard–Salamon, Lemma 2.5): for
`z ∈ V` and `y ∈ L²(0, T; Y)`,
`((ιWV ∘ L_T)† z + 𝓕_T† y)(t) = B† ((S_V(T - t))† z + c_t† y)` for a.e. `t ∈ (0, T)`. -/
theorem coeFn_adjoint_input {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) (z : V)
    (y : L2 Y T) :
    ⇑(((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y) =ᵐ[μI T]
      fun t => (sys.B†) (((sys.tailA T t)†) z + ((sys.tailC T t)†) y) := by
  set lam := ((sys.ιWV ∘L sys.Lop T)†) z + ((sys.𝓕 T)†) y with hlam
  set p : ℝ → V := fun t => ((sys.tailA T t)†) z + ((sys.tailC T t)†) y with hp
  have hpc : Continuous p := continuous_costate T z y
  set ψ : ℝ → U := fun t => (sys.B†) (p t) with hψ
  have hψc : Continuous ψ := (sys.B†).continuous.comp hpc
  -- Step 3: the fundamental theorem of calculus along the needle
  have hFTC : ∀ u₀ : U, ∀ β ∈ Icc 0 T,
      ⟪lam, cut T 0 (constL2 T u₀) - cut T β (constL2 T u₀)⟫_ℝ =
        ∫ t in (0 : ℝ)..β, ⟪p t, sys.B u₀⟫_ℝ := by
    intro u₀
    have hgc : Continuous fun t => ⟪p t, sys.B u₀⟫_ℝ := hpc.inner continuous_const
    set F : ℝ → ℝ := fun β => ⟪lam, cut T 0 (constL2 T u₀) - cut T β (constL2 T u₀)⟫_ℝ -
      ∫ t in (0 : ℝ)..β, ⟪p t, sys.B u₀⟫_ℝ with hF
    have hcont : ContinuousOn F (Icc 0 T) := by
      refine (Continuous.sub ?_ ?_).continuousOn
      · exact continuous_const.inner (continuous_const.sub (continuous_cut_apply T _))
      · exact intervalIntegral.continuous_primitive (fun a b => hgc.intervalIntegrable a b) 0
    have hder : ∀ β ∈ Ico 0 T, HasDerivWithinAt F 0 (Ici β) β := by
      intro β hβ
      have h1 := hasDerivWithinAt_needle hH1 hH2 hT z y u₀ hβ
      have h2 := (hgc.integral_hasStrictDerivAt 0 β).hasDerivAt.hasDerivWithinAt (s := Ici β)
      have := h1.sub h2
      rwa [sub_self] at this
    intro β hβ
    have h := constant_of_has_deriv_right_zero hcont hder β hβ
    simp only [hF, sub_self, inner_zero_right, intervalIntegral.integral_same] at h
    linarith
  -- Step 4: vanishing integrals over `(0, β]`, then Lebesgue differentiation
  have hlamI : IntegrableOn (⇑lam) (Ioc 0 T) := (Lp.memLp lam).integrable one_le_two
  have hψI : IntegrableOn ψ (Ioc 0 T) := hψc.integrableOn_Ioc
  have hint : ∀ β ∈ Icc 0 T, ∫ t in Ioc 0 β, (lam t - ψ t) = 0 := by
    intro β hβ
    have hlβ : IntegrableOn (⇑lam) (Ioc 0 β) := hlamI.mono_set (Ioc_subset_Ioc_right hβ.2)
    have hψβ : IntegrableOn ψ (Ioc 0 β) := hψc.integrableOn_Ioc
    refine ext_inner_right ℝ fun u₀ => ?_
    rw [inner_zero_left, real_inner_comm,
      ← integral_inner (f := fun t => lam t - ψ t) (hlβ.sub hψβ) u₀]
    have e1 : (fun t => ⟪u₀, lam t - ψ t⟫_ℝ) =
        fun t => ⟪lam t, u₀⟫_ℝ - ⟪p t, sys.B u₀⟫_ℝ := by
      funext t
      rw [real_inner_comm, inner_sub_left, hψ, ContinuousLinearMap.adjoint_inner_left]
    rw [e1, integral_sub (hlβ.inner_const u₀)
      ((hpc.inner continuous_const).integrableOn_Ioc), ← inner_step hβ lam u₀, hFTC u₀ β hβ,
      intervalIntegral.integral_of_le hβ.1, sub_self]
  have h0 := ae_eq_zero_of_integral_Ioc (hlamI.sub hψI) hint
  filter_upwards [h0] with t ht
  exact sub_eq_zero.1 ht

end System

end DataDrivenControl
