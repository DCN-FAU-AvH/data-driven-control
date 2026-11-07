module

public import DataDrivenControl.Controllability.FattoriniHautus

/-!
# Fattorini–Hautus, step FH1: the unobservable subspace

Paper: `prop:fattorini-hautus` (cited from Boyer, Thm III.3.7; proved here).

## Main declarations (namespace `DataDrivenControl.FH`)

* `FH.unobs sys`: the closed subspace `N = ⋂_{τ > 0} ℛ_τ(0)^⊥ ⊆ X` of states that no input
  can detect at any horizon (`mem_unobs`, `isClosed_unobs`).
* `FH.mem_unobs_of_forall` (**FH1**): under `hyp:H1` and analyticity, `η ⊥ ℛ_{T'}(0)` for one
  `T' > 0` already gives `η ∈ N`.  Proof: `ψ(r) = B† S(r)† η` vanishes a.e. on `(0, T')`
  (duality `adjoint_Lop_ae_eq` at the smoothed `S(δ)† η ∈ D(A†)`), hence on `(0, ∞)` by
  real analyticity of `r ↦ B† S(δ)† S(r)† η` (`exists_clm_bstarExt`); pairing with `L_τ u`
  through `S(ε)† η` and letting `ε ↓ 0` gives `η ⊥ ℛ_τ(0)` for every `τ`.
* `FH.adjoint_real_mem_unobs`: `N` is invariant under `S(t)†` (`S(t) ℛ_τ ⊆ ℛ_{τ+t}`,
  `FH.SX_ιW_L`); `FH.adjoint_resolvent_mem_unobs`: hence under `R(μ, A)†` for real `μ` beyond
  the growth bound (Laplace transform).
* `FH.bstar_eq_zero_of_mem_unobs`: if `a ∈ D(A†)` and `a, A† a ∈ N`, then `B† a = 0`
  (`eq:weak-mild-diff` with `x₀ = 0` and a constant input).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal

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

/-- The **unobservable subspace** `N = ⋂_{τ > 0} ℛ_τ(0)^⊥ ⊆ X` (`prop:fattorini-hautus`, proof):
the states orthogonal to every reachable set from `0`. -/
def unobs (sys : System U W X V Y) : Submodule ℝ X where
  carrier := {η | ∀ τ : ℝ, 0 < τ → ∀ u : L2 U τ, ⟪η, sys.ιW (sys.Lop τ u)⟫_ℝ = 0}
  add_mem' {a b} ha hb τ hτ u := by rw [inner_add_left, ha τ hτ u, hb τ hτ u, add_zero]
  zero_mem' _ _ _ := inner_zero_left _
  smul_mem' c a ha τ hτ u := by rw [real_inner_smul_left, ha τ hτ u, mul_zero]

open scoped Classical in
/-- `B† : D(A†) → U` (`System.Bstar`), extended by `0` outside `D(A†)`. -/
def bstarExt (sys : System U W X V Y) (x : X) : U :=
  if hx : x ∈ sys.A.adjoint.domain then sys.Bstar ⟨x, hx⟩ else 0

variable {sys : System U W X V Y}

/-- Membership in `N`: `η ⊥ L_τ u` for every `τ > 0` and `u ∈ L²(0, τ; U)`. -/
theorem mem_unobs {η : X} :
    η ∈ unobs sys ↔ ∀ τ : ℝ, 0 < τ → ∀ u : L2 U τ, ⟪η, sys.ιW (sys.Lop τ u)⟫_ℝ = 0 :=
  Iff.rfl

/-- `N` is closed. -/
theorem isClosed_unobs : IsClosed (unobs sys : Set X) := by
  have : (unobs sys : Set X) = ⋂ τ : ℝ, ⋂ (_ : 0 < τ), ⋂ u : L2 U τ,
      {η | ⟪η, sys.ιW (sys.Lop τ u)⟫_ℝ = 0} := by
    ext η
    simp only [SetLike.mem_coe, mem_unobs, mem_iInter, mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun τ => isClosed_iInter fun _ => isClosed_iInter fun u =>
    isClosed_eq (continuous_id.inner continuous_const) continuous_const

/-- `bstarExt` is `B†` on `D(A†)`. -/
theorem bstarExt_eq {x : X} (hx : x ∈ sys.A.adjoint.domain) :
    bstarExt sys x = sys.Bstar ⟨x, hx⟩ := by
  rw [bstarExt, dite_eq_left hx]

/-- Under `hyp:H1`, `η ∈ N` annihilates `L_τ u` for every square-integrable input and every
`τ`. -/
theorem inner_L_eq_zero {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {η : X} (hη : η ∈ unobs sys)
    {τ : ℝ} {u : ℝ → U} (hu : MemLp u 2 (μI τ)) : ⟪η, sys.ιW (sys.L τ u)⟫_ℝ = 0 := by
  rcases le_or_gt τ 0 with hτ | hτ
  · rw [L_of_nonpos hτ, map_zero, inner_zero_right]
  · have := hη τ hτ (hu.toLp u)
    rwa [Lop_apply hH1 hT, L_congr_ae hu.coeFn_toLp] at this

/-- `L_t 0 = 0`. -/
theorem L_zero (t : ℝ) : sys.L t (0 : ℝ → U) = 0 :=
  L_eq_of_ιWV (by simp [convV])

/-- **`S(t) ℛ_τ(0) ⊆ ℛ_{τ+t}(0)`**: `S(t) L_τ u = L_{τ+t} ũ`, with `ũ` the input `u` on
`(0, τ]` followed by `0`. -/
theorem SX_ιW_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t)
    {u : ℝ → U} (hu : MemLp u 2 (μI τ)) :
    sys.SX.real t (sys.ιW (sys.L τ u)) = sys.ιW (sys.L (τ + t) ((Ioc 0 τ).indicator u)) := by
  have hu' : MemLp ((Ioc 0 τ).indicator u) 2 (μI (τ + t)) := (memLp_indicator_Ioc hu).restrict _
  rw [L_add_time hH1 hT hτ ht hu', map_add, ιW_SW]
  have h1 : sys.L τ ((Ioc 0 τ).indicator u) = sys.L τ u := by
    refine L_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [indicator_of_mem hr]
  have h2 : sys.L t (fun r => (Ioc 0 τ).indicator u (τ + r)) = 0 := by
    have : (fun r => (Ioc 0 τ).indicator u (τ + r)) =ᵐ[μI t] (0 : ℝ → U) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact indicator_of_notMem (fun h => by linarith [h.2, hr.1]) _
    rw [L_congr_ae this, L_zero]
  rw [h1, h2, map_zero, add_zero]

/-- **`N` is invariant under the adjoint semigroup**: `S(t)† N ⊆ N` for `t ≥ 0`. -/
theorem adjoint_real_mem_unobs {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {η : X}
    (hη : η ∈ unobs sys) {t : ℝ} (ht : 0 ≤ t) : sys.SX.adjoint.real t η ∈ unobs sys := by
  intro τ hτ u
  rw [C0Semigroup.inner_adjoint_real_apply, Lop_apply hH1 hT, SX_ιW_L hH1 hT hτ.le ht
    (Lp.memLp u)]
  exact inner_L_eq_zero hH1 hT hη ((memLp_indicator_Ioc (Lp.memLp u)).restrict _)

/-- **`N` is invariant under `R(μ, A)†`** for real `μ` beyond the growth bound of `S`
(`R(μ, A) = ∫₀^∞ e^{-μ t} S(t) dt`). -/
theorem adjoint_resolvent_mem_unobs {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {M ω : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (ω * t)) {μ : ℝ} (hμ : ω < μ) {η : X}
    (hη : η ∈ unobs sys) : ContinuousLinearMap.adjoint (resolvent sys.A μ) η ∈ unobs sys := by
  intro τ hτ u
  have hR := sys.SX.resolvent_eq_integral_real (𝕜 := ℝ) hS hμ (sys.ιW (sys.Lop τ u))
  have hint := sys.SX.integrableOn_exp_smul_real_apply (𝕜 := ℝ) hS (μ := μ) hμ
    (sys.ιW (sys.Lop τ u))
  rw [ContinuousLinearMap.adjoint_inner_left]
  erw [hR]
  rw [← integral_inner (𝕜 := ℝ) ?_ η]
  · refine (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_).trans (integral_zero _ _)
    rw [real_inner_smul_right, ← C0Semigroup.inner_adjoint_real_apply,
      adjoint_real_mem_unobs hH1 hT hη (le_of_lt ht) τ hτ u, mul_zero]
  · refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only
    congr 1
    rw [Real.exp_eq_exp_ℝ]
    simp

/-- **`B† a = 0` on `N`** (`eq:weak-mild-diff` at `x₀ = 0`): if `a ∈ D(A†)` and both `a` and
`A† a` lie in `N`, then `B† a = 0`.  With the constant input `v = B† a`,
`0 = ⟪a, L_1 v⟫ = ∫₀¹ (⟪A† a, L_s v⟫ + ⟪B† a, v⟫) ds = ‖B† a‖²`. -/
theorem bstar_eq_zero_of_mem_unobs {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {a : X}
    (ha : a ∈ sys.A.adjoint.domain) (haN : a ∈ unobs sys)
    (hAa : sys.A.adjoint ⟨a, ha⟩ ∈ unobs sys) : sys.Bstar ⟨a, ha⟩ = 0 := by
  set v := sys.Bstar ⟨a, ha⟩ with hv
  have hu : ∀ s : ℝ, MemLp (fun _ : ℝ => v) 2 (μI s) := fun s => memLp_const v
  have h := inner_mild_eq hH1 hT (hu 1) 0 ha 1 ⟨zero_le_one, le_rfl⟩
  rw [mild_zero_left, inner_L_eq_zero hH1 hT haN (hu 1), inner_zero_right, zero_add] at h
  have h2 : ∫ s in (0 : ℝ)..1, (⟪sys.A.adjoint ⟨a, ha⟩, sys.mild 0 (fun _ => v) s⟫_ℝ +
      ⟪v, v⟫_ℝ) = ⟪v, v⟫_ℝ := by
    rw [intervalIntegral.integral_congr (g := fun _ => ⟪v, v⟫_ℝ) fun s _ => by
      simp only
      rw [mild_zero_left, inner_L_eq_zero hH1 hT hAa (hu s), zero_add]]
    simp
  rw [h2] at h
  exact inner_self_eq_zero.1 h.symm

/-- For `ε > 0`, `x ↦ B† S(ε)† x` is a bounded operator `P_ε ∈ L(X, U)` (graph-norm bound of
`B†` and `A† S(ε)† = (A S(ε))†`, analyticity). -/
theorem exists_clm_bstarExt (hA : sys.SX.IsAnalytic) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[ℝ] U, ∀ x, P x = bstarExt sys (sys.SX.adjoint.real ε x) := by
  have hmem : ∀ x, sys.SX.adjoint.real ε x ∈ sys.A.adjoint.domain := fun x =>
    (hA.adjoint_real_mem_adjoint_domain hε x).1
  let f : X →ₗ[ℝ] U := sys.Bstar.toFun ∘ₗ
    ((sys.SX.adjoint.real ε : X →ₗ[ℝ] X).codRestrict sys.Bstar.domain hmem)
  have hf : ∀ x, f x = bstarExt sys (sys.SX.adjoint.real ε x) := fun x =>
    (bstarExt_eq (hmem x)).symm
  obtain ⟨c, hc0, hc⟩ := exists_norm_Bstar_le (sys := sys)
  refine ⟨f.mkContinuous (c * (‖sys.SX.real ε‖ + ‖hA.gen ε‖)) fun x => ?_, fun x => hf x⟩
  rw [hf, bstarExt_eq (hmem x)]
  refine (hc ⟨_, hmem x⟩).trans ?_
  obtain ⟨h1, h2⟩ := hA.adjoint_real_mem_adjoint_domain hε x
  have h2' : sys.A.adjoint ⟨_, hmem x⟩ = ContinuousLinearMap.adjoint (hA.gen ε) x := h2
  rw [h2']
  have n1 : ‖sys.SX.adjoint.real ε x‖ ≤ ‖sys.SX.real ε‖ * ‖x‖ := by
    rw [C0Semigroup.adjoint_real]
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  have n2 : ‖ContinuousLinearMap.adjoint (hA.gen ε) x‖ ≤ ‖hA.gen ε‖ * ‖x‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  calc c * (‖sys.SX.adjoint.real ε x‖ + ‖ContinuousLinearMap.adjoint (hA.gen ε) x‖)
      ≤ c * (‖sys.SX.real ε‖ * ‖x‖ + ‖hA.gen ε‖ * ‖x‖) := by gcongr
    _ = c * (‖sys.SX.real ε‖ + ‖hA.gen ε‖) * ‖x‖ := by ring

/-- `B† S(s)† S(δ)† η = B† S(δ + s)† η` (`s, δ ≥ 0`, `S(δ)† η ∈ D(A†)`). -/
theorem bstar_adjoint_real_adjoint_real {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) {η : X}
    (h : sys.SX.adjoint.real δ η ∈ sys.A.adjoint.domain) :
    sys.Bstar ⟨sys.SX.adjoint.real s (sys.SX.adjoint.real δ η),
      sys.SX.adjoint_real_mem_adjoint_domain h s⟩ =
      bstarExt sys (sys.SX.adjoint.real (δ + s) η) := by
  have e : sys.SX.adjoint.real (δ + s) η = sys.SX.adjoint.real s (sys.SX.adjoint.real δ η) := by
    rw [add_comm, sys.SX.adjoint.real_add_apply hs hδ]
  rw [e, bstarExt_eq]

/-- **FH1, the vanishing of `ψ`**: if `η ⊥ ℛ_{T'}(0)` and `0 < δ < T'`, then
`B† S(δ + s)† η = 0` for every `s > 0`. -/
theorem bstarExt_adjoint_eq_zero_aux {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) {T' : ℝ} {η : X}
    (hη : ∀ u : L2 U T', ⟪η, sys.ιW (sys.Lop T' u)⟫_ℝ = 0) {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T')
    {s : ℝ} (hs : 0 < s) : bstarExt sys (sys.SX.adjoint.real (δ + s) η) = 0 := by
  set ξ := sys.SX.adjoint.real δ η with hξdef
  have hξ : ξ ∈ sys.A.adjoint.domain := (hA.adjoint_real_mem_adjoint_domain hδ η).1
  set a := T' - δ with ha_def
  have ha : 0 < a := sub_pos.2 hδT
  -- (i) `ξ ⊥ ℛ_a(0)`
  have hi : ∀ v : L2 U a, ⟪ξ, sys.ιW (sys.Lop a v)⟫_ℝ = 0 := by
    intro v
    have hv' : MemLp ((Ioc 0 a).indicator v) 2 (μI T') := by
      have := (memLp_indicator_Ioc (Lp.memLp v)).restrict (Ioc 0 (a + δ))
      rwa [show a + δ = T' by rw [ha_def]; ring] at this
    rw [hξdef, C0Semigroup.inner_adjoint_real_apply, Lop_apply hH1 hT,
      SX_ιW_L hH1 hT ha.le hδ.le (Lp.memLp v), show a + δ = T' by rw [ha_def]; ring]
    have := hη (hv'.toLp _)
    rwa [Lop_apply hH1 hT, L_congr_ae hv'.coeFn_toLp] at this
  -- (ii) the adjoint of `ιW ∘ L_a` kills `ξ`
  set F := sys.ιW.comp (sys.Lop a)
  have hF : ContinuousLinearMap.adjoint F ξ = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ), ContinuousLinearMap.adjoint_inner_left]
    exact hi _
  -- (iii) duality: `B† S(a - r)† ξ = 0` for a.e. `r ∈ (0, a]`
  have hae := adjoint_Lop_ae_eq hH1 hT a hξ
  rw [hF] at hae
  -- (iv) the analytic function `g(s) = B† S(δ)† S(s)† η`
  obtain ⟨P, hP⟩ := exists_clm_bstarExt hA hδ
  set g : ℝ → U := fun s => P (sys.SX.adjoint.real s η) with hg
  have hgs : ∀ s : ℝ, 0 ≤ s → g s = bstarExt sys (sys.SX.adjoint.real (δ + s) η) := by
    intro s hs
    rw [hg]; simp only
    rw [hP, ← sys.SX.adjoint.real_add_apply hδ.le hs]
  have hgc : Continuous g := P.continuous.comp (sys.SX.adjoint.continuous_real_apply η)
  have hg0 : EqOn (fun r => g (a - r)) 0 (Ioo 0 a) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo
      (hgc.comp (continuous_const.sub continuous_id)).continuousOn continuousOn_const
    refine ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self ?_
    filter_upwards [hae, Lp.coeFn_zero U 2 (μI a), ae_restrict_mem measurableSet_Ioc]
      with r h1 h2 hr
    rw [h2] at h1
    have hr' : 0 ≤ a - r := sub_nonneg.2 hr.2
    simp only [Pi.zero_apply]
    rw [hgs _ hr', ← bstar_adjoint_real_adjoint_real hδ.le hr' hξ]
    exact h1.symm
  have hgan : AnalyticOnNhd ℝ g (Ioi 0) := fun s hs =>
    (P.analyticAt _).comp (hA.adjoint.analyticOnNhd η s hs)
  have hzero : EqOn g 0 (Ioi 0) := by
    refine hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
      (z₀ := a / 2) (half_pos ha) ?_
    filter_upwards [Ioo_mem_nhds (half_pos ha) (half_lt_self ha)] with r hr
    have := hg0 (show a - r ∈ Ioo 0 a from ⟨by linarith [hr.2], by linarith [hr.1]⟩)
    simpa using this
  rw [← hgs s hs.le]
  exact hzero hs

/-- **FH1, `ψ ≡ 0`**: if `η ⊥ ℛ_{T'}(0)` (`T' > 0`), then `B† S(σ)† η = 0` for every `σ > 0`. -/
theorem bstarExt_adjoint_eq_zero {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (hA : sys.SX.IsAnalytic) {T' : ℝ} (hT' : 0 < T') {η : X}
    (hη : ∀ u : L2 U T', ⟪η, sys.ιW (sys.Lop T' u)⟫_ℝ = 0) {σ : ℝ} (hσ : 0 < σ) :
    bstarExt sys (sys.SX.adjoint.real σ η) = 0 := by
  set δ := min σ T' / 2 with hδ
  have hm : 0 < min σ T' := lt_min hσ hT'
  have hδ0 : 0 < δ := half_pos hm
  have hδσ : δ < σ := (half_lt_self hm).trans_le (min_le_left _ _)
  have hδT : δ < T' := (half_lt_self hm).trans_le (min_le_right _ _)
  have := bstarExt_adjoint_eq_zero_aux hH1 hT hA hη hδ0 hδT (sub_pos.2 hδσ)
  rwa [add_sub_cancel] at this

/-- **FH1** (`prop:fattorini-hautus`, proof): under `hyp:H1` and analyticity, a state orthogonal
to `ℛ_{T'}(0)` for one `T' > 0` is orthogonal to `ℛ_τ(0)` for every `τ > 0`, i.e. lies in `N`.
-/
theorem mem_unobs_of_forall {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hA : sys.SX.IsAnalytic)
    {T' : ℝ} (hT' : 0 < T') {η : X}
    (hη : ∀ u : L2 U T', ⟪η, sys.ιW (sys.Lop T' u)⟫_ℝ = 0) : η ∈ unobs sys := by
  intro τ hτ u
  set y := sys.ιW (sys.Lop τ u) with hy
  -- `⟪S(ε)† η, y⟫ = 0` for `ε > 0`
  have hε : ∀ ε : ℝ, 0 < ε → ⟪sys.SX.adjoint.real ε η, y⟫_ℝ = 0 := by
    intro ε hε
    have hξ : sys.SX.adjoint.real ε η ∈ sys.A.adjoint.domain :=
      (hA.adjoint_real_mem_adjoint_domain hε η).1
    rw [hy, Lop_apply hH1 hT, inner_L_eq_integral hH1 hT (Lp.memLp u) hξ]
    refine (setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_).trans (integral_zero _ _)
    rw [bstar_adjoint_real_adjoint_real hε.le (sub_nonneg.2 hr.2) hξ,
      bstarExt_adjoint_eq_zero hH1 hT hA hT' hη (by linarith [hr.2]), inner_zero_left]
  have hc : Continuous fun ε : ℝ => ⟪sys.SX.adjoint.real ε η, y⟫_ℝ :=
    (sys.SX.adjoint.continuous_real_apply η).inner continuous_const
  have h1 : Tendsto (fun ε : ℝ => ⟪sys.SX.adjoint.real ε η, y⟫_ℝ) (𝓝[>] 0)
      (𝓝 ⟪sys.SX.adjoint.real 0 η, y⟫_ℝ) := hc.continuousWithinAt.tendsto
  have h0 : Tendsto (fun ε : ℝ => ⟪sys.SX.adjoint.real ε η, y⟫_ℝ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ε hε' => (hε ε hε').symm)
  have := tendsto_nhds_unique h1 h0
  simpa using this

end FH

end DataDrivenControl
