module

public import DataDrivenControl.LQR.ModelBased
public import DataDrivenControl.FundamentalLemma.Willems

/-!
# The data-driven regulator

Paper: `eq:lqr-cost-traj`, `eq:lqr-admissible`, `eq:lqr-data-problem`, `thm:lqr-data`
(`app:lqr-data`).

## Main declarations

* `Traj U W Y = (ℝ → U) × (ℝ → W) × (ℝ → Y)`: candidate trajectories `(u, x, y)`;
  `TrajEquiv T p q`: equality as elements of `L²(I; U) × C(I; W) × L²(I; Y)` (inputs and outputs
  a.e. on `(0, T]`, states on `[0, T]`), the sense in which the minimiser is unique.
* `System.trajCost wts T p`: the trajectory cost `𝒥(u, x, y)` of `eq:lqr-cost-traj`.
* `System.dataAdmissible T 𝒢 x₀`: the data-compatible trajectories `𝒯_𝒢(x₀)` of
  `eq:lqr-admissible`, for a bounded operator `𝒢` on `U × W × V₋₁ × Y` (the record Gramian
  `sys.recordGramian T x̄₀ ū xd`).  The problem `eq:lqr-data-problem` is
  `IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T 𝒢 x₀)`.
* `System.lqr_data`: `thm:lqr-data`, first part (only `hyp:H1`).
* `System.mem_dataAdmissible_mildW`, `System.eq_mildW_of_mem_dataAdmissible`: the map
  `Λ u = (u, x(·; x₀, u), C x(·; x₀, u))` of `app:lqr-data` lands in `𝒯_𝒢(x₀)`, and every element
  of `𝒯_𝒢(x₀)` is `Λ` of its input (`thm:willems-gramian`); `System.trajCost_eq_lqrCost`
  (`𝒥 ∘ Λ = J(·; x₀)`); `System.isMinOn_lqrCost_of_isMinOn_trajCost`.
* `System.lqr_data_riccati`: `thm:lqr-data`, second part, from a `RiccatiSolution`
  (the conclusion of `thm:lqr-riccati`); `System.lqr_data_riccati_of_riccatiTheorem`: the same
  under `hyp:H2`, `hyp:compat` and `RiccatiTheorem`, as in the paper.  Since the theorem is now
  proved, `System.lqr_data_riccati_of_H1_H2` (`LQR/RiccatiExistence`) gives the second part
  under `hyp:H1` and `hyp:H2` alone.

## Upstream results used

`System.willems_tfae`, `System.eq_mild_of_trajectory`, `System.hasWeakDeriv_mildW`
(`FundamentalLemma/Willems`); `System.existsUnique_isMinOn_lqrCost`, `System.lqrCost_congr_ae`,
`RiccatiSolution.optimal` (`LQR/ModelBased`); `System.continuousOn_mildW`,
`System.mildW_congr_ae` (`System/Mild`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

/-- Candidate trajectories `(u, x, y)`: input, `W`-valued state and output, as functions. -/
abbrev Traj (U W Y : Type*) : Type _ := (ℝ → U) × (ℝ → W) × (ℝ → Y)

/-- Two trajectories are equal as elements of `L²(I; U) × C(I; W) × L²(I; Y)`: inputs and
outputs agree a.e. on `(0, T]`, states agree on `[0, T]`. -/
def TrajEquiv {U W Y : Type*} (T : ℝ) (p q : Traj U W Y) : Prop :=
  p.1 =ᵐ[μI T] q.1 ∧ EqOn p.2.1 q.2.1 (Icc 0 T) ∧ p.2.2 =ᵐ[μI T] q.2.2

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-- The **trajectory cost** (`eq:lqr-cost-traj`)
`𝒥(u, x, y) = ⟨x(T), G x(T)⟩_{V,V'} + ∫₀ᵀ (‖y(t)‖² + ⟨u(t), R u(t)⟩) dt`. -/
def trajCost (wts : LQRWeights U V) (T : ℝ) (p : Traj U W Y) : ℝ :=
  wts.G (sys.ιWV (p.2.1 T)) (sys.ιWV (p.2.1 T)) +
    ∫ t in Ioc 0 T, (‖p.2.2 t‖ ^ 2 + ⟪p.1 t, wts.R (p.1 t)⟫_ℝ)

/-- The **data-compatible trajectories** `𝒯_𝒢(x₀)` (`eq:lqr-admissible`): `u ∈ L²(I; U)`,
`y ∈ L²(I; Y)`, `x ∈ C(I; W) ∩ H¹(I; V₋₁)` with `x(0) = x₀`, and
`(u, x, ẋ, y)(t) ∈ (ker 𝒢)ᗮ` for a.e. `t ∈ I`, where `ẋ` is the weak derivative of `x` in
`V₋₁`. -/
def dataAdmissible (T : ℝ) (G : sys.GraphSpace →L[ℝ] sys.GraphSpace) (x₀ : W) :
    Set (Traj U W Y) :=
  {p | MemLp p.1 2 (μI T) ∧ MemLp p.2.2 2 (μI T) ∧ ContinuousOn p.2.1 (Icc 0 T) ∧
    p.2.1 0 = x₀ ∧
    ∃ xd : ℝ → sys.SV.Extrap, HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (p.2.1 t))) xd ∧
      ∀ᵐ t ∂(μI T), GraphSpace.mk (p.1 t) (p.2.1 t) (xd t) (p.2.2 t) ∈ G.kerᗮ}

variable {sys}

/-! ### The data-compatible trajectories are the mild trajectories -/

/-- Causality on `[0, T]`: an input class on `(0, T]` determines the mild state at every
`t ≤ T`. -/
theorem mildW_congr_ae_of_le {T t : ℝ} {u v : ℝ → U} (h : u =ᵐ[μI T] v) (ht : t ≤ T) (x₀ : W) :
    sys.mildW x₀ u t = sys.mildW x₀ v t :=
  mildW_congr_ae (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht) le_rfl) h) x₀

/-- Along a mild trajectory the trajectory cost `eq:lqr-cost-traj` is the model-based cost
`eq:lqr-cost` (`𝒥(Λ u) = J(u; x₀)` in `app:lqr-data`). -/
theorem trajCost_eq_lqrCost {T : ℝ} (hT : 0 ≤ T) (wts : LQRWeights U V) {x₀ : W}
    {q : Traj U W Y} (hx : EqOn q.2.1 (sys.mildW x₀ q.1) (Icc 0 T))
    (hy : q.2.2 =ᵐ[μI T] sys.outputW x₀ q.1) :
    sys.trajCost wts T q = sys.lqrCost wts T x₀ q.1 := by
  unfold trajCost lqrCost
  rw [hx ⟨hT, le_rfl⟩]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hy] with t ht
  rw [ht, outputW]

/-- The mild trajectory `Λ u = (u, x(·; x₀, u), C x(·; x₀, u))` is data compatible
(`thm:willems-gramian`, (i) ⇒ (ii); `app:lqr-data`). -/
theorem mem_dataAdmissible_mildW {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {w₀ : W} {ū : ℝ → U}
    (hū : MemLp ū 2 (μI T)) {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) (x₀ : W) {u : ℝ → U} (hu : MemLp u 2 (μI T)) :
    ((u, sys.mildW x₀ u, sys.outputW x₀ u) : Traj U W Y) ∈
      sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ := by
  have hxc := continuousOn_mildW hH1 hT hu x₀
  have hy : MemLp (sys.outputW x₀ u) 2 (μI T) :=
    memLp_μI_of_continuousOn (sys.C.continuous.comp_continuousOn hxc)
  have hxd' := hasWeakDeriv_mildW hH1 hT hu (w₀ := x₀)
  refine ⟨hu, hy, hxc, mildW_zero_time _ _, _, hxd', ?_⟩
  have h1 : (∀ᵐ t ∂(μI T), sys.vecField (u t) (sys.mildW x₀ u t) =
      sys.vecField (u t) (sys.mildW x₀ u t)) ∧
      (∀ᵐ t ∂(μI T), sys.outputW x₀ u t = sys.C (sys.mildW x₀ u t)) :=
    ⟨Eventually.of_forall fun _ => rfl, Eventually.of_forall fun _ => rfl⟩
  exact ((willems_tfae hH1 hT hū hxd hinf hu hxc hxd' hy).out 1 2).1 h1

/-- Every data-compatible trajectory is the mild trajectory generated by `x₀` and its input
(`thm:willems-gramian`, (ii) ⇒ (i) and its last sentence; `app:lqr-data`). -/
theorem eq_mildW_of_mem_dataAdmissible {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {w₀ : W}
    {ū : ℝ → U} (hū : MemLp ū 2 (μI T)) {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) {x₀ : W} {q : Traj U W Y}
    (hq : q ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀) :
    EqOn q.2.1 (sys.mildW x₀ q.1) (Icc 0 T) ∧ q.2.2 =ᵐ[μI T] sys.outputW x₀ q.1 := by
  obtain ⟨hu, hy, hxc, hx0, xd', hxd', hG⟩ := hq
  obtain ⟨hdyn, hout⟩ := ((willems_tfae hH1 hT hū hxd hinf hu hxc hxd' hy).out 2 1).1 hG
  have h := eq_mild_of_trajectory hH1 hT hu hxc hxd' hdyn hout
  rwa [hx0] at h

/-- The input of a minimiser of the data-driven problem minimises the model-based cost
`J(·; x₀)` over `L²(0, T; U)`. -/
theorem isMinOn_lqrCost_of_isMinOn_trajCost {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (wts : LQRWeights U V) {w₀ : W} {ū : ℝ → U} (hū : MemLp ū 2 (μI T))
    {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) {x₀ : W} {q : Traj U W Y}
    (hq : q ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀)
    (hmin : IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀)
      q) :
    IsMinOn (fun v : L2 U T => sys.lqrCost wts T x₀ v) univ (hq.1.toLp q.1) ∧
      sys.trajCost wts T q = sys.lqrCost wts T x₀ (hq.1.toLp q.1) := by
  obtain ⟨hx, hy⟩ := eq_mildW_of_mem_dataAdmissible hH1 hT hū hxd hinf hq
  have hq' : sys.trajCost wts T q = sys.lqrCost wts T x₀ (hq.1.toLp q.1) := by
    rw [trajCost_eq_lqrCost hT.le wts hx hy]
    exact lqrCost_congr_ae wts x₀ hq.1.coeFn_toLp.symm
  refine ⟨isMinOn_univ_iff.2 fun v => ?_, hq'⟩
  have hv := mem_dataAdmissible_mildW hH1 hT hū hxd hinf x₀ (Lp.memLp v)
  rw [← hq', ← trajCost_eq_lqrCost (q := ((⇑v, sys.mildW x₀ v, sys.outputW x₀ v) : Traj U W Y))
    hT.le wts (fun _ _ => rfl) (ae_eq_refl _)]
  exact isMinOn_iff.1 hmin _ hv

/-- **Data-driven LQR** (`thm:lqr-data`, first part; the problem is `eq:lqr-data-problem`).
Under `hyp:H1`, let `(x̄, ȳ)` be the mild solution generated by `(x̄₀, ū)` with `x̄₀ ∈ W`, `ẋ̄` a
weak derivative of `x̄` in `V₋₁`, and suppose `(ū, x̄)` is informative in `U × W`; let
`𝒢 = 𝒢(ū, x̄, ẋ̄, ȳ)`.  Then for every `x₀ ∈ W` the data-driven problem has a minimiser
`(u⋆, x⋆, y⋆)` over `𝒯_𝒢(x₀)`, unique in `L²(I; U) × C(I; W) × L²(I; Y)`; `u⋆` minimises the
model-based cost `J(·; x₀)` of `eq:lqr-cost` over `L²(I; U)` (so it is its unique minimiser,
`existsUnique_isMinOn_lqrCost`), and `(x⋆, y⋆)` is its mild solution. -/
theorem lqr_data {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (wts : LQRWeights U V) {w₀ : W}
    {ū : ℝ → U} (hū : MemLp ū 2 (μI T)) {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) (x₀ : W) :
    ∃ p, p ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ ∧
      IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀) p ∧
      (∀ q, q ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ →
        IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀) q →
        TrajEquiv T q p) ∧
      (∀ v : L2 U T, sys.lqrCost wts T x₀ p.1 ≤ sys.lqrCost wts T x₀ v) ∧
      EqOn p.2.1 (sys.mildW x₀ p.1) (Icc 0 T) ∧ p.2.2 =ᵐ[μI T] sys.outputW x₀ p.1 := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_isMinOn_lqrCost hH1 hT wts x₀
  set A := sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ with hA
  refine ⟨((⇑u, sys.mildW x₀ u, sys.outputW x₀ u) : Traj U W Y),
    mem_dataAdmissible_mildW hH1 hT hū hxd hinf x₀ (Lp.memLp u), ?_, ?_,
    isMinOn_univ_iff.1 hu, fun _ _ => rfl, ae_eq_refl _⟩
  · refine isMinOn_iff.2 fun q hq => ?_
    obtain ⟨hx, hy⟩ := eq_mildW_of_mem_dataAdmissible hH1 hT hū hxd hinf hq
    rw [trajCost_eq_lqrCost hT.le wts (fun _ _ => rfl) (ae_eq_refl _),
      trajCost_eq_lqrCost hT.le wts hx hy,
      lqrCost_congr_ae wts x₀ (u := q.1) hq.1.coeFn_toLp.symm]
    exact isMinOn_univ_iff.1 hu _
  · intro q hq hmin
    have hqu : hq.1.toLp q.1 = u :=
      huniq _ (isMinOn_lqrCost_of_isMinOn_trajCost hH1 hT wts hū hxd hinf hq hmin).1
    have hae : q.1 =ᵐ[μI T] u := by
      rw [← hqu]; exact hq.1.coeFn_toLp.symm
    obtain ⟨hx, hy⟩ := eq_mildW_of_mem_dataAdmissible hH1 hT hū hxd hinf hq
    refine ⟨hae, fun t ht => ?_, ?_⟩
    · rw [hx ht]; exact mildW_congr_ae_of_le hae ht.2 x₀
    · filter_upwards [hy, ae_restrict_mem measurableSet_Ioc] with t h1 h2
      rw [h1]
      simp only [outputW, mildW_congr_ae_of_le hae h2.2 x₀]

/-- **Data-driven LQR recovers the Riccati feedback** (`thm:lqr-data`, second part), with
`thm:lqr-riccati` entering as a `RiccatiSolution`: every minimiser `(u⋆, x⋆, y⋆)` of the
data-driven problem satisfies `u⋆(t) = -R⁻¹ B^⋆ P(t) x⋆(t)` for a.e. `t ∈ I`, and the minimal
value is `⟨x₀, P(0) x₀⟩_{V,V'}`.  The paper assumes `hyp:H2` and `hyp:compat` here; they enter
only through `thm:lqr-riccati`, i.e. through `ric` (see `lqr_data_riccati_of_riccatiTheorem`). -/
theorem lqr_data_riccati {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (wts : LQRWeights U V)
    {w₀ : W} {ū : ℝ → U} (hū : MemLp ū 2 (μI T)) {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) (ric : sys.RiccatiSolution wts T) (x₀ : W)
    {p : Traj U W Y} (hp : p ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀)
    (hmin : IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀)
      p) :
    (∀ᵐ t ∂(μI T), p.1 t = -wts.Rinv (sys.bStarP (ric.P t) (p.2.1 t))) ∧
      sys.trajCost wts T p = ric.P 0 (sys.ιWV x₀) (sys.ιWV x₀) := by
  obtain ⟨u, humin, hfb, hval⟩ := ric.optimal x₀
  obtain ⟨hmin', hcost⟩ := isMinOn_lqrCost_of_isMinOn_trajCost hH1 hT wts hū hxd hinf hp hmin
  have hpu : hp.1.toLp p.1 = u :=
    (existsUnique_isMinOn_lqrCost hH1 hT wts x₀).unique hmin' humin
  have hae : p.1 =ᵐ[μI T] u := by
    rw [← hpu]; exact hp.1.coeFn_toLp.symm
  obtain ⟨hx, -⟩ := eq_mildW_of_mem_dataAdmissible hH1 hT hū hxd hinf hp
  refine ⟨?_, by rw [hcost, hpu, hval]⟩
  filter_upwards [hae, hfb, ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3
  rw [h1, h2, hx (Ioc_subset_Icc_self h3), mildW_congr_ae_of_le hae h3.2 x₀]

/-- `thm:lqr-data`, second part, with the paper's hypotheses: under `hyp:H1`, `hyp:H2`,
`hyp:compat` and the cited `thm:lqr-riccati` (`RiccatiTheorem`), there is a Riccati operator `P`
such that every minimiser of the data-driven problem is the feedback
`u⋆(t) = -R⁻¹ B^⋆ P(t) x⋆(t)` with minimal value `⟨x₀, P(0) x₀⟩_{V,V'}`. -/
theorem lqr_data_riccati_of_riccatiTheorem {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T)
    (hc : sys.Compat) (hT : 0 < T) (wts : LQRWeights U V) (hric : sys.RiccatiTheorem wts T)
    {w₀ : W} {ū : ℝ → U} (hū : MemLp ū 2 (μI T)) {xd : ℝ → sys.SV.Extrap}
    (hxd : HasWeakDeriv T (fun t => sys.SV.toExtrap (sys.ιWV (sys.mildW w₀ ū t))) xd)
    (hinf : Informative T ū (sys.mildW w₀ ū)) (x₀ : W) :
    ∃ ric : sys.RiccatiSolution wts T, ∀ p : Traj U W Y,
      p ∈ sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀ →
      IsMinOn (sys.trajCost wts T) (sys.dataAdmissible T (sys.recordGramian T w₀ ū xd) x₀) p →
      (∀ᵐ t ∂(μI T), p.1 t = -wts.Rinv (sys.bStarP (ric.P t) (p.2.1 t))) ∧
        sys.trajCost wts T p = ric.P 0 (sys.ιWV x₀) (sys.ιWV x₀) := by
  obtain ⟨ric⟩ := hric hH1 hH2 hc
  exact ⟨ric, fun p hp hmin => lqr_data_riccati hH1 hT wts hū hxd hinf ric x₀ hp hmin⟩

end System

end DataDrivenControl
