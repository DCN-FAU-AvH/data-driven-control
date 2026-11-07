module

public import DataDrivenControl.Examples.Delay.Solution
public import DataDrivenControl.Examples.Delay.Translation

/-!
# The delay semigroup and its generator

* `Delay.State h E = WithLp 2 (E × L²(0, h; E))`: the state space `X = ℝⁿ × L²(-h, 0; ℝⁿ)`, with
  the history on `(0, h]` (`ψ(s) = φ(s - h)`).
* `Equation.stateAt d v t = (x(t), x_t)` for the free solution from `v = (r, ψ)`
  (`Equation.orbit`, `Equation.trajOf`); linear in `v` (`stateAt_add`, `stateAt_smul`), bounded
  on `[0, τ]` (`norm_stateAt_le`, from the Grönwall bound `Equation.norm_sol_le`), continuous in
  `t` (`continuousOn_stateAt`: continuity of the solution and of translation in `L²`), with the
  semigroup law `stateAt_stateAt` (time shift and uniqueness, `Equation.sol_add_time`).
* `Equation.semigroup : C0Semigroup ℝ (State h E)` (`semigroup_apply`, `semigroup_real_apply`);
  growth bounds `exists_norm_semigroup_le`, `norm_semigroup_le`.
* **The generator** (`mem_generator_domain_iff`, `generator_apply`):
  `D(A) = {(g(h), g) : g ∈ H¹(0, h; E)}` and `A (g(h), g) = (L g, g')` with
  `L g = d.rhs g 0 = ∑ₖ Aₖ g(h - hₖ) + L_d g`.  The easy inclusion
  (`tendsto_diffQuot_of_hasWeakDeriv`) uses the regularity `Equation.hasWeakDeriv_traj` and the
  `L²` convergence of difference quotients of `H¹` signals (`tendsto_diffQuot_window`); the hard
  inclusion (`exists_hasWeakDeriv_of_mem_generator_domain`) passes from `L²` convergence of
  difference quotients to a weak derivative (`exists_ae_eq_of_tendsto_diffQuot_window`, test
  functions and du Bois-Reymond) and gets the endpoint `g(h) = x(0)` from the window at time
  `h / 2`, which straddles the history and the solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The **state space** `X = E × L²(-h, 0; E)` of the delay equation (`ex:intro-delay`), with the
history on `(0, h]` (`ψ(s) = φ(s - h)`) and the Hilbert product norm. -/
abbrev State (h : ℝ) (E : Type*) [NormedAddCommGroup E] : Type _ := WithLp 2 (E × L2 E h)

/-- `‖(a, b)‖ ≤ ‖a‖ + ‖b‖` in `WithLp 2 (E × F)`. -/
theorem norm_toLp_le {F : Type*} [NormedAddCommGroup F] (a : E) (b : F) :
    ‖WithLp.toLp 2 (a, b)‖ ≤ ‖a‖ + ‖b‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [← Real.sqrt_sq (add_nonneg (norm_nonneg a) (norm_nonneg b))]
  exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg a, norm_nonneg b])

/-- The window at `0` of an `L²` class is the class itself. -/
theorem window_coeFn_zero {T : ℝ} (w : L2 E T) : window T (⇑w) 0 = w := by
  have hm : MemLp (fun σ => (w : ℝ → E) (0 + σ)) 2 (μI T) := by
    simpa only [zero_add] using Lp.memLp w
  rw [window_eq_toLp hm]
  refine (MemLp.toLp_congr hm (Lp.memLp w) (ae_of_all _ fun σ => by simp only [zero_add])).trans ?_
  exact Lp.toLp_coeFn w (Lp.memLp w)

/-- A state is determined by its components. -/
theorem state_ext {h : ℝ} {v w : State h E} (h1 : v.fst = w.fst) (h2 : v.snd = w.snd) : v = w := by
  rw [WithLp.ext_iff]
  exact Prod.ext h1 h2

/-- Windows of a translate are translated windows. -/
theorem window_comp_add {T : ℝ} (f : ℝ → E) (s t : ℝ) :
    window T (fun σ => f (s + σ)) t = window T f (s + t) :=
  window_eq_of_ae (ae_of_all _ fun σ => by simp only [add_assoc])

/-- The window at `0` of a square-integrable signal is its class. -/
theorem window_zero_eq_toLp {T : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T)) :
    window T f 0 = hf.toLp f := by
  have hm : MemLp (fun σ => f (0 + σ)) 2 (μI T) := by simpa only [zero_add] using hf
  rw [window_eq_toLp hm]
  exact MemLp.toLp_congr hm hf (ae_of_all _ fun σ => by simp only [zero_add])

/-- Continuous functions on `[0, a]` that agree a.e. on `(0, a]` agree on `[0, a]`. -/
theorem eqOn_Icc_of_ae {F : Type*} [NormedAddCommGroup F] {u w : ℝ → F} {a : ℝ} (ha : 0 < a)
    (hu : ContinuousOn u (Icc 0 a)) (hw : ContinuousOn w (Icc 0 a))
    (h : ∀ᵐ σ ∂(μI a), u σ = w σ) : EqOn u w (Icc 0 a) := by
  have h' : u =ᵐ[volume.restrict (Icc 0 a)] w := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    exact h
  exact Measure.eqOn_of_ae_eq h' hu hw (by simp [interior_Icc, closure_Ioo ha.ne])

/-- Averages of a continuous function converge: `t⁻¹ ∫₀ᵗ G → G 0` as `t → 0⁺`. -/
theorem tendsto_inv_smul_intervalIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {G : ℝ → F} {δ : ℝ} (hδ : 0 < δ) (hG : ContinuousOn G (Icc 0 δ)) :
    Tendsto (fun t => t⁻¹ • ∫ s in (0 : ℝ)..t, G s) (𝓝[>] 0) (𝓝 (G 0)) := by
  have hd : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, G s) (G 0) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (by simp)
      ⟨Ioc 0 δ, mem_of_superset (Ioo_mem_nhdsGT hδ) Ioo_subset_Ioc_self,
        (hG.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc⟩
      ((hG 0 ⟨le_rfl, hδ.le⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT hδ) Ioo_subset_Icc_self))
  have e : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, e] at hd
  refine hd.congr fun t => ?_
  rw [slope_def_module, intervalIntegral.integral_same, sub_zero, sub_zero]

namespace Equation

variable {h : ℝ} (d : Equation h E)

/-- The free orbit `t ↦ x(t)` of the state `v = (r, ψ)`: the solution with initial value `v.fst`,
history (the representative of) `v.snd` and no forcing. -/
def orbit (v : State h E) : ℝ → E := d.sol v.fst (⇑v.snd) 0

/-- The trajectory (in shifted time) of the state `v`. -/
def trajOf (v : State h E) : ℝ → E := traj h (⇑v.snd) (d.orbit v)

/-- The state `(x(t), x_t)` reached at time `t` from `v`. -/
def stateAt (v : State h E) (t : ℝ) : State h E :=
  WithLp.toLp 2 (d.orbit v t, window h (d.trajOf v) t)

/-- The first component of `S(t) v` is `x(t)`. -/
@[simp] theorem stateAt_fst (v : State h E) (t : ℝ) : (d.stateAt v t).fst = d.orbit v t := rfl

/-- The second component of `S(t) v` is the history `x_t`. -/
@[simp] theorem stateAt_snd (v : State h E) (t : ℝ) :
    (d.stateAt v t).snd = window h (d.trajOf v) t := rfl

/-- The zero forcing is integrable. -/
theorem integrableOn_zero_forcing (τ : ℝ) : IntegrableOn (0 : ℝ → E) (Ioc 0 τ) :=
  integrableOn_zero

/-- The free solution is continuous on `[0, τ]`. -/
theorem continuousOn_orbit (v : State h E) (τ : ℝ) : ContinuousOn (d.orbit v) (Icc 0 τ) :=
  d.continuousOn_sol (Lp.memLp v.snd) (integrableOn_zero_forcing τ)

/-- The trajectory of a state is square integrable on `(0, h + τ]`. -/
theorem memLp_trajOf (v : State h E) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (d.trajOf v) 2 (μI (h + τ)) :=
  memLp_traj d.h_pos.le hτ (Lp.memLp v.snd) (d.continuousOn_orbit v τ)

/-- `t ↦ (x(t), x_t)` is continuous in `X` (continuity of translation in `L²`). -/
theorem continuousOn_stateAt (v : State h E) (τ : ℝ) : ContinuousOn (d.stateAt v) (Icc 0 τ) := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · rw [Icc_eq_empty (not_le.2 hτ)]
    exact continuousOn_empty _
  exact (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := L2 E h)).comp_continuousOn
    ((d.continuousOn_orbit v τ).prodMk (continuousOn_window (d.memLp_trajOf v hτ)))

/-- `S(0) v = v`. -/
theorem stateAt_zero (v : State h E) : d.stateAt v 0 = v := by
  refine state_ext ?_ ?_
  · simp [orbit]
  · rw [stateAt_snd, ← window_coeFn_zero v.snd]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      traj_of_le _ _ (by simpa using hσ.2))

/-- The free solution is additive in the state. -/
theorem orbit_add (v w : State h E) {t : ℝ} (ht : 0 ≤ t) :
    d.orbit (v + w) t = d.orbit v t + d.orbit w t := by
  have hz : ∀ τ, IntegrableOn (0 : ℝ → E) (Ioc 0 τ) := integrableOn_zero_forcing
  rw [orbit, WithLp.add_fst, WithLp.add_snd,
    d.sol_congr_hist (Lp.memLp _) (Lp.coeFn_add v.snd w.snd) hz ht,
    ← add_zero (0 : ℝ → E), d.sol_add (Lp.memLp v.snd) (Lp.memLp w.snd) hz hz ht]
  rfl

/-- The free solution is homogeneous in the state. -/
theorem orbit_smul (c : ℝ) (v : State h E) {t : ℝ} (ht : 0 ≤ t) :
    d.orbit (c • v) t = c • d.orbit v t := by
  have hz : ∀ τ, IntegrableOn (0 : ℝ → E) (Ioc 0 τ) := integrableOn_zero_forcing
  rw [orbit, WithLp.smul_fst, WithLp.smul_snd,
    d.sol_congr_hist (Lp.memLp _) (Lp.coeFn_smul c v.snd) hz ht,
    ← smul_zero c, d.sol_smul (Lp.memLp v.snd) hz c ht]
  · rfl

/-- `S(t)` is additive. -/
theorem stateAt_add (v w : State h E) {t : ℝ} (ht : 0 ≤ t) :
    d.stateAt (v + w) t = d.stateAt v t + d.stateAt w t := by
  refine state_ext ?_ ?_
  · simp only [stateAt_fst, WithLp.add_fst, d.orbit_add v w ht]
  · simp only [stateAt_snd, WithLp.add_snd]
    have he : d.trajOf (v + w) =ᵐ[μI (h + t)] d.trajOf v + d.trajOf w := by
      have h1 : d.trajOf (v + w) = traj h (⇑(v + w).snd) (d.orbit v + d.orbit w) :=
        traj_congr_right _ fun s hs => d.orbit_add v w hs
      rw [h1, trajOf, trajOf, ← traj_add]
      refine traj_ae_congr ?_ _ _
      rw [WithLp.add_snd]
      exact Lp.coeFn_add _ _
    rw [window_congr_ae he ht (by linarith), window_add_of_memLp
      (memLp_comp_add (d.memLp_trajOf v ht) ht (by linarith))
      (memLp_comp_add (d.memLp_trajOf w ht) ht (by linarith))]

/-- `S(t)` is homogeneous. -/
theorem stateAt_smul (c : ℝ) (v : State h E) {t : ℝ} (ht : 0 ≤ t) :
    d.stateAt (c • v) t = c • d.stateAt v t := by
  refine state_ext ?_ ?_
  · simp only [stateAt_fst, WithLp.smul_fst, d.orbit_smul c v ht]
  · simp only [stateAt_snd, WithLp.smul_snd]
    have he : d.trajOf (c • v) =ᵐ[μI (h + t)] c • d.trajOf v := by
      have h1 : d.trajOf (c • v) = traj h (⇑(c • v).snd) (c • d.orbit v) :=
        traj_congr_right _ fun s hs => d.orbit_smul c v hs
      rw [h1, trajOf, ← traj_smul]
      refine traj_ae_congr ?_ _ _
      rw [WithLp.smul_snd]
      exact Lp.coeFn_smul _ _
    rw [window_congr_ae he ht (by linarith), window_smul]

/-! ### Bounds and the semigroup law -/

/-- The history constant `Kψ τ` is nonnegative. -/
theorem Kψ_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ d.Kψ τ := by
  unfold Kψ
  positivity

/-- `‖x(t)‖ ≤ (1 + Kψ τ) e^{K τ} ‖v‖` on `[0, τ]`. -/
theorem norm_orbit_le (v : State h E) {τ t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖d.orbit v t‖ ≤ (1 + d.Kψ τ) * Real.exp (d.K * τ) * ‖v‖ := by
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  refine (d.norm_sol_le (Lp.memLp v.snd) (integrableOn_zero_forcing τ) ht).trans ?_
  simp only [Pi.zero_apply, norm_zero, integral_zero, add_zero]
  rw [← Lp.norm_def]
  have h1 := WithLp.norm_fst_le (x := v)
  have h2 := WithLp.norm_snd_le (x := v)
  have hK := d.Kψ_nonneg hτ
  have h3 : ‖v.fst‖ + d.Kψ τ * ‖v.snd‖ ≤ (1 + d.Kψ τ) * ‖v‖ := by nlinarith
  calc (‖v.fst‖ + d.Kψ τ * ‖v.snd‖) * Real.exp (d.K * τ)
      ≤ ((1 + d.Kψ τ) * ‖v‖) * Real.exp (d.K * τ) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- The bound `(1 + Kψ τ) e^{K τ} (1 + √h) + 1` of the solution operators on `[0, τ]`. -/
def opBound (τ : ℝ) : ℝ := (1 + d.Kψ τ) * Real.exp (d.K * τ) * (1 + √h) + 1

/-- `‖S(t) v‖ ≤ opBound τ ‖v‖` on `[0, τ]`. -/
theorem norm_stateAt_le (v : State h E) {τ t : ℝ} (ht : t ∈ Icc 0 τ) :
    ‖d.stateAt v t‖ ≤ d.opBound τ * ‖v‖ := by
  have hτ : 0 ≤ τ := ht.1.trans ht.2
  set M := (1 + d.Kψ τ) * Real.exp (d.K * τ) * ‖v‖ with hM
  have hM0 : 0 ≤ M := by
    have := d.Kψ_nonneg hτ
    positivity
  have h1 := d.norm_orbit_le v ht
  have h2 := norm_window_traj_le d.h_pos.le (Lp.memLp v.snd) ht.1 (d.continuousOn_orbit v t) hM0
    fun ρ hρ => d.norm_orbit_le v ⟨hρ.1, hρ.2.trans ht.2⟩
  rw [← Lp.norm_def] at h2
  refine (norm_toLp_le _ _).trans ?_
  have h3 : ‖v.snd‖ ≤ ‖v‖ := WithLp.norm_snd_le (x := v)
  have h4 : 0 ≤ √h := Real.sqrt_nonneg h
  calc ‖d.orbit v t‖ + ‖window h (d.trajOf v) t‖ ≤ M + (‖v‖ + √h * M) := by
        have : ‖window h (d.trajOf v) t‖ ≤ ‖v.snd‖ + √h * M := h2
        linarith
    _ = d.opBound τ * ‖v‖ := by
        simp only [hM, opBound]
        ring

/-- Restarting at time `s`: `x(t; S(s) v) = x(s + t; v)`. -/
theorem orbit_stateAt (v : State h E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    d.orbit (d.stateAt v s) t = d.orbit v (s + t) := by
  have e := d.sol_add_time (r := v.fst) (f := 0) (Lp.memLp v.snd) integrableOn_zero_forcing hs ht
  have e0 : (fun σ => (0 : ℝ → E) (s + σ)) = 0 := rfl
  rw [e0] at e
  rw [orbit, stateAt_fst, stateAt_snd, d.sol_congr_hist (Lp.memLp _)
    (coeFn_window (memLp_comp_add (d.memLp_trajOf v hs) hs (by linarith)))
    integrableOn_zero_forcing ht]
  exact e.symm

/-- Restarting at time `s` translates the trajectory (a.e.). -/
theorem trajOf_stateAt (v : State h E) {s : ℝ} (hs : 0 ≤ s) (T : ℝ) :
    d.trajOf (d.stateAt v s) =ᵐ[μI T] fun σ => d.trajOf v (s + σ) := by
  have h1 : d.trajOf (d.stateAt v s) =
      traj h (⇑(d.stateAt v s).snd) (fun σ => d.orbit v (s + σ)) :=
    traj_congr_right _ fun t ht => d.orbit_stateAt v hs ht
  have h2 := traj_shift (h := h) hs (⇑v.snd) (d.orbit v)
  rw [h1]
  exact (traj_ae_congr (coeFn_window (memLp_comp_add (d.memLp_trajOf v hs) hs (by linarith))) _
    _).trans (Filter.EventuallyEq.of_eq h2)

/-- **The semigroup law** `S(t) S(s) v = S(s + t) v`. -/
theorem stateAt_stateAt (v : State h E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    d.stateAt (d.stateAt v s) t = d.stateAt v (s + t) := by
  refine state_ext (d.orbit_stateAt v hs ht) ?_
  rw [stateAt_snd, stateAt_snd, window_congr_ae (d.trajOf_stateAt v hs (h + t)) ht (by linarith)]
  exact window_eq_of_ae (ae_of_all _ fun σ => by simp only [add_assoc])

/-! ### The C₀-semigroup -/

/-- The solution operator `S(t)` as a linear map. -/
def opₗ (t : ℝ≥0) : State h E →ₗ[ℝ] State h E where
  toFun v := d.stateAt v t
  map_add' v w := d.stateAt_add v w t.2
  map_smul' c v := d.stateAt_smul c v t.2

/-- The solution operator `S(t) (r, ψ) = (x(t), x_t)`. -/
def op (t : ℝ≥0) : State h E →L[ℝ] State h E :=
  (d.opₗ t).mkContinuous (d.opBound t) fun v => d.norm_stateAt_le v ⟨t.2, le_rfl⟩

/-- `op t v = S(t) v`. -/
theorem op_apply (t : ℝ≥0) (v : State h E) : d.op t v = d.stateAt v t := rfl

/-- `S(0) = 1`. -/
theorem op_zero : d.op 0 = 1 := by
  ext1 v
  rw [op_apply, NNReal.coe_zero, stateAt_zero]
  rfl

/-- The semigroup law `S(s + t) = S(s) S(t)`. -/
theorem op_add (s t : ℝ≥0) : d.op (s + t) = (d.op s).comp (d.op t) := by
  ext1 v
  rw [ContinuousLinearMap.comp_apply, op_apply, op_apply, op_apply, NNReal.coe_add,
    d.stateAt_stateAt v (NNReal.coe_nonneg t) (NNReal.coe_nonneg s), add_comm]

/-- Strong continuity at `0`. -/
theorem tendsto_op (v : State h E) : Tendsto (fun t => d.op t v) (𝓝 0) (𝓝 v) := by
  have hc : ContinuousWithinAt (d.stateAt v) (Icc 0 1) 0 :=
    d.continuousOn_stateAt v 1 0 ⟨le_rfl, zero_le_one⟩
  have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝 0) (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using NNReal.continuous_coe.tendsto 0
    · filter_upwards [Iio_mem_nhds (zero_lt_one : (0 : ℝ≥0) < 1)] with t ht
      exact ⟨t.2, le_of_lt (by exact_mod_cast ht)⟩
  have := hc.tendsto.comp h1
  rwa [d.stateAt_zero] at this

/-- **The delay semigroup** `S(t) (r, ψ) = (x(t), x_t)` on `X = E × L²(-h, 0; E)`
(`ex:intro-delay`): semigroup law `stateAt_stateAt`, strong continuity from the continuity of the
solution and of translation in `L²` (`continuousOn_window`). -/
def semigroup : C0Semigroup ℝ (State h E) :=
  C0Semigroup.ofTendsto d.op d.op_zero d.op_add d.tendsto_op

/-- `S(t) v = (x(t), x_t)`. -/
theorem semigroup_apply (t : ℝ≥0) (v : State h E) : d.semigroup t v = d.stateAt v t := rfl

/-- `S(t) v = (x(t), x_t)` at real times `t ≥ 0`. -/
theorem semigroup_real_apply {t : ℝ} (ht : 0 ≤ t) (v : State h E) :
    d.semigroup.real t v = d.stateAt v t := by
  rw [C0Semigroup.real, semigroup_apply, Real.coe_toNNReal _ ht]

/-- **Growth bound** of the delay semigroup. -/
theorem exists_norm_semigroup_le :
    ∃ M ω : ℝ, 1 ≤ M ∧ ∀ t : ℝ≥0, ‖d.semigroup t‖ ≤ M * Real.exp (ω * t) :=
  d.semigroup.exists_norm_le_exp

/-- Explicit bound: `‖S(t)‖ ≤ (1 + Kψ t) e^{K t} (1 + √h) + 1`. -/
theorem norm_semigroup_le (t : ℝ≥0) : ‖d.semigroup t‖ ≤ d.opBound t :=
  ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (mul_nonneg (mul_nonneg
    (by linarith [d.Kψ_nonneg (NNReal.coe_nonneg t)]) (Real.exp_pos _).le) (by positivity))
    zero_le_one) fun v => d.norm_stateAt_le v ⟨t.2, le_rfl⟩

/-! ### The generator -/

/-- `L ψ = rhs ψ 0 = ∑ₖ Aₖ ψ(h - hₖ) + L_d ψ` only sees the history. -/
theorem rhs_traj_zero (g x : ℝ → E) : d.rhs (traj h g x) 0 = d.rhs g 0 := by
  have hw : window h (traj h g x) 0 = window h g 0 :=
    window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      traj_of_le _ _ (by linarith [hσ.2]))
  simp only [rhs, hw, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [traj_of_le _ _ (d.sub_τ_le k)]

variable {g g' : ℝ → E}

/-- The orbit of an `H¹` history: `S(t) (g(h), g) = (x(t), x_t)` with `x = sol (g h) g 0`. -/
theorem stateAt_of_hasWeakDeriv (hg : HasWeakDeriv h g g') {t : ℝ} (ht : 0 ≤ t) :
    d.stateAt (WithLp.toLp 2 (g h, hg.memLp.toLp g)) t =
      WithLp.toLp 2 (d.sol (g h) g 0 t, window h (traj h g (d.sol (g h) g 0)) t) := by
  have hcoe : ⇑(hg.memLp.toLp g) =ᵐ[μI h] g := hg.memLp.coeFn_toLp
  have ho : ∀ s, 0 ≤ s → d.orbit (WithLp.toLp 2 (g h, hg.memLp.toLp g)) s = d.sol (g h) g 0 s :=
    fun s hs => d.sol_congr_hist (Lp.memLp _) hcoe integrableOn_zero_forcing hs
  refine state_ext (ho t ht) ?_
  rw [stateAt_snd, trajOf, traj_congr_right _ ho, WithLp.toLp_snd, WithLp.toLp_snd]
  exact window_congr_ae (traj_ae_congr hcoe _ (h + t)) ht (by linarith)

/-- **The generator on `H¹` histories** (easy inclusion): the difference quotients of
`(g(h), g)` converge to `(L g, g')`. -/
theorem tendsto_diffQuot_of_hasWeakDeriv (hg : HasWeakDeriv h g g') :
    Tendsto (d.semigroup.diffQuot (WithLp.toLp 2 (g h, hg.memLp.toLp g))) (𝓝[>] 0)
      (𝓝 (WithLp.toLp 2 (d.rhs g 0, hg.memLp_deriv.toLp g'))) := by
  have hx : d.IsSolOn 1 (g h) g 0 (d.sol (g h) g 0) :=
    d.isSolOn_sol hg.memLp (integrableOn_zero_forcing 1)
  have hz := d.hasWeakDeriv_traj zero_le_one hg MemLp.zero hx
  have hx0 : d.sol (g h) g 0 0 = g h := d.sol_zero_time _ _ _
  have hw0 : window h (traj h g (d.sol (g h) g 0)) 0 = hg.memLp.toLp g := by
    rw [← window_zero_eq_toLp hg.memLp]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      traj_of_le _ _ (by linarith [hσ.2]))
  have hw0' : window h (traj h g' fun s => d.rhs (traj h g (d.sol (g h) g 0)) s +
      (0 : ℝ → E) s) 0 = hg.memLp_deriv.toLp g' := by
    rw [← window_zero_eq_toLp hg.memLp_deriv]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ =>
      traj_of_le _ _ (by linarith [hσ.2]))
  have hA : Tendsto (fun t => t⁻¹ • (d.sol (g h) g 0 t - d.sol (g h) g 0 0)) (𝓝[>] 0)
      (𝓝 (d.rhs g 0)) := by
    have hG : ContinuousOn (fun s => d.rhs (traj h g (d.sol (g h) g 0)) s + (0 : ℝ → E) s)
        (Icc 0 1) := (d.continuousOn_rhs hz.continuousOn).add continuousOn_const
    have := tendsto_inv_smul_intervalIntegral zero_lt_one hG
    simp only [Pi.zero_apply, add_zero, d.rhs_traj_zero] at this
    refine this.congr' ?_
    filter_upwards [mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Ioo_subset_Ioc_self] with t ht
    rw [hx.2 t ⟨ht.1.le, ht.2⟩, hx0, add_sub_cancel_left]
    simp only [Pi.zero_apply, add_zero]
  have hB := tendsto_diffQuot_window hz d.h_pos.le (by linarith : h < h + 1)
  rw [hw0'] at hB
  have hlim := ((WithLp.prod_continuous_toLp (p := 2) (α := E) (β := L2 E h)).tendsto _).comp
    (hA.prodMk_nhds hB)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [C0Semigroup.diffQuot, d.semigroup_real_apply ht.le, d.stateAt_of_hasWeakDeriv hg ht.le]
  refine state_ext ?_ ?_
  · simp only [Function.comp_apply, WithLp.toLp_fst, WithLp.smul_fst, WithLp.sub_fst, hx0]
  · simp only [Function.comp_apply, WithLp.toLp_snd, WithLp.smul_snd, WithLp.sub_snd, hw0]

/-- `(g(h), g) ∈ D(A)` for every `H¹` history `g` (`ex:intro-delay`). -/
theorem mem_generator_domain_of_hasWeakDeriv (hg : HasWeakDeriv h g g') :
    WithLp.toLp 2 (g h, hg.memLp.toLp g) ∈ d.semigroup.generator.domain :=
  d.semigroup.mem_generator_domain_of_tendsto (d.tendsto_diffQuot_of_hasWeakDeriv hg)

/-- A state with an `H¹` representative of its history and matching endpoint. -/
theorem eq_toLp_of_hasWeakDeriv {v : State h E} (hg : HasWeakDeriv h g g') (h1 : v.fst = g h)
    (h2 : ⇑v.snd =ᵐ[μI h] g) : v = WithLp.toLp 2 (g h, hg.memLp.toLp g) :=
  state_ext h1 (Lp.ext (h2.trans hg.memLp.coeFn_toLp.symm))

/-- **The generator acts by differentiation**: if `v = (g(h), g)` with `g ∈ H¹` then
`A v = (L g, g')`, `L g = ∑ₖ Aₖ g(h - hₖ) + L_d g`. -/
theorem generator_apply {v : State h E} (hv : v ∈ d.semigroup.generator.domain)
    (hg : HasWeakDeriv h g g') (h1 : v.fst = g h) (h2 : ⇑v.snd =ᵐ[μI h] g) :
    d.semigroup.generator ⟨v, hv⟩ = WithLp.toLp 2 (d.rhs g 0, hg.memLp_deriv.toLp g') :=
  d.semigroup.generator_apply_eq hv (by
    rw [eq_toLp_of_hasWeakDeriv hg h1 h2]
    exact d.tendsto_diffQuot_of_hasWeakDeriv hg)

/-- **The hard inclusion** `D(A) ⊆ {(g(h), g) : g ∈ H¹}`: the `L²` convergence of the difference
quotients of the history gives a weak derivative (`exists_ae_eq_of_tendsto_diffQuot_window`), and
the endpoint `g(h) = x(0)` follows by applying this at time `h / 2`, where the window straddles
the history and the solution. -/
theorem exists_hasWeakDeriv_of_mem_generator_domain {v : State h E}
    (hv : v ∈ d.semigroup.generator.domain) :
    ∃ g g' : ℝ → E, HasWeakDeriv h g g' ∧ v.fst = g h ∧ ⇑v.snd =ᵐ[μI h] g := by
  set z := d.trajOf v with hzdef
  set x := d.orbit v with hxdef
  have hsnd : ∀ (w : State h E) (hw : w ∈ d.semigroup.generator.domain),
      Tendsto (fun t : ℝ => t⁻¹ • ((d.stateAt w t).snd - w.snd)) (𝓝[>] 0)
        (𝓝 (d.semigroup.generator ⟨w, hw⟩).snd) := by
    intro w hw
    have := ((WithLp.continuous_snd (p := 2) (α := E) (β := L2 E h)).tendsto _).comp
      (d.semigroup.tendsto_generator ⟨w, hw⟩)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp_apply, C0Semigroup.diffQuot, d.semigroup_real_apply ht.le,
      WithLp.smul_snd, WithLp.sub_snd]
  -- Step 1: the history has a weak derivative.
  set G := (d.semigroup.generator ⟨v, hv⟩).snd with hGdef
  have hv0 : window h z 0 = v.snd := by rw [← stateAt_snd, d.stateAt_zero]
  have h1 : Tendsto (fun t : ℝ => t⁻¹ • (window h z t - window h z 0)) (𝓝[>] 0) (𝓝 G) := by
    have := hsnd v hv
    simp only [stateAt_snd] at this
    rwa [← hv0] at this
  obtain ⟨c, hc⟩ := exists_ae_eq_of_tendsto_diffQuot_window d.h_pos zero_lt_one
    (d.memLp_trajOf v zero_le_one) h1
  set gh : ℝ → E := fun σ => c + ∫ u in (0 : ℝ)..σ, G u with hghdef
  have hgh : HasWeakDeriv h gh ⇑G := ⟨Lp.memLp G, fun σ _ => by simp [hghdef]⟩
  have hsndg : ⇑v.snd =ᵐ[μI h] gh := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hc
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hc] with σ hσ hσI
    show _ = c + ∫ u in (0 : ℝ)..σ, G u
    rw [← hσ hσI]
    exact (traj_of_le _ _ hσI.2).symm
  refine ⟨gh, G, hgh, ?_, hsndg⟩
  -- Step 2: the endpoint, from the window at time `s = h / 2`.
  set s := h / 2 with hsdef
  have hs0 : 0 < s := half_pos d.h_pos
  have hsh : s < h := half_lt_self d.h_pos
  have hvs : d.stateAt v s ∈ d.semigroup.generator.domain := by
    have := d.semigroup.mem_generator_domain_apply hv s.toNNReal
    rwa [semigroup_apply, Real.coe_toNNReal _ hs0.le] at this
  set G₂ := (d.semigroup.generator ⟨d.stateAt v s, hvs⟩).snd with hG₂def
  have h2 : Tendsto (fun t : ℝ => t⁻¹ • (window h (fun σ => z (s + σ)) t -
      window h (fun σ => z (s + σ)) 0)) (𝓝[>] 0) (𝓝 G₂) := by
    refine (hsnd _ hvs).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [d.stateAt_stateAt v hs0.le ht.le, stateAt_snd, stateAt_snd, window_comp_add,
      window_comp_add, add_zero]
  have hzs : MemLp (fun σ => z (s + σ)) 2 (μI (h + 1)) :=
    memLp_comp_add (d.memLp_trajOf v (τ := s + 1) (by linarith)) hs0.le (by linarith)
  obtain ⟨c₂, hc₂⟩ := exists_ae_eq_of_tendsto_diffQuot_window d.h_pos zero_lt_one hzs h2
  set q : ℝ → E := fun σ => c₂ + ∫ u in (0 : ℝ)..σ, G₂ u with hqdef
  have hqc : ContinuousOn q (Icc 0 h) :=
    continuousOn_const.add (continuousOn_primitive_Ioc ((Lp.memLp G₂).integrable one_le_two))
  have hghc : ContinuousOn gh (Icc 0 h) :=
    continuousOn_const.add (continuousOn_primitive_Ioc ((Lp.memLp G).integrable one_le_two))
  have e1 : EqOn q (fun σ => gh (s + σ)) (Icc 0 (h - s)) := by
    refine eqOn_Icc_of_ae (by linarith) (hqc.mono (Icc_subset_Icc_right (by linarith)))
      (hghc.comp (f := fun σ => s + σ) (by fun_prop)
        fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩) ?_
    have a1 : ∀ᵐ σ ∂(μI (h - s)), z (s + σ) = q σ :=
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right (by linarith)) hc₂
    have a2 : ∀ᵐ σ ∂(μI (h - s)), (⇑v.snd) (s + σ) = gh (s + σ) :=
      ae_comp_add hsndg hs0.le (by linarith)
    filter_upwards [a1, a2, ae_restrict_mem measurableSet_Ioc] with σ e₁ e₂ e₃
    rw [← e₁, ← e₂]
    exact traj_of_le _ _ (by linarith [e₃.2])
  have e2 : EqOn (fun ρ => q (h - s + ρ)) x (Icc 0 s) := by
    refine eqOn_Icc_of_ae hs0 (hqc.comp (f := fun ρ => h - s + ρ) (by fun_prop)
      fun ρ hρ => ⟨by linarith [hρ.1], by linarith [hρ.2]⟩) (d.continuousOn_orbit v s) ?_
    have a1 : ∀ᵐ ρ ∂(μI s), z (s + (h - s + ρ)) = q (h - s + ρ) :=
      ae_comp_add hc₂ (by linarith) (by linarith)
    filter_upwards [a1, ae_restrict_mem measurableSet_Ioc] with ρ e₁ e₂
    rw [← e₁, show s + (h - s + ρ) = h + ρ by ring]
    show traj h (⇑v.snd) (d.orbit v) (h + ρ) = d.orbit v ρ
    rw [traj_of_lt _ _ (by linarith [e₂.1]), add_sub_cancel_left]
  have f1 : q (h - s) = gh (s + (h - s)) := e1 ⟨by linarith, le_rfl⟩
  have f2 : q (h - s + 0) = x 0 := e2 ⟨le_rfl, hs0.le⟩
  rw [add_zero] at f2
  rw [show s + (h - s) = h by ring] at f1
  rw [← f1, f2]
  simp [hxdef, orbit]

/-- **The generator of the delay semigroup** (`ex:intro-delay`):
`D(A) = {(g(h), g) : g ∈ H¹(0, h; E)}`. -/
theorem mem_generator_domain_iff (v : State h E) :
    v ∈ d.semigroup.generator.domain ↔
      ∃ g g' : ℝ → E, HasWeakDeriv h g g' ∧ v.fst = g h ∧ ⇑v.snd =ᵐ[μI h] g := by
  refine ⟨d.exists_hasWeakDeriv_of_mem_generator_domain, ?_⟩
  rintro ⟨g, g', hg, h1, h2⟩
  rw [eq_toLp_of_hasWeakDeriv hg h1 h2]
  exact d.mem_generator_domain_of_hasWeakDeriv hg

end Equation

end Delay

end DataDrivenControl
