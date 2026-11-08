module

public import DataDrivenControl.Examples.InformativityConverse.Trig
public import DataDrivenControl.Examples.Delay.Unbounded
public import DataDrivenControl.Informativity.Informative
public import DataDrivenControl.Analysis.ExpSums

/-!
# Informativity in `U × X` does not imply informativity in `U × W`

Paper: the remark after `lem:informative-gramian` (`informativity.tex`): "informativity in
`U × W` implies informativity in `U × X`; the converse fails in general".  The implication is
`Informative.map_of_denseRange` and `System.Informative.mild_of_mildW`
(`Informativity/Informative`).  This file proves that the converse fails, for a record of a
system that satisfies the paper's standing assumptions.

## The system

The delay system of `ex:intro-delay` (`Examples/Delay`) with `h = 2π`, `E = U = Y = ℝ`, `L = 0`,
`M = 0`, `B₀ = 1` and the delayed output `y(t) = x(t - 2π)`:

`ẋ(t) = u(t)`,  `y(t) = x(t - 2π)`  (`model`; `model_L_eval`, `model_M_eval`).

It is `Delay.Model.sys : System U W X X Y` with `W = D(A)` (graph norm) and
`X = V = ℝ × L²(0, 2π)`, so `hyp:H1`, `hyp:H2` (every horizon) and `hyp:compat` hold
(`model_standing`), and `C` is unbounded on `X` (`model_not_exists_bound_C`).  As in
`Examples/Delay`, the history lives on `(0, 2π]`.

## The record

`x(t) = ∑ₙ 2^{-n} cos(n t)` (`xs`), the input `ū = ẋ` (`us`), the initial state
`x̄₀ = (x(0), x_0) ∈ W` with history `x` on `(0, 2π]` (`x₀`).  By periodicity the state of
the record is `x̄(t) = (x(t), x(t + ·)) = state t` (`ιW_mildW_eq_state`).

## Main results

* `not_informative_W`: for every `T`, the record is **not informative in `U × W`**.  The
  functional `(r, g) ↦ g(2π) - g(0) = ∫₀^{2π} (A v)₂` is continuous on `W` but not on `X`, and
  vanishes on `x̄(t)` because `x` is `2π`-periodic; its Riesz representer `β = A^* (0, 1) ∈ W`
  (`annihilatorW`, `annihilatorW_ne_zero`) gives the annihilator `(0, β)`.
* `informative_X`, `informative_mild`: for every `T > 0`, the same record is **informative in
  `U × X`** (state `ιW ∘ x̄ = sys.mild (ιW x̄₀) ū`).
* `exists_informative_not_informativeW`: the counterexample packaged with the standing
  assumptions; `not_forall_informativeW_of_informative`: the converse of
  `System.Informative.mild_of_mildW` is false.

## Proof of informativity in `U × X`

An annihilator `(α, (β₁, β₂))` gives `α ū(t) + β₁ x(t) + ∫₀^{2π} β₂(σ) x(t + σ) dσ = 0` for
a.e. `t ∈ (0, T)`.  Expanding `cos(n (t + σ))`, the left side is the trigonometric series
`∑ₙ 2^{-n} (cos(n t) (β₁ + Cₙ) - sin(n t) (α n + Sₙ))` with the cosine and sine moments
`Cₙ`, `Sₙ` of `β₂` (`hasSum_integral_mul_xs`).  Its coefficients decay geometrically, so
`trigSeries_coeff_eq_zero` (`Analysis/ExpSums`, identity theorem) applies on any interval:
`β₁ + Cₙ = 0` for all `n` and `α n + Sₙ = 0` for `n ≥ 1`.  Riemann–Lebesgue
(`tendsto_cosMoment`, `tendsto_sinMoment`) gives `β₁ = 0` and `α = 0`, and completeness of
the trigonometric system (`ae_eq_zero_of_moments_eq_zero`) gives `β₂ = 0`.

## Deviations

None in the statement.  The paper gives no example; this one works for every horizon `T > 0`
(informativity in `U × X` needs no `T ≥ 2π`, since `x` is real analytic), and the failure in
`U × W` holds for every `T`.

## Upstream results used

`Delay.Model.H1`, `Model.H2`, `Model.compat`, `Model.not_exists_bound_C_of_atom_zero`,
`Equation.mem_generator_domain_iff`, `Equation.generator_apply`,
`Equation.mem_generator_domain_of_hasWeakDeriv`, `window_sub_window_eq_integral`
(`Examples/Delay`); `C0Semigroup.eq_mildSol_of_strong` (`Semigroup/Inhomogeneous`);
`System.ιW_mildW`, `System.ιWV_L` (`System/Mild`); `informative_iff`, `Informative.eq_zero`,
`Informative.congr` (`Informativity/Informative`); `trigSeries_coeff_eq_zero`,
`accPt_Ioo_inter_of_ae` (`Analysis/ExpSums`); `inner_window`, `coeFn_window`,
`continuousOn_window` (`Signal/Shift`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace InformativityConverse

open Delay

/-! ### The system -/

/-- **The delay system of the counterexample**: `h = 2π`, `E = U = Y = ℝ`, `L = 0`, `M = 0`,
`B₀ = 1`, and the delayed output `y(t) = x(t - 2π)` (one point delay `2π`, a Dirac measure,
`DelayOp.ofPoints`).  The equation is `ẋ = u`. -/
def model : Model (2 * π) ℝ ℝ ℝ where
  L := DelayOp.ofPoints Real.two_pi_pos (N := 0) (fun k => k.elim0) (fun k => k.elim0)
    (fun k => k.elim0) 0
  M := DelayOp.ofPoints Real.two_pi_pos (N := 0) (fun k => k.elim0) (fun k => k.elim0)
    (fun k => k.elim0) 0
  M_noAtom := fun k => Fin.elim0 k
  B₀ := ContinuousLinearMap.id ℝ ℝ
  C := DelayOp.ofPoints Real.two_pi_pos (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
    (fun _ => 2 * π) (fun _ => ⟨Real.two_pi_pos.le, le_rfl⟩) 0

/-- The model has no state feedback: `L x_s = 0`. -/
@[simp] theorem model_L_eval (z : ℝ → ℝ) (s : ℝ) : model.L.eval z s = 0 := by
  simp [model, DelayOp.eval_ofPoints]

/-- The model is retarded: `M x_s = 0`. -/
@[simp] theorem model_M_eval (z : ℝ → ℝ) (s : ℝ) : model.M.eval z s = 0 := by
  simp [model, DelayOp.eval_ofPoints]

/-- `B u = (u, 0)`. -/
@[simp] theorem model_Bop (u : ℝ) : model.Bop u = WithLp.toLp 2 (u, 0) := rfl

/-- The standing assumptions `hyp:H1`, `hyp:H2` (at every horizon) and `hyp:compat` hold. -/
theorem model_standing (T : ℝ) : model.sys.H1 T ∧ model.sys.H2 T ∧ model.sys.Compat :=
  ⟨model.H1 T, model.H2 T, model.compat⟩

/-- The output `y(t) = x(t - 2π)` makes `C` unbounded on `X`: informativity in `U × W` is the
relevant notion for this system. -/
theorem model_not_exists_bound_C :
    ¬ ∃ K : ℝ, ∀ w : model.S.Dom, ‖model.sys.C w‖ ≤ K * ‖model.sys.ιW w‖ := by
  have hatom : ∀ θ, model.C.atom θ =
      (Measure.dirac (2 * π)).real {θ} • ContinuousLinearMap.id ℝ ℝ :=
    fun _ => Fin.sum_univ_one _
  refine model.not_exists_bound_C_of_atom_zero ⟨Real.two_pi_pos, le_rfl⟩ ?_ ?_
  · rw [hatom, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton 0),
      indicator_of_notMem (by simp [Real.pi_ne_zero]), ENNReal.toReal_zero, zero_smul]
  · rw [hatom, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _),
      indicator_of_mem (mem_singleton _), Pi.one_apply, ENNReal.toReal_one, one_smul]
    intro h
    have := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
    simp at this

/-! ### The signals and the states -/

/-- The translates of `x` are `H¹`, with derivative the translates of `ū`. -/
theorem hasWeakDeriv_shift (T t : ℝ) :
    HasWeakDeriv T (fun σ => xs (t + σ)) (fun σ => us (t + σ)) :=
  HasWeakDeriv.of_hasDerivAt (fun σ => HasDerivAt.comp_const_add t σ (hasDerivAt_xs (t + σ)))
    (continuous_us.comp (continuous_const.add continuous_id))

/-- `x ∈ H¹(0, T)` with weak derivative `ū`. -/
theorem hasWeakDeriv_xs (T : ℝ) : HasWeakDeriv T xs us :=
  HasWeakDeriv.of_hasDerivAt hasDerivAt_xs continuous_us

/-- The input is square integrable on every window. -/
theorem memLp_us (T : ℝ) : MemLp us 2 (μI T) :=
  memLp_μI_of_continuousOn continuous_us.continuousOn

/-- The state signal is square integrable on every window. -/
theorem memLp_xs (T : ℝ) : MemLp xs 2 (μI T) :=
  memLp_μI_of_continuousOn continuous_xs.continuousOn

/-- The state of the record at time `t`: `x̄(t) = (x(t), x_t)` with the history
`x_t = x(t - 2π + ·) = x(t + ·)` on `(0, 2π]` (periodicity). -/
def state (t : ℝ) : State (2 * π) ℝ := WithLp.toLp 2 (xs t, window (2 * π) xs t)

/-- The first component is `g(2π) - M g` for the history `g = x(t + ·)`: `M = 0` and
`x(t + 2π) = x(t)`. -/
theorem state_fst (t : ℝ) :
    (state t).fst = xs (t + 2 * π) - model.M.eval (fun σ => xs (t + σ)) 0 := by
  rw [model_M_eval, sub_zero, xs_add_two_pi]
  rfl

/-- `x̄(t) ∈ D(A)`. -/
theorem state_mem (t : ℝ) : state t ∈ model.S.generator.domain :=
  (model.mem_generator_domain_iff (state t)).2
    ⟨_, _, hasWeakDeriv_shift (2 * π) t, state_fst t,
      coeFn_window (hasWeakDeriv_shift (2 * π) t).memLp⟩

/-- `A x̄(t) = (0, ū_t)`: the generator differentiates the history, and `L = 0`. -/
theorem generator_state (t : ℝ) :
    model.S.generator ⟨state t, state_mem t⟩ = WithLp.toLp 2 (0, window (2 * π) us t) := by
  have hg := hasWeakDeriv_shift (2 * π) t
  rw [model.generator_apply (state_mem t) hg (coeFn_window hg.memLp), model_L_eval,
    ← window_eq_toLp hg.memLp_deriv]

/-- The initial state `x̄₀ = (x(0), x_0) ∈ W = D(A)` of the record. -/
def x₀ : model.S.Dom := model.S.toDom ⟨state 0, state_mem 0⟩

/-- `t ↦ x̄(t)` is the strong solution of `ẋ̄ = A x̄ + B ū` from `x̄(0)`, hence the mild one. -/
theorem state_eq_mildSol {t : ℝ} (ht : 0 ≤ t) :
    state t = model.S.mildSol (state 0) (fun r => model.Bop (us r)) t := by
  set G : ℝ → State (2 * π) ℝ := fun s => WithLp.toLp 2 (0, window (2 * π) us s) with hGdef
  have hGc : ContinuousOn G (Icc 0 t) :=
    (WithLp.prod_continuous_toLp (p := 2) (α := ℝ) (β := L2 ℝ (2 * π))).comp_continuousOn
      (continuousOn_const.prodMk (continuousOn_window (memLp_us (2 * π + t))))
  have hGi : IntegrableOn G (Ioc 0 t) := hGc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hBi : IntegrableOn (fun s => model.Bop (us s)) (Ioc 0 t) :=
    (model.Bop.continuous.comp continuous_us).integrableOn_Ioc
  refine model.S.eq_mildSol_of_strong (τ := t) (x := state) (g := G)
    (f := fun s => model.Bop (us s)) (fun s _ => state_mem s) (fun s _ => generator_state s)
    hGi hBi ?_ t ⟨ht, le_rfl⟩
  intro s hs
  have hGBi : IntervalIntegrable (fun r => G r + model.Bop (us r)) volume 0 s :=
    intervalIntegrable_of_integrableOn (hGi.add hBi) hs
  have kf : (∫ r in (0 : ℝ)..s, (G r + model.Bop (us r))).fst =
      ∫ r in (0 : ℝ)..s, (G r + model.Bop (us r)).fst :=
    ((WithLp.fstL 2 ℝ ℝ (L2 ℝ (2 * π))).intervalIntegral_comp_comm hGBi).symm
  have ks : (∫ r in (0 : ℝ)..s, (G r + model.Bop (us r))).snd =
      ∫ r in (0 : ℝ)..s, (G r + model.Bop (us r)).snd :=
    ((WithLp.sndL 2 ℝ ℝ (L2 ℝ (2 * π))).intervalIntegral_comp_comm hGBi).symm
  refine state_ext ?_ ?_
  · rw [WithLp.add_fst, kf]
    simp only [hGdef, WithLp.add_fst, WithLp.toLp_fst, model_Bop, zero_add, state]
    rw [integral_us]
    ring
  · rw [WithLp.add_snd, ks]
    simp only [hGdef, WithLp.add_snd, WithLp.toLp_snd, model_Bop, add_zero, state]
    rw [← window_sub_window_eq_integral (hasWeakDeriv_xs (2 * π + s)) Real.two_pi_pos.le hs.1
      le_rfl]
    abel

/-- **The record in `X`**: `x̄(t) = S(t) x̄₀ + L_t ū = (x(t), x_t)`. -/
theorem ιW_mildW_eq_state {t : ℝ} (ht : 0 ≤ t) :
    model.sys.ιW (model.sys.mildW x₀ us t) = state t := by
  rw [System.ιW_mildW, state_eq_mildSol ht]
  have hL : model.sys.ιW (model.sys.L t us) = model.sys.convV t us :=
    System.ιWV_L (model.H1 1) one_pos (memLp_us t)
  rw [System.mild, hL]
  rfl

/-- `A x̄(t) = (0, ū_t)` along the record. -/
theorem domGen_mildW {t : ℝ} (ht : 0 ≤ t) :
    model.S.domGen (model.sys.mildW x₀ us t) = WithLp.toLp 2 (0, window (2 * π) us t) := by
  have e : (⟨model.S.domIncl (model.sys.mildW x₀ us t), model.S.domIncl_mem _⟩ :
      model.S.generator.domain) = ⟨state t, state_mem t⟩ :=
    Subtype.ext (ιW_mildW_eq_state ht)
  rw [← model.S.generator_domIncl, e, generator_state]

/-! ### Not informative in `U × W` -/

/-- The constant `1 ∈ L²(0, 2π)`. -/
def oneL2 : L2 ℝ (2 * π) := (memLp_const (1 : ℝ)).toLp _

/-- The representative of `1 ∈ L²(0, 2π)`. -/
theorem coeFn_oneL2 : ⇑oneL2 =ᵐ[μI (2 * π)] fun _ => (1 : ℝ) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

/-- `e = (0, 1) ∈ X`; `⟪e, (r, g)⟫_X = ∫₀^{2π} g`. -/
def eX : State (2 * π) ℝ := WithLp.toLp 2 (0, oneL2)

/-- `⟪e, (0, ū_t)⟫_X = ∫₀^{2π} ū(t + σ) dσ = x(t + 2π) - x(t) = 0`. -/
theorem inner_eX_window {t : ℝ} (ht : 0 ≤ t) :
    ⟪eX, WithLp.toLp 2 ((0 : ℝ), window (2 * π) us t)⟫_ℝ = 0 := by
  rw [WithLp.prod_inner_apply]
  simp only [eX, WithLp.ofLp_toLp, inner_zero_left, zero_add]
  rw [inner_window (memLp_us (t + 2 * π)) ht le_rfl]
  have e : ∫ σ in Ioc 0 (2 * π), ⟪oneL2 σ, us (t + σ)⟫_ℝ = ∫ σ in Ioc 0 (2 * π), us (t + σ) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_oneL2] with σ hσ
    rw [hσ, Real.inner_apply, one_mul]
  rw [e, ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_comp_add_left (fun s => us s) t, integral_us, add_zero,
    xs_add_two_pi, sub_self]

/-- `⟪e, e⟫_X = 2π`. -/
theorem inner_eX_self : ⟪eX, eX⟫_ℝ = 2 * π := by
  rw [WithLp.prod_inner_apply]
  simp only [eX, WithLp.ofLp_toLp, inner_zero_left, zero_add]
  rw [L2.inner_def, integral_congr_ae (g := fun _ => (1 : ℝ)) ?_]
  · simp [Real.two_pi_pos.le]
  · filter_upwards [coeFn_oneL2] with σ hσ
    rw [hσ, Real.inner_apply, one_mul]

/-- **The annihilator in `W`**: `β = A^* e`, with `A^*` the Hilbert adjoint of `A ∈ L(W, X)`.
It is the Riesz representer of `w ↦ ⟪e, A w⟫_X = ∫₀^{2π} (A w)₂`, i.e. of
`(g(2π), g) ↦ g(2π) - g(0)`, which is continuous on `W = D(A)` but not on `X`. -/
def annihilatorW : model.S.Dom :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := model.S.Dom) (F := State (2 * π) ℝ) model.S.domGen eX

/-- `⟪β, w⟫_W = ⟪e, A w⟫_X`. -/
theorem inner_annihilatorW (w : model.S.Dom) : ⟪annihilatorW, w⟫_ℝ = ⟪eX, model.S.domGen w⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- `β ≠ 0`: on `w = (2π, σ ↦ σ)`, `A w = e` and `⟪β, w⟫_W = ‖e‖² = 2π`. -/
theorem annihilatorW_ne_zero : annihilatorW ≠ 0 := by
  intro h0
  have hg : HasWeakDeriv (2 * π) (fun σ : ℝ => σ) (fun _ => (1 : ℝ)) :=
    HasWeakDeriv.of_hasDerivAt (fun σ => hasDerivAt_id' σ) continuous_const
  have hmem := model.mem_generator_domain_of_hasWeakDeriv hg
  have hA : model.S.domGen (model.S.toDom ⟨_, hmem⟩) = eX := by
    rw [C0Semigroup.domGen_toDom, model.generator_apply hmem hg hg.memLp.coeFn_toLp,
      model_L_eval]
    rfl
  have h1 := inner_annihilatorW (model.S.toDom ⟨_, hmem⟩)
  rw [h0, inner_zero_left, hA, inner_eX_self] at h1
  linarith [Real.two_pi_pos]

/-- **The record is not informative in `U × W`**, on any window: `(0, β)` annihilates it. -/
theorem not_informative_W (T : ℝ) : ¬ Informative T us (model.sys.mildW x₀ us) := by
  intro hI
  refine annihilatorW_ne_zero (hI.eq_zero (a := (0 : ℝ)) (b := annihilatorW) ?_).2
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [inner_zero_left, zero_add, inner_annihilatorW, domGen_mildW ht.1.le, inner_eX_window ht.1.le]

/-! ### Informative in `U × X` -/

/-- `⟪b, x̄(t)⟫_X = b₁ x(t) + ∫₀^{2π} b₂(σ) x(t + σ) dσ`. -/
theorem inner_state (b : State (2 * π) ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ⟪b, state t⟫_ℝ = b.fst * xs t + ∫ σ in Ioc 0 (2 * π), b.snd σ * xs (t + σ) := by
  rw [WithLp.prod_inner_apply]
  simp only [state, WithLp.ofLp_toLp, WithLp.ofLp_fst, WithLp.ofLp_snd, Real.inner_apply]
  rw [inner_window (memLp_xs (t + 2 * π)) ht le_rfl]
  simp only [Real.inner_apply]

/-- **The record is informative in `U × X`** on every window `(0, T]`, `T > 0`. -/
theorem informative_state {T : ℝ} (hT : 0 < T) : Informative T us state := by
  rw [informative_iff]
  intro a b hab
  have hf : MemLp (⇑b.snd) 2 (μI (2 * π)) := Lp.memLp b.snd
  set M : ℝ := ∫ σ in Ioc 0 (2 * π), |b.snd σ| with hM
  have h34 : ‖(3 / 4 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hg : Summable fun n : ℕ => (3 / 4 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hng : Summable fun n : ℕ => (n : ℝ) * (3 / 4 : ℝ) ^ n :=
    (hasSum_coe_mul_geometric_of_norm_lt_one h34).summable
  -- the coefficients of the annihilation identity decay geometrically
  have hAs : Summable fun n : ℕ =>
      ‖coef n * (b.fst + cosMoment b.snd n)‖ * (3 / 2 : ℝ) ^ n := by
    refine (hg.mul_left (|b.fst| + M)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (coef_pos n), mul_comm (coef n), mul_assoc,
      coef_mul_pow]
    exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans
      (add_le_add le_rfl (abs_cosMoment_le hf n))) (by positivity)
  have hBs : Summable fun n : ℕ =>
      ‖-(coef n * (a * n + sinMoment b.snd n))‖ * (3 / 2 : ℝ) ^ n := by
    refine ((hng.mul_left |a|).add (hg.mul_left M)).of_nonneg_of_le (fun n => by positivity)
      fun n => ?_
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (coef_pos n), mul_comm (coef n),
      mul_assoc, coef_mul_pow]
    have h1 : |a * n + sinMoment b.snd n| ≤ |a| * n + M := by
      refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sinMoment_le hf n))
      rw [abs_mul, Nat.abs_cast]
    calc |a * n + sinMoment b.snd n| * (3 / 4 : ℝ) ^ n ≤ (|a| * n + M) * (3 / 4 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = |a| * (n * (3 / 4 : ℝ) ^ n) + M * (3 / 4 : ℝ) ^ n := by ring
  -- the annihilation identity is a trigonometric series, a.e. on `(0, T)`
  have hzero : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∑' n : ℕ, (Real.cos (n * t) • (coef n * (b.fst + cosMoment b.snd n)) +
        Real.sin (n * t) • -(coef n * (a * n + sinMoment b.snd n))) = 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hab,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    refine HasSum.tsum_eq ?_
    rw [inner_state b htI.1.le, Real.inner_apply] at ht
    have h := ((summable_us t).hasSum.mul_left a).add
      (((summable_xs t).hasSum.mul_left b.fst).add (hasSum_integral_mul_xs hf t))
    convert h using 1
    · funext n
      simp only [smul_eq_mul]
      ring
    · exact ht.symm
  obtain ⟨hA0, hB0⟩ := trigSeries_coeff_eq_zero (E := ℝ) (by norm_num : (1 : ℝ) < 3 / 2) hAs hBs
    (accPt_Ioo_inter_of_ae hzero (t₀ := T / 2) ⟨by linarith, by linarith⟩) fun t ht => ht.2
  have hC0 : ∀ n : ℕ, cosMoment b.snd n = -b.fst := fun n => by
    rcases mul_eq_zero.1 (hA0 n) with h | h
    · exact absurd h (coef_pos n).ne'
    · linarith
  have hS0 : ∀ n : ℕ, n ≠ 0 → sinMoment b.snd n = -(a * n) := fun n hn => by
    rcases mul_eq_zero.1 (neg_eq_zero.1 (hB0 n hn)) with h | h
    · exact absurd h (coef_pos n).ne'
    · linarith
  -- Riemann–Lebesgue: `β₁ = 0` and `α = 0`
  have hb₁ : b.fst = 0 := by
    have h := tendsto_cosMoment hf
    simp only [hC0] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    linarith
  have ha : a = 0 := by
    have hle : ∀ᶠ n : ℕ in atTop, |a| ≤ |sinMoment b.snd n| := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [hS0 n (by omega), abs_neg, abs_mul, Nat.abs_cast]
      exact le_mul_of_one_le_right (abs_nonneg a) (by exact_mod_cast hn)
    have h := ge_of_tendsto (tendsto_sinMoment hf).abs hle
    rw [abs_zero] at h
    exact abs_nonpos_iff.1 h
  -- completeness of the trigonometric system: `β₂ = 0`
  have hb₂ : b.snd = 0 := by
    have hC' : ∀ n : ℕ, cosMoment b.snd n = 0 := fun n => by rw [hC0, hb₁, neg_zero]
    have hS' : ∀ n : ℕ, sinMoment b.snd n = 0 := fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [sinMoment]
      · rw [hS0 n hn.ne', ha, zero_mul, neg_zero]
    exact Lp.eq_zero_iff_ae_eq_zero.2 (ae_eq_zero_of_moments_eq_zero hf hC' hS')
  exact ⟨ha, state_ext (hb₁.trans WithLp.zero_fst.symm) (hb₂.trans WithLp.zero_snd.symm)⟩

/-- **The record is informative in `U × X`**: the state `ιW ∘ x̄` (the remark after
`lem:informative-gramian`, with `X` in place of `W`), on every window `(0, T]`, `T > 0`. -/
theorem informative_X {T : ℝ} (hT : 0 < T) :
    Informative T us (fun t => model.sys.ιW (model.sys.mildW x₀ us t)) := by
  refine (informative_state hT).congr (ae_of_all _ fun _ => rfl) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (ιW_mildW_eq_state ht.1.le).symm

/-- The same, for the record generated by `ιW x̄₀ ∈ X` (state `sys.mild`), the form of
`System.Informative.mild_of_mildW`. -/
theorem informative_mild {T : ℝ} (hT : 0 < T) :
    Informative T us (model.sys.mild (model.sys.ιW x₀) us) := by
  have := informative_X hT
  simpa only [System.ιW_mildW] using this

/-! ### The counterexample -/

/-- **Informativity in `U × X` does not imply informativity in `U × W`** (remark after
`lem:informative-gramian`): there is a system satisfying `hyp:H1`, `hyp:H2` (every horizon) and
`hyp:compat` — the delay system `ẋ = u`, `y(t) = x(t - 2π)` — and a record generated by
`(x̄₀, ū)`, `x̄₀ ∈ W`, `ū ∈ L²`, that is informative in `U × X` but not in `U × W` on every window
`(0, T]`, `T > 0`. -/
theorem exists_informative_not_informativeW :
    ∃ (h : ℝ) (m : Model h ℝ ℝ ℝ) (w₀ : m.S.Dom) (u : ℝ → ℝ),
      (∀ T, m.sys.H1 T ∧ m.sys.H2 T) ∧ m.sys.Compat ∧ (∀ T, MemLp u 2 (μI T)) ∧
      ∀ T, 0 < T → Informative T u (m.sys.mild (m.sys.ιW w₀) u) ∧
        ¬ Informative T u (m.sys.mildW w₀ u) :=
  ⟨2 * π, model, x₀, us, fun T => ⟨model.H1 T, model.H2 T⟩, model.compat, memLp_us,
    fun _ hT => ⟨informative_mild hT, not_informative_W _⟩⟩

/-- **The converse of `System.Informative.mild_of_mildW` is false**: informativity in `U × X`
of a record with `x̄₀ ∈ W` does not imply its informativity in `U × W`, even under the standing
assumptions. -/
theorem not_forall_informativeW_of_informative :
    ¬ ∀ (U W X V Y : Type) [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
      [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
      (sys : System U W X V Y) (T : ℝ) (w₀ : W) (u : ℝ → U),
      sys.H1 T → sys.H2 T → sys.Compat → 0 < T → MemLp u 2 (μI T) →
      Informative T u (sys.mild (sys.ιW w₀) u) → Informative T u (sys.mildW w₀ u) := fun H =>
  not_informative_W 1 (H ℝ model.S.Dom (State (2 * π) ℝ) (State (2 * π) ℝ) ℝ model.sys 1 x₀ us
    (model.H1 1) (model.H2 1) model.compat one_pos (memLp_us 1) (informative_mild one_pos))

end InformativityConverse

end DataDrivenControl
