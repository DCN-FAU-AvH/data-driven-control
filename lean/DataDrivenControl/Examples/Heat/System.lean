module

public import DataDrivenControl.Examples.Heat.Estimates
public import DataDrivenControl.System.ControlRealization

/-!
# The boundary-controlled heat equation as a `System`

Paper: `ex:intro-pde` (`introduction.tex`), `ex:boundary-heat-informative` (`informativity.tex`),
`app:boundary-heat-informative` (`appendix_proofs.tex`): the point observation on `W`,
`eq:heat-control-X`, `hyp:H1`, `hyp:H2`, `hyp:compat`, and `B⋆φ = -φ(0)`;
`app:control-realization` for `B⋆`.

## Setting

`ControlData` extends the modal data of `Examples/Heat/Spaces` by control coefficients `bₙ`
(bounded) and the boundedness on `(0, ∞)` of the impulse response `h(t) = ∑ₙ cₙ bₙ e^{λₙ t}`
and of its termwise derivative `h'(t) = ∑ₙ cₙ bₙ λₙ e^{λₙ t}` (`eq:heat-separated-kernel`,
scalar form; `Examples/Heat/Kernel` proves both for the heat equation).  The spaces are
`W ↪ X ↪ V` of `Examples/Heat/Spaces`; indices start at `0`.

## Main declarations

* `d.B : ℝ →L[ℝ] d.V`, `B 1 = b = (bₙ / wₙ)ₙ ∈ X₋₁` (`ctrlVec`), which lies in `V` because `h` is
  bounded (`memLp_obs_ctrlVec`).
* `d.C : d.W →L[ℝ] ℝ`, **the trace formula in time**
  `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds`, `g = C S(·) w`, `g' = C S(·) A_V w` (`C_apply`); on `D(A)`
  it is the modal formula `C w = ∑ₙ cₙ ⟪eₙ, ι_W w⟫` (`hasSum_C`, from `hasSum_trace`).
* `d.sys e : System ℝ d.W X d.V ℝ` with `SX = diagSemigroup e λ` (`sys_SX`).
* `compat` (`hyp:compat`, `W = D(A_V)` by construction), `H2` (`hyp:H2` with constant `1`:
  `C S(t) w` is the second component of `w ∈ V`, `C_SW`), `H1` (`hyp:H1` in every `T > 0`:
  `eq:heat-control-X` and the `V`-bound of `A_{X,-1} L_T u` from `exists_control_bound`, then
  `eq:heat-W-domain`).
* `inner_ιW_Lop`: `⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪bₙ, u(r)⟫ dr`, and `approxControllable`
  (distinct `λₙ`, `bₙ ≠ 0`) from `System.approxControllable_of_modal`.
* `hasSum_Bstar`: `B⋆ η = ∑ₙ bₙ ⟪eₙ, η⟫` on `D(A⋆)` (`System.inner_Bstar_of_dual`).
* Unboundedness: `B_one_not_mem_range` (`∑ bₙ² = ∞ ⇒ B 1 ∉ X`) and
  `not_exists_bound_C` (`∑ cₙ² = ∞ ⇒ C` is not bounded by `‖·‖_X` on `D(A)`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

/-- **Control data**: modal data (`ModalData`) with bounded control coefficients `bₙ`, such that
the impulse response `h(t) = ∑ₙ cₙ bₙ e^{λₙ t}` and its termwise derivative
`h'(t) = ∑ₙ cₙ bₙ λₙ e^{λₙ t}` are bounded on `(0, ∞)` (`eq:heat-separated-kernel`, scalar form).
The heat equation has `bₙ = -eₙ(0)` (`app:boundary-heat-informative`, `b = -δ₀`). -/
structure ControlData extends ModalData where
  /-- The control coefficients `bₙ`. -/
  b : ℕ → ℝ
  exists_abs_b_le : ∃ K, ∀ n, |b n| ≤ K
  exists_abs_kernel_le : ∃ M, ∀ t > 0, |∑' n, c n * b n * Real.exp (lam n * t)| ≤ M
  exists_abs_kernelDeriv_le :
    ∃ M, ∀ t > 0, |∑' n, c n * b n * lam n * Real.exp (lam n * t)| ≤ M

namespace ControlData

variable (d : ControlData)

/-- `b = (bₙ / wₙ)ₙ ∈ X₋₁`. -/
theorem summable_ctrl_sq : Summable fun n => (d.b n / d.wt n) ^ 2 := by
  obtain ⟨K, hK⟩ := d.exists_abs_b_le
  refine (d.summable_inv_wt.mul_left (K ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _)
    fun n => ?_
  have hw := d.wt_pos n
  have h1 := d.one_le_wt n
  have hb : d.b n ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK n) 2
  show (d.b n / d.wt n) ^ 2 ≤ K ^ 2 * (d.wt n)⁻¹
  rw [div_pow, div_eq_mul_inv]
  have : (d.wt n ^ 2)⁻¹ ≤ (d.wt n)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hw]; nlinarith
  exact mul_le_mul hb this (by positivity) (by positivity)

/-- The control vector `b = B 1 ∈ X₋₁`, coordinates `bₙ / wₙ`. -/
def ctrlVec : Xm1 := mkL2 (fun n => d.b n / d.wt n) d.summable_ctrl_sq

/-- Coordinates of `b ∈ X₋₁`. -/
theorem ctrlVec_apply (n : ℕ) : d.ctrlVec n = d.b n / d.wt n := rfl

/-- The free output of `b` is the impulse response `h(t) = ∑ₙ cₙ bₙ e^{λₙ t}`. -/
theorem hasSum_obs_ctrlVec {t : ℝ} (ht : 0 < t) :
    HasSum (fun n => d.c n * d.b n * Real.exp (d.lam n * t)) (d.obs d.ctrlVec t) := by
  convert d.hasSum_obs ht d.ctrlVec using 1
  funext n
  rw [ctrlVec_apply]
  field_simp [(d.wt_pos n).ne']

/-- `h` is square integrable on `(0, 1]` (it is bounded), so `b ∈ V`. -/
theorem memLp_obs_ctrlVec : MemLp (d.obs d.ctrlVec) 2 (μI 1) := by
  obtain ⟨M, hM⟩ := d.exists_abs_kernel_le
  refine MemLp.of_bound (d.aestronglyMeasurable_obs _ measurableSet_Ioc fun t ht => ht.1) M ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  rw [Real.norm_eq_abs, (d.hasSum_obs_ctrlVec ht.1).tsum_eq.symm]
  exact hM t ht.1

/-- `b ∈ V`. -/
def ctrlV : d.V := d.mkV d.ctrlVec d.memLp_obs_ctrlVec

/-- The control operator `B ∈ L(ℝ, V)`, `r ↦ r b` (Neumann boundary control). -/
def B : ℝ →L[ℝ] d.V := ContinuousLinearMap.toSpanSingleton ℝ d.ctrlV

/-- `B r = r b`. -/
theorem B_apply (r : ℝ) : d.B r = r • d.ctrlV := rfl

/-- The `X₋₁` component of `B r`. -/
theorem fstV_B (r : ℝ) : d.fstV (d.B r) = r • d.ctrlVec := by
  rw [B_apply, map_smul]; rfl

/-! ### The observation operator -/

/-- The constant `1` is square integrable on `(0, 1]`. -/
theorem memLp_one : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (μI 1) := memLp_const 1

/-- The ramp `1 - s` is square integrable on `(0, 1]`. -/
theorem memLp_ramp : MemLp (fun s : ℝ => 1 - s) 2 (μI 1) := by
  refine MemLp.of_bound ((by fun_prop : Continuous fun s : ℝ => 1 - s).aestronglyMeasurable) 1 ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hs.1, hs.2]

/-- The constant `1 ∈ L²(0, 1)`. -/
def oneL2 : L2 ℝ 1 := memLp_one.toLp _

/-- The ramp `s ↦ 1 - s ∈ L²(0, 1)`. -/
def rampL2 : L2 ℝ 1 := memLp_ramp.toLp _

/-- **The observation operator `C ∈ L(W, ℝ)`**: `C w = ⟪1, g⟫ - ⟪1 - s, g'⟫` in `L²(0, 1)`, with
`(g, g')` the second components of `w` and `A_V w` in `V` (the trace inequality in time). -/
def C : d.W →L[ℝ] ℝ :=
  (innerSL ℝ oneL2).comp (d.sndV.comp d.SV.domIncl) -
    (innerSL ℝ rampL2).comp (d.sndV.comp d.SV.domGen)

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (e : HilbertBasis ℕ ℝ X)

/-- **The trace formula in time**: `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds` with `g = C S(·) ι_W w`
and `g' = C S(·) A_{X,-1} ι_W w` (`app:boundary-heat-informative`). -/
theorem C_apply (w : d.W) :
    d.C w = (∫ s in Ioc 0 1, d.obs (d.toXm1 e (d.ιW e w)) s) -
      ∫ s in Ioc 0 1, (1 - s) * d.obs (d.genXm1 e (d.ιW e w)) s := by
  simp only [C, sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    MeasureTheory.L2.inner_def]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [memLp_one.coeFn_toLp, d.sndV_domIncl_ae e w] with s h1 h2
    rw [oneL2, h1, h2, RCLike.inner_apply, conj_trivial, mul_one]
  · refine integral_congr_ae ?_
    filter_upwards [memLp_ramp.coeFn_toLp, d.sndV_domGen_ae e w] with s h1 h2
    rw [rampL2, h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]

/-- `C` on `D(A)`: the modal formula. -/
theorem hasSum_C (w : d.W) (hw : d.ιW e w ∈ (d.SX e).generator.domain) :
    HasSum (fun n => d.c n * ⟪e n, d.ιW e w⟫_ℝ) (d.C w) := by
  rw [d.C_apply e w]
  exact d.hasSum_trace e _ ((mem_generator_domain_diag_iff e d.lam d.bddAbove_lam _).1 hw)

/-- `C S_W(t) w = C S(t) ι_W w` is the free output for `t > 0`. -/
theorem C_SW {t : ℝ} (ht : 0 < t) (w : d.W) :
    d.C (d.SW.real t w) = d.obs (d.toXm1 e (d.ιW e w)) t := by
  have hx : d.ιW e (d.SW.real t w) = (d.SX e).real t (d.ιW e w) := (d.consistent_ιW e).real t w
  have hD : d.ιW e (d.SW.real t w) ∈ (d.SX e).generator.domain := by
    rw [hx]; exact (isAnalytic_diagSemigroup e d.lam d.bddAbove_lam).mem_generator_domain ht _
  refine (d.hasSum_C e _ hD).unique ?_
  convert d.hasSum_obs_toXm1 e ht (d.ιW e w) using 1
  funext n
  rw [hx, inner_diagSemigroup_real _ _ _ ht.le]
  ring

/-! ### The system -/

/-- **The boundary-controlled heat system** in modal form. -/
def sys : System ℝ d.W X d.V ℝ where
  ιW := d.ιW e
  ιV := d.ιV e
  ιW_injective := d.ιW_injective e
  ιV_injective := d.ιV_injective e
  ιW_denseRange := d.denseRange_ιW e
  ιV_denseRange := d.denseRange_ιV e
  SW := d.SW
  SX := d.SX e
  SV := d.SV
  consistentW := d.consistent_ιW e
  consistentV := d.consistent_ιV e
  B := d.B
  C := d.C

/-- The embedding `W ↪ X` of the heat system. -/
@[simp] theorem sys_ιW : (d.sys e).ιW = d.ιW e := rfl
/-- The embedding `X ↪ V` of the heat system. -/
@[simp] theorem sys_ιV : (d.sys e).ιV = d.ιV e := rfl
/-- The semigroup on `W`. -/
@[simp] theorem sys_SW : (d.sys e).SW = d.SW := rfl
/-- The semigroup on `X` is the diagonal semigroup with the eigenvalues `λₙ`. -/
@[simp] theorem sys_SX : (d.sys e).SX = diagSemigroup e d.lam d.bddAbove_lam := rfl
/-- The semigroup on `V`. -/
@[simp] theorem sys_SV : (d.sys e).SV = d.SV := rfl
/-- The control operator. -/
@[simp] theorem sys_B : (d.sys e).B = d.B := rfl
/-- The observation operator. -/
@[simp] theorem sys_C : (d.sys e).C = d.C := rfl

/-- `W ↪ V` is the inclusion `D(A_V) ↪ V`. -/
theorem sys_ιWV (w : d.W) : (d.sys e).ιWV w = d.SV.domIncl w := d.ιV_ιW e w

/-- **`hyp:compat`**. -/
theorem compat : (d.sys e).Compat := by
  refine ⟨⟨1, fun v hv => ⟨d.SV.toDom ⟨v, hv⟩, ?_, ?_⟩⟩, ?_⟩
  · rw [sys_ιWV]; rfl
  · rw [one_mul]; exact d.SV.norm_toDom_le _
  · convert dense_univ (X := d.W)
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, sys_ιWV]
    exact d.SV.domIncl_mem w

/-- **`hyp:H2`** at horizon `1`. -/
theorem H2_one : (d.sys e).H2 1 := by
  refine ⟨1, fun w => ?_⟩
  have hae : (fun t => (d.sys e).C ((d.sys e).SW.real t w)) =ᵐ[μI 1]
      (d.sndV ((d.sys e).ιWV w) : ℝ → ℝ) := by
    rw [sys_ιWV, d.domIncl_eq_ιV e]
    have h1 : (fun t => (d.sys e).C ((d.sys e).SW.real t w)) =ᵐ[μI 1]
        d.obs (d.fstV (d.ιV e (d.ιW e w))) :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [d.fstV_ιV e, ← d.C_SW e ht.1 w]; rfl
    exact h1.trans (d.sndV_ae _).symm
  rw [eLpNorm_congr_ae hae, one_mul, ← Lp.enorm_def, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have := d.norm_V_sq ((d.sys e).ιWV w)
  nlinarith [norm_nonneg (d.sndV ((d.sys e).ιWV w)), norm_nonneg ((d.sys e).ιWV w),
    sq_nonneg ‖d.fstV ((d.sys e).ιWV w)‖]

/-- **`hyp:H2`** at every horizon. -/
theorem H2 (T : ℝ) : (d.sys e).H2 T := System.H2.of_pos (d.sys e) (d.H2_one e) one_pos T

/-! ### `hyp:H1` -/

/-- `‖A_{X,-1}‖_{L(X, X₋₁)} ≤ 1`. -/
theorem norm_genXm1_le : ‖d.genXm1 e‖ ≤ 1 :=
  (Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)

/-- The control convolution is integrable. -/
theorem integrableOn_conv {T : ℝ} (u : L2 ℝ T) :
    IntegrableOn (fun r => d.SV.real (T - r) (d.B (u r))) (Ioc 0 T) := by
  have hu : Integrable (u : ℝ → ℝ) (μI T) := (Lp.memLp u).integrable one_le_two
  exact d.SV.integrableOn_conv (d.B.integrable_comp hu)

/-- The `X₋₁` coordinates of the control convolution `∫₀ᵀ S_V(T - r) B u(r) dr`. -/
theorem fstV_conv_apply {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    d.fstV (∫ r in Ioc 0 T, d.SV.real (T - r) (d.B (u r))) n =
      d.b n / d.wt n * ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r := by
  have hint := d.integrableOn_conv u
  rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← inner_stdBasis]
  have h := (innerSL ℝ (stdBasis n)).integral_comp_comm (d.fstV.integrable_comp hint)
  simp only [innerSL_apply_apply] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hTr : 0 ≤ T - r := by linarith [hr.2]
  rw [inner_stdBasis, d.fstV_SV_real hTr, d.fstV_B, d.Sm_apply hTr, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, ctrlVec_apply]
  ring

/-- The state `x ∈ X` with the coordinates of `L_T u` is the control convolution in `V`. -/
theorem ιV_eq_conv {T : ℝ} (u : L2 ℝ T) (x : X)
    (hx : ∀ n, ⟪e n, x⟫_ℝ = d.b n * ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r) :
    d.ιV e x = ∫ r in Ioc 0 T, d.SV.real (T - r) (d.B (u r)) := by
  refine d.V_ext (ext_Xm1 fun n => ?_)
  rw [d.fstV_ιV e, d.toXm1_apply e, hx, d.fstV_conv_apply]
  field_simp [(d.wt_pos n).ne']

/-- **`hyp:H1`** in every positive time (`app:boundary-heat-informative`). -/
theorem H1 {T : ℝ} (hT : 0 < T) : (d.sys e).H1 T := by
  obtain ⟨C₀, hC₀⟩ := d.exists_control_bound e d.exists_abs_b_le d.exists_abs_kernelDeriv_le hT
  refine ⟨(‖d.ιV e‖ + 2) * C₀, fun u => ?_⟩
  obtain ⟨x, hx, hxn, h, hh⟩ := hC₀ u
  have hv := (d.mem_SV_generator_domain_iff e x).2 h
  refine ⟨d.SV.toDom ⟨d.ιV e x, hv⟩, ?_, ?_⟩
  · rw [sys_ιWV]
    exact d.ιV_eq_conv e u x hx
  · calc ‖d.SV.toDom ⟨d.ιV e x, hv⟩‖
        ≤ ‖d.ιV e x‖ + ‖d.SV.generator ⟨d.ιV e x, hv⟩‖ := d.SV.norm_toDom_le _
      _ ≤ ‖d.ιV e‖ * (C₀ * ‖u‖) + (C₀ * ‖u‖ + C₀ * ‖u‖) := by
          refine add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))) ?_
          rw [d.SV_generator_ιV e x h]
          refine (d.norm_V_le _).trans (add_le_add ?_ ?_)
          · rw [d.fstV_mkV]
            exact ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (d.norm_genXm1_le e))).trans hxn
          · rw [d.sndV_mkV]; exact hh
      _ = (‖d.ιV e‖ + 2) * C₀ * ‖u‖ := by ring

/-- The modal coordinates of the input-to-state map:
`⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪bₙ, u(r)⟫ dr`. -/
theorem inner_ιW_Lop {T : ℝ} (hT : 0 < T) (u : L2 ℝ T) (n : ℕ) :
    ⟪e n, (d.sys e).ιW ((d.sys e).Lop T u)⟫_ℝ =
      ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * ⟪d.b n, u r⟫_ℝ := by
  have hL := (d.sys e).ιWV_L (d.H1 e hT) hT (Lp.memLp u)
  rw [(d.sys e).Lop_apply (d.H1 e hT) hT u]
  set w := (d.sys e).L T u
  have h1 : d.toXm1 e (d.ιW e w) = d.fstV (∫ r in Ioc 0 T, d.SV.real (T - r) (d.B (u r))) := by
    rw [← d.fstV_ιV e]
    exact congrArg d.fstV hL
  have h2 := congrArg (fun a : Xm1 => a n) h1
  simp only [d.toXm1_apply e, d.fstV_conv_apply] at h2
  have hw := (d.wt_pos n).ne'
  rw [sys_ιW]
  have h3 : ⟪e n, d.ιW e w⟫_ℝ = d.b n * ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r := by
    field_simp at h2
    linarith [h2]
  rw [h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Approximate controllability** in every positive time, from the modal coordinates
(`System.approxControllable_of_modal`), for distinct eigenvalues and `bₙ ≠ 0`. -/
theorem approxControllable (hinj : Function.Injective d.lam) (hb0 : ∀ n, d.b n ≠ 0) {T : ℝ}
    (hT : 0 < T) : (d.sys e).ApproxControllable T := by
  obtain ⟨K, hK⟩ := d.exists_abs_b_le
  exact System.approxControllable_of_modal (d.sys e) e hinj (fun s hs => d.summable_exp hs)
    (β := d.b) (Cβ := K) (fun n => by rw [Real.norm_eq_abs]; exact hK n) hb0 hT (d.H1 e hT)
    (fun u n => d.inner_ιW_Lop e hT u n)

/-! ### `B⋆` on `D(A⋆)` and unboundedness -/

/-- **`B⋆` in modal form** (`app:control-realization`; `app:boundary-heat-informative`:
`B⋆φ = -φ(0)` for the heat equation): `B⋆ η = ∑ₙ bₙ ⟪eₙ, η⟫` for `η ∈ D(A⋆)`. -/
theorem hasSum_Bstar {η : X} (hη : η ∈ (d.sys e).A.adjoint.domain) :
    HasSum (fun n => d.b n * ⟪e n, η⟫_ℝ) ((d.sys e).Bstar ⟨η, hη⟩) := by
  have hA : (d.sys e).A.adjoint = (d.SX e).generator :=
    generator_adjoint_diag e d.lam d.bddAbove_lam
  have hηD : η ∈ (d.SX e).generator.domain := hA ▸ hη
  have hs := (mem_generator_domain_diag_iff e d.lam d.bddAbove_lam η).1 hηD
  have hsum : Summable fun n => (d.wt n * ⟪e n, η⟫_ℝ) ^ 2 := by
    refine (((Diagonal.summable_inner_sq e η).mul_left 2).add (hs.mul_left 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) fun n => ?_
    simp only [ModalData.wt]
    nlinarith [sq_nonneg (⟪e n, η⟫_ℝ + d.lam n * ⟪e n, η⟫_ℝ)]
  set ηm := mkL2 (fun n => d.wt n * ⟪e n, η⟫_ℝ) hsum with hηm
  set ζ : d.V →L[ℝ] ℝ := (innerSL ℝ ηm).comp d.fstV with hζdef
  have hζ : ∀ x : X, ζ ((d.sys e).ιV x) = ⟪((⟨η, hη⟩ : (d.sys e).A.adjoint.domain) : X), x⟫_ℝ := by
    intro x
    simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, sys_ιV, d.fstV_ιV e]
    refine (lp.hasSum_inner ηm (d.toXm1 e x)).unique ?_
    convert e.hasSum_inner_mul_inner η x using 1
    funext n
    rw [hηm, mkL2_apply, d.toXm1_apply e, RCLike.inner_apply, conj_trivial, real_inner_comm η]
    field_simp [(d.wt_pos n).ne']
  have h := System.inner_Bstar_of_dual (d.H1 e one_pos) one_pos ⟨η, hη⟩ ζ hζ 1
  have h1 : ⟪(d.sys e).Bstar ⟨η, hη⟩, (1 : ℝ)⟫_ℝ = (d.sys e).Bstar ⟨η, hη⟩ := by
    simp [RCLike.inner_apply]
  rw [show (d.sys e).Bstar ⟨η, hη⟩ = ζ ((d.sys e).B 1) from h1.symm.trans h]
  simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, sys_B, d.fstV_B,
    one_smul]
  convert lp.hasSum_inner ηm d.ctrlVec using 1
  funext n
  rw [hηm, mkL2_apply, ctrlVec_apply, RCLike.inner_apply, conj_trivial]
  field_simp [(d.wt_pos n).ne']

/-- **`B` is unbounded on `X`**: if `∑ bₙ² = ∞`, then `B 1 ∉ X`. -/
theorem B_one_not_mem_range (h : ¬ Summable fun n => d.b n ^ 2) :
    (d.sys e).B 1 ∉ Set.range (d.sys e).ιV := by
  rintro ⟨x, hx⟩
  apply h
  refine (Diagonal.summable_inner_sq e x).congr fun n => ?_
  have h2 := congrArg (fun v => d.fstV v n) hx
  simp only [sys_ιV, sys_B, d.fstV_ιV e, d.fstV_B, one_smul, d.toXm1_apply e,
    ctrlVec_apply] at h2
  have hw := (d.wt_pos n).ne'
  rw [div_eq_inv_mul] at h2
  rw [mul_left_cancel₀ (inv_ne_zero hw) h2]

/-- **`C` is unbounded on `X`**: if `∑ cₙ² = ∞`, there is no `K` with
`|C w| ≤ K ‖ι_W w‖` on `D(A)`. -/
theorem not_exists_bound_C (h : ¬ Summable fun n => d.c n ^ 2) :
    ¬ ∃ K : ℝ, ∀ w : d.W, (d.sys e).ιW w ∈ (d.sys e).A.domain →
      ‖(d.sys e).C w‖ ≤ K * ‖(d.sys e).ιW w‖ := by
  rintro ⟨K, hK⟩
  apply h
  refine summable_of_sum_range_le (c := K ^ 2) (fun n => sq_nonneg _) fun N => ?_
  set a : ℕ → ℝ := fun n => if n < N then d.c n else 0 with ha
  have ha0 : ∀ n ∉ Finset.range N, a n = 0 := fun n hn => by
    simp only [ha, Finset.mem_range] at hn ⊢; simp [hn]
  have has : Summable fun n => a n ^ 2 :=
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by rw [ha0 n hn]; ring
  set x : X := ModalData.toX e (mkL2 a has) with hx
  have hxe : ∀ n, ⟪e n, x⟫_ℝ = a n := fun n => by
    rw [hx, ModalData.toX, Diagonal.inner_diagMap, inner_stdBasis, mkL2_apply, one_mul]
  have hxD : x ∈ (d.SX e).generator.domain := by
    rw [mem_generator_domain_diag_iff]
    exact summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      rw [hxe, ha0 n hn]; ring
  obtain ⟨w, hw⟩ := d.exists_ιW_eq e hxD
  set S := ∑ n ∈ Finset.range N, d.c n ^ 2 with hSdef
  have hsumS : ∀ f : ℕ → ℝ, (∀ n, f n = if n < N then d.c n ^ 2 else 0) → HasSum f S := by
    intro f hf
    have h0 : HasSum f (∑ n ∈ Finset.range N, f n) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by
        rw [hf]; simp only [Finset.mem_range] at hn; simp [hn]
    have hs : ∑ n ∈ Finset.range N, f n = S := Finset.sum_congr rfl fun n hn => by
      rw [hf]; simp only [Finset.mem_range] at hn; simp [hn]
    rwa [hs] at h0
  have hCw : d.C w = S := by
    refine (d.hasSum_C e w (hw ▸ hxD)).unique (hsumS _ fun n => ?_)
    rw [hw, hxe]; simp only [ha]; split_ifs <;> ring
  have hnx : ‖x‖ ^ 2 = S := (Diagonal.hasSum_inner_sq e x).unique (hsumS _ fun n => by
    rw [hxe]; simp only [ha]; split_ifs <;> ring)
  have hb := hK w (by rw [sys_ιW, hw]; exact hxD)
  rw [sys_C, sys_ιW, hw, hCw, Real.norm_eq_abs] at hb
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => sq_nonneg _
  have h1 : S ≤ K * ‖x‖ := (le_abs_self S).trans hb
  have h2 : S ^ 2 ≤ K ^ 2 * S := by
    have := pow_le_pow_left₀ hS0 h1 2
    rwa [mul_pow, hnx] at this
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

end ControlData

end BoundaryHeat

end DataDrivenControl
