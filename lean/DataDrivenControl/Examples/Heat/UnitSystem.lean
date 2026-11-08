module

public import DataDrivenControl.Examples.Heat.Control
public import DataDrivenControl.System.ControlRealization

/-!
# The boundary-controlled heat equation with unit diffusivity

Paper: `ex:intro-pde` (`introduction.tex`), `app:boundary-heat-informative`
(`appendix_proofs.tex`).

The heat equation `∂ₜx = ∂_ξξ x` on `(0, 1)` with Neumann control `∂_ξ x(t, 0) = u(t)`,
`∂_ξ x(t, 1) = 0` and point observation `y(t) = x(t, ξ₀)`, `ξ₀ ∈ (0, 1)`, on
`W ↪ X = L²(0, 1) ↪ V` with the paper's `V` (`eq:heat-localized-V`) and `W = D(A_V)`
(`eq:heat-W-domain`), `Examples/Heat/Spaces`.  `Examples/Heat/System` rescales time to reach
every diffusivity `ν > 0`.

## Main declarations

* `C hξ₀ χ hχ : W χ →L[ℝ] ℝ`, the point observation (`C_apply`, `hasSum_C`: `C w = ∑ₙ cₙ ⟪eₙ, w⟫`
  on `D(A)`; `C_SW`: `C S(t) w = (S(t) w)(ξ₀)`).
* `unitHeatSystem hξ₀ χ hχ : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ`, with `B` the Neumann control
  (`Examples/Heat/Control`) and `C` the point observation.
* `unitHeatSystem_H1`, `unitHeatSystem_H2` (every horizon), `unitHeatSystem_compat`.
* `unitHeatSystem_Bstar` (`B⋆η = -η(0)`) and `B_not_mem_range` (`B 1 = b = -δ₀ ∉ X`).
* `unitHeatSystem_approxControllable` (in every `T > 0`, from the modal coordinates, since the
  `λₙ` are simple and `bₙ ≠ 0`; the paper uses `prop:fattorini-hautus`).

## Hypotheses on `χ`

The paper takes `χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀`.  The construction needs `χ ∈ C¹` with
`supp χ ⊆ (0, 1)` (`Cutoff`), and the observation only uses `χ(ξ₀) = 1`.

## Deviation from the paper: the definition of `C`

The paper obtains `C ∈ L(W, ℝ)` from the time trace of `F_w ∈ H¹(0, ∞; H¹(0, 1))` and the
embedding `H¹(0, 1) ↪ C[0, 1]`.  Here `C` is the trace formula in time
`C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds` with `g = (S(·) w)(ξ₀)` and `g' = (S(·) A_V w)(ξ₀)`.  It is
continuous on `W` because `|(S(t) z)(ξ₀)| ≤ eᵗ ‖F_z(t)‖` (`abs_orbit_le`) makes
`z ↦ (S(·) z)(ξ₀)` bounded from `V` to `L²(0, 1)` (`pointObs`), and it is the point evaluation at
`ξ₀` on `D(A) = H²_N(0, 1)` (`ModalData.hasSum_trace`).  The same bound gives `hyp:H2`, as in the
paper.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

open CosineBasis

/-! ### The point observation -/

/-- `(S(t) x)(ξ) = ∑ₙ eₙ(ξ) e^{λₙ t} ⟪eₙ, x⟫` for `x ∈ X` and `t > 0`. -/
theorem hasSum_orbit_toXm1 {t : ℝ} (ht : 0 < t) (x : L2 ℝ 1) (ξ : ℝ) :
    HasSum (fun n => obsCoeff ξ n * Real.exp (eig n * t) * ⟪cosBasis n, x⟫_ℝ)
      (orbit (heatModal.toXm1 cosBasis x) t ξ) := by
  convert hasSum_orbit ht (heatModal.toXm1 cosBasis x) ξ using 1
  funext n
  rw [orbCoeff_mul_toXm1, obsCoeff_eq_cosFun]
  ring

/-- `(S(t) A_{X,-1} x)(ξ) = ∑ₙ eₙ(ξ) λₙ e^{λₙ t} ⟪eₙ, x⟫` for `x ∈ X` and `t > 0`. -/
theorem hasSum_orbit_genXm1 {t : ℝ} (ht : 0 < t) (x : L2 ℝ 1) (ξ : ℝ) :
    HasSum (fun n => obsCoeff ξ n * eig n * Real.exp (eig n * t) * ⟪cosBasis n, x⟫_ℝ)
      (orbit (heatModal.genXm1 cosBasis x) t ξ) := by
  convert hasSum_orbit ht (heatModal.genXm1 cosBasis x) ξ using 1
  funext n
  rw [orbCoeff_mul_genXm1, obsCoeff_eq_cosFun]
  ring

/-- `t ↦ (S(t) z)(ξ)` is strongly measurable on `(0, 1]`. -/
theorem aestronglyMeasurable_orbit_apply (a : Xm1) (ξ : ℝ) :
    AEStronglyMeasurable (fun t => orbit a t ξ) (μI 1) :=
  (((BoundedContinuousFunction.lipschitz_eval_const ξ).continuous.comp_continuousOn
    (continuousOn_orbitL a)).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc

variable {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (χ : Cutoff) (hχ : χ ξ₀ = 1)

include hξ₀ hχ in
/-- **The point value is bounded by the localised norm**: for `z ∈ V`,
`‖(S(·) z)(ξ₀)‖_{L²(0,1)} ≤ e ‖F_z‖_{L²(0,∞)} ≤ e ‖z‖_V`, since `|(S(t) z)(ξ₀)| ≤ eᵗ ‖F_z(t)‖`
(`abs_orbit_le`). -/
theorem eLpNorm_orbit_apply_le (v : V χ) :
    eLpNorm (fun t => orbit (fstV χ v) t ξ₀) 2 (μI 1) ≤ ENNReal.ofReal (Real.exp 1 * ‖v‖) := by
  have h1 : eLpNorm (fun t => orbit (fstV χ v) t ξ₀) 2 (μI 1) ≤
      ENNReal.ofReal (Real.exp 1) * eLpNorm (fun t => orbitH χ t (fstV χ v)) 2 (μI 1) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (aestronglyMeasurable_orbit_apply _ _)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [Real.norm_eq_abs]
        exact (abs_orbit_le χ hξ₀ hχ ht.1 _).trans
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht.2) (norm_nonneg _))) 2
  have h2 : eLpNorm (fun t => orbitH χ t (fstV χ v)) 2 (μI 1) ≤ ‖sndV χ v‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (sndV_ae χ v)]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
  have h3 : ‖sndV χ v‖ ≤ ‖v‖ := by
    nlinarith [norm_V_sq χ v, norm_nonneg v, norm_nonneg (sndV χ v), sq_nonneg ‖fstV χ v‖]
  have h4 : ‖sndV χ v‖ₑ ≤ ENNReal.ofReal ‖v‖ := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal h3
  calc _ ≤ ENNReal.ofReal (Real.exp 1) * ‖sndV χ v‖ₑ := h1.trans (by gcongr)
    _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal ‖v‖ := by gcongr
    _ = _ := (ENNReal.ofReal_mul (Real.exp_pos 1).le).symm

include hξ₀ hχ in
/-- The point value `t ↦ (S(t) z)(ξ₀)` of `z ∈ V` is square integrable on `(0, 1]`. -/
theorem memLp_orbit_apply (v : V χ) : MemLp (fun t => orbit (fstV χ v) t ξ₀) 2 (μI 1) :=
  (eLpNorm_orbit_apply_le hξ₀ χ hχ v).trans_lt ENNReal.ofReal_lt_top

/-- **The point output** `V →L[ℝ] L²(0, 1)`, `z ↦ (S(·) z)(ξ₀)` on `(0, 1]`, of norm at most `e`. -/
def pointObs : V χ →L[ℝ] L2 ℝ 1 :=
  LinearMap.mkContinuous
    { toFun := fun v => (memLp_orbit_apply hξ₀ χ hχ v).toLp _
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp [orbit])
      map_smul' := fun r v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun t => by simp [orbit]) }
    (Real.exp 1) fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNorm_orbit_apply_le hξ₀ χ hχ v)

/-- `pointObs v` is `t ↦ (S(t) z)(ξ₀)`. -/
theorem pointObs_ae (v : V χ) :
    (pointObs hξ₀ χ hχ v : ℝ → ℝ) =ᵐ[μI 1] fun t => orbit (fstV χ v) t ξ₀ :=
  (memLp_orbit_apply hξ₀ χ hχ v).coeFn_toLp

/-- The ramp `s ↦ 1 - s` is square integrable on `(0, 1]`. -/
theorem memLp_ramp : MemLp (fun s : ℝ => 1 - s) 2 (μI 1) := by
  refine MemLp.of_bound ((by fun_prop : Continuous fun s : ℝ => 1 - s).aestronglyMeasurable) 1 ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hs.1, hs.2]

/-- The ramp `s ↦ 1 - s ∈ L²(0, 1)`. -/
def rampL2 : L2 ℝ 1 := memLp_ramp.toLp _

/-- **The point observation** `C ∈ L(W, ℝ)`: `C w = ⟪1, g⟫ - ⟪1 - s, g'⟫` in `L²(0, 1)`, with
`g = (S(·) w)(ξ₀)` and `g' = (S(·) A_V w)(ξ₀)` (the trace formula in time). -/
def C : W χ →L[ℝ] ℝ :=
  (innerSL ℝ oneL2).comp ((pointObs hξ₀ χ hχ).comp (SV χ).domIncl) -
    (innerSL ℝ rampL2).comp ((pointObs hξ₀ χ hχ).comp (SV χ).domGen)

/-- **The trace formula in time**: `C w = ∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds` with `g = (S(·) x)(ξ₀)`,
`g' = (S(·) A_{X,-1} x)(ξ₀)` and `x = ι_W w`. -/
theorem C_apply (w : W χ) :
    C hξ₀ χ hχ w = (∫ s in Ioc 0 1, orbit (heatModal.toXm1 cosBasis (ιW χ w)) s ξ₀) -
      ∫ s in Ioc 0 1, (1 - s) * orbit (heatModal.genXm1 cosBasis (ιW χ w)) s ξ₀ := by
  simp only [C, sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  rw [toXm1_ιW, ← fstV_domGen]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [coeFn_oneL2, pointObs_ae hξ₀ χ hχ ((SV χ).domIncl w)] with s h1 h2
    rw [h1, h2, RCLike.inner_apply, conj_trivial, mul_one]
  · refine integral_congr_ae ?_
    filter_upwards [memLp_ramp.coeFn_toLp, pointObs_ae hξ₀ χ hχ ((SV χ).domGen w)] with s h1 h2
    rw [rampL2, h1, h2, RCLike.inner_apply, conj_trivial, mul_comm]

/-- **`C` on `D(A)`**: `C w = ∑ₙ cₙ ⟪eₙ, ι_W w⟫` (`ModalData.hasSum_trace`). -/
theorem hasSum_C (w : W χ) (hw : ιW χ w ∈ SX.generator.domain) :
    HasSum (fun n => obsCoeff ξ₀ n * ⟪cosBasis n, ιW χ w⟫_ℝ) (C hξ₀ χ hχ w) := by
  rw [C_apply]
  exact heatModal.hasSum_trace (abs_obsCoeff_le ξ₀) (Diagonal.summable_inner_sq cosBasis _)
    ((mem_generator_domain_diag_iff cosBasis heatModal.lam heatModal.bddAbove_lam _).1 hw)
    (fun s hs => hasSum_orbit_toXm1 hs.1 _ ξ₀) (fun s hs => hasSum_orbit_genXm1 hs.1 _ ξ₀)

/-- **The free output**: `C S(t) w = (S(t) w)(ξ₀)` for `t > 0`. -/
theorem C_SW {t : ℝ} (ht : 0 < t) (w : W χ) :
    C hξ₀ χ hχ ((SW χ).real t w) = orbit (heatModal.toXm1 cosBasis (ιW χ w)) t ξ₀ := by
  have hx : ιW χ ((SW χ).real t w) = SX.real t (ιW χ w) := (consistent_ιW χ).real t w
  have hD : ιW χ ((SW χ).real t w) ∈ SX.generator.domain := by
    rw [hx]
    exact (isAnalytic_diagSemigroup cosBasis heatModal.lam
      heatModal.bddAbove_lam).mem_generator_domain ht _
  refine (hasSum_C hξ₀ χ hχ _ hD).unique ?_
  convert hasSum_orbit_toXm1 ht (ιW χ w) ξ₀ using 1
  funext n
  rw [hx, inner_diagSemigroup_real _ _ _ ht.le, heatModal_lam]
  ring

/-! ### The system -/

/-- **The boundary-controlled heat system with unit diffusivity** (`ex:intro-pde` with `ν = 1`):
`W = D(A_V) ↪ L²(0, 1) ↪ V`, `V` as in `eq:heat-localized-V`. -/
def unitHeatSystem : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ where
  ιW := ιW χ
  ιV := ιV χ
  ιW_injective := ιW_injective χ
  ιV_injective := ιV_injective χ
  ιW_denseRange := denseRange_ιW χ
  ιV_denseRange := denseRange_ιV χ
  SW := SW χ
  SX := SX
  SV := SV χ
  consistentW := consistent_ιW χ
  consistentV := consistent_ιV χ
  B := B χ
  C := C hξ₀ χ hχ

/-- The embedding `W ↪ X`. -/
@[simp] theorem unitHeatSystem_ιW : (unitHeatSystem hξ₀ χ hχ).ιW = ιW χ := rfl
/-- The embedding `X ↪ V`. -/
@[simp] theorem unitHeatSystem_ιV : (unitHeatSystem hξ₀ χ hχ).ιV = ιV χ := rfl
/-- The control operator. -/
@[simp] theorem unitHeatSystem_B : (unitHeatSystem hξ₀ χ hχ).B = B χ := rfl

/-- `W ↪ V` is the inclusion `D(A_V) ↪ V`. -/
theorem unitHeatSystem_ιWV (w : W χ) : (unitHeatSystem hξ₀ χ hχ).ιWV w = (SV χ).domIncl w :=
  ιV_ιW χ w

/-- **`hyp:compat`** (`W = D(A_V)` by construction). -/
theorem unitHeatSystem_compat : (unitHeatSystem hξ₀ χ hχ).Compat := by
  refine ⟨⟨1, fun v hv => ⟨(SV χ).toDom ⟨v, hv⟩, ?_, ?_⟩⟩, ?_⟩
  · rw [unitHeatSystem_ιWV]; rfl
  · rw [one_mul]; exact (SV χ).norm_toDom_le _
  · convert dense_univ (X := W χ)
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, unitHeatSystem_ιWV]
    exact (SV χ).domIncl_mem w

/-- `‖A_{X,-1}‖ ≤ 1`. -/
theorem norm_genXm1_le : ‖heatModal.genXm1 cosBasis‖ ≤ 1 :=
  (Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)

/-- **`hyp:H1`** at every positive horizon (`app:boundary-heat-informative`). -/
theorem unitHeatSystem_H1_pos {T : ℝ} (hT : 0 < T) : (unitHeatSystem hξ₀ χ hχ).H1 T := by
  obtain ⟨C₀, hC₀⟩ := exists_control_bound χ hT
  refine ⟨(‖ιV χ‖ + 2) * C₀, fun u => ?_⟩
  obtain ⟨x, hx, hxn, h, hh⟩ := hC₀ u
  have hv := (mem_SV_generator_domain_iff χ x).2 h
  refine ⟨(SV χ).toDom ⟨ιV χ x, hv⟩, ?_, ?_⟩
  · rw [unitHeatSystem_ιWV]
    exact ιV_eq_conv χ u x hx
  · calc ‖(SV χ).toDom ⟨ιV χ x, hv⟩‖
        ≤ ‖ιV χ x‖ + ‖(SV χ).generator ⟨ιV χ x, hv⟩‖ := (SV χ).norm_toDom_le _
      _ ≤ ‖ιV χ‖ * (C₀ * ‖u‖) + (C₀ * ‖u‖ + C₀ * ‖u‖) := by
          refine add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))) ?_
          rw [SV_generator_ιV χ x h]
          refine (norm_V_le χ _).trans (add_le_add ?_ ?_)
          · rw [fstV_mkV]
            exact ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) norm_genXm1_le)).trans hxn
          · rw [sndV_mkV]; exact hh
      _ = (‖ιV χ‖ + 2) * C₀ * ‖u‖ := by ring

/-- **`hyp:H1`** at every horizon. -/
theorem unitHeatSystem_H1 (T : ℝ) : (unitHeatSystem hξ₀ χ hχ).H1 T :=
  System.H1.of_pos (unitHeatSystem hξ₀ χ hχ) (unitHeatSystem_H1_pos hξ₀ χ hχ one_pos) one_pos T

/-- **`hyp:H2`** at horizon `1`: `C S(t) w = (S(t) w)(ξ₀)` and
`‖(S(·) w)(ξ₀)‖_{L²(0,1)} ≤ e ‖w‖_V` (`eLpNorm_orbit_apply_le`). -/
theorem unitHeatSystem_H2_one : (unitHeatSystem hξ₀ χ hχ).H2 1 := by
  refine ⟨Real.exp 1, fun w => ?_⟩
  have hae : (fun t => (unitHeatSystem hξ₀ χ hχ).C ((unitHeatSystem hξ₀ χ hχ).SW.real t w))
      =ᵐ[μI 1] fun t => orbit (fstV χ ((unitHeatSystem hξ₀ χ hχ).ιWV w)) t ξ₀ :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      (C_SW hξ₀ χ hχ ht.1 w).trans (by rw [unitHeatSystem_ιWV, toXm1_ιW])
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_orbit_apply_le hξ₀ χ hχ _

/-- **`hyp:H2`** at every horizon. -/
theorem unitHeatSystem_H2 (T : ℝ) : (unitHeatSystem hξ₀ χ hχ).H2 T :=
  System.H2.of_pos (unitHeatSystem hξ₀ χ hχ) (unitHeatSystem_H2_one hξ₀ χ hχ) one_pos T

/-- **`B` is unbounded on `X`**: `B 1 = b = -δ₀ ∉ X` (`∑ₙ bₙ² = ∞`). -/
theorem B_not_mem_range : B χ 1 ∉ Set.range (ιV χ) := by
  rintro ⟨x, hx⟩
  apply not_summable_ctrlCoeff_sq
  refine (Diagonal.summable_inner_sq cosBasis x).congr fun n => ?_
  have h := congrArg (fun v => fstV χ v n) hx
  simp only [fstV_ιV, fstV_B, one_smul, ModalData.toXm1_apply, ctrlVec_apply, heatModal_wt] at h
  rw [div_eq_inv_mul] at h
  rw [mul_left_cancel₀ (inv_ne_zero (one_sub_eig_pos n).ne') h]

/-- **`B⋆` in modal form**: `B⋆η = ∑ₙ bₙ ⟪eₙ, η⟫` on `D(A⋆)` (`System.inner_Bstar_of_dual`). -/
theorem hasSum_unitHeatSystem_Bstar {η : L2 ℝ 1}
    (hη : η ∈ (unitHeatSystem hξ₀ χ hχ).A.adjoint.domain) :
    HasSum (fun n => ctrlCoeff n * ⟪cosBasis n, η⟫_ℝ)
      ((unitHeatSystem hξ₀ χ hχ).Bstar ⟨η, hη⟩) := by
  have hA : (unitHeatSystem hξ₀ χ hχ).A.adjoint = SX.generator :=
    generator_adjoint_diag cosBasis heatModal.lam heatModal.bddAbove_lam
  have hηD : η ∈ SX.generator.domain := hA ▸ hη
  have hs := (mem_generator_domain_diag_iff cosBasis heatModal.lam heatModal.bddAbove_lam η).1 hηD
  have hsum : Summable fun n => ((1 - eig n) * ⟪cosBasis n, η⟫_ℝ) ^ 2 := by
    refine (((Diagonal.summable_inner_sq cosBasis η).mul_left 2).add
      (hs.mul_left 2)).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => ?_
    simp only [heatModal_lam]
    nlinarith [sq_nonneg (⟪cosBasis n, η⟫_ℝ + eig n * ⟪cosBasis n, η⟫_ℝ)]
  set ηm := mkL2 (fun n => (1 - eig n) * ⟪cosBasis n, η⟫_ℝ) hsum with hηm
  set ζ : V χ →L[ℝ] ℝ := (innerSL ℝ ηm).comp (fstV χ) with hζdef
  have hζ : ∀ x : L2 ℝ 1, ζ ((unitHeatSystem hξ₀ χ hχ).ιV x) =
      ⟪((⟨η, hη⟩ : (unitHeatSystem hξ₀ χ hχ).A.adjoint.domain) : L2 ℝ 1), x⟫_ℝ := by
    intro x
    simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, unitHeatSystem_ιV,
      fstV_ιV]
    refine (lp.hasSum_inner ηm (heatModal.toXm1 cosBasis x)).unique ?_
    convert cosBasis.hasSum_inner_mul_inner η x using 1
    funext n
    rw [hηm, mkL2_apply, heatModal.toXm1_apply, heatModal_wt, RCLike.inner_apply, conj_trivial,
      real_inner_comm η]
    field_simp [(one_sub_eig_pos n).ne']
  have h := System.inner_Bstar_of_dual (unitHeatSystem_H1_pos hξ₀ χ hχ one_pos) one_pos ⟨η, hη⟩
    ζ hζ 1
  have h1 : ⟪(unitHeatSystem hξ₀ χ hχ).Bstar ⟨η, hη⟩, (1 : ℝ)⟫_ℝ =
      (unitHeatSystem hξ₀ χ hχ).Bstar ⟨η, hη⟩ := by
    simp [RCLike.inner_apply]
  rw [show (unitHeatSystem hξ₀ χ hχ).Bstar ⟨η, hη⟩ = ζ ((unitHeatSystem hξ₀ χ hχ).B 1) from
    h1.symm.trans h]
  simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, unitHeatSystem_B,
    fstV_B, one_smul]
  convert lp.hasSum_inner ηm ctrlVec using 1
  funext n
  rw [hηm, mkL2_apply, ctrlVec_apply, RCLike.inner_apply, conj_trivial]
  field_simp [(one_sub_eig_pos n).ne']

/-- **`B⋆` is minus the trace at `0`** (`app:boundary-heat-informative`, `B⋆φ = -φ(0)`): for
`η ∈ D(A⋆) = H²_N(0, 1)` the class of `φ`, `B⋆ η = -φ(0)`. -/
theorem unitHeatSystem_Bstar {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') {η : L2 ℝ 1}
    (hη : η ∈ (unitHeatSystem hξ₀ χ hχ).A.adjoint.domain) (hηφ : (η : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (unitHeatSystem hξ₀ χ hχ).Bstar ⟨η, hη⟩ = -φ 0 :=
  (hasSum_unitHeatSystem_Bstar hξ₀ χ hχ hη).unique (PDE.hasSum_ctrlCoeff_mul_inner h hηφ)

/-! ### Approximate controllability -/

/-- The modal coordinates of the input-to-state map:
`⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪bₙ, u(r)⟫ dr`. -/
theorem inner_ιW_Lop {T : ℝ} (hT : 0 < T) (u : L2 ℝ T) (n : ℕ) :
    ⟪cosBasis n, (unitHeatSystem hξ₀ χ hχ).ιW ((unitHeatSystem hξ₀ χ hχ).Lop T u)⟫_ℝ =
      ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * ⟪ctrlCoeff n, u r⟫_ℝ := by
  have hH1 := unitHeatSystem_H1_pos hξ₀ χ hχ hT
  have hL := (unitHeatSystem hξ₀ χ hχ).ιWV_L hH1 hT (Lp.memLp u)
  rw [(unitHeatSystem hξ₀ χ hχ).Lop_apply hH1 hT u]
  set w := (unitHeatSystem hξ₀ χ hχ).L T u
  have h1 : heatModal.toXm1 cosBasis (ιW χ w) =
      fstV χ (∫ r in Ioc 0 T, (SV χ).real (T - r) (B χ (u r))) := by
    rw [← fstV_ιV]
    exact congrArg (fstV χ) hL
  have h2 := congrArg (fun a : Xm1 => a n) h1
  simp only [heatModal.toXm1_apply, fstV_conv_apply, heatModal_wt] at h2
  have hw := (one_sub_eig_pos n).ne'
  have h3 : ⟪cosBasis n, ιW χ w⟫_ℝ =
      ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := by
    calc ⟪cosBasis n, ιW χ w⟫_ℝ = (1 - eig n) * ((1 - eig n)⁻¹ * ⟪cosBasis n, ιW χ w⟫_ℝ) := by
          rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      _ = (1 - eig n) * (ctrlCoeff n / (1 - eig n) *
            ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r) := by rw [h2]
      _ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := by field_simp
  rw [unitHeatSystem_ιW, h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Approximate controllability** of `(A, B)` in every `T > 0` (`ex:boundary-heat-informative`;
from the modal coordinates, since the `λₙ` are simple and `bₙ ≠ 0`, instead of through
`prop:fattorini-hautus`). -/
theorem unitHeatSystem_approxControllable {T : ℝ} (hT : 0 < T) :
    (unitHeatSystem hξ₀ χ hχ).ApproxControllable T :=
  System.approxControllable_of_modal (unitHeatSystem hξ₀ χ hχ) cosBasis eig_injective
    (fun s hs => heatModal.summable_exp hs) (β := ctrlCoeff) (Cβ := Real.sqrt 2)
    (fun n => by rw [Real.norm_eq_abs]; exact abs_ctrlCoeff_le n) ctrlCoeff_ne_zero hT
    (unitHeatSystem_H1_pos hξ₀ χ hχ hT) (fun u n => inner_ιW_Lop hξ₀ χ hχ hT u n)

end BoundaryHeat

end DataDrivenControl
