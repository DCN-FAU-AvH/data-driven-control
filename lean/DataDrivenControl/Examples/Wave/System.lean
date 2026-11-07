module

public import DataDrivenControl.Examples.Wave.Spaces
public import DataDrivenControl.System.ControlRealization

/-!
# The wave equation with Dirichlet control: the main theorems

Paper: `ex:intro-wave` (`introduction.tex`); Section 7 (`numerics.tex`) calls the wave group
non-analytic.

The system `waveSystem s f c q : System ℝ X X V ℝ` of `Examples/Wave/Spaces` (modal model,
`X = WithLp 2 (X₁ × X₂)` with Hilbert bases `s`, `f`, `W = X`, `V` the weighted `ℓ²` in the
energy modes, modes numbered from `0` with `ωₙ = c (n + 1) π`) satisfies the paper's standing
assumptions, and its operators are those of the PDE in modal form.

## Main declarations

* `waveSystem_H1` (**`hyp:H1`** at every horizon): at `T = 2/c` the state reached is
  `aₙ = -c √2 ∫₀ᵀ sin(ωₙ r) u(r) dr`, `bₙ = c √2 ∫₀ᵀ cos(ωₙ r) u(r) dr`, and Bessel's inequality
  for the families `cos(ωₙ ·)`, `sin(ωₙ ·)`, orthogonal on every interval of length `2/c`
  (`Examples/Wave/Fourier`), gives `‖L_T u‖_X ≤ 2 √c ‖u‖`; `System.H1.of_pos`
  (`app:finite-horizon-output`) extends it to every horizon, which replaces splitting `[0, T]`
  into intervals of length `2/c`.
* `waveSystem_H2` (**`hyp:H2`** at every horizon): `C S(t) x = ∑ₙ qₙ (aₙ cos(ωₙ t) + bₙ sin(ωₙ t))`
  and the synthesis inequality give `‖C S(·) x‖_{L²(0, 2/c)} ≤ √(2/c) ‖x‖_V`, because the
  weight of `V` dominates `qₙ²`.
* `waveSystem_compat` (**`hyp:compat`**, in `Examples/Wave/Spaces`).
* The ties to the PDE in modal form: `waveSystem_SX` (`S_X` is the block-rotation group with
  `ωₙ = c (n + 1) π`), `hasSum_waveSystem_C` (`C x = ∑ₙ qₙ aₙ`), `inner_waveSystem_Lop` (the
  modal coordinates of `L_T u`, i.e. the variation-of-constants formula for
  `aₙ' = ωₙ bₙ`, `bₙ' = -ωₙ aₙ + c √2 u`), `hasSum_waveSystem_Bstar` (`B⋆ η = ∑ₙ c √2 bₙ(η)` on
  `D(A⋆)`), `waveSystem_B_not_mem_range`, `waveSystem_B_apply_not_mem_range` (`B` is unbounded
  on `X`: `B u ∉ X` for `u ≠ 0`) and `norm_waveSystem_C_le`
  (`C` is bounded on `X`, automatic since `W = X`).
* `waveSystem_not_isAnalytic`: the wave group is not analytic (Section 7).
* `exists_wave`: **`ex:intro-wave`** in existential form.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Wave

variable {X₁ X₂ : Type*} [NormedAddCommGroup X₁] [InnerProductSpace ℝ X₁] [CompleteSpace X₁]
  [NormedAddCommGroup X₂] [InnerProductSpace ℝ X₂] [CompleteSpace X₂]
  (s : HilbertBasis ℕ ℝ X₁) (f : HilbertBasis ℕ ℝ X₂) (c : ℝ) (q : X₁)

/-! ### The control convolution in modal coordinates -/

theorem integrableOn_conv {T : ℝ} (u : L2 ℝ T) :
    IntegrableOn
      (fun r => (waveSystem s f c q).SV.real (T - r) ((waveSystem s f c q).B (u r))) (Ioc 0 T) :=
  (waveSystem s f c q).SV.integrableOn_conv
    ((waveSystem s f c q).B.integrable_comp ((Lp.memLp u).integrable one_le_two))

/-- First `V`-coordinates of the control convolution `∫₀ᵀ S_V(T - r) B u(r) dr`. -/
theorem inner_fst_convV {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    ⟪stdBasis n, ((waveSystem s f c q).convV T u).fst⟫_ℝ =
      sw s c q n * (c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.sin (freq c n * (T - r)) * u r) := by
  rw [System.convV, inner_fst_integral (integrableOn_conv s f c q u), ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [waveSystem_SV, waveSystem_B, Bop_apply,
    Rotation.inner_fst_rotGroup_real _ _ _ (sub_nonneg.2 hr.2), WithLp.smul_fst, WithLp.smul_snd,
    real_inner_smul_right, real_inner_smul_right, inner_fst_ctrlVec, inner_snd_ctrlVec]
  ring

/-- Second `V`-coordinates of the control convolution `∫₀ᵀ S_V(T - r) B u(r) dr`. -/
theorem inner_snd_convV {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    ⟪stdBasis n, ((waveSystem s f c q).convV T u).snd⟫_ℝ =
      sw s c q n * (c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.cos (freq c n * (T - r)) * u r) := by
  rw [System.convV, inner_snd_integral (integrableOn_conv s f c q u), ← integral_const_mul,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [waveSystem_SV, waveSystem_B, Bop_apply,
    Rotation.inner_snd_rotGroup_real _ _ _ (sub_nonneg.2 hr.2), WithLp.smul_fst, WithLp.smul_snd,
    real_inner_smul_right, real_inner_smul_right, inner_fst_ctrlVec, inner_snd_ctrlVec]
  ring

/-! ### `hyp:H1` -/

/-- **`hyp:H1`** at the horizon `2/c`: `‖L_{2/c} u‖_X ≤ 2 √c ‖u‖` (Bessel's inequality). -/
theorem waveSystem_H1_period (hc : 0 < c) : (waveSystem s f c q).H1 (2 / c) := by
  refine ⟨2 * Real.sqrt c, fun u => ?_⟩
  have hsin : ∀ n, ∫ r in Ioc 0 (2 / c), Real.sin (freq c n * (2 / c - r)) * u r =
      -∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * u r := fun n => by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [mul_sub, Real.sin_sub, sin_freq_mul_period hc.ne', cos_freq_mul_period hc.ne']
    ring
  have hcos : ∀ n, ∫ r in Ioc 0 (2 / c), Real.cos (freq c n * (2 / c - r)) * u r =
      ∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * u r := fun n => by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [mul_sub, Real.cos_sub, sin_freq_mul_period hc.ne', cos_freq_mul_period hc.ne']
    ring
  have hs2 := summable_sq_integral_sin hc u
  have hc2 := summable_sq_integral_cos hc u
  obtain ⟨w, hw⟩ := Rotation.exists_coord_eq s f
    (fun n => -(c * Real.sqrt 2 * ∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * u r))
    (fun n => c * Real.sqrt 2 * ∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * u r)
    ((hs2.mul_left ((c * Real.sqrt 2) ^ 2)).congr fun n => by ring)
    ((hc2.mul_left ((c * Real.sqrt 2) ^ 2)).congr fun n => by ring)
  refine ⟨w, ?_, ?_⟩
  · show (waveSystem s f c q).ιWV w = (waveSystem s f c q).convV (2 / c) u
    rw [waveSystem_ιWV]
    refine Rotation.ext_coord stdBasis stdBasis (fun n => ?_) fun n => ?_
    · rw [inner_fst_ιV, inner_fst_convV, (hw n).1, hsin n]
      ring
    · rw [inner_snd_ιV, inner_snd_convV, (hw n).2, hcos n]
  · have h1 : ‖w‖ ^ 2 = (c * Real.sqrt 2) ^ 2 *
        (∑' n, (∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * u r) ^ 2 +
          ∑' n, (∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * u r) ^ 2) := by
      refine (Rotation.hasSum_coord_sq s f w).unique ?_
      convert (hs2.hasSum.add hc2.hasSum).mul_left ((c * Real.sqrt 2) ^ 2) using 1
      funext n
      rw [(hw n).1, (hw n).2]
      ring
    have h2 := (le_div_iff₀ hc).1 (tsum_sq_integral_sin_le hc u)
    have h3 := (le_div_iff₀ hc).1 (tsum_sq_integral_cos_le hc u)
    have hγ2 : (c * Real.sqrt 2) ^ 2 = 2 * c ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have h4 : ‖w‖ ^ 2 ≤ (2 * Real.sqrt c * ‖u‖) ^ 2 := by
      rw [h1, hγ2, mul_pow, mul_pow, Real.sq_sqrt hc.le]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity : (0 : ℝ) ≤ 2 * c)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- **`hyp:H1`** at every horizon (`ex:intro-wave`). -/
theorem waveSystem_H1 (hc : 0 < c) (T : ℝ) : (waveSystem s f c q).H1 T :=
  System.H1.of_pos _ (waveSystem_H1_period s f c q hc) (by positivity) T

/-- **The input-to-state map in modal coordinates**: for `T > 0` and `u ∈ L²(0, T)`,
`aₙ(T) = c √2 ∫₀ᵀ sin(ωₙ (T - r)) u(r) dr` and `bₙ(T) = c √2 ∫₀ᵀ cos(ωₙ (T - r)) u(r) dr`, the
variation-of-constants formula for `aₙ' = ωₙ bₙ`, `bₙ' = -ωₙ aₙ + c √2 u`, `x(0) = 0`: `B` is the
Dirichlet boundary control. -/
theorem inner_waveSystem_Lop (hc : 0 < c) {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    ⟪s n, ((waveSystem s f c q).Lop T u).fst⟫_ℝ =
        c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.sin (freq c n * (T - r)) * u r ∧
      ⟪f n, ((waveSystem s f c q).Lop T u).snd⟫_ℝ =
        c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.cos (freq c n * (T - r)) * u r := by
  have hH1 := waveSystem_H1_period s f c q hc
  have hT0 : (0 : ℝ) < 2 / c := by positivity
  rw [(waveSystem s f c q).Lop_apply hH1 hT0 u]
  have hL := (waveSystem s f c q).ιWV_L hH1 hT0 (Lp.memLp u)
  rw [waveSystem_ιWV] at hL
  constructor
  · have h := congrArg (fun v : Vsp => ⟪stdBasis n, v.fst⟫_ℝ) hL
    simp only [inner_fst_ιV, inner_fst_convV] at h
    exact mul_left_cancel₀ (sw_pos s c q n).ne' h
  · have h := congrArg (fun v : Vsp => ⟪stdBasis n, v.snd⟫_ℝ) hL
    simp only [inner_snd_ιV, inner_snd_convV] at h
    exact mul_left_cancel₀ (sw_pos s c q n).ne' h

/-! ### `hyp:H2` -/

/-- **`hyp:H2`** at the horizon `2/c`: `‖C S(·) x‖_{L²(0, 2/c)} ≤ √(2/c) ‖x‖_V` (the synthesis
inequality, with `qₙ² ≤ vₙ`). -/
theorem waveSystem_H2_period (hc : 0 < c) : (waveSystem s f c q).H2 (2 / c) := by
  refine ⟨Real.sqrt (2 / c), fun x => ?_⟩
  have hq := Diagonal.summable_inner_sq s q
  have ha := Diagonal.summable_inner_sq s x.fst
  have hb := Diagonal.summable_inner_sq f x.snd
  have hqn : ∀ n, ⟪s n, q⟫_ℝ ^ 2 ≤ ‖q‖ ^ 2 := fun n => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_inner_le_norm s q n) 2
  have hα : Summable fun n => |⟪s n, q⟫_ℝ * ⟪s n, x.fst⟫_ℝ| :=
    (hq.add ha).of_nonneg_of_le (fun n => abs_nonneg _) fun n => by
      rw [abs_mul]
      nlinarith [sq_abs ⟪s n, q⟫_ℝ, sq_abs ⟪s n, x.fst⟫_ℝ,
        sq_nonneg (|⟪s n, q⟫_ℝ| - |⟪s n, x.fst⟫_ℝ|)]
  have hβ : Summable fun n => |⟪s n, q⟫_ℝ * ⟪f n, x.snd⟫_ℝ| :=
    (hq.add hb).of_nonneg_of_le (fun n => abs_nonneg _) fun n => by
      rw [abs_mul]
      nlinarith [sq_abs ⟪s n, q⟫_ℝ, sq_abs ⟪f n, x.snd⟫_ℝ,
        sq_nonneg (|⟪s n, q⟫_ℝ| - |⟪f n, x.snd⟫_ℝ|)]
  have hα2 : Summable fun n => (⟪s n, q⟫_ℝ * ⟪s n, x.fst⟫_ℝ) ^ 2 :=
    (ha.mul_left (‖q‖ ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hqn n) (sq_nonneg _)
  have hβ2 : Summable fun n => (⟪s n, q⟫_ℝ * ⟪f n, x.snd⟫_ℝ) ^ 2 :=
    (hb.mul_left (‖q‖ ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hqn n) (sq_nonneg _)
  have hae : (fun t => (waveSystem s f c q).C ((waveSystem s f c q).SW.real t x)) =ᵐ[μI (2 / c)]
      fun t => ∑' n, (⟪s n, q⟫_ℝ * ⟪s n, x.fst⟫_ℝ * Real.cos (freq c n * t) +
        ⟪s n, q⟫_ℝ * ⟪f n, x.snd⟫_ℝ * Real.sin (freq c n * t)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    dsimp only
    rw [← (hasSum_waveSystem_C s f c q _).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [waveSystem_SW, Rotation.inner_fst_rotGroup_real s f (freq c) ht.1.le]
    ring
  rw [eLpNorm_congr_ae hae]
  refine (eLpNorm_tsum_le hc hα hβ hα2 hβ2).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / c), waveSystem_ιWV]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (norm_nonneg (ιV s f c q x))]
  refine Real.sqrt_le_sqrt (hasSum_le (fun n => ?_) (hα2.add hβ2).hasSum
    (hasSum_norm_ιV_sq s f c q x))
  have h := sq_inner_le_vwt s c q n
  rw [mul_pow, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg ⟪s n, x.fst⟫_ℝ),
    mul_le_mul_of_nonneg_right h (sq_nonneg ⟪f n, x.snd⟫_ℝ)]

/-- **`hyp:H2`** at every horizon (`ex:intro-wave`). -/
theorem waveSystem_H2 (hc : 0 < c) (T : ℝ) : (waveSystem s f c q).H2 T :=
  System.H2.of_pos _ (waveSystem_H2_period s f c q hc) (by positivity) T

/-- **`B` is unbounded on `X`**: `B u ∉ X` for every `u ≠ 0` (`c ≠ 0`). -/
theorem waveSystem_B_apply_not_mem_range (hc : c ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    (waveSystem s f c q).B u ∉ Set.range (waveSystem s f c q).ιV := by
  rintro ⟨x, hx⟩
  refine waveSystem_B_not_mem_range s f c q hc ⟨u⁻¹ • x, ?_⟩
  rw [map_smul, hx, waveSystem_B, Bop_apply, Bop_apply, smul_smul, inv_mul_cancel₀ hu]

/-! ### `B⋆` on `D(A⋆)` -/

/-- **`B⋆` in modal form** (`app:control-realization`): `B⋆ η = ∑ₙ c √2 bₙ(η)` for
`η ∈ D(A⋆)`, `bₙ(η) = ⟪fₙ, η₂⟫`.  The series converges because `D(A⋆)` has
`∑ₙ ωₙ² bₙ(η)² < ∞`.  In function language (`Wave.PDE.waveSystemL2_Bstar`): for `η = (φ, ψ) ∈ L² × H⁻¹` with
the energy inner product of `X`, `bₙ(η) = ⟨ψ, sₙ⟩ / ωₙ` and `sₙ'(0) = √2 nπ` (paper's `n`), so
`B⋆ η = ∑ₙ √2 ⟨ψ, sₙ⟩ / (nπ) = ∂ξ((-∂ξξ)⁻¹ ψ)(0)`, the normal derivative at the controlled
end `ξ = 0` that defines Dirichlet boundary control. -/
theorem hasSum_waveSystem_Bstar (hc : 0 < c) {η : WithLp 2 (X₁ × X₂)}
    (hη : η ∈ (waveSystem s f c q).A.adjoint.domain) :
    HasSum (fun n => c * Real.sqrt 2 * ⟪f n, η.snd⟫_ℝ) ((waveSystem s f c q).Bstar ⟨η, hη⟩) := by
  have hA : (waveSystem s f c q).A.adjoint =
      (Rotation.rotGroup s f fun n => -freq c n).generator := by
    show (Rotation.rotGroup s f (freq c)).generator.adjoint = _
    rw [← C0Semigroup.generator_adjoint, Rotation.adjoint_rotGroup]
  have hηD : η ∈ (Rotation.rotGroup s f fun n => -freq c n).generator.domain := hA ▸ hη
  have hgen := (Rotation.hasSum_sq_generator s f _ ⟨η, hηD⟩).summable
  have hcoord := (Rotation.hasSum_coord_sq s f η).summable
  have hbd : ∀ n, (⟪s n, η.fst⟫_ℝ / sw s c q n) ^ 2 + (⟪f n, η.snd⟫_ℝ / sw s c q n) ^ 2 ≤
      (⟪s n, η.fst⟫_ℝ ^ 2 + ⟪f n, η.snd⟫_ℝ ^ 2) +
        (-freq c n) ^ 2 * (⟪s n, η.fst⟫_ℝ ^ 2 + ⟪f n, η.snd⟫_ℝ ^ 2) := fun n => by
    have h1 := div_sw_sq_le s c q ⟪s n, η.fst⟫_ℝ n
    have h2 := div_sw_sq_le s c q ⟪f n, η.snd⟫_ℝ n
    rw [neg_sq]
    nlinarith
  have hsum := hcoord.add hgen
  have ha : Summable fun n => (⟪s n, η.fst⟫_ℝ / sw s c q n) ^ 2 :=
    hsum.of_nonneg_of_le (fun n => sq_nonneg _) fun n =>
      (le_add_of_nonneg_right (sq_nonneg _)).trans (hbd n)
  have hb : Summable fun n => (⟪f n, η.snd⟫_ℝ / sw s c q n) ^ 2 :=
    hsum.of_nonneg_of_le (fun n => sq_nonneg _) fun n =>
      (le_add_of_nonneg_left (sq_nonneg _)).trans (hbd n)
  -- The dual vector `η_m ∈ V` with `⟪η_m, ι_V x⟫ = ⟪η, x⟫`.
  set ηm : Vsp := WithLp.toLp 2 (mkL2 _ ha, mkL2 _ hb) with hηm
  have hζ : ∀ x : WithLp 2 (X₁ × X₂), innerSL ℝ ηm ((waveSystem s f c q).ιV x) = ⟪η, x⟫_ℝ := by
    intro x
    rw [innerSL_apply_apply, waveSystem_ιV]
    refine (Rotation.hasSum_inner_coord stdBasis stdBasis ηm _).unique ?_
    convert Rotation.hasSum_inner_coord s f η x using 1
    funext n
    simp only [inner_fst_ιV, inner_snd_ιV, hηm, WithLp.toLp_fst, WithLp.toLp_snd,
      inner_stdBasis_mkL2]
    field_simp [(sw_pos s c q n).ne']
  have h := System.inner_Bstar_of_dual (waveSystem_H1_period s f c q hc) (by positivity)
    ⟨η, hη⟩ (innerSL ℝ ηm) hζ 1
  have h1 : ⟪(waveSystem s f c q).Bstar ⟨η, hη⟩, (1 : ℝ)⟫_ℝ =
      (waveSystem s f c q).Bstar ⟨η, hη⟩ := by
    simp [RCLike.inner_apply]
  rw [show (waveSystem s f c q).Bstar ⟨η, hη⟩ = innerSL ℝ ηm ((waveSystem s f c q).B 1) from
    h1.symm.trans h, innerSL_apply_apply, waveSystem_B, Bop_apply, one_smul]
  convert Rotation.hasSum_inner_coord stdBasis stdBasis ηm (ctrlVec s c q) using 1
  funext n
  simp only [inner_fst_ctrlVec, inner_snd_ctrlVec, hηm, WithLp.toLp_snd, inner_stdBasis_mkL2,
    mul_zero, zero_add]
  field_simp [(sw_pos s c q n).ne']

/-- `B⋆ η = ∑ₙ c √2 bₙ(η)` for `η ∈ D(A⋆)` (`hasSum_waveSystem_Bstar`). -/
theorem waveSystem_Bstar_eq_tsum (hc : 0 < c) {η : WithLp 2 (X₁ × X₂)}
    (hη : η ∈ (waveSystem s f c q).A.adjoint.domain) :
    (waveSystem s f c q).Bstar ⟨η, hη⟩ = ∑' n, c * Real.sqrt 2 * ⟪f n, η.snd⟫_ℝ :=
  (hasSum_waveSystem_Bstar s f c q hc hη).tsum_eq.symm

/-! ### Non-analyticity -/

/-- **The wave group is not analytic** (Section 7): the displacement `y` with modal coordinates
`1/(n + 1)` lies in `X₁` but `∑ₙ (ωₙ yₙ)² = ∑ₙ (c π)² = ∞`, so `(y, 0) ∉ D(A)`; since `S(1)` is
onto (a group), `S(1)` maps some state outside `D(A)`, while an analytic semigroup maps `X` into
`D(A)` at every positive time. -/
theorem waveSystem_not_isAnalytic (hc : c ≠ 0) : ¬ (waveSystem s f c q).SX.IsAnalytic := by
  have hsum : Summable fun n : ℕ => (((n : ℝ) + 1)⁻¹) ^ 2 :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).congr fun n => by
      push_cast
      rw [inv_pow]
  obtain ⟨y, hy⟩ := Diagonal.exists_inner_eq s _ hsum
  refine Rotation.not_isAnalytic s f (freq c) (y := y) fun hs => ?_
  have h1 : (fun n => (freq c n * ⟪s n, y⟫_ℝ) ^ 2) = fun _ => (c * Real.pi) ^ 2 :=
    funext fun n => by
      rw [hy]
      unfold freq
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
  rw [h1] at hs
  have h0 : (c * Real.pi) ^ 2 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  exact hc ((mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)).resolve_right Real.pi_ne_zero)

/-! ### The paper's statement -/

/-- **`ex:intro-wave`** (existential form): on `X = X₁ × X₂` (the modal model of
`L²(0, 1) × H⁻¹(0, 1)`, Hilbert bases `s` and `f`, modes numbered from `0`) there are a Hilbert
space `V` and a system on `W = X ↪ V` whose semigroup is the block-rotation group with
`ωₙ = c (n + 1) π`, whose input-to-state map has the modal coordinates of the Dirichlet-controlled
wave equation (`aₙ' = ωₙ bₙ`, `bₙ' = -ωₙ aₙ + c √2 u`), with `B⋆ η = ∑ₙ c √2 bₙ(η)` on `D(A⋆)`
and `C x = ∑ₙ qₙ aₙ`, such that `hyp:H1`, `hyp:H2` (every horizon) and `hyp:compat` hold, `B` is
unbounded on `X` (`B u ∉ X` for `u ≠ 0`), `C` is bounded on `X`, and the semigroup is not
analytic. -/
theorem exists_wave (hc : 0 < c) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ (WithLp 2 (X₁ × X₂)) (WithLp 2 (X₁ × X₂)) V ℝ),
      sys.ιW = ContinuousLinearMap.id ℝ _ ∧
      sys.SX = Rotation.rotGroup s f (freq c) ∧
      (∀ (T : ℝ) (u : L2 ℝ T) (n : ℕ),
        ⟪s n, (sys.Lop T u).fst⟫_ℝ =
            c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.sin (freq c n * (T - r)) * u r ∧
          ⟪f n, (sys.Lop T u).snd⟫_ℝ =
            c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.cos (freq c n * (T - r)) * u r) ∧
      (∀ (η : WithLp 2 (X₁ × X₂)) (hη : η ∈ sys.A.adjoint.domain),
        HasSum (fun n => c * Real.sqrt 2 * ⟪f n, η.snd⟫_ℝ) (sys.Bstar ⟨η, hη⟩)) ∧
      (∀ x, HasSum (fun n => ⟪s n, q⟫_ℝ * ⟪s n, x.fst⟫_ℝ) (sys.C x)) ∧
      (∀ T, sys.H1 T) ∧ (∀ T, sys.H2 T) ∧ sys.Compat ∧
      (∀ u : ℝ, u ≠ 0 → sys.B u ∉ Set.range sys.ιV) ∧
      (∀ x, ‖sys.C x‖ ≤ ‖q‖ * ‖sys.ιW x‖) ∧
      ¬ sys.SX.IsAnalytic :=
  ⟨Vsp, inferInstance, inferInstance, inferInstance, waveSystem s f c q, rfl, rfl,
    fun _ u n => inner_waveSystem_Lop s f c q hc u n,
    fun _ hη => hasSum_waveSystem_Bstar s f c q hc hη, hasSum_waveSystem_C s f c q,
    waveSystem_H1 s f c q hc, waveSystem_H2 s f c q hc, waveSystem_compat s f c q,
    fun _ hu => waveSystem_B_apply_not_mem_range s f c q hc.ne' hu, norm_waveSystem_C_le s f c q,
    waveSystem_not_isAnalytic s f c q hc.ne'⟩

end Wave

end DataDrivenControl
