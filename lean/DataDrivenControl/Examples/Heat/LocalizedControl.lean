module

public import DataDrivenControl.Examples.Heat.LocalizedSpaces

/-!
# The Neumann control on the localised spaces: `B ∈ L(ℝ, V)` and `hyp:H1`

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`): `eq:heat-separated-kernel`,
`eq:heat-control-X` and the convolution estimate behind `hyp:H1`, for the localised `V` of
`eq:heat-localized-V` (`Examples/Heat/LocalizedSpaces`).

## Main declarations

* `hasSum_conv`, `abs_integral_conv_le`: the exchange `∑ₙ pₙ e^{λₙ s} ∫₀ᵀ e^{λₙ (T - r)} u =
  ∫₀ᵀ (∑ₙ pₙ e^{λₙ (s + T - r)}) u` and the Cauchy–Schwarz bound `|∫₀ᵀ k(s + T - r) u(r) dr| ≤
  M √T ‖u‖` for `|k| ≤ M` on `(0, ∞)`.
* `orbit_genXm1_eq`, `orbitDL_genXm1_eq`: for `x = L_T u`, `χ S(s) A_{X,-1} x` is the convolution
  of `u` with `q'(s + T - ·)`, with the kernels `kernelDeriv`, `kernelDerivX` of
  `Examples/Heat/LocalizedKernel` (`S(s) A_{X,-1} L_T u = ∫₀ᵀ q'(s + T - r) u(r) dr`).
* **`exists_control_bound_loc`**: `eq:heat-control-X` (`‖L_T u‖_X ≤ C ‖u‖`) and
  `‖A_{X,-1} L_T u‖_V ≤ C ‖u‖` (the paper's estimate
  `∫₀^∞ e^{-2s} ‖χ S(s) a‖²_{H¹} ds ≤ T e^{2T} ‖u‖² ∫₀^∞ e^{-2t} ‖q'(t)‖²_{H¹} dt`, here through the
  uniform bound of `q'` and `∂_ξ q'` on `supp χ`).
* `ctrlVec` (`b = -δ₀ ∈ X₋₁`) and **`memLp_orbitH_ctrlVec`** (`b ∈ V`, from
  `b = S(1) b - A_{X,-1} L_1 1`); `ctrlV`, **`B χ : ℝ →L[ℝ] V χ`**.
* `fstV_conv_apply`, `ιV_eq_conv`: the control convolution `∫₀ᵀ S_V(T - r) B u(r) dr` in `V`.

## Deviation from the paper

The paper bounds `∫₀^∞ e^{-2t} (‖q(t)‖²_{H¹} + ‖q'(t)‖²_{H¹}) dt` (`eq:heat-separated-kernel`).
Here `q'` and `∂_ξ q'` are bounded uniformly on `(0, ∞) × supp χ` (a stronger, pointwise form),
and `b ∈ V` follows from `b = S(1) b - A_{X,-1} L_1 1` instead of from the bound on `q`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

namespace Localized

open CosineBasis

/-! ### Convolutions with modal kernels -/

/-- **The exchange of `∑ₙ` and `∫₀ᵀ`**: for `|pₙ| ≤ C (n + 1)ᵏ` and `s > 0`,
`∑ₙ pₙ e^{λₙ s} ∫₀ᵀ e^{λₙ (T - r)} u(r) dr = ∫₀ᵀ (∑ₙ pₙ e^{λₙ (s + T - r)}) u(r) dr`. -/
theorem hasSum_conv {p : ℕ → ℝ} {C : ℝ} {k : ℕ} (hp : ∀ n, |p n| ≤ C * ((n : ℝ) + 1) ^ k)
    {s T : ℝ} (hs : 0 < s) (u : L2 ℝ T) :
    HasSum (fun n => p n * Real.exp (eig n * s) *
        ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r)
      (∫ r in Ioc 0 T, (∑' n, p n * Real.exp (eig n * (s + T - r))) * u r) := by
  have hu1 : Integrable (u : ℝ → ℝ) (μI T) := (Lp.memLp u).integrable one_le_two
  set B : ℕ → ℝ := fun n => |p n| * Real.exp (eig n * s) with hB
  have hBs : Summable B := by
    refine ((summable_pow_mul_exp_eig k hs).mul_left C).of_nonneg_of_le (fun n => by positivity)
      fun n => ?_
    simp only [hB]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hp n) (Real.exp_pos _).le
  set F : ℕ → ℝ → ℝ := fun n r => p n * Real.exp (eig n * (s + T - r)) * u r with hF
  have hFb : ∀ n, ∀ r ∈ Ioc 0 T, ‖p n * Real.exp (eig n * (s + T - r))‖ ≤ B n := fun n r hr => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hB]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonpos_left (by linarith [hr.2]) (eig_nonpos n)
  have hFi : ∀ n, Integrable (F n) (μI T) := fun n =>
    hu1.bdd_mul (by fun_prop : Continuous fun r =>
        p n * Real.exp (eig n * (s + T - r))).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc (hFb n))
  have hFn : ∀ n, ∫ r in Ioc 0 T, ‖F n r‖ ≤ B n * ∫ r in Ioc 0 T, ‖(u : ℝ → ℝ) r‖ := by
    intro n
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hFi n).norm (hu1.norm.const_mul _) measurableSet_Ioc
      fun r hr => ?_
    simp only [hF, norm_mul]
    rw [← norm_mul]
    exact mul_le_mul_of_nonneg_right (hFb n r hr) (norm_nonneg _)
  have hFs : Summable fun n => ∫ r in Ioc 0 T, ‖F n r‖ :=
    (hBs.mul_right _).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hFn
  have hH := hasSum_integral_of_summable_integral_norm hFi hFs
  convert hH using 1
  · funext n
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hF]
    rw [show eig n * (s + T - r) = eig n * s + eig n * (T - r) by ring, Real.exp_add]
    ring
  · refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hF]
    rw [tsum_mul_right]

/-- **Cauchy–Schwarz for the convolution**: if `k` is continuous on `(0, ∞)` with `|k| ≤ M`
there, then `|∫₀ᵀ k(s + T - r) u(r) dr| ≤ M √T ‖u‖` for `s > 0`. -/
theorem abs_integral_conv_le {k : ℝ → ℝ} {M : ℝ} (hk : ContinuousOn k (Ioi 0))
    (hM : ∀ τ > 0, |k τ| ≤ M) {s T : ℝ} (hs : 0 < s) (hT : 0 < T) (u : L2 ℝ T) :
    |∫ r in Ioc 0 T, k (s + T - r) * u r| ≤ M * Real.sqrt T * ‖u‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 one_pos)
  have hmemk : MemLp (fun r => k (s + T - r)) 2 (μI T) := by
    refine MemLp.of_bound ?_ M (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      refine hk.comp (by fun_prop) fun r hr => ?_
      show 0 < s + T - r
      linarith [hr.2]
    · rw [Real.norm_eq_abs]; exact hM _ (by linarith [hr.2])
  have hk2 : ∫ r in Ioc 0 T, k (s + T - r) ^ 2 ≤ M ^ 2 * T := by
    calc ∫ r in Ioc 0 T, k (s + T - r) ^ 2 ≤ ∫ _ in Ioc 0 T, M ^ 2 := by
          refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Ioc
            fun r hr => ?_
          · exact (memLp_two_iff_integrable_sq hmemk.aestronglyMeasurable).1 hmemk
          · rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM _ (by linarith [hr.2])) 2
      _ = M ^ 2 * T := by simp [hT.le, mul_comm]
  have hcs := (sq_integral_mul_le hmemk u).trans (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
  refine (Real.abs_le_sqrt hcs).trans (le_of_eq ?_)
  rw [show M ^ 2 * T * ‖u‖ ^ 2 = (M * Real.sqrt T * ‖u‖) ^ 2 by
    rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]]
  exact Real.sqrt_sq (by positivity)

/-! ### The orbit of `A_{X,-1} L_T u` -/

/-- `wₙ e^{λₙ s} (A_{X,-1} x)ₙ = λₙ e^{λₙ s} ⟪eₙ, x⟫`. -/
theorem orbCoeff_mul_genXm1 (s : ℝ) (x : L2 ℝ 1) (n : ℕ) :
    orbCoeff s n * heatModal.genXm1 cosBasis x n = eig n * Real.exp (eig n * s) * ⟪cosBasis n, x⟫_ℝ := by
  rw [heatModal.genXm1_apply, heatModal_wt, heatModal_lam, orbCoeff]
  have h := (one_sub_eig_pos n).ne'
  field_simp

/-- **`S(s) A_{X,-1} L_T u = ∫₀ᵀ q'(s + T - r) u(r) dr`** at `ξ`, with
`q'(τ)(ξ) = kernelDeriv ξ τ` (`s > 0`). -/
theorem orbit_genXm1_eq {T s : ℝ} (hs : 0 < s) (u : L2 ℝ T) {x : L2 ℝ 1}
    (hx : ∀ n, ⟪cosBasis n, x⟫_ℝ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r)
    (ξ : ℝ) :
    orbit (heatModal.genXm1 cosBasis x) s ξ = ∫ r in Ioc 0 T, kernelDeriv ξ (s + T - r) * u r := by
  refine (hasSum_orbit hs _ ξ).unique ?_
  have h := hasSum_conv (abs_coeffDeriv_le ξ) hs u
  convert h using 1
  funext n
  rw [orbCoeff_mul_genXm1, hx, ← obsCoeff_eq_cosFun_apply]
  ring
  rfl

/-- **`∂_ξ S(s) A_{X,-1} L_T u = ∫₀ᵀ ∂_ξ q'(s + T - r) u(r) dr`** at `ξ`, with
`∂_ξ q'(τ)(ξ) = kernelDerivX ξ τ` (`s > 0`). -/
theorem orbitDL_genXm1_eq {T s : ℝ} (hs : 0 < s) (u : L2 ℝ T) {x : L2 ℝ 1}
    (hx : ∀ n, ⟪cosBasis n, x⟫_ℝ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r)
    (ξ : ℝ) :
    orbitDL s (heatModal.genXm1 cosBasis x) ξ =
      ∫ r in Ioc 0 T, kernelDerivX ξ (s + T - r) * u r := by
  refine (hasSum_orbitDL_apply hs _ ξ).unique ?_
  have h := hasSum_conv (abs_coeffDerivX_le ξ) hs u
  convert h using 1
  funext n
  rw [orbCoeff_mul_genXm1, hx]
  ring
  rfl

/-- `‖[f]‖_{L²(0,1)} ≤ C` if `|f| ≤ C` (the interval has length `1`). -/
theorem norm_toL2_le {f : ℝ →ᵇ ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ ξ, |f ξ| ≤ C) : ‖toL2 f‖ ≤ C := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).1 ?_
  rw [norm_toL2_sq]
  calc ∫ ξ in Ioc 0 1, f ξ ^ 2 ≤ ∫ _ in Ioc (0 : ℝ) 1, C ^ 2 :=
        setIntegral_mono_on (f.continuous.pow 2).integrableOn_Ioc (integrableOn_const (by simp))
          measurableSet_Ioc fun ξ _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h ξ) 2
    _ = C ^ 2 := by simp

variable (χ : Cutoff)

/-- `‖F_z(t)‖ ≤ e^{-t} (‖[χ S(t) z]‖ + ‖[∂_ξ (χ S(t) z)]‖)`. -/
theorem norm_orbitH_le (t : ℝ) (a : Xm1) :
    ‖orbitH χ t a‖ ≤ Real.exp (-t) * (‖locFst χ t a‖ + ‖locSnd χ t a‖) := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  have he : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h0 := norm_nonneg (locFst χ t a)
  have h1 := norm_nonneg (locSnd χ t a)
  have h2 : ‖locFst χ t a‖ ^ 2 + ‖locSnd χ t a‖ ^ 2 ≤ (‖locFst χ t a‖ + ‖locSnd χ t a‖) ^ 2 := by
    nlinarith
  rw [norm_orbitH_sq, he, mul_pow]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- **The pointwise bound of `F_{A_{X,-1} L_T u}`**: `‖F_a(s)‖ ≤ c ‖u‖ e^{-s}` for `s > 0`, from the
uniform kernel bounds on `supp χ ⊆ [d_χ, 1)` (`exists_abs_kernelDeriv_le_unif`); outside `supp χ`
both `χ` and `χ'` vanish. -/
theorem exists_norm_orbitH_genXm1_le {T : ℝ} (hT : 0 < T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : L2 ℝ T) (x : L2 ℝ 1),
      (∀ n, ⟪cosBasis n, x⟫_ℝ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r) →
      ∀ s > 0, ‖orbitH χ s (heatModal.genXm1 cosBasis x)‖ ≤ c * ‖u‖ * Real.exp (-s) := by
  obtain ⟨d, hd, hdχ⟩ := χ.exists_pos_le
  obtain ⟨K, hK⟩ := exists_abs_kernelDeriv_le_unif hd
  set K' := max K 0 with hK'
  set K₀ := ‖χ.bcf‖ with hK₀
  set K₁ := ‖χ.derivBcf‖ with hK₁
  refine ⟨(2 * K₀ + K₁) * (K' * Real.sqrt T), by positivity, fun u x hx s hs => ?_⟩
  set a := heatModal.genXm1 cosBasis x with ha
  set B := K' * Real.sqrt T * ‖u‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hpt : ∀ ξ ∈ tsupport χ, |orbit a s ξ| ≤ B ∧ |orbitDL s a ξ| ≤ B := by
    intro ξ hξ
    have hξ' := χ.tsupport_subset hξ
    have hdξ := hdχ ξ hξ
    constructor
    · rw [ha, orbit_genXm1_eq hs u hx]
      exact abs_integral_conv_le (continuousOn_kernelDeriv ξ)
        (fun τ hτ => ((hK τ hτ ξ hξ' hdξ).1).trans (le_max_left _ _)) hs hT u
    · rw [ha, orbitDL_genXm1_eq hs u hx]
      exact abs_integral_conv_le (continuousOn_kernelDerivX ξ)
        (fun τ hτ => ((hK τ hτ ξ hξ' hdξ).2).trans (le_max_left _ _)) hs hT u
  have hχb : ∀ ξ, |χ ξ| ≤ K₀ := fun ξ => by
    rw [← Real.norm_eq_abs]; exact χ.bcf.norm_coe_le_norm ξ
  have hχb' : ∀ ξ, |deriv χ ξ| ≤ K₁ := fun ξ => by
    rw [← Real.norm_eq_abs]; exact χ.derivBcf.norm_coe_le_norm ξ
  have hloc1 : locFst χ s a = toL2 (χ.bcf * orbitL s a) := rfl
  have hloc2 : locSnd χ s a = toL2 (χ.derivBcf * orbitL s a + χ.bcf * orbitDL s a) := rfl
  have h1 : ‖locFst χ s a‖ ≤ K₀ * B := by
    rw [hloc1]
    refine norm_toL2_le (by positivity) fun ξ => ?_
    show |χ ξ * orbit a s ξ| ≤ K₀ * B
    by_cases hξ : ξ ∈ tsupport χ
    · rw [abs_mul]; exact mul_le_mul (hχb ξ) (hpt ξ hξ).1 (abs_nonneg _) (norm_nonneg _)
    · rw [χ.eq_zero_of_notMem hξ, zero_mul, abs_zero]; positivity
  have h2 : ‖locSnd χ s a‖ ≤ (K₁ + K₀) * B := by
    rw [hloc2]
    refine norm_toL2_le (by positivity) fun ξ => ?_
    show |deriv χ ξ * orbit a s ξ + χ ξ * orbitDL s a ξ| ≤ (K₁ + K₀) * B
    by_cases hξ : ξ ∈ tsupport χ
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, add_mul]
      exact add_le_add (mul_le_mul (hχb' ξ) (hpt ξ hξ).1 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (hχb ξ) (hpt ξ hξ).2 (abs_nonneg _) (norm_nonneg _))
    · rw [χ.eq_zero_of_notMem hξ, χ.deriv_eq_zero_of_notMem hξ, zero_mul, zero_mul, add_zero,
        abs_zero]
      positivity
  calc ‖orbitH χ s a‖ ≤ Real.exp (-s) * (‖locFst χ s a‖ + ‖locSnd χ s a‖) := norm_orbitH_le χ s a
    _ ≤ Real.exp (-s) * (K₀ * B + (K₁ + K₀) * B) := by gcongr
    _ = (2 * K₀ + K₁) * (K' * Real.sqrt T) * ‖u‖ * Real.exp (-s) := by rw [hB]; ring

/-- **`eq:heat-control-X` and `A_{X,-1} L_T u ∈ V`** (`app:boundary-heat-informative`): for `T > 0`
and `u ∈ L²(0, T)`, the state `x = L_T u ∈ X` (coordinates `bₙ ∫₀ᵀ e^{λₙ (T - r)} u(r) dr`)
satisfies `‖x‖_X ≤ C ‖u‖`, and `F_{A_{X,-1} x} ∈ L²(0, ∞)` with norm at most `C ‖u‖`. -/
theorem exists_control_bound_loc {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ u : L2 ℝ T, ∃ x : L2 ℝ 1,
      (∀ n, ⟪cosBasis n, x⟫_ℝ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r) ∧
      ‖x‖ ≤ C * ‖u‖ ∧
      ∃ h : MemLp (fun t => orbitH χ t (heatModal.genXm1 cosBasis x)) 2 (volume.restrict (Ioi 0)),
        ‖h.toLp _‖ ≤ C * ‖u‖ := by
  obtain ⟨C₀, hC₀⟩ := heatModal.exists_control_bound cosBasis (b := ctrlCoeff)
    ⟨Real.sqrt 2, abs_ctrlCoeff_le⟩ ⟨0, fun t _ => by simp [heatModal]⟩ hT
  obtain ⟨c, hc0, hc⟩ := exists_norm_orbitH_genXm1_le χ hT
  refine ⟨max C₀ c, fun u => ?_⟩
  obtain ⟨x, hx, hxn, -⟩ := hC₀ u
  have hx' : ∀ n, ⟪cosBasis n, x⟫_ℝ =
      ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := hx
  have hexp : IntegrableOn (fun t : ℝ => (c * ‖u‖) ^ 2 * Real.exp (-2 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul _
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      ‖orbitH χ t (heatModal.genXm1 cosBasis x)‖ ^ 2 ≤ (c * ‖u‖) ^ 2 * Real.exp (-2 * t) := by
    intro t ht
    have h := hc u x hx' t ht
    have he : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hint : IntegrableOn (fun t => ‖orbitH χ t (heatModal.genXm1 cosBasis x)‖ ^ 2) (Ioi 0) :=
    Integrable.mono' hexp ((aestronglyMeasurable_orbitH χ _).norm.pow 2)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt t ht)
  have hm : MemLp (fun t => orbitH χ t (heatModal.genXm1 cosBasis x)) 2 (volume.restrict (Ioi 0)) :=
    (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_orbitH χ _)).2 hint
  refine ⟨x, hx', hxn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), hm, ?_⟩
  have hsq : ‖hm.toLp _‖ ^ 2 ≤ (c * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hcongr : ∫ t, ⟪(hm.toLp _ : ℝ → HPair) t, (hm.toLp _ : ℝ → HPair) t⟫_ℝ
        ∂(volume.restrict (Ioi 0)) =
        ∫ t in Ioi 0, ‖orbitH χ t (heatModal.genXm1 cosBasis x)‖ ^ 2 :=
      integral_congr_ae (by
        filter_upwards [hm.coeFn_toLp] with t ht
        rw [ht, real_inner_self_eq_norm_sq])
    rw [hcongr]
    calc ∫ t in Ioi 0, ‖orbitH χ t (heatModal.genXm1 cosBasis x)‖ ^ 2
        ≤ ∫ t in Ioi 0, (c * ‖u‖) ^ 2 * Real.exp (-2 * t) :=
          setIntegral_mono_on hint hexp measurableSet_Ioi hpt
      _ = (c * ‖u‖) ^ 2 / 2 := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 0, mul_zero, Real.exp_zero]
          ring
      _ ≤ (c * ‖u‖) ^ 2 := by nlinarith [sq_nonneg (c * ‖u‖)]
  have hn : ‖hm.toLp _‖ ≤ c * ‖u‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-! ### The control operator -/

/-- `b = (bₙ / wₙ)ₙ ∈ X₋₁` is square summable. -/
theorem summable_ctrlVec_sq : Summable fun n => (ctrlCoeff n / (1 - eig n)) ^ 2 := by
  refine (summable_inv_one_sub_eig.mul_left 2).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  have hw := one_sub_eig_pos n
  have hw1 : 1 ≤ 1 - eig n := by linarith [eig_nonpos n]
  have hb : ctrlCoeff n ^ 2 ≤ 2 := by
    rw [← sq_abs]
    calc |ctrlCoeff n| ^ 2 ≤ Real.sqrt 2 ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_ctrlCoeff_le n) 2
      _ = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hw]
  nlinarith

/-- **The control vector** `b = -δ₀ ∈ X₋₁`, coordinates `bₙ / wₙ` (`app:boundary-heat-informative`). -/
def ctrlVec : Xm1 := mkL2 (fun n => ctrlCoeff n / (1 - eig n)) summable_ctrlVec_sq

/-- Coordinates of `b`. -/
theorem ctrlVec_apply (n : ℕ) : ctrlVec n = ctrlCoeff n / (1 - eig n) := rfl

/-- `λ ∫₀¹ e^{λ (1 - r)} dr = e^λ - 1`. -/
theorem mul_integral_exp_one_sub (l : ℝ) :
    l * ∫ r in Ioc 0 1, Real.exp (l * (1 - r)) = Real.exp l - 1 := by
  rw [← integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => -Real.exp (l * (1 - r)))
      (fun r _ => ?_)
      ((by fun_prop : Continuous fun r => l * Real.exp (l * (1 - r))).intervalIntegrable _ _)]
  · simp only [sub_self, mul_zero, Real.exp_zero, sub_zero, mul_one]
    ring
  · have h1 : HasDerivAt (fun r : ℝ => l * (1 - r)) (-l) r := by
      simpa using ((hasDerivAt_id' r).const_sub 1).const_mul l
    convert h1.exp.neg using 1
    ring

/-- **`b = S(1) b - A_{X,-1} L_1 1`**: `A_{X,-1} L_1 1 = ∫₀¹ S(1 - r) A_{-1} b dr = S(1) b - b`. -/
theorem ctrlVec_eq (x : L2 ℝ 1)
    (hx : ∀ n, ⟪cosBasis n, x⟫_ℝ =
      ctrlCoeff n * ∫ r in Ioc 0 1, Real.exp (eig n * (1 - r)) * ControlData.oneL2 r) :
    ctrlVec = heatModal.toXm1 cosBasis (heatModal.smoothing cosBasis one_pos ctrlVec) -
      heatModal.genXm1 cosBasis x := by
  refine ext_Xm1 fun n => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, heatModal.toXm1_smoothing, heatModal.Sm_apply zero_le_one,
    heatModal.genXm1_apply, hx]
  have h1 : ∫ r in Ioc 0 1, Real.exp (eig n * (1 - r)) * ControlData.oneL2 r =
      ∫ r in Ioc 0 1, Real.exp (eig n * (1 - r)) :=
    integral_congr_ae (by
      filter_upwards [ControlData.memLp_one.coeFn_toLp] with r hr
      rw [ControlData.oneL2, hr, mul_one])
  rw [h1]
  have h2 := mul_integral_exp_one_sub (eig n)
  simp only [ctrlVec_apply, heatModal_lam, heatModal_wt, mul_one]
  linear_combination (ctrlCoeff n / (1 - eig n)) * h2

/-- **`b ∈ V`** (`app:boundary-heat-informative`): from `b = S(1) b - A_{X,-1} L_1 1`, with
`S(1) b ∈ X ⊆ V` and `A_{X,-1} L_1 1 ∈ V` (`exists_control_bound_loc`). -/
theorem memLp_orbitH_ctrlVec :
    MemLp (fun t => orbitH χ t ctrlVec) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨C, hC⟩ := exists_control_bound_loc χ one_pos
  obtain ⟨x, hx, -, hm, -⟩ := hC ControlData.oneL2
  rw [ctrlVec_eq x hx]
  refine ((memLp_orbitH_toXm1 χ (heatModal.smoothing cosBasis one_pos ctrlVec)).sub hm).ae_eq
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, map_sub]

/-- `b ∈ V`. -/
def ctrlV : V χ := mkV χ ctrlVec (memLp_orbitH_ctrlVec χ)

/-- **The control operator** `B ∈ L(ℝ, V)`, `r ↦ r b` (Neumann boundary control at `0`). -/
def B : ℝ →L[ℝ] V χ := ContinuousLinearMap.toSpanSingleton ℝ (ctrlV χ)

/-- `B r = r b`. -/
theorem B_apply (r : ℝ) : B χ r = r • ctrlV χ := rfl

/-- The `X₋₁` component of `B r`. -/
theorem fstV_B (r : ℝ) : fstV χ (B χ r) = r • ctrlVec := by
  rw [B_apply, map_smul]; rfl

/-! ### The control convolution in `V` -/

/-- The control convolution is integrable. -/
theorem integrableOn_conv {T : ℝ} (u : L2 ℝ T) :
    IntegrableOn (fun r => (SV χ).real (T - r) (B χ (u r))) (Ioc 0 T) := by
  have hu : Integrable (u : ℝ → ℝ) (μI T) := (Lp.memLp u).integrable one_le_two
  exact (SV χ).integrableOn_conv ((B χ).integrable_comp hu)

/-- The `X₋₁` coordinates of the control convolution `∫₀ᵀ S_V(T - r) B u(r) dr`. -/
theorem fstV_conv_apply {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    fstV χ (∫ r in Ioc 0 T, (SV χ).real (T - r) (B χ (u r))) n =
      ctrlCoeff n / (1 - eig n) * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := by
  have hint := integrableOn_conv χ u
  rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← inner_stdBasis]
  have h := (innerSL ℝ (stdBasis n)).integral_comp_comm ((fstV χ).integrable_comp hint)
  simp only [innerSL_apply_apply] at h
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hTr : 0 ≤ T - r := by linarith [hr.2]
  rw [inner_stdBasis, fstV_SV_real χ hTr, fstV_B, heatModal.Sm_apply hTr, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, ctrlVec_apply, heatModal_lam]
  ring

/-- The state `x ∈ X` with the coordinates of `L_T u` is the control convolution in `V`. -/
theorem ιV_eq_conv {T : ℝ} (u : L2 ℝ T) (x : L2 ℝ 1)
    (hx : ∀ n, ⟪cosBasis n, x⟫_ℝ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r) :
    ιV χ x = ∫ r in Ioc 0 T, (SV χ).real (T - r) (B χ (u r)) := by
  refine V_ext χ (ext_Xm1 fun n => ?_)
  rw [fstV_ιV, heatModal.toXm1_apply, hx, fstV_conv_apply, heatModal_wt, div_eq_mul_inv]
  ring

end Localized

end BoundaryHeat

end DataDrivenControl
