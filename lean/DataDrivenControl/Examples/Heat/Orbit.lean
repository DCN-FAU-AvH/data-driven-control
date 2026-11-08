module

public import DataDrivenControl.Examples.Heat.Cutoff
public import DataDrivenControl.Examples.Heat.PDE

/-!
# The localised orbit `F_z(t) = e^{-t} χ S(t) z` of the heat semigroup

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`), `eq:heat-localized-V`.

For `z ∈ X₋₁` (coordinates `a ∈ ℓ²`, `zₙ = wₙ aₙ`, `wₙ = 1 - λₙ`) and `t > 0`, the state `S(t) z`
is the smooth function `ξ ↦ ∑ₙ wₙ e^{λₙ t} aₙ eₙ(ξ)` (`orbit a t`), with `ξ`-derivative
`∑ₙ wₙ e^{λₙ t} aₙ eₙ'(ξ)` (`orbitDL t a`).  The paper's `F_z(t) = e^{-t} χ S(t) z ∈ H¹(0, 1)` is
recorded as the pair `e^{-t} ([χ S(t) z], [∂_ξ (χ S(t) z)]) ∈ L²(0, 1) × L²(0, 1)` (`orbitH χ t`),
whose squared norm is `e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)}` with
`‖f‖²_{H¹(0,1)} = ‖f‖²_{L²(0,1)} + ‖f'‖²_{L²(0,1)}` (`H1sq`).

## Main declarations

* `orbitL t, orbitDL t : X₋₁ →L[ℝ] C_b(ℝ)`, `orbit a t`: `hasSum_orbit`, `hasDerivAt_orbit`
  (`∂_ξ orbit = orbitDL`), the shift `orbitL_Sm` (`S(t) S(s) = S(t + s)`), `continuousOn_orbitL`.
* `H1sq f = ∫₀¹ f² + ∫₀¹ (f')²`; `orbitH χ t : X₋₁ →L[ℝ] L²(0,1) × L²(0,1)`;
  **`norm_orbitH_sq_eq`**: `‖F_z(t)‖² = e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)}`.
* `orbitH_Sm`: `F_{S(s) z}(t) = e^s F_z(t + s)`; `continuousOn_orbitH`, `aestronglyMeasurable_orbitH`.
* **`integral_H1sq_orbit`**: `∫₀^∞ e^{-2t} ‖S(t) x‖²_{H¹(0,1)} dt = ½ ‖x‖²_X` for `x ∈ X = L²(0, 1)`
  (the paper's eigenfunction identity; `hasSum_H1sq_orbit`, orthogonality of `eₙ` and `eₙ'`).
* **`norm_orbitH_sq_le`**: `‖χ f‖²_{H¹} ≤ c_χ ‖f‖²_{H¹}` with `c_χ = 3‖χ‖²_∞ + 2‖χ'‖²_∞`;
  `memLp_orbitH_toXm1`, `integral_norm_orbitH_sq_le` (`X ↪ V`).
* **`abs_orbit_le`**: if `χ(ξ₀) = 1`, then `|(S(t) z)(ξ₀)| ≤ ‖∂_ξ (χ S(t) z)‖_{L²(0,1)} ≤
  eᵗ ‖F_z(t)‖` (`χ(0) = 0`, the fundamental theorem of calculus and Cauchy–Schwarz).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

open CosineBasis

/-! ### The orbit `S(t) z` -/

/-- The coefficients `wₙ e^{λₙ t}` of `S(t) : X₋₁ → X` in the coordinates of `X₋₁`. -/
def orbCoeff (t : ℝ) (n : ℕ) : ℝ := (1 - eig n) * Real.exp (eig n * t)

/-- `wₙ = 1 - λₙ > 0`. -/
theorem one_sub_eig_pos (n : ℕ) : 0 < 1 - eig n := by linarith [eig_nonpos n]

/-- `wₙ = 1 - λₙ ≤ (1 + π²)(n + 1)²`. -/
theorem one_sub_eig_le (n : ℕ) : 1 - eig n ≤ (1 + Real.pi ^ 2) * ((n : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [eig, sub_neg_eq_add, mul_pow]
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (by linarith : (0 : ℝ) ≤ 2 * n + 1)]

/-- `∑ₙ (wₙ e^{λₙ t} βₙ)² < ∞` for `t > 0` and `|βₙ| ≤ C (n + 1)`. -/
theorem summable_orbCoeff_mul_sq {t : ℝ} (ht : 0 < t) {β : ℕ → ℝ} {C : ℝ}
    (hβ : ∀ n, |β n| ≤ C * ((n : ℝ) + 1)) : Summable fun n => (orbCoeff t n * β n) ^ 2 := by
  refine ((summable_pow_mul_exp_eig 6 (by linarith : 0 < 2 * t)).mul_left
    ((1 + Real.pi ^ 2) ^ 2 * C ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  have h0 : 0 ≤ 1 - eig n := (one_sub_eig_pos n).le
  have h2 : β n ^ 2 ≤ C ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [← sq_abs, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hβ n) 2
  have h3 : Real.exp (eig n * t) ^ 2 = Real.exp (eig n * (2 * t)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : (1 - eig n) ^ 2 ≤ ((1 + Real.pi ^ 2) * ((n : ℝ) + 1) ^ 2) ^ 2 :=
    pow_le_pow_left₀ h0 (one_sub_eig_le n) 2
  calc (orbCoeff t n * β n) ^ 2 = (1 - eig n) ^ 2 * β n ^ 2 * Real.exp (eig n * (2 * t)) := by
        rw [orbCoeff, ← h3]; ring
    _ ≤ ((1 + Real.pi ^ 2) * ((n : ℝ) + 1) ^ 2) ^ 2 * (C ^ 2 * ((n : ℝ) + 1) ^ 2) *
          Real.exp (eig n * (2 * t)) := by gcongr
    _ = (1 + Real.pi ^ 2) ^ 2 * C ^ 2 * (((n : ℝ) + 1) ^ 6 * Real.exp (eig n * (2 * t))) := by
        ring

/-- The series of `S(t) z` converges in `C_b(ℝ)`. -/
theorem summable_orbCoeff_cos_sq {t : ℝ} (ht : 0 < t) :
    Summable fun n => (orbCoeff t n * (fun _ => Real.sqrt 2) n) ^ 2 :=
  summable_orbCoeff_mul_sq ht (C := Real.sqrt 2) fun n => by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sqrt_nonneg 2]

/-- The series of `∂_ξ S(t) z` converges in `C_b(ℝ)`. -/
theorem summable_orbCoeff_deriv_sq {t : ℝ} (ht : 0 < t) :
    Summable fun n => (orbCoeff t n * (fun n : ℕ => Real.sqrt 2 * Real.pi * n) n) ^ 2 :=
  summable_orbCoeff_mul_sq ht (C := Real.sqrt 2 * Real.pi) fun n => by
    have : (0 : ℝ) ≤ Real.sqrt 2 * Real.pi := by positivity
    rw [abs_of_nonneg (by positivity)]
    nlinarith

/-- `z ↦ S(t) z` from `X₋₁` to `C_b(ℝ)` (`t > 0`): the cosine series `∑ₙ wₙ e^{λₙ t} aₙ eₙ`;
`0` for `t ≤ 0` (junk). -/
def orbitL (t : ℝ) : Xm1 →L[ℝ] (ℝ →ᵇ ℝ) :=
  if ht : 0 < t then
    seriesCLM (orbCoeff t) (fun _ => Real.sqrt 2) cosBCF norm_cosBCF_le
      (summable_orbCoeff_cos_sq ht)
  else 0

/-- `z ↦ ∂_ξ S(t) z` from `X₋₁` to `C_b(ℝ)` (`t > 0`): `∑ₙ wₙ e^{λₙ t} aₙ eₙ'`. -/
def orbitDL (t : ℝ) : Xm1 →L[ℝ] (ℝ →ᵇ ℝ) :=
  if ht : 0 < t then
    seriesCLM (orbCoeff t) (fun n : ℕ => Real.sqrt 2 * Real.pi * n) cosDerivBCF
      norm_cosDerivBCF_le (summable_orbCoeff_deriv_sq ht)
  else 0

/-- **The orbit** `ξ ↦ (S(t) z)(ξ)` of `z ∈ X₋₁` (coordinates `a`) at time `t > 0`, the cosine
series `∑ₙ wₙ e^{λₙ t} aₙ eₙ(ξ)`. -/
def orbit (a : Xm1) (t : ℝ) : ℝ → ℝ := ⇑(orbitL t a)

/-- `orbitL t` for `t > 0`. -/
theorem orbitL_of_pos {t : ℝ} (ht : 0 < t) :
    orbitL t = seriesCLM (orbCoeff t) (fun _ => Real.sqrt 2) cosBCF norm_cosBCF_le
      (summable_orbCoeff_cos_sq ht) := dite_eq_left ht

/-- `orbitDL t` for `t > 0`. -/
theorem orbitDL_of_pos {t : ℝ} (ht : 0 < t) :
    orbitDL t = seriesCLM (orbCoeff t) (fun n : ℕ => Real.sqrt 2 * Real.pi * n) cosDerivBCF
      norm_cosDerivBCF_le (summable_orbCoeff_deriv_sq ht) := dite_eq_left ht

/-- `S(t) z = ∑ₙ wₙ e^{λₙ t} aₙ eₙ` in `C_b(ℝ)`. -/
theorem hasSum_orbitL {t : ℝ} (ht : 0 < t) (a : Xm1) :
    HasSum (fun n => (orbCoeff t n * a n) • cosBCF n) (orbitL t a) := by
  rw [orbitL_of_pos ht]; exact hasSum_seriesCLM _ _ _ _ _ a

/-- `∂_ξ S(t) z = ∑ₙ wₙ e^{λₙ t} aₙ eₙ'` in `C_b(ℝ)`. -/
theorem hasSum_orbitDL {t : ℝ} (ht : 0 < t) (a : Xm1) :
    HasSum (fun n => (orbCoeff t n * a n) • cosDerivBCF n) (orbitDL t a) := by
  rw [orbitDL_of_pos ht]; exact hasSum_seriesCLM _ _ _ _ _ a

/-- `(S(t) z)(ξ) = ∑ₙ wₙ e^{λₙ t} aₙ eₙ(ξ)`. -/
theorem hasSum_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) (ξ : ℝ) :
    HasSum (fun n => orbCoeff t n * a n * cosFun n ξ) (orbit a t ξ) := by
  rw [orbit, orbitL_of_pos ht]
  exact hasSum_seriesCLM_apply _ _ _ _ _ a ξ

/-- `(∂_ξ S(t) z)(ξ) = ∑ₙ wₙ e^{λₙ t} aₙ eₙ'(ξ)`. -/
theorem hasSum_orbitDL_apply {t : ℝ} (ht : 0 < t) (a : Xm1) (ξ : ℝ) :
    HasSum (fun n => orbCoeff t n * a n * cosDeriv n ξ) (orbitDL t a ξ) := by
  rw [orbitDL_of_pos ht]
  exact hasSum_seriesCLM_apply _ _ _ _ _ a ξ

/-- `∑ₙ (n + 1) |wₙ e^{λₙ t} aₙ| < ∞` for `t > 0`. -/
theorem summable_succ_mul_abs_orbCoeff {t : ℝ} (ht : 0 < t) (a : Xm1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * |orbCoeff t n * a n| := by
  have h := summable_orbCoeff_mul_sq ht (β := fun n : ℕ => (n : ℝ) + 1) (C := 1) fun n => by
    rw [one_mul, abs_of_nonneg (by positivity)]
  refine (summable_abs_mul_abs h (summable_sq a)).congr fun n => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  ring

/-- **`∂_ξ (S(t) z) = orbitDL t z`** for `t > 0` (termwise differentiation). -/
theorem hasDerivAt_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) (ξ : ℝ) :
    HasDerivAt (orbit a t) (orbitDL t a ξ) ξ := by
  have hf : orbit a t = fun ξ => ∑' n, (orbCoeff t n * a n) * cosFun n ξ :=
    funext fun ξ => (hasSum_orbit ht a ξ).tsum_eq.symm
  have hd : orbitDL t a ξ = ∑' n, (orbCoeff t n * a n) * cosDeriv n ξ :=
    (hasSum_orbitDL_apply ht a ξ).tsum_eq.symm
  rw [hf, hd]
  exact hasDerivAt_tsum_cosFun (summable_succ_mul_abs_orbCoeff ht a) ξ

/-- `wₙ e^{λₙ t} (S(s) a)ₙ = wₙ e^{λₙ (t + s)} aₙ`. -/
theorem orbCoeff_mul_Sm (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (a : Xm1) (n : ℕ) :
    orbCoeff t n * heatModal.Sm.real s a n = orbCoeff (t + s) n * a n := by
  rw [heatModal.Sm_apply hs, heatModal_lam, orbCoeff, orbCoeff, mul_add, Real.exp_add]
  ring

/-- `S(t) S(s) z = S(t + s) z`. -/
theorem orbitL_Sm {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (a : Xm1) :
    orbitL t (heatModal.Sm.real s a) = orbitL (t + s) a := by
  rw [orbitL_of_pos ht, orbitL_of_pos (by linarith), seriesCLM_apply, seriesCLM_apply]
  exact tsum_congr fun n => by rw [orbCoeff_mul_Sm t hs]

/-- `∂_ξ S(t) S(s) z = ∂_ξ S(t + s) z`. -/
theorem orbitDL_Sm {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (a : Xm1) :
    orbitDL t (heatModal.Sm.real s a) = orbitDL (t + s) a := by
  rw [orbitDL_of_pos ht, orbitDL_of_pos (by linarith), seriesCLM_apply, seriesCLM_apply]
  exact tsum_congr fun n => by rw [orbCoeff_mul_Sm t hs]

/-- `t ↦ S(t) z` is continuous on `(0, ∞)` in `C_b(ℝ)`. -/
theorem continuousOn_orbitL (a : Xm1) : ContinuousOn (fun t => orbitL t a) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hev : (fun τ => orbitL (t / 2) (heatModal.Sm.real (τ - t / 2) a)) =ᶠ[𝓝 t]
      fun τ => orbitL τ a := by
    filter_upwards [Ioi_mem_nhds (half_lt_self ht')] with τ hτ
    have hτ' : t / 2 < τ := hτ
    rw [orbitL_Sm (half_pos ht') (by linarith), add_sub_cancel]
  exact ((orbitL (t / 2)).continuous.comp ((heatModal.Sm.continuous_real_apply a).comp
    (continuous_id.sub continuous_const))).continuousAt.congr hev

/-- `t ↦ ∂_ξ S(t) z` is continuous on `(0, ∞)` in `C_b(ℝ)`. -/
theorem continuousOn_orbitDL (a : Xm1) : ContinuousOn (fun t => orbitDL t a) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hev : (fun τ => orbitDL (t / 2) (heatModal.Sm.real (τ - t / 2) a)) =ᶠ[𝓝 t]
      fun τ => orbitDL τ a := by
    filter_upwards [Ioi_mem_nhds (half_lt_self ht')] with τ hτ
    have hτ' : t / 2 < τ := hτ
    rw [orbitDL_Sm (half_pos ht') (by linarith), add_sub_cancel]
  exact ((orbitDL (t / 2)).continuous.comp ((heatModal.Sm.continuous_real_apply a).comp
    (continuous_id.sub continuous_const))).continuousAt.congr hev

/-! ### The `H¹(0, 1)` norm and the localised orbit -/

/-- **The squared `H¹(0, 1)` norm** `‖f‖²_{H¹(0,1)} = ∫₀¹ f² + ∫₀¹ (f')²` (for `f ∈ C¹`). -/
def H1sq (f : ℝ → ℝ) : ℝ := (∫ ξ in Ioc 0 1, f ξ ^ 2) + ∫ ξ in Ioc 0 1, deriv f ξ ^ 2

/-- `‖f‖²_{H¹} ≥ 0`. -/
theorem H1sq_nonneg (f : ℝ → ℝ) : 0 ≤ H1sq f :=
  show 0 ≤ (∫ ξ in Ioc 0 1, f ξ ^ 2) + ∫ ξ in Ioc 0 1, deriv f ξ ^ 2 from add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

/-- `‖S(t) z‖²_{H¹(0,1)} = ‖[S(t) z]‖²_{L²} + ‖[∂_ξ S(t) z]‖²_{L²}` for `t > 0`. -/
theorem H1sq_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) :
    H1sq (orbit a t) = ‖toL2 (orbitL t a)‖ ^ 2 + ‖toL2 (orbitDL t a)‖ ^ 2 := by
  have e2 : ∫ ξ in Ioc 0 1, deriv (orbit a t) ξ ^ 2 = ∫ ξ in Ioc 0 1, (orbitDL t a) ξ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun ξ => by
      simp only [(hasDerivAt_orbit ht a ξ).deriv])
  rw [H1sq, e2, norm_toL2_sq, norm_toL2_sq]
  rfl

/-- **`‖S(t) z‖²_{H¹(0,1)} = ∑ₙ (wₙ e^{λₙ t} aₙ)² (1 - λₙ)`** for `t > 0` (orthonormality of `eₙ`
and orthogonality of `eₙ'`, `‖eₙ'‖² = -λₙ`). -/
theorem hasSum_H1sq_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) :
    HasSum (fun n => (orbCoeff t n * a n) ^ 2 * (1 - eig n)) (H1sq (orbit a t)) := by
  have h1 := hasSum_sq_of_orthogonal (u := fun n => toL2 (cosBCF n)) (r := fun _ => 1)
    (c := fun n => orbCoeff t n * a n) (fun n m => inner_toL2_cosBCF n m)
    (by simpa only [map_smul] using (hasSum_orbitL ht a).mapL toL2)
  have h2 := hasSum_sq_of_orthogonal (u := fun n => toL2 (cosDerivBCF n))
    (r := fun n => -cosEig n) (c := fun n => orbCoeff t n * a n)
    (fun n m => inner_toL2_cosDerivBCF n m)
    (by simpa only [map_smul] using (hasSum_orbitDL ht a).mapL toL2)
  rw [H1sq_orbit ht]
  convert h1.add h2 using 1
  funext n
  rw [show cosEig n = eig n from rfl]
  ring

/-- `‖S(t) z‖²_{H¹(0,1)}` is continuous in `t > 0`. -/
theorem continuousOn_H1sq_orbit (a : Xm1) :
    ContinuousOn (fun t => H1sq (orbit a t)) (Ioi 0) := by
  refine ContinuousOn.congr ?_ fun t ht => H1sq_orbit ht a
  exact ((toL2.continuous.comp_continuousOn (continuousOn_orbitL a)).norm.pow 2).add
    ((toL2.continuous.comp_continuousOn (continuousOn_orbitDL a)).norm.pow 2)

/-- `L²(0, 1) × L²(0, 1)`, the home of `F_z(t) = e^{-t} (χ S(t) z, ∂_ξ (χ S(t) z))`. -/
abbrev HPair : Type := WithLp 2 (L2 ℝ 1 × L2 ℝ 1)

/-- Multiplication by a fixed bounded continuous function. -/
def mulL (f : ℝ →ᵇ ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] (ℝ →ᵇ ℝ) := ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ) f

/-- `mulL f g = f g`. -/
@[simp] theorem mulL_apply (f g : ℝ →ᵇ ℝ) (ξ : ℝ) : mulL f g ξ = f ξ * g ξ := rfl

/-- `z ↦ [χ S(t) z] ∈ L²(0, 1)`. -/
def locFst (χ : Cutoff) (t : ℝ) : Xm1 →L[ℝ] L2 ℝ 1 := toL2 ∘L mulL χ.bcf ∘L orbitL t

/-- `z ↦ [∂_ξ (χ S(t) z)] = [χ' S(t) z + χ ∂_ξ S(t) z] ∈ L²(0, 1)`. -/
def locSnd (χ : Cutoff) (t : ℝ) : Xm1 →L[ℝ] L2 ℝ 1 :=
  toL2 ∘L (mulL χ.derivBcf ∘L orbitL t + mulL χ.bcf ∘L orbitDL t)

/-- **The localised orbit** `F_z(t) = e^{-t} χ S(t) z ∈ H¹(0, 1)`, recorded as the pair
`e^{-t} ([χ S(t) z], [∂_ξ (χ S(t) z)]) ∈ L²(0, 1) × L²(0, 1)` (`eq:heat-localized-V`). -/
def orbitH (χ : Cutoff) (t : ℝ) : Xm1 →L[ℝ] HPair :=
  Real.exp (-t) • ((WithLp.prodContinuousLinearEquiv 2 ℝ (L2 ℝ 1) (L2 ℝ 1)).symm.toContinuousLinearMap
    ∘L (locFst χ t).prod (locSnd χ t))

variable (χ : Cutoff)

/-- The first component of `F_z(t)`. -/
theorem orbitH_fst (t : ℝ) (a : Xm1) : (orbitH χ t a).fst = Real.exp (-t) • locFst χ t a := rfl

/-- The second component of `F_z(t)`. -/
theorem orbitH_snd (t : ℝ) (a : Xm1) : (orbitH χ t a).snd = Real.exp (-t) • locSnd χ t a := rfl

/-- `‖F_z(t)‖² = e^{-2t} (‖[χ S(t) z]‖² + ‖[∂_ξ (χ S(t) z)]‖²)`. -/
theorem norm_orbitH_sq (t : ℝ) (a : Xm1) :
    ‖orbitH χ t a‖ ^ 2 = Real.exp (-2 * t) * (‖locFst χ t a‖ ^ 2 + ‖locSnd χ t a‖ ^ 2) := by
  have he : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [WithLp.prod_norm_sq_eq_of_L2, orbitH_fst, orbitH_snd, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he]
  ring

/-- `‖[χ S(t) z]‖² = ∫₀¹ (χ S(t) z)²`. -/
theorem norm_locFst_sq (t : ℝ) (a : Xm1) :
    ‖locFst χ t a‖ ^ 2 = ∫ ξ in Ioc 0 1, (χ ξ * orbit a t ξ) ^ 2 :=
  norm_toL2_sq _

/-- `‖[∂_ξ (χ S(t) z)]‖² = ∫₀¹ (χ' S(t) z + χ ∂_ξ S(t) z)²`. -/
theorem norm_locSnd_sq (t : ℝ) (a : Xm1) :
    ‖locSnd χ t a‖ ^ 2 =
      ∫ ξ in Ioc 0 1, (deriv χ ξ * orbit a t ξ + χ ξ * orbitDL t a ξ) ^ 2 :=
  norm_toL2_sq _

/-- `∂_ξ (χ S(t) z) = χ' S(t) z + χ ∂_ξ S(t) z`. -/
theorem hasDerivAt_mul_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) (ξ : ℝ) :
    HasDerivAt (fun ξ => χ ξ * orbit a t ξ)
      (deriv χ ξ * orbit a t ξ + χ ξ * orbitDL t a ξ) ξ :=
  (χ.hasDerivAt ξ).mul (hasDerivAt_orbit ht a ξ)

/-- **The norm of the localised orbit** (`eq:heat-localized-V`): for `t > 0`,
`‖F_z(t)‖² = e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)} = e^{-2t} (∫₀¹ (χ S(t) z)² + ∫₀¹ (∂_ξ (χ S(t) z))²)`. -/
theorem norm_orbitH_sq_eq {t : ℝ} (ht : 0 < t) (a : Xm1) :
    ‖orbitH χ t a‖ ^ 2 = Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit a t ξ) := by
  rw [norm_orbitH_sq, norm_locFst_sq, norm_locSnd_sq, H1sq]
  simp only [(hasDerivAt_mul_orbit χ ht a _).deriv]

/-- `‖e^{-t} q‖ ≤ ‖F_z(t)‖` for the second component: `‖[∂_ξ (χ S(t) z)]‖ ≤ eᵗ ‖F_z(t)‖`. -/
theorem norm_locSnd_le (t : ℝ) (a : Xm1) :
    ‖locSnd χ t a‖ ≤ Real.exp t * ‖orbitH χ t a‖ := by
  have h1 : ‖(orbitH χ t a).snd‖ ≤ ‖orbitH χ t a‖ := by
    have := WithLp.prod_norm_sq_eq_of_L2 (orbitH χ t a)
    nlinarith [norm_nonneg (orbitH χ t a), norm_nonneg (orbitH χ t a).snd,
      sq_nonneg ‖(orbitH χ t a).fst‖]
  rw [orbitH_snd, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ‖locSnd χ t a‖ = Real.exp t * (Real.exp (-t) * ‖locSnd χ t a‖) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp t * ‖orbitH χ t a‖ := by gcongr

/-- `[χ S(t) S(s) z] = [χ S(t + s) z]`. -/
theorem locFst_Sm {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (a : Xm1) :
    locFst χ t (heatModal.Sm.real s a) = locFst χ (t + s) a := by
  simp only [locFst, ContinuousLinearMap.comp_apply, orbitL_Sm ht hs]

/-- `[∂_ξ (χ S(t) S(s) z)] = [∂_ξ (χ S(t + s) z)]`. -/
theorem locSnd_Sm {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (a : Xm1) :
    locSnd χ t (heatModal.Sm.real s a) = locSnd χ (t + s) a := by
  simp only [locSnd, ContinuousLinearMap.comp_apply, add_apply,
    orbitL_Sm ht hs, orbitDL_Sm ht hs]

/-- **`F_{S(s) z}(t) = e^s F_z(t + s)`** (`app:boundary-heat-informative`). -/
theorem orbitH_Sm {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (a : Xm1) :
    orbitH χ t (heatModal.Sm.real s a) = Real.exp s • orbitH χ (t + s) a := by
  simp only [orbitH, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, locFst_Sm χ ht hs, locSnd_Sm χ ht hs, smul_smul,
    ← Real.exp_add]
  congr 2
  ring

/-- `t ↦ F_z(t)` is continuous on `(0, ∞)`. -/
theorem continuousOn_orbitH (a : Xm1) : ContinuousOn (fun t => orbitH χ t a) (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hev : (fun τ => Real.exp (-(τ - t / 2)) •
      orbitH χ (t / 2) (heatModal.Sm.real (τ - t / 2) a)) =ᶠ[𝓝 t] fun τ => orbitH χ τ a := by
    filter_upwards [Ioi_mem_nhds (half_lt_self ht')] with τ hτ
    have hτ' : t / 2 < τ := hτ
    rw [orbitH_Sm χ (half_pos ht') (by linarith), smul_smul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_smul, add_sub_cancel]
  refine ContinuousAt.congr ?_ hev
  exact ((Real.continuous_exp.comp (continuous_id.sub continuous_const).neg).smul
    ((orbitH χ (t / 2)).continuous.comp ((heatModal.Sm.continuous_real_apply a).comp
      (continuous_id.sub continuous_const)))).continuousAt

/-- `t ↦ F_z(t)` is strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_orbitH (a : Xm1) :
    AEStronglyMeasurable (fun t => orbitH χ t a) (volume.restrict (Ioi 0)) :=
  (continuousOn_orbitH χ a).aestronglyMeasurable measurableSet_Ioi

/-! ### `X ↪ V`: the eigenfunction identity and the localisation bound -/

/-- `wₙ e^{λₙ t} (x/w)ₙ = e^{λₙ t} ⟪eₙ, x⟫` for `x ∈ X`. -/
theorem orbCoeff_mul_toXm1 (t : ℝ) (x : L2 ℝ 1) (n : ℕ) :
    orbCoeff t n * heatModal.toXm1 cosBasis x n = Real.exp (eig n * t) * ⟪cosBasis n, x⟫_ℝ := by
  rw [heatModal.toXm1_apply, heatModal_wt, orbCoeff]
  have h := (one_sub_eig_pos n).ne'
  calc (1 - eig n) * Real.exp (eig n * t) * ((1 - eig n)⁻¹ * ⟪cosBasis n, x⟫_ℝ)
      = ((1 - eig n) * (1 - eig n)⁻¹) * (Real.exp (eig n * t) * ⟪cosBasis n, x⟫_ℝ) := by ring
    _ = Real.exp (eig n * t) * ⟪cosBasis n, x⟫_ℝ := by rw [mul_inv_cancel₀ h, one_mul]

/-- **`∫₀^∞ e^{-2t} ‖S(t) x‖²_{H¹(0,1)} dt = ½ ‖x‖²_X`** in `ℝ≥0∞` (`x ∈ X = L²(0, 1)`). -/
theorem lintegral_H1sq_orbit (x : L2 ℝ 1) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-2 * t) *
      H1sq (orbit (heatModal.toXm1 cosBasis x) t)) = ENNReal.ofReal (‖x‖ ^ 2 / 2) := by
  set xs : ℕ → ℝ := fun n => ⟪cosBasis n, x⟫_ℝ with hxs
  set F : ℕ → ℝ → ℝ := fun n t =>
    xs n ^ 2 * (1 - eig n) * Real.exp (-(2 * (1 - eig n)) * t) with hF
  have hF0 : ∀ n t, 0 ≤ F n t := fun n t => by
    have := one_sub_eig_pos n
    simp only [hF]
    positivity
  have hpt : ∀ t, 0 < t → HasSum (fun n => F n t)
      (Real.exp (-2 * t) * H1sq (orbit (heatModal.toXm1 cosBasis x) t)) := by
    intro t ht
    have h := (hasSum_H1sq_orbit ht (heatModal.toXm1 cosBasis x)).mul_left (Real.exp (-2 * t))
    convert h using 1
    funext n
    rw [orbCoeff_mul_toXm1]
    have he : Real.exp (-(2 * (1 - eig n)) * t) = Real.exp (-2 * t) * Real.exp (eig n * t) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    simp only [hF, hxs]
    rw [he]
    ring
  have hint : ∀ n, ∫ t in Ioi 0, F n t = xs n ^ 2 / 2 := by
    intro n
    have hw := (one_sub_eig_pos n).ne'
    simp only [hF]
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [one_sub_eig_pos n]) 0, mul_zero,
      Real.exp_zero]
    field_simp
  have hintg : ∀ n, IntegrableOn (F n) (Ioi 0) := fun n =>
    (integrableOn_exp_mul_Ioi (by linarith [one_sub_eig_pos n]) 0).const_mul _
  have hmeas : ∀ n, Measurable (F n) := fun n => by simp only [hF]; fun_prop
  calc ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-2 * t) *
        H1sq (orbit (heatModal.toXm1 cosBasis x) t))
      = ∫⁻ t in Ioi 0, ∑' n, ENNReal.ofReal (F n t) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [← (hpt t ht).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => hF0 n t)
          (hpt t ht).summable]
    _ = ∑' n, ∫⁻ t in Ioi 0, ENNReal.ofReal (F n t) :=
        lintegral_tsum fun n => (hmeas n).ennreal_ofReal.aemeasurable
    _ = ∑' n, ENNReal.ofReal (xs n ^ 2 / 2) := by
        refine tsum_congr fun n => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hintg n) (Eventually.of_forall (hF0 n)),
          hint n]
    _ = ENNReal.ofReal (‖x‖ ^ 2 / 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((Diagonal.summable_inner_sq cosBasis x).div_const 2)]
        congr 1
        exact ((Diagonal.hasSum_inner_sq cosBasis x).div_const 2).tsum_eq

/-- `t ↦ e^{-2t} ‖S(t) z‖²_{H¹}` is strongly measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_H1sq_orbit (a : Xm1) :
    AEStronglyMeasurable (fun t => Real.exp (-2 * t) * H1sq (orbit a t))
      (volume.restrict (Ioi 0)) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    (continuousOn_H1sq_orbit a)).aestronglyMeasurable measurableSet_Ioi

/-- `t ↦ e^{-2t} ‖S(t) x‖²_{H¹}` is integrable on `(0, ∞)` for `x ∈ X`. -/
theorem integrableOn_H1sq_orbit (x : L2 ℝ 1) :
    IntegrableOn (fun t => Real.exp (-2 * t) * H1sq (orbit (heatModal.toXm1 cosBasis x) t))
      (Ioi 0) := by
  refine ⟨aestronglyMeasurable_H1sq_orbit _, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (H1sq_nonneg _)), lintegral_H1sq_orbit]
  exact ENNReal.ofReal_lt_top

/-- **The eigenfunction identity** (`app:boundary-heat-informative`):
`∫₀^∞ e^{-2t} ‖S(t) x‖²_{H¹(0,1)} dt = ½ ‖x‖²_X` for `x ∈ X = L²(0, 1)`. -/
theorem integral_H1sq_orbit (x : L2 ℝ 1) :
    ∫ t in Ioi 0, Real.exp (-2 * t) * H1sq (orbit (heatModal.toXm1 cosBasis x) t) =
      ‖x‖ ^ 2 / 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (H1sq_nonneg _)) (aestronglyMeasurable_H1sq_orbit _),
    lintegral_H1sq_orbit, ENNReal.toReal_ofReal (by positivity)]

/-- The constant `c_χ = 3 ‖χ‖²_∞ + 2 ‖χ'‖²_∞` of `‖χ f‖²_{H¹} ≤ c_χ ‖f‖²_{H¹}`. -/
def cutConst : ℝ := 3 * ‖χ.bcf‖ ^ 2 + 2 * ‖χ.derivBcf‖ ^ 2

/-- **`‖χ f‖²_{H¹} ≤ c_χ ‖f‖²_{H¹}`** for `f = S(t) z`: `‖F_z(t)‖² ≤ c_χ e^{-2t} ‖S(t) z‖²_{H¹}`. -/
theorem norm_orbitH_sq_le {t : ℝ} (ht : 0 < t) (a : Xm1) :
    ‖orbitH χ t a‖ ^ 2 ≤ cutConst χ * (Real.exp (-2 * t) * H1sq (orbit a t)) := by
  set K₀ := ‖χ.bcf‖
  set K₁ := ‖χ.derivBcf‖
  set f := orbitL t a
  set f' := orbitDL t a
  have hb0 : ∀ ξ, χ ξ ^ 2 ≤ K₀ ^ 2 := fun ξ => by
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (χ.bcf.norm_coe_le_norm ξ) 2
  have hb1 : ∀ ξ, deriv χ ξ ^ 2 ≤ K₁ ^ 2 := fun ξ => by
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (χ.derivBcf.norm_coe_le_norm ξ) 2
  have hi : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn g (Ioc 0 1) := fun g hg =>
    hg.integrableOn_Ioc
  have hfc : Continuous fun ξ => f ξ ^ 2 := f.continuous.pow 2
  have hf'c : Continuous fun ξ => f' ξ ^ 2 := f'.continuous.pow 2
  have I1 : ∫ ξ in Ioc 0 1, (χ ξ * orbit a t ξ) ^ 2 ≤ K₀ ^ 2 * ∫ ξ in Ioc 0 1, f ξ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hi _ ((χ.continuous.mul f.continuous).pow 2))
      (hi _ (continuous_const.mul hfc)) measurableSet_Ioc fun ξ _ => ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hb0 ξ) (sq_nonneg _)
  have I2 : ∫ ξ in Ioc 0 1, (deriv χ ξ * orbit a t ξ + χ ξ * orbitDL t a ξ) ^ 2 ≤
      2 * K₁ ^ 2 * (∫ ξ in Ioc 0 1, f ξ ^ 2) + 2 * K₀ ^ 2 * ∫ ξ in Ioc 0 1, f' ξ ^ 2 := by
    have hi1 : IntegrableOn (fun ξ => 2 * K₁ ^ 2 * f ξ ^ 2) (Ioc 0 1) :=
      hi _ (continuous_const.mul hfc)
    have hi2 : IntegrableOn (fun ξ => 2 * K₀ ^ 2 * f' ξ ^ 2) (Ioc 0 1) :=
      hi _ (continuous_const.mul hf'c)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi1 hi2]
    refine setIntegral_mono_on (hi _ (((χ.continuous_deriv.mul f.continuous).add
      (χ.continuous.mul f'.continuous)).pow 2)) (hi1.add hi2) measurableSet_Ioc
      fun ξ _ => ?_
    have h1 := mul_le_mul_of_nonneg_right (hb1 ξ) (sq_nonneg (f ξ))
    have h2 := mul_le_mul_of_nonneg_right (hb0 ξ) (sq_nonneg (f' ξ))
    have h3 := two_mul_le_add_sq (deriv χ ξ * f ξ) (χ ξ * f' ξ)
    show (deriv χ ξ * f ξ + χ ξ * f' ξ) ^ 2 ≤ 2 * K₁ ^ 2 * f ξ ^ 2 + 2 * K₀ ^ 2 * f' ξ ^ 2
    nlinarith [mul_pow (deriv χ ξ) (f ξ) 2, mul_pow (χ ξ) (f' ξ) 2]
  have hA : 0 ≤ ∫ ξ in Ioc 0 1, f ξ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hB : 0 ≤ ∫ ξ in Ioc 0 1, f' ξ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hH : H1sq (orbit a t) = (∫ ξ in Ioc 0 1, f ξ ^ 2) + ∫ ξ in Ioc 0 1, f' ξ ^ 2 := by
    rw [H1sq_orbit ht, norm_toL2_sq, norm_toL2_sq]
  rw [norm_orbitH_sq, norm_locFst_sq, norm_locSnd_sq, hH, cutConst]
  have hE := Real.exp_pos (-2 * t)
  have hK0 : 0 ≤ K₀ ^ 2 := sq_nonneg _
  have hK1 : 0 ≤ K₁ ^ 2 := sq_nonneg _
  have hsum : (∫ ξ in Ioc 0 1, (χ ξ * orbit a t ξ) ^ 2) +
      ∫ ξ in Ioc 0 1, (deriv χ ξ * orbit a t ξ + χ ξ * orbitDL t a ξ) ^ 2 ≤
      (3 * K₀ ^ 2 + 2 * K₁ ^ 2) *
        ((∫ ξ in Ioc 0 1, f ξ ^ 2) + ∫ ξ in Ioc 0 1, f' ξ ^ 2) := by
    nlinarith
  calc Real.exp (-2 * t) * ((∫ ξ in Ioc 0 1, (χ ξ * orbit a t ξ) ^ 2) +
        ∫ ξ in Ioc 0 1, (deriv χ ξ * orbit a t ξ + χ ξ * orbitDL t a ξ) ^ 2)
      ≤ Real.exp (-2 * t) * ((3 * K₀ ^ 2 + 2 * K₁ ^ 2) *
        ((∫ ξ in Ioc 0 1, f ξ ^ 2) + ∫ ξ in Ioc 0 1, f' ξ ^ 2)) := by gcongr
    _ = _ := by ring

/-- For `x ∈ X`, `t ↦ ‖F_x(t)‖²` is integrable on `(0, ∞)`. -/
theorem integrableOn_norm_orbitH_sq (x : L2 ℝ 1) :
    IntegrableOn (fun t => ‖orbitH χ t (heatModal.toXm1 cosBasis x)‖ ^ 2) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_H1sq_orbit x).const_mul (cutConst χ))
    ((aestronglyMeasurable_orbitH χ _).norm.pow 2)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_orbitH_sq_le χ ht _

/-- **`X ↪ V`**: for `x ∈ X`, `F_x ∈ L²(0, ∞; L²(0,1) × L²(0,1))`. -/
theorem memLp_orbitH_toXm1 (x : L2 ℝ 1) :
    MemLp (fun t => orbitH χ t (heatModal.toXm1 cosBasis x)) 2 (volume.restrict (Ioi 0)) :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_orbitH χ _)).2
    (integrableOn_norm_orbitH_sq χ x)

/-- **`X ↪ V`, the bound**: `∫₀^∞ ‖F_x(t)‖² dt ≤ (c_χ / 2) ‖x‖²`. -/
theorem integral_norm_orbitH_sq_le (x : L2 ℝ 1) :
    ∫ t in Ioi 0, ‖orbitH χ t (heatModal.toXm1 cosBasis x)‖ ^ 2 ≤ cutConst χ / 2 * ‖x‖ ^ 2 := by
  calc ∫ t in Ioi 0, ‖orbitH χ t (heatModal.toXm1 cosBasis x)‖ ^ 2
      ≤ ∫ t in Ioi 0, cutConst χ *
          (Real.exp (-2 * t) * H1sq (orbit (heatModal.toXm1 cosBasis x) t)) :=
        setIntegral_mono_on (integrableOn_norm_orbitH_sq χ x)
          ((integrableOn_H1sq_orbit x).const_mul _) measurableSet_Ioi
          fun t ht => norm_orbitH_sq_le χ ht _
    _ = cutConst χ / 2 * ‖x‖ ^ 2 := by
        rw [integral_const_mul, integral_H1sq_orbit]; ring

/-! ### The point value at `ξ₀` -/

/-- **The point value through the localised `H¹` norm** (`app:boundary-heat-informative`): if
`ξ₀ ∈ (0, 1)` and `χ(ξ₀) = 1`, then `|(S(t) z)(ξ₀)| ≤ eᵗ ‖F_z(t)‖` for `t > 0`.  Since `χ(0) = 0`,
`(S(t) z)(ξ₀) = (χ S(t) z)(ξ₀) = ∫₀^{ξ₀} ∂_ξ (χ S(t) z)`, which Cauchy–Schwarz bounds by
`‖∂_ξ (χ S(t) z)‖_{L²(0,1)}`. -/
theorem abs_orbit_le {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (hχ : χ ξ₀ = 1) {t : ℝ} (ht : 0 < t)
    (a : Xm1) : |orbit a t ξ₀| ≤ Real.exp t * ‖orbitH χ t a‖ := by
  set g : ℝ →ᵇ ℝ := χ.derivBcf * orbitL t a + χ.bcf * orbitDL t a with hg
  have hloc : locSnd χ t a = toL2 g := rfl
  have hI : ξ₀ ∈ Icc (0 : ℝ) 1 := ⟨hξ₀.1.le, hξ₀.2.le⟩
  have hftc : orbit a t ξ₀ = ∫ ξ in (0 : ℝ)..ξ₀, g ξ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := ξ₀)
      (f := fun ξ => χ ξ * orbit a t ξ) (f' := ⇑g)
      (fun ξ _ => hasDerivAt_mul_orbit χ ht a ξ) (g.continuous.intervalIntegrable _ _)
    rw [h, χ.apply_zero, hχ]
    ring
  have hint : ∫ ξ in (0 : ℝ)..ξ₀, g ξ = ⟪indicatorConstLp 2 (measurableSet_Ioc (a := 0) (b := ξ₀))
      (measure_ne_top (μI 1) _) (1 : ℝ), toL2 g⟫_ℝ := by
    rw [PDE.inner_indicator_eq_integral hI]
    exact (PDE.intervalIntegral_congr_of_ae_eq (coeFn_toL2 g) hI).symm
  have hind : ‖indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := ξ₀))
      (measure_ne_top (μI 1) _) (1 : ℝ)‖ ≤ 1 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    refine Real.rpow_le_one measureReal_nonneg ?_ (by positivity)
    have h1 : (μI 1).real (Ioc 0 ξ₀) ≤ (μI 1).real univ := measureReal_mono (subset_univ _)
    have h2 : (μI 1).real univ = 1 := by simp [Measure.real]
    linarith
  calc |orbit a t ξ₀| = |⟪indicatorConstLp 2 (measurableSet_Ioc (a := 0) (b := ξ₀))
        (measure_ne_top (μI 1) _) (1 : ℝ), toL2 g⟫_ℝ| := by rw [hftc, hint]
    _ ≤ ‖indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := ξ₀))
        (measure_ne_top (μI 1) _) (1 : ℝ)‖ * ‖toL2 g‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖locSnd χ t a‖ := by rw [hloc]; gcongr
    _ ≤ Real.exp t * ‖orbitH χ t a‖ := by rw [one_mul]; exact norm_locSnd_le χ t a

end BoundaryHeat

end DataDrivenControl
