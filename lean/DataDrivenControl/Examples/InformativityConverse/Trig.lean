module

public import Mathlib
public import DataDrivenControl.Signal.Basic

/-!
# A periodic signal and the trigonometric system on `(0, 2π]`

The analysis behind the counterexample to the converse of "informativity in `U × W` implies
informativity in `U × X`" (remark after `lem:informative-gramian`, `informativity.tex`):

* the `2π`-periodic signal `x(t) = ∑ₙ 2^{-n} cos(n t)` and its derivative
  `ū(t) = -∑ₙ n 2^{-n} sin(n t)`, the state and the input of the record;
* the cosine and sine moments `Cₖ(f) = ∫₀^{2π} f(σ) cos(k σ) dσ`, `Sₖ(f) = ∫₀^{2π} f(σ) sin(k σ) dσ`
  of `f ∈ L²(0, 2π)`, their decay (Riemann–Lebesgue) and the completeness of the trigonometric
  system: if all of them vanish, then `f = 0` a.e.  Both follow from Parseval's identity on
  `AddCircle (2π)` (Mathlib's `hasSum_sq_fourierCoeffOn`), since the complex Fourier
  coefficient of `f` is `(Cₙ(f) - i Sₙ(f)) / (2π)`.

## Main declarations

* `coef n = 2^{-n}`, `xs`, `us`: `hasDerivAt_xs` (`ẋ = ū`), `continuous_xs`, `continuous_us`,
  `xs_add_two_pi` (periodicity), `integral_us` (`∫ₐᵇ ū = x(b) - x(a)`);
* `cosMoment`, `sinMoment`, `abs_cosMoment_le`, `abs_sinMoment_le`;
* `hasSum_integral_mul_xs`: `∫₀^{2π} f(σ) x(t + σ) dσ = ∑ₙ 2^{-n} (cos(n t) Cₙ(f) - sin(n t) Sₙ(f))`
  (dominated convergence);
* `fourierCoeffOn_ofReal`: the complex Fourier coefficients of a real `f` on `(0, 2π]`;
* `tendsto_cosMoment`, `tendsto_sinMoment` (Riemann–Lebesgue);
* `ae_eq_zero_of_moments_eq_zero` (completeness of the trigonometric system in `L²(0, 2π)`).

## Upstream results used

Mathlib only: `hasDerivAt_tsum`, `continuous_tsum`, `hasSum_integral_of_summable_integral_norm`,
`fourierCoeffOn_eq_integral`, `fourier_coe_apply`, `hasSum_sq_fourierCoeffOn` and
`tsum_sq_fourierCoeffOn` (Parseval on `AddCircle`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace DataDrivenControl

namespace InformativityConverse

/-! ### The signal `x(t) = ∑ₙ 2^{-n} cos(n t)` -/

/-- The coefficients `2^{-n}` of the signal. -/
def coef (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

/-- `2^{-n} > 0`. -/
theorem coef_pos (n : ℕ) : 0 < coef n := by
  unfold coef
  positivity

/-- `∑ₙ 2^{-n} < ∞`. -/
theorem summable_coef : Summable coef :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- `∑ₙ n 2^{-n} < ∞`. -/
theorem summable_coef_mul : Summable fun n : ℕ => coef n * n := by
  have hr : ‖(2 : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  refine (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.congr fun n => ?_
  rw [coef, mul_comm]

/-- `coef n (3/2)ⁿ = (3/4)ⁿ`. -/
theorem coef_mul_pow (n : ℕ) : coef n * (3 / 2 : ℝ) ^ n = (3 / 4 : ℝ) ^ n := by
  rw [coef, ← mul_pow]
  norm_num

/-- The state signal `x(t) = ∑ₙ 2^{-n} cos(n t)`, `2π`-periodic and real analytic. -/
def xs (t : ℝ) : ℝ := ∑' n : ℕ, coef n * Real.cos (n * t)

/-- The input signal `ū(t) = ẋ(t) = -∑ₙ n 2^{-n} sin(n t)`. -/
def us (t : ℝ) : ℝ := ∑' n : ℕ, -(coef n * n * Real.sin (n * t))

/-- `|2^{-n} cos y| ≤ 2^{-n}`. -/
theorem norm_coef_mul_cos_le (n : ℕ) (y : ℝ) : ‖coef n * Real.cos y‖ ≤ coef n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (coef_pos n)]
  exact mul_le_of_le_one_right (coef_pos n).le (Real.abs_cos_le_one _)

/-- `|n 2^{-n} sin y| ≤ n 2^{-n}`. -/
theorem norm_coef_mul_sin_le (n : ℕ) (y : ℝ) : ‖-(coef n * n * Real.sin y)‖ ≤ coef n * n := by
  have h0 : 0 ≤ coef n * n := mul_nonneg (coef_pos n).le n.cast_nonneg
  rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  exact mul_le_of_le_one_right h0 (Real.abs_sin_le_one _)

/-- The series of `x(t)` converges absolutely. -/
theorem summable_xs (t : ℝ) : Summable fun n : ℕ => coef n * Real.cos (n * t) :=
  summable_coef.of_norm_bounded fun n => norm_coef_mul_cos_le n _

/-- The series of `ū(t)` converges absolutely. -/
theorem summable_us (t : ℝ) : Summable fun n : ℕ => -(coef n * n * Real.sin (n * t)) :=
  summable_coef_mul.of_norm_bounded fun n => norm_coef_mul_sin_le n _

/-- **`ẋ = ū`**: termwise differentiation. -/
theorem hasDerivAt_xs (t : ℝ) : HasDerivAt xs (us t) t := by
  have hd : ∀ (n : ℕ) (y : ℝ), HasDerivAt (fun y => coef n * Real.cos (n * y))
      (-(coef n * n * Real.sin (n * y))) y := fun n y => by
    have := (((hasDerivAt_id' y).const_mul (n : ℝ)).cos).const_mul (coef n)
    convert this using 1
    ring
  exact hasDerivAt_tsum (y₀ := 0) summable_coef_mul hd
    (fun n y => norm_coef_mul_sin_le n _) (summable_xs 0) t

/-- `ū` is continuous (uniform convergence). -/
theorem continuous_us : Continuous us :=
  continuous_tsum (fun n => by fun_prop) summable_coef_mul fun n y => norm_coef_mul_sin_le n _

/-- `x` is continuous. -/
theorem continuous_xs : Continuous xs :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_xs t).continuousAt

/-- `x` is `2π`-periodic. -/
theorem xs_add_two_pi (t : ℝ) : xs (t + 2 * π) = xs t := by
  unfold xs
  congr 1
  funext n
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

/-- `∫ₐᵇ ū = x(b) - x(a)`. -/
theorem integral_us (a b : ℝ) : ∫ s in a..b, us s = xs b - xs a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_xs t)
    (continuous_us.intervalIntegrable a b)

/-! ### Cosine and sine moments on `(0, 2π]` -/

/-- The cosine moment `Cₖ(f) = ∫₀^{2π} f(σ) cos(k σ) dσ`. -/
def cosMoment (f : ℝ → ℝ) (k : ℝ) : ℝ := ∫ σ in Ioc 0 (2 * π), f σ * Real.cos (k * σ)

/-- The sine moment `Sₖ(f) = ∫₀^{2π} f(σ) sin(k σ) dσ`. -/
def sinMoment (f : ℝ → ℝ) (k : ℝ) : ℝ := ∫ σ in Ioc 0 (2 * π), f σ * Real.sin (k * σ)

variable {f : ℝ → ℝ}

/-- `C_{-k}(f) = Cₖ(f)`. -/
theorem cosMoment_neg (k : ℝ) : cosMoment f (-k) = cosMoment f k := by
  simp only [cosMoment, neg_mul, Real.cos_neg]

/-- `S_{-k}(f) = -Sₖ(f)`. -/
theorem sinMoment_neg (k : ℝ) : sinMoment f (-k) = -sinMoment f k := by
  simp only [sinMoment, neg_mul, Real.sin_neg, mul_neg, integral_neg]

/-- `f ∈ L²(0, 2π)` times a bounded continuous function is integrable. -/
theorem integrable_mul_of_bound (hf : MemLp f 2 (μI (2 * π))) {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hgc : ∀ σ, ‖g σ‖ ≤ c) : Integrable (fun σ => f σ * g σ) (μI (2 * π)) :=
  (hf.integrable one_le_two).mul_bdd hg.aestronglyMeasurable (ae_of_all _ hgc)

/-- `f(σ) cos(k σ)` is integrable on `(0, 2π]`. -/
theorem integrable_mul_cos (hf : MemLp f 2 (μI (2 * π))) (k : ℝ) :
    Integrable (fun σ => f σ * Real.cos (k * σ)) (μI (2 * π)) :=
  integrable_mul_of_bound hf (by fun_prop) fun σ => by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

/-- `f(σ) sin(k σ)` is integrable on `(0, 2π]`. -/
theorem integrable_mul_sin (hf : MemLp f 2 (μI (2 * π))) (k : ℝ) :
    Integrable (fun σ => f σ * Real.sin (k * σ)) (μI (2 * π)) :=
  integrable_mul_of_bound hf (by fun_prop) fun σ => by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _

/-- `|Cₖ(f)| ≤ ∫ |f|`. -/
theorem abs_cosMoment_le (hf : MemLp f 2 (μI (2 * π))) (k : ℝ) :
    |cosMoment f k| ≤ ∫ σ in Ioc 0 (2 * π), |f σ| := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (integrable_mul_cos hf k).norm
    (hf.integrable one_le_two).abs fun σ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `|Sₖ(f)| ≤ ∫ |f|`. -/
theorem abs_sinMoment_le (hf : MemLp f 2 (μI (2 * π))) (k : ℝ) :
    |sinMoment f k| ≤ ∫ σ in Ioc 0 (2 * π), |f σ| := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (integrable_mul_sin hf k).norm
    (hf.integrable one_le_two).abs fun σ => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-- **The translates of `x` against `f`**: `∫₀^{2π} f(σ) x(t + σ) dσ` is the trigonometric
series `∑ₙ 2^{-n} (cos(n t) Cₙ(f) - sin(n t) Sₙ(f))` (dominated convergence). -/
theorem hasSum_integral_mul_xs (hf : MemLp f 2 (μI (2 * π))) (t : ℝ) :
    HasSum (fun n : ℕ => coef n *
        (Real.cos (n * t) * cosMoment f n - Real.sin (n * t) * sinMoment f n))
      (∫ σ in Ioc 0 (2 * π), f σ * xs (t + σ)) := by
  have hfi : Integrable f (μI (2 * π)) := hf.integrable one_le_two
  set F : ℕ → ℝ → ℝ := fun n σ => f σ * (coef n * Real.cos (n * (t + σ))) with hF
  have hFi : ∀ n, Integrable (F n) (μI (2 * π)) := fun n =>
    integrable_mul_of_bound hf (by fun_prop) fun σ => norm_coef_mul_cos_le n _
  have hFs : Summable fun n => ∫ σ, ‖F n σ‖ ∂(μI (2 * π)) := by
    refine (summable_coef.mul_right (∫ σ, ‖f σ‖ ∂(μI (2 * π)))).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    refine integral_mono (hFi n).norm (hfi.norm.const_mul _) fun σ => ?_
    rw [hF, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_coef_mul_cos_le n _) (norm_nonneg _)
  have h := hasSum_integral_of_summable_integral_norm hFi hFs
  convert h using 1
  · funext n
    have e : F n = fun σ => (coef n * Real.cos (n * t)) * (f σ * Real.cos (n * σ)) -
        (coef n * Real.sin (n * t)) * (f σ * Real.sin (n * σ)) := by
      funext σ
      simp only [hF]
      rw [mul_add, Real.cos_add]
      ring
    rw [e, integral_sub ((integrable_mul_cos hf n).const_mul _)
      ((integrable_mul_sin hf n).const_mul _), integral_const_mul, integral_const_mul,
      cosMoment, sinMoment]
    ring
  · refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [hF, xs]
    rw [tsum_mul_left]

/-! ### Fourier coefficients, Riemann–Lebesgue and completeness -/

/-- The complex Fourier coefficient of a real `f` on `(0, 2π]` is `(Cₙ(f) - i Sₙ(f)) / (2π)`. -/
theorem fourierCoeffOn_ofReal (hf : MemLp f 2 (μI (2 * π))) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n =
      (2 * π)⁻¹ • ((cosMoment f n : ℂ) - (sinMoment f n : ℂ) * Complex.I) := by
  rw [fourierCoeffOn_eq_integral]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have he : ∀ σ : ℝ, fourier (-n) (σ : AddCircle (2 * π - 0)) • (f σ : ℂ) =
      ((f σ * Real.cos (n * σ) : ℝ) : ℂ) - ((f σ * Real.sin (n * σ) : ℝ) : ℂ) * Complex.I := by
    intro σ
    rw [fourier_coe_apply, smul_eq_mul]
    have harg : 2 * (π : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (σ : ℂ) / ((2 * π - 0 : ℝ) : ℂ) =
        ((-(n * σ) : ℝ) : ℂ) * Complex.I := by
      rw [sub_zero]
      push_cast
      field_simp
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    push_cast
    ring
  simp_rw [he]
  have hc : IntervalIntegrable (fun σ => ((f σ * Real.cos (n * σ) : ℝ) : ℂ)) volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).2
      (integrable_mul_cos hf n).ofReal
  have hs0 : IntervalIntegrable (fun σ => ((f σ * Real.sin (n * σ) : ℝ) : ℂ)) volume 0 (2 * π) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).2
      (integrable_mul_sin hf n).ofReal
  have hs : IntervalIntegrable (fun σ => ((f σ * Real.sin (n * σ) : ℝ) : ℂ) * Complex.I)
      volume 0 (2 * π) := hs0.mul_const _
  rw [intervalIntegral.integral_sub hc hs, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, sub_zero, one_div]
  rfl

/-- The real part of the Fourier coefficient is `Cₙ(f) / (2π)`. -/
theorem re_fourierCoeffOn_ofReal (hf : MemLp f 2 (μI (2 * π))) (n : ℤ) :
    (fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n).re = (2 * π)⁻¹ * cosMoment f n := by
  rw [fourierCoeffOn_ofReal hf, Complex.smul_re]
  simp

/-- The imaginary part of the Fourier coefficient is `-Sₙ(f) / (2π)`. -/
theorem im_fourierCoeffOn_ofReal (hf : MemLp f 2 (μI (2 * π))) (n : ℤ) :
    (fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n).im = -((2 * π)⁻¹ * sinMoment f n) := by
  rw [fourierCoeffOn_ofReal hf, Complex.smul_im]
  simp

/-- The Fourier coefficients of `f ∈ L²(0, 2π)` tend to `0` (Parseval). -/
theorem tendsto_fourierCoeffOn_ofReal (hf : MemLp f 2 (μI (2 * π))) :
    Tendsto (fun n : ℕ => fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n) atTop (𝓝 0) := by
  have hf' : MemLp (fun σ => (f σ : ℂ)) 2 (μI (2 * π)) := hf.ofReal
  have hs := (hasSum_sq_fourierCoeffOn Real.two_pi_pos hf').summable
  have h0 := hs.tendsto_cofinite_zero
  have hN : Tendsto (fun n : ℕ =>
      ‖fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n‖ ^ 2) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact h0.comp Nat.cast_injective.tendsto_cofinite
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := hN.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- **Riemann–Lebesgue** for the cosine moments. -/
theorem tendsto_cosMoment (hf : MemLp f 2 (μI (2 * π))) :
    Tendsto (fun n : ℕ => cosMoment f n) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto 0).comp (tendsto_fourierCoeffOn_ofReal hf)
  have h2 := h.const_mul (2 * π)
  simp only [Complex.zero_re, mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [re_fourierCoeffOn_ofReal hf, Int.cast_natCast, ← mul_assoc,
    mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]

/-- **Riemann–Lebesgue** for the sine moments. -/
theorem tendsto_sinMoment (hf : MemLp f 2 (μI (2 * π))) :
    Tendsto (fun n : ℕ => sinMoment f n) atTop (𝓝 0) := by
  have h := (Complex.continuous_im.tendsto 0).comp (tendsto_fourierCoeffOn_ofReal hf)
  have h2 := h.const_mul (-(2 * π))
  simp only [Complex.zero_im, mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [im_fourierCoeffOn_ofReal hf, Int.cast_natCast, neg_mul_neg, ← mul_assoc,
    mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul]

/-- **Completeness of the trigonometric system** in `L²(0, 2π)`: if all cosine and sine
moments of `f` vanish, then `f = 0` a.e. on `(0, 2π]` (Parseval). -/
theorem ae_eq_zero_of_moments_eq_zero (hf : MemLp f 2 (μI (2 * π)))
    (hC : ∀ n : ℕ, cosMoment f n = 0) (hS : ∀ n : ℕ, sinMoment f n = 0) :
    f =ᵐ[μI (2 * π)] 0 := by
  have hc : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos (fun σ => (f σ : ℂ)) n = 0 := by
    intro n
    have hC' : cosMoment f n = 0 := by
      obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
      · rw [Int.cast_natCast]; exact hC m
      · rw [Int.cast_neg, Int.cast_natCast, cosMoment_neg]; exact hC m
    have hS' : sinMoment f n = 0 := by
      obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
      · rw [Int.cast_natCast]; exact hS m
      · rw [Int.cast_neg, Int.cast_natCast, sinMoment_neg, hS m, neg_zero]
    rw [fourierCoeffOn_ofReal hf, hC', hS']
    simp
  have hf' : MemLp (fun σ => (f σ : ℂ)) 2 (μI (2 * π)) := hf.ofReal
  have hP := tsum_sq_fourierCoeffOn Real.two_pi_pos hf'
  simp only [hc, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsum_zero,
    sub_zero] at hP
  have hI : ∫ σ in (0 : ℝ)..2 * π, ‖(f σ : ℂ)‖ ^ 2 = 0 := by
    have hinv : (2 * π)⁻¹ ≠ 0 := inv_ne_zero Real.two_pi_pos.ne'
    exact (smul_eq_zero.1 hP.symm).resolve_left hinv
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hI
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le] at hI
  have h0 := (integral_eq_zero_iff_of_nonneg (fun σ => sq_nonneg (f σ)) hf.integrable_sq).1 hI
  filter_upwards [h0] with σ hσ
  simpa using hσ

end InformativityConverse

end DataDrivenControl
