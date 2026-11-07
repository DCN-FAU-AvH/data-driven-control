module

public import DataDrivenControl.Examples.Heat.Kernel
public import DataDrivenControl.Analysis.CosineBasis

/-!
# The localised impulse response of the boundary-controlled heat equation

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`), `eq:heat-separated-kernel`.

`Examples/Heat/Kernel` bounds the impulse response `h(t) = C S(t) b` at the observation point
`ξ₀`.  The paper's localised space `V` (`eq:heat-localized-V`) measures the orbit `χ S(t) b`, and
its `ξ`-derivative, on the whole support of the cut-off `χ`.  The functions
`kernelDeriv ξ t = ∑ₙ eₙ(ξ) bₙ λₙ e^{λₙ t} = ∂ₜ (S(t) b)(ξ)` (of `Examples/Heat/Kernel`, now read as
a function of `ξ`) and `kernelDerivX ξ t = ∑ₙ eₙ'(ξ) bₙ λₙ e^{λₙ t} = ∂_ξ ∂ₜ (S(t) b)(ξ)` are the
kernels of `q'(t)` and of its `ξ`-derivative in the paper's convolution estimate.  They are bounded
uniformly in `t > 0` and in `ξ ∈ [d, 1)`, for every `d > 0`: every `ξ ∈ supp χ` satisfies
`|ξ - 2m| ≥ d_χ`.

## Main declarations

* `kernelDerivX`; `hasDerivAt_kernelDeriv_x` (`∂_ξ kernelDeriv = kernelDerivX`, termwise
  differentiation of the cosine series), `continuousOn_kernelDerivX`;
* `imageTermX`, `imageTermDerivX`: the `x`-derivatives of `imageTerm` and of `imageTermDeriv`
  (`hasDerivAt_imageTerm_x`, `hasDerivAt_imageTermDeriv_x`);
* `kernelDerivX_eq_tsum`: the image series of `kernelDerivX` on `(0, 1)`;
* `exists_abs_kernelDeriv_le_unif`: **`eq:heat-separated-kernel` on `supp χ`**: `|kernelDeriv ξ t|`
  and `|kernelDerivX ξ t|` are bounded for `t > 0` and `d ≤ ξ < 1`.

## Proof

As in `Examples/Heat/Kernel`: for `0 < t ≤ 1`, `|x| ≥ d` and `i ≤ k`, an image term
`(πt)^{-1/2} e^{-x²/4t}` times `t^{-k} |x|^i` is at most `(8/d²)^{k+1} (k+1)! e^{-x²/8}`
(`abs_imageTerm_mul_le`), and `e^{-(2m - ξ)²/8} ≤ e^{1/4} e^{-m²/4}` for `ξ ∈ [0, 1]` gives a
majorant that does not depend on `ξ` (`exp_image_le`).  On `[1, ∞)` the modal series are dominated
by their values at `t = 1`.  The image series of `kernelDeriv` is differentiated termwise in `ξ`,
and the result is identified with `kernelDerivX` by uniqueness of derivatives.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace DataDrivenControl

namespace BoundaryHeat

namespace Localized

open CosineBasis

/-- `cₙ = eₙ(ξ)` for every `ξ`: the observation coefficient at `ξ` is the value of the cosine
eigenfunction. -/
theorem obsCoeff_eq_cosFun_apply (ξ : ℝ) (n : ℕ) : obsCoeff ξ n = cosFun n ξ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [obsCoeff]
  · rw [cosFun_of_ne_zero hn]
    simp [obsCoeff, hn]

/-! ### The kernels as functions of `ξ` -/

/-- The `ξ`-derivative of `kernelDeriv`: `∂_ξ ∂ₜ (S(t) b)(ξ) = ∑ₙ eₙ'(ξ) bₙ λₙ e^{λₙ t}`
(`eq:heat-separated-kernel`).  It is meaningful for `t > 0`. -/
def kernelDerivX (ξ t : ℝ) : ℝ :=
  ∑' n, cosDeriv n ξ * ctrlCoeff n * eig n * Real.exp (eig n * t)

/-- `|eₙ(ξ) bₙ λₙ| ≤ 2π² (n + 1)²`. -/
theorem abs_coeffDeriv_le (ξ : ℝ) (n : ℕ) :
    |obsCoeff ξ n * ctrlCoeff n * eig n| ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (abs_obsCoeff_mul_ctrlCoeff_le ξ n) (abs_eig_le n) (abs_nonneg _)
    (by norm_num)

/-- `|eₙ'(ξ) bₙ λₙ| ≤ 2π³ (n + 1)³`. -/
theorem abs_coeffDerivX_le (ξ : ℝ) (n : ℕ) :
    |cosDeriv n ξ * ctrlCoeff n * eig n| ≤ 2 * Real.pi ^ 3 * ((n : ℝ) + 1) ^ 3 := by
  rw [abs_mul, abs_mul]
  have h1 : |cosDeriv n ξ| ≤ Real.sqrt 2 * Real.pi * ((n : ℝ) + 1) :=
    (abs_cosDeriv_le n ξ).trans (by gcongr; linarith)
  have h2 := abs_ctrlCoeff_le n
  have h3 := abs_eig_le n
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc |cosDeriv n ξ| * |ctrlCoeff n| * |eig n|
      ≤ (Real.sqrt 2 * Real.pi * ((n : ℝ) + 1)) * Real.sqrt 2 *
          (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) := by gcongr
    _ = (Real.sqrt 2 * Real.sqrt 2) * (Real.pi ^ 3 * ((n : ℝ) + 1) ^ 3) := by ring
    _ = 2 * Real.pi ^ 3 * ((n : ℝ) + 1) ^ 3 := by rw [h22]; ring

/-- `∂_ξ kernelDeriv ξ t = kernelDerivX ξ t` for `t > 0` (termwise differentiation of the cosine
series). -/
theorem hasDerivAt_kernelDeriv_x {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    HasDerivAt (fun ξ => kernelDeriv ξ t) (kernelDerivX ξ t) ξ := by
  set a : ℕ → ℝ := fun n => ctrlCoeff n * eig n * Real.exp (eig n * t) with ha
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) * |a n| := by
    refine ((summable_pow_mul_exp_eig 3 ht).mul_left (Real.sqrt 2 * Real.pi ^ 2)).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have h1 := abs_ctrlCoeff_le n
    have h2 := abs_eig_le n
    simp only [ha, abs_mul, Real.abs_exp]
    calc ((n : ℝ) + 1) * (|ctrlCoeff n| * |eig n| * Real.exp (eig n * t))
        ≤ ((n : ℝ) + 1) * (Real.sqrt 2 * (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) *
            Real.exp (eig n * t)) := by gcongr
      _ = Real.sqrt 2 * Real.pi ^ 2 * (((n : ℝ) + 1) ^ 3 * Real.exp (eig n * t)) := by ring
  have h := hasDerivAt_tsum_cosFun hsum ξ
  have e1 : (fun ξ => kernelDeriv ξ t) = fun ξ => ∑' n, a n * cosFun n ξ := by
    funext ξ
    simp only [kernelDeriv, ha, obsCoeff_eq_cosFun_apply]
    exact tsum_congr fun n => by ring
  have e2 : kernelDerivX ξ t = ∑' n, a n * cosDeriv n ξ := by
    simp only [kernelDerivX, ha]
    exact tsum_congr fun n => by ring
  rw [e1, e2]
  exact h

/-- `kernelDerivX ξ` is continuous on `(0, ∞)`. -/
theorem continuousOn_kernelDerivX (ξ : ℝ) : ContinuousOn (kernelDerivX ξ) (Ioi 0) :=
  continuousOn_tsum_modal (abs_coeffDerivX_le ξ)

/-! ### The image terms and their `x`-derivatives -/

/-- The `x`-derivative of `imageTerm`: `imageTerm x t · (-x/2t)`. -/
def imageTermX (x t : ℝ) : ℝ := imageTerm x t * (-x / (2 * t))

/-- The mixed derivative `∂ₓ ∂ₜ imageTerm x t = imageTerm x t · (3x/4t² - x³/8t³)`. -/
def imageTermDerivX (x t : ℝ) : ℝ :=
  imageTerm x t * (3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3))

/-- `∂ₓ imageTerm x t = imageTermX x t`. -/
theorem hasDerivAt_imageTerm_x (t x : ℝ) :
    HasDerivAt (fun x => imageTerm x t) (imageTermX x t) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * t)) (-x / (2 * t)) x := by
    have := (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).neg).div_const (4 * t)
    refine this.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun y => by
      show -y ^ 2 / (4 * t) = -(y * y) / (4 * t)
      ring
  have h2 := h1.exp.const_mul (Real.sqrt (Real.pi * t))⁻¹
  show HasDerivAt (fun x => (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))) _ x
  refine h2.congr_deriv ?_
  simp only [imageTermX, imageTerm]
  ring

/-- `∂ₓ imageTermDeriv x t = imageTermDerivX x t`. -/
theorem hasDerivAt_imageTermDeriv_x (t x : ℝ) :
    HasDerivAt (fun x => imageTermDeriv x t) (imageTermDerivX x t) x := by
  have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) (x / (2 * t ^ 2)) x := by
    have := (((hasDerivAt_id' x).mul (hasDerivAt_id' x)).div_const (4 * t ^ 2)).sub_const
      (1 / (2 * t))
    refine this.congr_deriv (by ring) |>.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun y => by
      show y ^ 2 / (4 * t ^ 2) - 1 / (2 * t) = y * y / (4 * t ^ 2) - 1 / (2 * t)
      ring
  have h := (hasDerivAt_imageTerm_x t x).mul h3
  show HasDerivAt (fun x => imageTerm x t * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) _ x
  refine h.congr_deriv ?_
  simp only [imageTermDerivX, imageTermX]
  ring

/-! ### Bounds on `(0, 1]` -/

/-- `yʲ e^{-2y} ≤ j! e^{-y}` for `y ≥ 0`. -/
theorem pow_mul_exp_neg_two_mul_le {y : ℝ} (hy : 0 ≤ y) (j : ℕ) :
    y ^ j * Real.exp (-(2 * y)) ≤ j.factorial * Real.exp (-y) := by
  have h := Real.pow_div_factorial_le_exp y hy j
  have hf : (0 : ℝ) < j.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  calc y ^ j * Real.exp (-(2 * y)) ≤ (Real.exp y * j.factorial) * Real.exp (-(2 * y)) := by
        gcongr
    _ = j.factorial * (Real.exp y * Real.exp (-(2 * y))) := by ring
    _ = j.factorial * Real.exp (-y) := by rw [← Real.exp_add]; ring_nf

/-- **The image-term bound**: for `0 < t ≤ 1`, `0 < d ≤ 1`, `|x| ≥ d` and `i ≤ k`,
`|imageTerm x t| t^{-k} |x|^i ≤ (8/d²)^{k+1} (k+1)! e^{-x²/8}`. -/
theorem abs_imageTerm_mul_le {x t d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : d ^ 2 ≤ x ^ 2)
    (ht : 0 < t) (ht1 : t ≤ 1) {i k : ℕ} (hik : i ≤ k) :
    |imageTerm x t| * (t⁻¹ ^ k * |x| ^ i) ≤
      (8 / d ^ 2) ^ (k + 1) * (k + 1).factorial * Real.exp (-(1 / 8) * x ^ 2) := by
  set s := t⁻¹ with hs_def
  set y := x ^ 2 * s / 8 with hy_def
  set r := 8 / d ^ 2 with hr_def
  have hs1 : 1 ≤ s := one_le_inv_iff₀.2 ⟨ht, ht1⟩
  have hs0 : 0 < s := by positivity
  have hy : 0 ≤ y := by positivity
  have hd2 : 0 < d ^ 2 := by positivity
  have hyx : -y ≤ -(1 / 8) * x ^ 2 := by rw [hy_def]; nlinarith [sq_nonneg x]
  have hry : r * y = s * (x ^ 2 / d ^ 2) := by rw [hr_def, hy_def]; ring
  have hsy : s ≤ r * y := by
    rw [hry]
    exact le_mul_of_one_le_right hs0.le ((one_le_div hd2).2 hx)
  have hxd : d ≤ |x| :=
    (pow_le_pow_iff_left₀ hd.le (abs_nonneg x) two_ne_zero).1 (by rwa [sq_abs])
  have hdd : d ^ 2 ≤ |x| := by nlinarith
  have hsx : s * |x| ≤ r * y := by
    rw [hry]
    calc s * |x| = s * |x| * 1 := (mul_one _).symm
      _ ≤ s * |x| * (|x| / d ^ 2) := by
          gcongr
          exact (one_le_div hd2).2 hdd
      _ = s * (x ^ 2 / d ^ 2) := by rw [← sq_abs x]; ring
  have hE : Real.exp (-x ^ 2 / (4 * t)) = Real.exp (-(2 * y)) := by
    congr 1; rw [hy_def, hs_def]; field_simp; ring
  have hsqrt : (Real.sqrt (Real.pi * t))⁻¹ ≤ s := by
    rw [hs_def]
    apply inv_anti₀ ht
    rw [Real.le_sqrt ht.le (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hT : |imageTerm x t| ≤ s * Real.exp (-(2 * y)) := by
    rw [imageTerm, hE, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    gcongr
  have hpow : s ^ k * |x| ^ i ≤ (r * y) ^ k := by
    have hk : s ^ k * |x| ^ i = s ^ (k - i) * (s * |x|) ^ i := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hik]
    rw [hk]
    calc s ^ (k - i) * (s * |x|) ^ i ≤ (r * y) ^ (k - i) * (r * y) ^ i := by gcongr
      _ = (r * y) ^ k := by rw [← pow_add, Nat.sub_add_cancel hik]
  have hj := pow_mul_exp_neg_two_mul_le hy (k + 1)
  calc |imageTerm x t| * (s ^ k * |x| ^ i)
      ≤ (s * Real.exp (-(2 * y))) * (r * y) ^ k := by gcongr
    _ ≤ (r * y * Real.exp (-(2 * y))) * (r * y) ^ k := by gcongr
    _ = r ^ (k + 1) * (y ^ (k + 1) * Real.exp (-(2 * y))) := by ring_nf
    _ ≤ r ^ (k + 1) * ((k + 1).factorial * Real.exp (-y)) := by gcongr
    _ ≤ r ^ (k + 1) * ((k + 1).factorial * Real.exp (-(1 / 8) * x ^ 2)) := by gcongr
    _ = _ := by ring

/-- The image-term bound with the uniform constant `(8/d²)⁴ · 24` (`k ≤ 3`). -/
theorem abs_imageTerm_mul_le_const {x t d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : d ^ 2 ≤ x ^ 2)
    (ht : 0 < t) (ht1 : t ≤ 1) {i k : ℕ} (hik : i ≤ k) (hk : k ≤ 3) :
    |imageTerm x t| * (t⁻¹ ^ k * |x| ^ i) ≤
      (8 / d ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * x ^ 2) := by
  refine (abs_imageTerm_mul_le hd hd1 hx ht ht1 hik).trans ?_
  have hr : 1 ≤ 8 / d ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h1 : (8 / d ^ 2) ^ (k + 1) ≤ (8 / d ^ 2) ^ 4 := pow_le_pow_right₀ hr (by omega)
  have h2 : ((k + 1).factorial : ℝ) ≤ 24 := by
    have : (k + 1).factorial ≤ 24 :=
      (Nat.factorial_le (show k + 1 ≤ 4 by omega)).trans (by decide)
    exact_mod_cast this
  gcongr

/-- `|∂ₜ imageTerm x t| ≤ (8/d²)⁴ · 24 · e^{-x²/8}` for `0 < t ≤ 1` and `|x| ≥ d`. -/
theorem abs_imageTermDeriv_le {x t d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : d ^ 2 ≤ x ^ 2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |imageTermDeriv x t| ≤ (8 / d ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * x ^ 2) := by
  set B := (8 / d ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * x ^ 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have h22 := abs_imageTerm_mul_le_const hd hd1 hx ht ht1 (i := 2) (k := 2) le_rfl (by norm_num)
  have h10 := abs_imageTerm_mul_le_const hd hd1 hx ht ht1 (i := 0) (k := 1) (by norm_num)
    (by norm_num)
  have ha : 0 ≤ t⁻¹ ^ 2 * |x| ^ 2 := by positivity
  have hb : 0 ≤ t⁻¹ ^ 1 * |x| ^ 0 := by positivity
  have hfac : |x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
      1 / 4 * (t⁻¹ ^ 2 * |x| ^ 2) + 1 / 2 * (t⁻¹ ^ 1 * |x| ^ 0) := by
    have e : x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) =
        1 / 4 * (t⁻¹ ^ 2 * |x| ^ 2) - 1 / 2 * (t⁻¹ ^ 1 * |x| ^ 0) := by
      rw [sq_abs, pow_zero]; ring
    rw [e, abs_le]
    constructor <;> linarith
  have hI := abs_nonneg (imageTerm x t)
  rw [imageTermDeriv, abs_mul]
  calc |imageTerm x t| * |x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
      ≤ |imageTerm x t| * (1 / 4 * (t⁻¹ ^ 2 * |x| ^ 2) + 1 / 2 * (t⁻¹ ^ 1 * |x| ^ 0)) := by
        gcongr
    _ = 1 / 4 * (|imageTerm x t| * (t⁻¹ ^ 2 * |x| ^ 2)) +
          1 / 2 * (|imageTerm x t| * (t⁻¹ ^ 1 * |x| ^ 0)) := by ring
    _ ≤ 1 / 4 * B + 1 / 2 * B := by gcongr
    _ ≤ B := by linarith

/-- `|∂ₓ ∂ₜ imageTerm x t| ≤ (8/d²)⁴ · 24 · e^{-x²/8}` for `0 < t ≤ 1` and `|x| ≥ d`. -/
theorem abs_imageTermDerivX_le {x t d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hx : d ^ 2 ≤ x ^ 2)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    |imageTermDerivX x t| ≤ (8 / d ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * x ^ 2) := by
  set B := (8 / d ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * x ^ 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have h21 := abs_imageTerm_mul_le_const hd hd1 hx ht ht1 (i := 1) (k := 2) (by norm_num)
    (by norm_num)
  have h33 := abs_imageTerm_mul_le_const hd hd1 hx ht ht1 (i := 3) (k := 3) le_rfl le_rfl
  have hfac : |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)| ≤
      3 / 4 * (t⁻¹ ^ 2 * |x| ^ 1) + 1 / 8 * (t⁻¹ ^ 3 * |x| ^ 3) := by
    have e1 : |3 * x / (4 * t ^ 2)| = 3 / 4 * (t⁻¹ ^ 2 * |x| ^ 1) := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2),
        abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      ring
    have e2 : |x ^ 3 / (8 * t ^ 3)| = 1 / 8 * (t⁻¹ ^ 3 * |x| ^ 3) := by
      rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 8 * t ^ 3)]
      ring
    rw [← e1, ← e2, sub_eq_add_neg, ← abs_neg (x ^ 3 / (8 * t ^ 3))]
    exact abs_add_le _ _
  have hI := abs_nonneg (imageTerm x t)
  rw [imageTermDerivX, abs_mul]
  calc |imageTerm x t| * |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)|
      ≤ |imageTerm x t| * (3 / 4 * (t⁻¹ ^ 2 * |x| ^ 1) + 1 / 8 * (t⁻¹ ^ 3 * |x| ^ 3)) := by
        gcongr
    _ = 3 / 4 * (|imageTerm x t| * (t⁻¹ ^ 2 * |x| ^ 1)) +
          1 / 8 * (|imageTerm x t| * (t⁻¹ ^ 3 * |x| ^ 3)) := by ring
    _ ≤ 3 / 4 * B + 1 / 8 * B := by gcongr
    _ ≤ B := by linarith

/-- Every image `2m - ξ` of a point `ξ ∈ [d, 1]` is at distance at least `d` from `0`. -/
theorem sq_le_sq_image_of_le {d ξ : ℝ} (hd : 0 < d) (hξ : d ≤ ξ) (hξ1 : ξ ≤ 1)
    (m : ℤ) : d ^ 2 ≤ (2 * m - ξ) ^ 2 := by
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    nlinarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- A majorant of the image Gaussians that does not depend on `ξ ∈ [0, 1]`:
`e^{-(2m - ξ)²/8} ≤ e^{1/4} e^{-(2m)²/16}`. -/
theorem exp_image_le {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) (m : ℤ) :
    Real.exp (-(1 / 8) * (2 * m - ξ) ^ 2) ≤
      Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [sq_nonneg ((m : ℝ) - ξ), mul_le_mul h1 h1 h0 zero_le_one]

/-- The summable majorant of the image terms, uniform in `ξ ∈ [0, 1]`. -/
theorem summable_image_majorant (K : ℝ) :
    Summable fun m : ℤ =>
      K * (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) :=
  ((summable_exp_neg_mul_sq 0 (by norm_num)).mul_left _).mul_left _

/-- The image term `imageTermDeriv (2m - ξ) t` with `ξ ∈ [d, 1]`, `0 < t ≤ 1`, against the uniform
majorant. -/
theorem norm_imageTermDeriv_le {d ξ t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hξ : d ≤ ξ) (hξ1 : ξ ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (m : ℤ) :
    ‖imageTermDeriv (2 * m - ξ) t‖ ≤ (8 / d ^ 2) ^ 4 * 24 *
      (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) := by
  rw [Real.norm_eq_abs]
  refine (abs_imageTermDeriv_le hd hd1 (sq_le_sq_image_of_le hd hξ hξ1 m) ht ht1).trans ?_
  gcongr
  exact exp_image_le (hd.le.trans hξ) hξ1 m

/-- The image term `imageTermDerivX (2m - ξ) t` with `ξ ∈ [d, 1]`, `0 < t ≤ 1`, against the uniform
majorant. -/
theorem norm_imageTermDerivX_le {d ξ t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hξ : d ≤ ξ)
    (hξ1 : ξ ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) (m : ℤ) :
    ‖imageTermDerivX (2 * m - ξ) t‖ ≤ (8 / d ^ 2) ^ 4 * 24 *
      (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) := by
  rw [Real.norm_eq_abs]
  refine (abs_imageTermDerivX_le hd hd1 (sq_le_sq_image_of_le hd hξ hξ1 m) ht ht1).trans ?_
  gcongr
  exact exp_image_le (hd.le.trans hξ) hξ1 m

/-! ### The image series of `kernelDerivX` -/

/-- **The image series of `kernelDerivX`** on `(0, 1)`:
`kernelDerivX ξ t = ∑ₘ ∂ₓ ∂ₜ imageTerm (2m - ξ) t`, by termwise `ξ`-differentiation of the image
series of `kernelDeriv` (`kernelDeriv_eq_tsum_imageTermDeriv`). -/
theorem kernelDerivX_eq_tsum {ξ t : ℝ} (hξ : ξ ∈ Ioo 0 1) (ht : 0 < t) (ht1 : t < 1) :
    kernelDerivX ξ t = ∑' m : ℤ, imageTermDerivX (2 * m - ξ) t := by
  set d := ξ / 2 with hd_def
  have hd : 0 < d := by have := hξ.1; positivity
  have hd1 : d ≤ 1 := by linarith [hξ.2]
  have hmem : ξ ∈ Ioo d 1 := ⟨by linarith [hξ.1], hξ.2⟩
  have hder : ∀ (m : ℤ) (y : ℝ), y ∈ Ioo d 1 →
      HasDerivAt (fun y => imageTermDeriv (2 * m - y) t) (-imageTermDerivX (2 * m - y) t) y := by
    intro m y _
    have h1 := hasDerivAt_imageTermDeriv_x t (2 * m - y)
    have h2 : HasDerivAt (fun y : ℝ => 2 * (m : ℝ) - y) (-1) y := by
      simpa using (hasDerivAt_id' y).const_sub (2 * (m : ℝ))
    exact (h1.comp y h2).congr_deriv (by ring)
  have hbd : ∀ (m : ℤ) (y : ℝ), y ∈ Ioo d 1 →
      ‖-imageTermDerivX (2 * m - y) t‖ ≤ (8 / d ^ 2) ^ 4 * 24 *
        (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) := by
    intro m y hy
    rw [norm_neg]
    exact norm_imageTermDerivX_le hd hd1 hy.1.le hy.2.le ht ht1.le m
  have hsum0 : Summable fun m : ℤ => imageTermDeriv (2 * m - ξ) t :=
    Summable.of_norm_bounded (summable_image_majorant _)
      fun m => norm_imageTermDeriv_le hd hd1 hmem.1.le hξ.2.le ht ht1.le m
  have hS := hasDerivAt_tsum_of_isPreconnected (summable_image_majorant _) isOpen_Ioo
    isPreconnected_Ioo hder hbd hmem hsum0 hmem
  have heq : (fun y => kernelDeriv y t) =ᶠ[𝓝 ξ]
      fun y => -∑' m : ℤ, imageTermDeriv (2 * m - y) t := by
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with y hy
    exact kernelDeriv_eq_tsum_imageTermDeriv hy ht ht1
  have h := (hasDerivAt_kernelDeriv_x ht ξ).unique (hS.neg.congr_of_eventuallyEq heq)
  rw [h, tsum_neg, neg_neg]

/-! ### The uniform bounds (`eq:heat-separated-kernel` on `supp χ`) -/

/-- **`eq:heat-separated-kernel` on `supp χ`**: for every `d > 0`, the kernels
`kernelDeriv ξ t = ∂ₜ (S(t) b)(ξ)` and `kernelDerivX ξ t = ∂_ξ ∂ₜ (S(t) b)(ξ)` are bounded for
`t > 0` and `ξ ∈ [d, 1)`: on `(0, 1)` by the image series (every image `2m - ξ` stays at distance
`d` from `0`), on `[1, ∞)` by the modal series. -/
theorem exists_abs_kernelDeriv_le_unif {d : ℝ} (hd : 0 < d) :
    ∃ K, ∀ t > 0, ∀ ξ ∈ Ioo (0 : ℝ) 1, d ≤ ξ → |kernelDeriv ξ t| ≤ K ∧ |kernelDerivX ξ t| ≤ K := by
  set d' := min d 1 with hd'
  have hd'0 : 0 < d' := lt_min hd one_pos
  have hd'1 : d' ≤ 1 := min_le_right _ _
  set Ki := ∑' m : ℤ, (8 / d' ^ 2) ^ 4 * 24 *
    (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) with hKi
  set K1 := 2 * Real.pi ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (eig n * 1) with hK1
  set K2 := 2 * Real.pi ^ 3 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 3 * Real.exp (eig n * 1) with hK2
  refine ⟨max Ki (max K1 K2), fun t ht ξ hξ hdξ => ?_⟩
  have hdξ' : d' ≤ ξ := (min_le_left _ _).trans hdξ
  rcases lt_or_ge t 1 with ht1 | ht1
  · constructor
    · refine le_trans ?_ (le_max_left _ _)
      rw [kernelDeriv_eq_tsum_imageTermDeriv hξ ht ht1, abs_neg, ← Real.norm_eq_abs]
      exact tsum_of_norm_bounded (summable_image_majorant _).hasSum
        fun m => norm_imageTermDeriv_le hd'0 hd'1 hdξ' hξ.2.le ht ht1.le m
    · refine le_trans ?_ (le_max_left _ _)
      rw [kernelDerivX_eq_tsum hξ ht ht1, ← Real.norm_eq_abs]
      exact tsum_of_norm_bounded (summable_image_majorant _).hasSum
        fun m => norm_imageTermDerivX_le hd'0 hd'1 hdξ' hξ.2.le ht ht1.le m
  · constructor
    · exact (abs_tsum_modal_le (abs_coeffDeriv_le ξ) one_pos ht1).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · exact (abs_tsum_modal_le (abs_coeffDerivX_le ξ) one_pos ht1).trans
        ((le_max_right _ _).trans (le_max_right _ _))

end Localized

end BoundaryHeat

end DataDrivenControl
