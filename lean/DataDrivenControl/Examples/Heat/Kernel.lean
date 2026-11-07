module

public import Mathlib

/-!
# The impulse response of the boundary-controlled heat equation

Paper: `ex:boundary-heat-informative` (`informativity.tex`), `app:boundary-heat-informative`
and `eq:heat-separated-kernel` (`appendix_proofs.tex`).

The Neumann heat equation on `(0, 1)` has eigenvalues `λₙ = -(nπ)²` and normalised
eigenfunctions `e₀ = 1`, `eₙ = √2 cos(nπξ)`.  The Neumann control at `0` has the modal
coefficients `bₙ = -eₙ(0)`, and the point observation at `ξ₀ ∈ (0, 1)` has the coefficients
`cₙ = eₙ(ξ₀)`.  The impulse response is
`h(t) = C S(t) b = ∑ₙ cₙ bₙ e^{λₙ t} = -(1 + 2 ∑_{n ≥ 1} cos(nπξ₀) e^{-n²π²t})`.

## Main declarations

* `eig`, `ctrlCoeff`, `obsCoeff`: `λₙ`, `bₙ`, `cₙ`; `eig_injective`, `eig_nonpos`, the bounds
  `|bₙ|, |cₙ| ≤ √2`, `ctrlCoeff_ne_zero`;
* `summable_pow_mul_exp_eig`: `∑ₙ (n + 1)ᵏ e^{λₙ t} < ∞` for `t > 0`;
* `kernel` (`h`) and `kernelDeriv` (`h'`): `hasDerivAt_kernel`, `continuousOn_kernel`,
  `continuousOn_kernelDeriv`;
* `kernel_eq_images`: the method of images
  `h(t) = -(πt)^{-1/2} ∑ₘ exp(-(2m - ξ₀)²/4t)`, from Poisson summation
  (`Complex.tsum_exp_neg_quadratic`);
* `exists_abs_kernel_le`, `exists_abs_kernelDeriv_le`: `h` and `h'` are bounded on `(0, ∞)`
  (the scalar form of `eq:heat-separated-kernel`);
* `not_summable_obsCoeff_sq`, `not_summable_ctrlCoeff_sq`: `(cₙ), (bₙ) ∉ ℓ²`, so neither `B` nor
  `C` is bounded on `X`.

## Auxiliary results

* Generic modal series `∑ₙ aₙ e^{λₙ t}` with polynomially bounded `aₙ`: `summable_modal`,
  `hasDerivAt_tsum_modal`, `continuousOn_tsum_modal`, `abs_tsum_modal_le`;
* `summable_exp_neg_mul_sq`: `∑ₘ exp(-c (2m - ξ)²) < ∞` (from the Jacobi theta series);
* the image terms `imageTerm x t = (πt)^{-1/2} exp(-x²/4t)` and their `t`-derivatives
  `imageTermDeriv`: `hasDerivAt_imageTerm`, `sq_le_sq_image` (`|2m - ξ₀| ≥ ξ₀`),
  `kernel_eq_tsum_imageTerm`, and `kernelDeriv_eq_tsum_imageTermDeriv` (termwise
  differentiation of the image series on `(0, 1)`).

## Proof of the bounds

On `(0, 1]`, with `y = x²/8t`, every image term and its `t`-derivative are bounded by
`yʲ e^{-2y} ≤ j! e^{-y} ≤ j! e^{-x²/8}` times powers of `8/ξ₀²`, uniformly in `t`, because the
images `x = 2m - ξ₀` stay at distance `ξ₀` from `0`.  On `[1, ∞)` the modal series is dominated
by its value at `t = 1`.  The image series is differentiated termwise, and its derivative is
identified with `kernelDeriv` by uniqueness of derivatives (both represent `h` on `(0, ∞)`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace DataDrivenControl

namespace BoundaryHeat

/-! ### Modal data -/

/-- The Neumann eigenvalues `λₙ = -(nπ)²` (`app:boundary-heat-informative`). -/
def eig (n : ℕ) : ℝ := -((n : ℝ) * Real.pi) ^ 2

/-- The modal coefficients `bₙ = -eₙ(0)` of the Neumann boundary control at `0`
(`app:boundary-heat-informative`: `b = -δ₀`, `b₀ = -1`, `bₙ = -√2`). -/
def ctrlCoeff (n : ℕ) : ℝ := if n = 0 then -1 else -Real.sqrt 2

/-- The modal coefficients `cₙ = eₙ(ξ₀)` of the point observation at `ξ₀`
(`ex:boundary-heat-informative`). -/
def obsCoeff (ξ₀ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else Real.sqrt 2 * Real.cos (n * Real.pi * ξ₀)

/-- The impulse response `h(t) = C S(t) b = ∑ₙ cₙ bₙ e^{λₙ t}` of the boundary-controlled heat
equation (`app:boundary-heat-informative`).  It is meaningful for `t > 0`. -/
def kernel (ξ₀ t : ℝ) : ℝ := ∑' n, obsCoeff ξ₀ n * ctrlCoeff n * Real.exp (eig n * t)

/-- The termwise derivative `h'(t) = ∑ₙ cₙ bₙ λₙ e^{λₙ t}` of `kernel`
(`eq:heat-separated-kernel`).  It is meaningful for `t > 0`. -/
def kernelDeriv (ξ₀ t : ℝ) : ℝ :=
  ∑' n, obsCoeff ξ₀ n * ctrlCoeff n * eig n * Real.exp (eig n * t)

/-- The eigenvalues `λₙ = -(nπ)²` are distinct. -/
theorem eig_injective : Function.Injective eig := by
  intro m n h
  have h' : ((m : ℝ) * Real.pi) ^ 2 = ((n : ℝ) * Real.pi) ^ 2 := by
    simpa [eig] using h
  have hm : (0 : ℝ) ≤ m * Real.pi := by positivity
  have hn : (0 : ℝ) ≤ n * Real.pi := by positivity
  have := (sq_eq_sq₀ hm hn).1 h'
  have := mul_right_cancel₀ Real.pi_ne_zero this
  exact_mod_cast this

/-- The eigenvalues are nonpositive. -/
theorem eig_nonpos (n : ℕ) : eig n ≤ 0 := by
  unfold eig; nlinarith [sq_nonneg ((n : ℝ) * Real.pi)]

/-- `λ₀ = 0`. -/
@[simp] theorem eig_zero : eig 0 = 0 := by
  simp [eig]

/-- `|λₙ| ≤ π² (n + 1)²`. -/
theorem abs_eig_le (n : ℕ) : |eig n| ≤ Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  rw [abs_of_nonpos (eig_nonpos n), eig, neg_neg, mul_pow, mul_comm]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  gcongr
  linarith

/-- `|cₙ| ≤ √2`. -/
theorem abs_obsCoeff_le (ξ₀ : ℝ) (n : ℕ) : |obsCoeff ξ₀ n| ≤ Real.sqrt 2 := by
  unfold obsCoeff
  split_ifs
  · simp only [abs_one]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt 2 * |Real.cos (n * Real.pi * ξ₀)| ≤ Real.sqrt 2 * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ = Real.sqrt 2 := mul_one _

/-- `|bₙ| ≤ √2`. -/
theorem abs_ctrlCoeff_le (n : ℕ) : |ctrlCoeff n| ≤ Real.sqrt 2 := by
  unfold ctrlCoeff
  split_ifs
  · simp only [abs_neg, abs_one]
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- `bₙ ≠ 0`: every mode is excited by the boundary control. -/
theorem ctrlCoeff_ne_zero (n : ℕ) : ctrlCoeff n ≠ 0 := by
  unfold ctrlCoeff
  split_ifs
  · norm_num
  · simp

/-- `|cₙ bₙ| ≤ 2`. -/
theorem abs_obsCoeff_mul_ctrlCoeff_le (ξ₀ : ℝ) (n : ℕ) : |obsCoeff ξ₀ n * ctrlCoeff n| ≤ 2 := by
  rw [abs_mul]
  calc |obsCoeff ξ₀ n| * |ctrlCoeff n| ≤ Real.sqrt 2 * Real.sqrt 2 :=
        mul_le_mul (abs_obsCoeff_le ξ₀ n) (abs_ctrlCoeff_le n) (abs_nonneg _)
          (Real.sqrt_nonneg _)
    _ = 2 := Real.mul_self_sqrt (by norm_num)

/-! ### Summability -/

/-- `e^{λₙ t}` is antitone in `t`: the uniform form of the summability on `[t₀, ∞)`. -/
theorem exp_eig_mul_le (n : ℕ) {t₀ t : ℝ} (h : t₀ ≤ t) :
    Real.exp (eig n * t) ≤ Real.exp (eig n * t₀) :=
  Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left h (eig_nonpos n))

/-- `∑ₙ (n + 1)ᵏ e^{λₙ t} < ∞` for `t > 0` (analytic smoothing of the heat semigroup). -/
theorem summable_pow_mul_exp_eig (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (eig n * t) := by
  set r := Real.pi ^ 2 * t with hr_def
  have hr : 0 < r := by positivity
  have h := (summable_nat_add_iff 1).mpr
    ((Real.summable_pow_mul_exp_neg_nat_mul k hr).mul_right (Real.exp r))
  refine h.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, mul_assoc]
  gcongr
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
      nlinarith
  simp only [eig, hr_def]
  have hpt : 0 ≤ Real.pi ^ 2 * t := by positivity
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hn hpt]

/-- Uniform summability on `[t₀, ∞)`: `(n + 1)ᵏ e^{λₙ t} ≤ (n + 1)ᵏ e^{λₙ t₀}` for `t ≥ t₀`,
with a summable majorant. -/
theorem pow_mul_exp_eig_le (k n : ℕ) {t₀ t : ℝ} (h : t₀ ≤ t) :
    ((n : ℝ) + 1) ^ k * Real.exp (eig n * t) ≤ ((n : ℝ) + 1) ^ k * Real.exp (eig n * t₀) := by
  exact mul_le_mul_of_nonneg_left (exp_eig_mul_le n h) (by positivity)

/-! ### Generic modal series -/

/-- A modal series `∑ₙ aₙ e^{λₙ t}` with `|aₙ| ≤ C (n + 1)ᵏ` converges for `t > 0`. -/
theorem summable_modal {a : ℕ → ℝ} {C : ℝ} {k : ℕ} (ha : ∀ n, |a n| ≤ C * ((n : ℝ) + 1) ^ k)
    {t : ℝ} (ht : 0 < t) : Summable fun n => a n * Real.exp (eig n * t) := by
  refine Summable.of_norm_bounded ((summable_pow_mul_exp_eig k ht).mul_left C) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, ← mul_assoc]
  gcongr
  exact ha n

/-- A modal series `∑ₙ aₙ e^{λₙ t}` with `|aₙ| ≤ C (n + 1)ᵏ` may be differentiated termwise
for `t > 0`. -/
theorem hasDerivAt_tsum_modal {a : ℕ → ℝ} {C : ℝ} {k : ℕ}
    (ha : ∀ n, |a n| ≤ C * ((n : ℝ) + 1) ^ k) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∑' n, a n * Real.exp (eig n * s))
      (∑' n, a n * eig n * Real.exp (eig n * t)) t := by
  have ht2 : 0 < t / 2 := half_pos ht
  have hC : 0 ≤ C := by
    have := ha 0; simp at this; linarith [abs_nonneg (a 0)]
  have hmem : t ∈ Ioi (t / 2) := half_lt_self ht
  have hderiv : ∀ (n : ℕ) (s : ℝ), s ∈ Ioi (t / 2) →
      HasDerivAt (fun s => a n * Real.exp (eig n * s)) (a n * eig n * Real.exp (eig n * s)) s := by
    intro n s _
    have := ((hasDerivAt_id' s).const_mul (eig n)).exp.const_mul (a n)
    convert this using 1
    ring
  have hbound : ∀ (n : ℕ) (s : ℝ), s ∈ Ioi (t / 2) →
      ‖a n * eig n * Real.exp (eig n * s)‖ ≤
        C * Real.pi ^ 2 * (((n : ℝ) + 1) ^ (k + 2) * Real.exp (eig n * (t / 2))) := by
    intro n s hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp]
    have h1 := ha n
    have h2 := abs_eig_le n
    have h3 : Real.exp (eig n * s) ≤ Real.exp (eig n * (t / 2)) :=
      exp_eig_mul_le n (le_of_lt hs)
    calc |a n| * |eig n| * Real.exp (eig n * s)
        ≤ (C * ((n : ℝ) + 1) ^ k) * (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2) *
            Real.exp (eig n * (t / 2)) := by gcongr
      _ = _ := by ring
  exact hasDerivAt_tsum_of_isPreconnected
    ((summable_pow_mul_exp_eig (k + 2) ht2).mul_left (C * Real.pi ^ 2)) isOpen_Ioi
    isPreconnected_Ioi hderiv hbound hmem (summable_modal ha ht) hmem

/-- A modal series `∑ₙ aₙ e^{λₙ t}` with `|aₙ| ≤ C (n + 1)ᵏ` is continuous on `(0, ∞)`. -/
theorem continuousOn_tsum_modal {a : ℕ → ℝ} {C : ℝ} {k : ℕ}
    (ha : ∀ n, |a n| ≤ C * ((n : ℝ) + 1) ^ k) :
    ContinuousOn (fun s => ∑' n, a n * Real.exp (eig n * s)) (Ioi 0) := fun _ ht =>
  (hasDerivAt_tsum_modal ha ht).continuousAt.continuousWithinAt

/-- The bound `|∑ₙ aₙ e^{λₙ t}| ≤ C ∑ₙ (n + 1)ᵏ e^{λₙ t₀}` for `t ≥ t₀ > 0`. -/
theorem abs_tsum_modal_le {a : ℕ → ℝ} {C : ℝ} {k : ℕ}
    (ha : ∀ n, |a n| ≤ C * ((n : ℝ) + 1) ^ k) {t₀ t : ℝ} (ht₀ : 0 < t₀) (h : t₀ ≤ t) :
    |∑' n, a n * Real.exp (eig n * t)| ≤
      C * ∑' n : ℕ, ((n : ℝ) + 1) ^ k * Real.exp (eig n * t₀) := by
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((summable_pow_mul_exp_eig k ht₀).mul_left C).hasSum fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, ← mul_assoc]
  exact mul_le_mul (ha n) (exp_eig_mul_le n h) (Real.exp_pos _).le
    (le_trans (abs_nonneg _) (ha n))

/-! ### The impulse response -/

/-- `|cₙ bₙ| ≤ 2 (n + 1)⁰`, in the form of the generic modal lemmas. -/
private theorem coeff_bound (ξ₀ : ℝ) (n : ℕ) :
    |obsCoeff ξ₀ n * ctrlCoeff n| ≤ 2 * ((n : ℝ) + 1) ^ 0 := by
  simpa using abs_obsCoeff_mul_ctrlCoeff_le ξ₀ n

/-- `|cₙ bₙ λₙ| ≤ 2π² (n + 1)²`. -/
private theorem coeffDeriv_bound (ξ₀ : ℝ) (n : ℕ) :
    |obsCoeff ξ₀ n * ctrlCoeff n * eig n| ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (abs_obsCoeff_mul_ctrlCoeff_le ξ₀ n) (abs_eig_le n) (abs_nonneg _)
    (by norm_num)

/-- The series of `kernel` converges for `t > 0`. -/
theorem summable_kernel (ξ₀ : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable fun n => obsCoeff ξ₀ n * ctrlCoeff n * Real.exp (eig n * t) :=
  summable_modal (coeff_bound ξ₀) ht

/-- The series of `kernelDeriv` converges for `t > 0`. -/
theorem summable_kernelDeriv (ξ₀ : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable fun n => obsCoeff ξ₀ n * ctrlCoeff n * eig n * Real.exp (eig n * t) :=
  summable_modal (coeffDeriv_bound ξ₀) ht

/-- `h' = kernelDeriv` is the derivative of `h = kernel` on `(0, ∞)`. -/
theorem hasDerivAt_kernel (ξ₀ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernel ξ₀) (kernelDeriv ξ₀ t) t :=
  hasDerivAt_tsum_modal (coeff_bound ξ₀) ht

/-- `h` is continuous on `(0, ∞)`. -/
theorem continuousOn_kernel (ξ₀ : ℝ) : ContinuousOn (kernel ξ₀) (Ioi 0) :=
  continuousOn_tsum_modal (coeff_bound ξ₀)

/-- `h'` is continuous on `(0, ∞)`. -/
theorem continuousOn_kernelDeriv (ξ₀ : ℝ) : ContinuousOn (kernelDeriv ξ₀) (Ioi 0) :=
  continuousOn_tsum_modal (coeffDeriv_bound ξ₀)

/-! ### The method of images -/

/-- Gaussian sums over the shifted even integers converge: `∑ₘ exp(-c (2m - ξ)²) < ∞` for
`c > 0` (from the Jacobi theta series). -/
theorem summable_exp_neg_mul_sq (ξ : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * (2 * m - ξ) ^ 2) := by
  have h := ((summable_jacobiTheta₂_term_iff (Complex.I * (-2 * c * ξ / Real.pi : ℝ))
    (Complex.I * (4 * c / Real.pi : ℝ))).2 (by simp; positivity)).norm.mul_left
      (Real.exp (-c * ξ ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/-- **Method of images** (`app:boundary-heat-informative`: `S(t) b = -K_N(t, ·, 0)`):
`h(t) = -(πt)^{-1/2} ∑ₘ exp(-(2m - ξ₀)²/4t)`.  Poisson summation
(`Complex.tsum_exp_neg_quadratic` with `a = πt`, `b = iξ₀/2`). -/
theorem kernel_eq_images {ξ₀ t : ℝ} (_hξ₀ : ξ₀ ∈ Ioo 0 1) (ht : 0 < t) :
    kernel ξ₀ t = -(Real.sqrt (Real.pi * t))⁻¹ *
      ∑' m : ℤ, Real.exp (-(2 * m - ξ₀) ^ 2 / (4 * t)) := by
  have ha : 0 < ((Real.pi * t : ℝ) : ℂ).re := by simp; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha (Complex.I * ξ₀ / 2)
  set f : ℤ → ℂ := fun n => Complex.exp (-Real.pi * ((Real.pi * t : ℝ) : ℂ) * n ^ 2 +
    2 * Real.pi * (Complex.I * ξ₀ / 2) * n) with hf_def
  have hf : Summable f := by
    have := (summable_jacobiTheta₂_term_iff (ξ₀ / 2 : ℂ) (Complex.I * (Real.pi * t : ℝ))).2
      (by simp; positivity)
    refine this.congr fun n => ?_
    simp only [jacobiTheta₂_term, hf_def]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hpair : ∀ n : ℕ, f n + f (-n) =
      ((2 * Real.cos (n * Real.pi * ξ₀) * Real.exp (eig n * t) : ℝ) : ℂ) := by
    intro n
    push_cast
    rw [Complex.two_cos, add_mul, ← Complex.exp_add, ← Complex.exp_add]
    simp only [hf_def, eig]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hterm : ∀ n : ℕ, ((obsCoeff ξ₀ n * ctrlCoeff n * Real.exp (eig n * t) : ℝ) : ℂ) =
      -(f n + f (-n)) + if n = 0 then 1 else 0 := by
    intro n
    rw [hpair]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [obsCoeff, ctrlCoeff, eig]; norm_num
    · simp only [obsCoeff, ctrlCoeff, hn, ↓reduceIte, add_zero]
      push_cast
      have : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
      linear_combination (-(Complex.cos (n * Real.pi * ξ₀)) * Complex.exp (eig n * t)) * this
  have hsum : HasSum (fun n : ℕ => ((obsCoeff ξ₀ n * ctrlCoeff n * Real.exp (eig n * t) : ℝ) : ℂ))
      (-(∑' n, f n)) := by
    have := (hf.hasSum.nat_add_neg.neg).add (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
    convert this using 1
    · funext n; exact hterm n
    · simp [hf_def]
  have hL : ((kernel ξ₀ t : ℝ) : ℂ) = -(∑' n, f n) := by
    rw [kernel, Complex.ofReal_tsum]; exact hsum.tsum_eq
  have hR1 : ((Real.pi * t : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi * t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hR2 : ∀ n : ℤ, Complex.exp (-Real.pi / ((Real.pi * t : ℝ) : ℂ) *
      (n + Complex.I * (Complex.I * ξ₀ / 2)) ^ 2) =
      ((Real.exp (-(2 * n - ξ₀) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  apply Complex.ofReal_injective
  rw [hL, hP, hR1, tsum_congr hR2, ← Complex.ofReal_tsum]
  push_cast
  ring

/-! ### Bounds on `(0, ∞)` (`eq:heat-separated-kernel`)

On `(0, 1]` every image term and its time derivative are bounded by `K e^{-x²/8}`, because
the images `x = 2m - ξ₀` stay at distance `ξ₀` from `0`.  On `[1, ∞)` the modal series is
dominated by its value at `t = 1`. -/

/-- One image term `(πt)^{-1/2} exp(-x²/4t)` of the Neumann heat kernel. -/
def imageTerm (x t : ℝ) : ℝ := (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))

/-- The `t`-derivative of `imageTerm x`. -/
def imageTermDeriv (x t : ℝ) : ℝ := imageTerm x t * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))

/-- `∂ₜ imageTerm x t = imageTerm x t · (x²/4t² - 1/2t)` for `t > 0`. -/
theorem hasDerivAt_imageTerm (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (imageTerm x) (imageTermDeriv x t) t := by
  have hpt : 0 < Real.pi * t := by positivity
  have hsq : Real.sqrt (Real.pi * t) ≠ 0 := (Real.sqrt_pos.2 hpt).ne'
  have h1 := (((hasDerivAt_id' t).const_mul Real.pi).sqrt (by simpa using hpt.ne')).inv hsq
  have h2 := ((hasDerivAt_inv ht.ne').const_mul (-x ^ 2 / 4)).exp
  have h3 := h1.mul h2
  have hfun : imageTerm x = fun s => (Real.sqrt (Real.pi * s))⁻¹ *
      Real.exp (-x ^ 2 / 4 * s⁻¹) := by
    funext s; simp only [imageTerm]; congr 2; ring
  rw [hfun]
  convert h3 using 1
  have hs2 : Real.sqrt (Real.pi * t) ^ 2 = Real.pi * t := Real.sq_sqrt hpt.le
  simp only [imageTermDeriv, imageTerm, mul_one, Pi.inv_apply]
  rw [show -x ^ 2 / (4 * t) = -x ^ 2 / 4 * t⁻¹ by ring]
  field_simp
  rw [hs2]
  ring

/-- `yʲ e^{-2y} ≤ j! e^{-y}` for `y ≥ 0`. -/
private theorem pow_mul_exp_le {y : ℝ} (hy : 0 ≤ y) (j : ℕ) :
    y ^ j * Real.exp (-(2 * y)) ≤ j.factorial * Real.exp (-y) := by
  have h := Real.pow_div_factorial_le_exp y hy j
  have hf : (0 : ℝ) < j.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  calc y ^ j * Real.exp (-(2 * y)) ≤ (Real.exp y * j.factorial) * Real.exp (-(2 * y)) := by
        gcongr
    _ = j.factorial * (Real.exp y * Real.exp (-(2 * y))) := by ring
    _ = j.factorial * Real.exp (-y) := by rw [← Real.exp_add]; ring_nf

/-- Bounds of the image terms on `(0, 1]`, uniform in the distance `|x| ≥ d`. -/
private theorem image_bounds {x t d : ℝ} (hd : 0 < d) (hx : d ^ 2 ≤ x ^ 2) (ht : 0 < t)
    (ht1 : t ≤ 1) :
    |imageTerm x t| ≤ 8 / d ^ 2 * Real.exp (-(1 / 8) * x ^ 2) ∧
      |imageTermDeriv x t| ≤ 832 / d ^ 4 * Real.exp (-(1 / 8) * x ^ 2) := by
  set s := t⁻¹ with hs_def
  set y := x ^ 2 * s / 8 with hy_def
  have hs1 : 1 ≤ s := one_le_inv_iff₀.2 ⟨ht, ht1⟩
  have hs0 : 0 < s := by positivity
  have hy : 0 ≤ y := by positivity
  have hyx : -y ≤ -(1 / 8) * x ^ 2 := by
    rw [hy_def]; nlinarith [sq_nonneg x]
  have hsy : s * d ^ 2 ≤ 8 * y := by
    rw [hy_def]; nlinarith
  have hsy' : s ≤ 8 / d ^ 2 * y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
  have hE : Real.exp (-x ^ 2 / (4 * t)) = Real.exp (-(2 * y)) := by
    congr 1; rw [hy_def, hs_def]; field_simp; ring
  have hsqrt : (Real.sqrt (Real.pi * t))⁻¹ ≤ s := by
    rw [hs_def]
    apply inv_anti₀ ht
    rw [Real.le_sqrt ht.le (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (-y) ≤ Real.exp (-(1 / 8) * x ^ 2) := Real.exp_le_exp.2 hyx
  have hT : |imageTerm x t| ≤ s * Real.exp (-(2 * y)) := by
    rw [imageTerm, hE, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
      abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    gcongr
  constructor
  · calc |imageTerm x t| ≤ s * Real.exp (-(2 * y)) := hT
      _ ≤ (8 / d ^ 2 * y) * Real.exp (-(2 * y)) := by gcongr
      _ = 8 / d ^ 2 * (y ^ 1 * Real.exp (-(2 * y))) := by ring
      _ ≤ 8 / d ^ 2 * ((1 : ℕ).factorial * Real.exp (-y)) := by
          exact mul_le_mul_of_nonneg_left (pow_mul_exp_le hy 1) (by positivity)
      _ ≤ 8 / d ^ 2 * Real.exp (-(1 / 8) * x ^ 2) := by
          simp only [Nat.factorial_one, Nat.cast_one, one_mul]; gcongr
  · have hfac : x ^ 2 / (4 * t ^ 2) - 1 / (2 * t) = 2 * y * s - s / 2 := by
      rw [hy_def, hs_def]; field_simp; ring
    have hfac' : |x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤ 2 * y * s + s / 2 := by
      rw [hfac, abs_le]; constructor <;> nlinarith
    have hss : s ^ 2 ≤ (8 / d ^ 2) ^ 2 * y ^ 2 := by
      rw [← mul_pow]; gcongr
    have hE0 : 0 ≤ Real.exp (-(2 * y)) := (Real.exp_pos _).le
    have h3 := pow_mul_exp_le hy 3
    have h2 := pow_mul_exp_le hy 2
    simp only [Nat.factorial, Nat.succ_eq_add_one] at h3 h2
    norm_num at h3 h2
    calc |imageTermDeriv x t| = |imageTerm x t| * |x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| := by
          rw [imageTermDeriv, abs_mul]
      _ ≤ (s * Real.exp (-(2 * y))) * (2 * y * s + s / 2) := by
          gcongr
      _ = (2 * y + 1 / 2) * s ^ 2 * Real.exp (-(2 * y)) := by ring
      _ ≤ (2 * y + 1 / 2) * ((8 / d ^ 2) ^ 2 * y ^ 2) * Real.exp (-(2 * y)) := by gcongr
      _ = 64 / d ^ 4 * (2 * (y ^ 3 * Real.exp (-(2 * y))) +
            1 / 2 * (y ^ 2 * Real.exp (-(2 * y)))) := by
          field_simp; ring
      _ ≤ 64 / d ^ 4 * (2 * (6 * Real.exp (-y)) + 1 / 2 * (2 * Real.exp (-y))) := by
          gcongr
      _ = 832 / d ^ 4 * Real.exp (-y) := by ring
      _ ≤ 832 / d ^ 4 * Real.exp (-(1 / 8) * x ^ 2) := by gcongr

/-- Every image `2m - ξ₀` is at distance at least `ξ₀` from `0`. -/
theorem sq_le_sq_image {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (m : ℤ) : ξ₀ ^ 2 ≤ (2 * m - ξ₀) ^ 2 := by
  obtain ⟨h0, h1⟩ := hξ₀
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm
    nlinarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- The summable majorant of the image terms. -/
private theorem summable_image_bound (ξ₀ : ℝ) :
    Summable fun m : ℤ => Real.exp (-(1 / 8) * (2 * (m : ℝ) - ξ₀) ^ 2) :=
  summable_exp_neg_mul_sq ξ₀ (by norm_num)

/-- `h(t) = -∑ₘ imageTerm (2m - ξ₀) t` on `(0, ∞)`. -/
theorem kernel_eq_tsum_imageTerm {ξ₀ t : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (ht : 0 < t) :
    kernel ξ₀ t = -∑' m : ℤ, imageTerm (2 * m - ξ₀) t := by
  rw [kernel_eq_images hξ₀ ht, neg_mul, ← tsum_mul_left]
  rfl

/-- `h'(t) = -∑ₘ ∂ₜ imageTerm (2m - ξ₀) t` on `(0, 1)`: the image series may be differentiated
termwise. -/
theorem kernelDeriv_eq_tsum_imageTermDeriv {ξ₀ t : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (ht : 0 < t)
    (ht1 : t < 1) : kernelDeriv ξ₀ t = -∑' m : ℤ, imageTermDeriv (2 * m - ξ₀) t := by
  have hd : 0 < ξ₀ := hξ₀.1
  have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
  have hder : ∀ (m : ℤ) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s => imageTerm (2 * m - ξ₀) s) (imageTermDeriv (2 * m - ξ₀) s) s :=
    fun m s hs => hasDerivAt_imageTerm _ hs.1
  have hbd : ∀ (m : ℤ) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      ‖imageTermDeriv (2 * m - ξ₀) s‖ ≤
        832 / ξ₀ ^ 4 * Real.exp (-(1 / 8) * (2 * (m : ℝ) - ξ₀) ^ 2) := by
    intro m s hs
    rw [Real.norm_eq_abs]
    exact (image_bounds hd (sq_le_sq_image hξ₀ m) hs.1 hs.2.le).2
  have hsum : Summable fun m : ℤ => imageTerm (2 * m - ξ₀) t := by
    have := (summable_exp_neg_mul_sq ξ₀ (c := 1 / (4 * t)) (by positivity)).mul_left
      (Real.sqrt (Real.pi * t))⁻¹
    refine this.congr fun m => ?_
    simp only [imageTerm]
    congr 2
    ring
  have hS : HasDerivAt (fun s => ∑' m : ℤ, imageTerm (2 * m - ξ₀) s)
      (∑' m : ℤ, imageTermDeriv (2 * m - ξ₀) t) t :=
    hasDerivAt_tsum_of_isPreconnected ((summable_image_bound ξ₀).mul_left (832 / ξ₀ ^ 4))
      isOpen_Ioo isPreconnected_Ioo hder hbd hmem hsum hmem
  have heq : kernel ξ₀ =ᶠ[𝓝 t] fun s => -∑' m : ℤ, imageTerm (2 * m - ξ₀) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact kernel_eq_tsum_imageTerm hξ₀ hs
  exact (hasDerivAt_kernel ξ₀ ht).unique (hS.neg.congr_of_eventuallyEq heq)

/-- `h` is bounded on `(0, ∞)` (`eq:heat-separated-kernel`, scalar form): every image is at
distance at least `ξ₀` from the observation point. -/
theorem exists_abs_kernel_le {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) :
    ∃ K, ∀ t > 0, |kernel ξ₀ t| ≤ K := by
  have hd : 0 < ξ₀ := hξ₀.1
  refine ⟨max (∑' m : ℤ, 8 / ξ₀ ^ 2 * Real.exp (-(1 / 8) * (2 * (m : ℝ) - ξ₀) ^ 2))
    (2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 0 * Real.exp (eig n * 1)), fun t ht => ?_⟩
  rcases le_or_gt t 1 with ht1 | ht1
  · refine le_trans ?_ (le_max_left _ _)
    rw [kernel_eq_tsum_imageTerm hξ₀ ht, abs_neg, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded ((summable_image_bound ξ₀).mul_left _).hasSum fun m => ?_
    rw [Real.norm_eq_abs]
    exact (image_bounds hd (sq_le_sq_image hξ₀ m) ht ht1).1
  · exact le_trans (abs_tsum_modal_le (coeff_bound ξ₀) one_pos ht1.le) (le_max_right _ _)

/-- `h'` is bounded on `(0, ∞)` (`eq:heat-separated-kernel`, scalar form). -/
theorem exists_abs_kernelDeriv_le {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) :
    ∃ K, ∀ t > 0, |kernelDeriv ξ₀ t| ≤ K := by
  have hd : 0 < ξ₀ := hξ₀.1
  refine ⟨max (∑' m : ℤ, 832 / ξ₀ ^ 4 * Real.exp (-(1 / 8) * (2 * (m : ℝ) - ξ₀) ^ 2))
    (2 * Real.pi ^ 2 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (eig n * 1)), fun t ht => ?_⟩
  rcases lt_or_ge t 1 with ht1 | ht1
  · refine le_trans ?_ (le_max_left _ _)
    rw [kernelDeriv_eq_tsum_imageTermDeriv hξ₀ ht ht1, abs_neg, ← Real.norm_eq_abs]
    refine tsum_of_norm_bounded ((summable_image_bound ξ₀).mul_left _).hasSum fun m => ?_
    rw [Real.norm_eq_abs]
    exact (image_bounds hd (sq_le_sq_image hξ₀ m) ht ht1.le).2
  · exact le_trans (abs_tsum_modal_le (coeffDeriv_bound ξ₀) one_pos ht1) (le_max_right _ _)

/-! ### Unboundedness of the observation and of the control -/

/-- `∑ₙ cₙ² = ∞` (`app:boundary-heat-informative`: point evaluation is unbounded on `X`).
This holds for every `ξ₀`, because `cos² (nθ) → 0` would force `cos (2nθ) → -1`. -/
theorem not_summable_obsCoeff_sq (ξ₀ : ℝ) : ¬ Summable fun n => obsCoeff ξ₀ n ^ 2 := by
  intro h
  have h0 := h.tendsto_atTop_zero
  -- `cos² (nθ) → 0`
  have hc : Tendsto (fun n : ℕ => Real.cos (n * Real.pi * ξ₀) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => obsCoeff ξ₀ n ^ 2 / 2) atTop (𝓝 0) := by
      simpa using h0.div_const 2
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [obsCoeff, hn, ↓reduceIte, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  -- along `2n`: `cos² (2nθ) → 0`
  have h2 : Tendsto (fun n : ℕ => Real.cos ((2 * n : ℕ) * Real.pi * ξ₀) ^ 2) atTop (𝓝 0) :=
    hc.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  -- but `cos (2nθ) = 2 cos² (nθ) - 1 → -1`
  have h3 : Tendsto (fun n : ℕ => Real.cos ((2 * n : ℕ) * Real.pi * ξ₀) ^ 2) atTop (𝓝 1) := by
    have h4 : Tendsto (fun n : ℕ => (2 * Real.cos (n * Real.pi * ξ₀) ^ 2 - 1) ^ 2) atTop
        (𝓝 ((2 * 0 - 1) ^ 2)) :=
      ((hc.const_mul 2).sub_const 1).pow 2
    norm_num at h4
    refine h4.congr fun n => ?_
    rw [show ((2 * n : ℕ) : ℝ) * Real.pi * ξ₀ = 2 * (n * Real.pi * ξ₀) by push_cast; ring,
      Real.cos_two_mul]
  exact zero_ne_one (tendsto_nhds_unique h2 h3)

/-- `∑ₙ bₙ² = ∞` (`app:boundary-heat-informative`: `b ∉ X`, the control is unbounded on `X`). -/
theorem not_summable_ctrlCoeff_sq : ¬ Summable fun n => ctrlCoeff n ^ 2 := by
  intro h
  have h0 := h.tendsto_atTop_zero
  have h2 : Tendsto (fun n : ℕ => ctrlCoeff n ^ 2) atTop (𝓝 2) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [ctrlCoeff, hn]
  exact (by norm_num : (0 : ℝ) ≠ 2) (tendsto_nhds_unique h0 h2)

end BoundaryHeat

end DataDrivenControl
