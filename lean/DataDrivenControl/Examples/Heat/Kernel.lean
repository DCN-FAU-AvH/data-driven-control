module

public import Mathlib
public import DataDrivenControl.Analysis.CosineBasis

/-!
# The modal numbers and the impulse response of the boundary-controlled heat equation

Paper: `ex:boundary-heat-informative` (`informativity.tex`), `app:boundary-heat-informative`
and `eq:heat-separated-kernel` (`appendix_proofs.tex`).

The Neumann heat equation on `(0, 1)` has eigenvalues `λₙ = -(nπ)²` and normalised
eigenfunctions `e₀ = 1`, `eₙ = √2 cos(nπξ)` (`CosineBasis.cosFun`).  The Neumann control at `0`
has the modal coefficients `bₙ = -eₙ(0)`, and the point observation at `ξ₀` has the coefficients
`cₙ = eₙ(ξ₀)`.  With `b = -δ₀`, the orbit is `(S(t) b)(ξ) = ∑ₙ eₙ(ξ) bₙ e^{λₙ t}` (`kernel ξ t`).

## Main declarations

* `eig`, `ctrlCoeff`, `obsCoeff`: `λₙ`, `bₙ`, `cₙ`, with `eig_eq_cosEig`, `ctrlCoeff_eq_neg_cosFun`,
  `obsCoeff_eq_cosFun`; `eig_injective`, `ctrlCoeff_ne_zero`, `|bₙ|, |cₙ| ≤ √2`;
  `not_summable_ctrlCoeff_sq`, `not_summable_obsCoeff_sq` (`b, (cₙ) ∉ ℓ²`: `B` and `C` are
  unbounded on `X`).
* `kernel ξ t = (S(t) b)(ξ)`, `kernelDeriv ξ t = ∂ₜ (S(t) b)(ξ)` (`q'(t)` at `ξ`) and
  `kernelDerivX ξ t = ∂_ξ ∂ₜ (S(t) b)(ξ)` (`hasDerivAt_kernelDeriv_x`).
* `kernel_eq_images`: **the method of images** `S(t) b = -K_N(t, ·, 0)`,
  `(S(t) b)(ξ) = -(πt)^{-1/2} ∑ₘ exp(-(2m - ξ)²/4t)` (Poisson summation,
  `Complex.tsum_exp_neg_quadratic`).
* `exists_abs_kernelDeriv_le_unif`: **`eq:heat-separated-kernel` on `supp χ`**: `q'` and `∂_ξ q'`
  are bounded on `(0, ∞) × [d, 1)` for every `d > 0`.

## Proof of the bounds

For `0 < t ≤ 1`, `|x| ≥ d` and `i ≤ k ≤ 3`, an image term `(πt)^{-1/2} e^{-x²/4t}` times
`t^{-k} |x|^i` is at most `(8/d²)⁴ · 24 · e^{-x²/8}` (`abs_imageTerm_mul_le_const`, from
`yʲ e^{-2y} ≤ j! e^{-y}`), and `e^{-(2m - ξ)²/8} ≤ e^{1/4} e^{-m²/4}` for `ξ ∈ [0, 1]` gives a
majorant independent of `ξ` (`exp_image_le`); every image `2m - ξ` of `ξ ∈ [d, 1]` is at distance
at least `d` from `0`.  The image series is differentiated termwise in `t` and in `ξ`, and the
results are identified with the modal series by uniqueness of derivatives.  On `[1, ∞)` the modal
series are dominated by their values at `t = 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace DataDrivenControl

namespace BoundaryHeat

open CosineBasis

/-! ### The modal numbers -/

/-- The Neumann eigenvalues `λₙ = -(nπ)²` (`app:boundary-heat-informative`). -/
def eig (n : ℕ) : ℝ := -((n : ℝ) * Real.pi) ^ 2

/-- The modal coefficients `bₙ = -eₙ(0)` of the Neumann boundary control at `0`
(`app:boundary-heat-informative`: `b = -δ₀`, `b₀ = -1`, `bₙ = -√2`). -/
def ctrlCoeff (n : ℕ) : ℝ := if n = 0 then -1 else -Real.sqrt 2

/-- The modal coefficients `cₙ = eₙ(ξ₀)` of the point observation at `ξ₀`
(`ex:boundary-heat-informative`). -/
def obsCoeff (ξ₀ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else Real.sqrt 2 * Real.cos (n * Real.pi * ξ₀)

/-- `λₙ = -(nπ)²` are the eigenvalues of the cosine basis. -/
theorem eig_eq_cosEig : eig = cosEig := rfl

/-- `cₙ = eₙ(ξ₀)`: the observation coefficients are the values of the eigenfunctions at `ξ₀`. -/
theorem obsCoeff_eq_cosFun (ξ₀ : ℝ) (n : ℕ) : obsCoeff ξ₀ n = cosFun n ξ₀ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [obsCoeff]
  · rw [cosFun_of_ne_zero hn]
    simp [obsCoeff, hn]

/-- `bₙ = -eₙ(0)`: the control coefficients are minus the values of the eigenfunctions at `0`. -/
theorem ctrlCoeff_eq_neg_cosFun (n : ℕ) : ctrlCoeff n = -cosFun n 0 := by
  rw [cosFun_apply_zero, ctrlCoeff, cosNorm]
  split_ifs <;> rfl

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

/-! ### Modal series -/

/-- `e^{λₙ t}` is antitone in `t`. -/
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

/-! ### The orbit of `b` and its derivatives -/

/-- The orbit `(S(t) b)(ξ) = ∑ₙ eₙ(ξ) bₙ e^{λₙ t}` of `b = -δ₀`, i.e. the impulse response
`C S(t) b` for the observation point `ξ` (`app:boundary-heat-informative`).  It is meaningful
for `t > 0`. -/
def kernel (ξ t : ℝ) : ℝ := ∑' n, obsCoeff ξ n * ctrlCoeff n * Real.exp (eig n * t)

/-- `q'(t)` at `ξ`: `∂ₜ (S(t) b)(ξ) = ∑ₙ eₙ(ξ) bₙ λₙ e^{λₙ t}` (`eq:heat-separated-kernel`). -/
def kernelDeriv (ξ t : ℝ) : ℝ :=
  ∑' n, obsCoeff ξ n * ctrlCoeff n * eig n * Real.exp (eig n * t)

/-- `∂_ξ q'(t)` at `ξ`: `∂_ξ ∂ₜ (S(t) b)(ξ) = ∑ₙ eₙ'(ξ) bₙ λₙ e^{λₙ t}`
(`eq:heat-separated-kernel`). -/
def kernelDerivX (ξ t : ℝ) : ℝ :=
  ∑' n, cosDeriv n ξ * ctrlCoeff n * eig n * Real.exp (eig n * t)

/-- `|eₙ(ξ) bₙ| ≤ 2 (n + 1)⁰`, in the form of the generic modal lemmas. -/
private theorem abs_coeff_le (ξ : ℝ) (n : ℕ) :
    |obsCoeff ξ n * ctrlCoeff n| ≤ 2 * ((n : ℝ) + 1) ^ 0 := by
  simpa using abs_obsCoeff_mul_ctrlCoeff_le ξ n

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

/-- `q' = kernelDeriv` is the derivative of `kernel` on `(0, ∞)`. -/
theorem hasDerivAt_kernel (ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (kernel ξ) (kernelDeriv ξ t) t :=
  hasDerivAt_tsum_modal (abs_coeff_le ξ) ht

/-- `q'` is continuous on `(0, ∞)`. -/
theorem continuousOn_kernelDeriv (ξ : ℝ) : ContinuousOn (kernelDeriv ξ) (Ioi 0) :=
  continuousOn_tsum_modal (abs_coeffDeriv_le ξ)

/-- `∂_ξ q'` is continuous on `(0, ∞)`. -/
theorem continuousOn_kernelDerivX (ξ : ℝ) : ContinuousOn (kernelDerivX ξ) (Ioi 0) :=
  continuousOn_tsum_modal (abs_coeffDerivX_le ξ)

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
  have e1 : (fun ξ => kernelDeriv ξ t) = fun ξ => ∑' n, a n * cosFun n ξ := by
    funext ξ
    simp only [kernelDeriv, ha, obsCoeff_eq_cosFun]
    exact tsum_congr fun n => by ring
  have e2 : kernelDerivX ξ t = ∑' n, a n * cosDeriv n ξ := by
    simp only [kernelDerivX, ha]
    exact tsum_congr fun n => by ring
  rw [e1, e2]
  exact hasDerivAt_tsum_cosFun hsum ξ

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
`(S(t) b)(ξ) = -(πt)^{-1/2} ∑ₘ exp(-(2m - ξ)²/4t)`.  Poisson summation
(`Complex.tsum_exp_neg_quadratic` with `a = πt`, `b = iξ/2`). -/
theorem kernel_eq_images {ξ t : ℝ} (ht : 0 < t) :
    kernel ξ t = -(Real.sqrt (Real.pi * t))⁻¹ *
      ∑' m : ℤ, Real.exp (-(2 * m - ξ) ^ 2 / (4 * t)) := by
  have ha : 0 < ((Real.pi * t : ℝ) : ℂ).re := by simp; positivity
  have hP := Complex.tsum_exp_neg_quadratic ha (Complex.I * ξ / 2)
  set f : ℤ → ℂ := fun n => Complex.exp (-Real.pi * ((Real.pi * t : ℝ) : ℂ) * n ^ 2 +
    2 * Real.pi * (Complex.I * ξ / 2) * n) with hf_def
  have hf : Summable f := by
    have := (summable_jacobiTheta₂_term_iff (ξ / 2 : ℂ) (Complex.I * (Real.pi * t : ℝ))).2
      (by simp; positivity)
    refine this.congr fun n => ?_
    simp only [jacobiTheta₂_term, hf_def]
    congr 1
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hpair : ∀ n : ℕ, f n + f (-n) =
      ((2 * Real.cos (n * Real.pi * ξ) * Real.exp (eig n * t) : ℝ) : ℂ) := by
    intro n
    push_cast
    rw [Complex.two_cos, add_mul, ← Complex.exp_add, ← Complex.exp_add]
    simp only [hf_def, eig]
    push_cast
    congr 1 <;> congr 1 <;> ring
  have hterm : ∀ n : ℕ, ((obsCoeff ξ n * ctrlCoeff n * Real.exp (eig n * t) : ℝ) : ℂ) =
      -(f n + f (-n)) + if n = 0 then 1 else 0 := by
    intro n
    rw [hpair]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [obsCoeff, ctrlCoeff, eig]; norm_num
    · simp only [obsCoeff, ctrlCoeff, hn, ↓reduceIte, add_zero]
      push_cast
      have : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
      linear_combination (-(Complex.cos (n * Real.pi * ξ)) * Complex.exp (eig n * t)) * this
  have hsum : HasSum (fun n : ℕ => ((obsCoeff ξ n * ctrlCoeff n * Real.exp (eig n * t) : ℝ) : ℂ))
      (-(∑' n, f n)) := by
    have := (hf.hasSum.nat_add_neg.neg).add (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
    convert this using 1
    · funext n; exact hterm n
    · simp [hf_def]
  have hL : ((kernel ξ t : ℝ) : ℂ) = -(∑' n, f n) := by
    rw [kernel, Complex.ofReal_tsum]; exact hsum.tsum_eq
  have hR1 : ((Real.pi * t : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi * t) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hR2 : ∀ n : ℤ, Complex.exp (-Real.pi / ((Real.pi * t : ℝ) : ℂ) *
      (n + Complex.I * (Complex.I * ξ / 2)) ^ 2) =
      ((Real.exp (-(2 * n - ξ) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
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

/-! ### The image terms -/

/-- One image term `(πt)^{-1/2} exp(-x²/4t)` of the Neumann heat kernel. -/
def imageTerm (x t : ℝ) : ℝ := (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t))

/-- The `t`-derivative of `imageTerm x`. -/
def imageTermDeriv (x t : ℝ) : ℝ := imageTerm x t * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))

/-- The `x`-derivative of `imageTerm`: `imageTerm x t · (-x/2t)`. -/
def imageTermX (x t : ℝ) : ℝ := imageTerm x t * (-x / (2 * t))

/-- The mixed derivative `∂ₓ ∂ₜ imageTerm x t = imageTerm x t · (3x/4t² - x³/8t³)`. -/
def imageTermDerivX (x t : ℝ) : ℝ :=
  imageTerm x t * (3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3))

/-- `∂ₜ imageTerm x t = imageTermDeriv x t` for `t > 0`. -/
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
theorem sq_le_sq_image {d ξ : ℝ} (hd : 0 < d) (hξ : d ≤ ξ) (hξ1 : ξ ≤ 1) (m : ℤ) :
    d ^ 2 ≤ (2 * m - ξ) ^ 2 := by
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
  refine (abs_imageTermDeriv_le hd hd1 (sq_le_sq_image hd hξ hξ1 m) ht ht1).trans ?_
  gcongr
  exact exp_image_le (hd.le.trans hξ) hξ1 m

/-- The image term `imageTermDerivX (2m - ξ) t` with `ξ ∈ [d, 1]`, `0 < t ≤ 1`, against the uniform
majorant. -/
theorem norm_imageTermDerivX_le {d ξ t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hξ : d ≤ ξ)
    (hξ1 : ξ ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) (m : ℤ) :
    ‖imageTermDerivX (2 * m - ξ) t‖ ≤ (8 / d ^ 2) ^ 4 * 24 *
      (Real.exp (1 / 4) * Real.exp (-(1 / 16) * (2 * (m : ℝ) - 0) ^ 2)) := by
  rw [Real.norm_eq_abs]
  refine (abs_imageTermDerivX_le hd hd1 (sq_le_sq_image hd hξ hξ1 m) ht ht1).trans ?_
  gcongr
  exact exp_image_le (hd.le.trans hξ) hξ1 m

/-! ### The image series -/

/-- `(S(t) b)(ξ) = -∑ₘ imageTerm (2m - ξ) t` for `t > 0`. -/
theorem kernel_eq_tsum_imageTerm {ξ t : ℝ} (ht : 0 < t) :
    kernel ξ t = -∑' m : ℤ, imageTerm (2 * m - ξ) t := by
  rw [kernel_eq_images ht, neg_mul, ← tsum_mul_left]
  rfl

/-- `q'(t)(ξ) = -∑ₘ ∂ₜ imageTerm (2m - ξ) t` on `(0, 1)`, for `ξ ∈ (0, 1)`: the image series may
be differentiated termwise in `t`. -/
theorem kernelDeriv_eq_tsum_imageTermDeriv {ξ t : ℝ} (hξ : ξ ∈ Ioo 0 1) (ht : 0 < t)
    (ht1 : t < 1) : kernelDeriv ξ t = -∑' m : ℤ, imageTermDeriv (2 * m - ξ) t := by
  have hmem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
  have hder : ∀ (m : ℤ) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s => imageTerm (2 * m - ξ) s) (imageTermDeriv (2 * m - ξ) s) s :=
    fun m s hs => hasDerivAt_imageTerm _ hs.1
  have hbd : ∀ (m : ℤ) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      ‖imageTermDeriv (2 * m - ξ) s‖ ≤
        (8 / ξ ^ 2) ^ 4 * 24 * Real.exp (-(1 / 8) * (2 * (m : ℝ) - ξ) ^ 2) := fun m s hs => by
    rw [Real.norm_eq_abs]
    exact abs_imageTermDeriv_le hξ.1 hξ.2.le (sq_le_sq_image hξ.1 le_rfl hξ.2.le m) hs.1 hs.2.le
  have hsum : Summable fun m : ℤ => imageTerm (2 * m - ξ) t := by
    have := (summable_exp_neg_mul_sq ξ (c := 1 / (4 * t)) (by positivity)).mul_left
      (Real.sqrt (Real.pi * t))⁻¹
    refine this.congr fun m => ?_
    simp only [imageTerm]
    congr 2
    ring
  have hS : HasDerivAt (fun s => ∑' m : ℤ, imageTerm (2 * m - ξ) s)
      (∑' m : ℤ, imageTermDeriv (2 * m - ξ) t) t :=
    hasDerivAt_tsum_of_isPreconnected
      ((summable_exp_neg_mul_sq ξ (by norm_num)).mul_left ((8 / ξ ^ 2) ^ 4 * 24))
      isOpen_Ioo isPreconnected_Ioo hder hbd hmem hsum hmem
  have heq : kernel ξ =ᶠ[𝓝 t] fun s => -∑' m : ℤ, imageTerm (2 * m - ξ) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact kernel_eq_tsum_imageTerm hs
  exact (hasDerivAt_kernel ξ ht).unique (hS.neg.congr_of_eventuallyEq heq)

/-- **The image series of `∂_ξ q'`** on `(0, 1)`:
`kernelDerivX ξ t = ∑ₘ ∂ₓ ∂ₜ imageTerm (2m - ξ) t`, by termwise `ξ`-differentiation of the image
series of `kernelDeriv`. -/
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

end BoundaryHeat

end DataDrivenControl
