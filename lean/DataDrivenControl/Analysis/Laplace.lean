module

public import Mathlib

/-!
# The Laplace transform

Used by `lem:transfer-laplace` (`eq:analytic-transfer-laplace`)
and the Laplace-uniqueness steps of `app:analytic-universal-sufficiency`.

Mathlib has `mellin` but no Laplace transform; the substitution `x = e^{-r}` turns Mellin
into Laplace only for functions with power bounds at `0` and `∞`, which is the wrong class here
(locally integrable functions of exponential growth), so the transform is set up directly.

All functions take values in a complex Banach space `E`; operator-valued functions
`f : ℝ → E →L[ℂ] F` are the special case `E := E →L[ℂ] F` (see `laplace_apply`).

## Main definitions

* `laplace f s = ∫_{(0,∞)} e^{-s r} f r dr` (a Bochner integral, `0` if it diverges);
* `LaplaceIntegrable f σ`: `r ↦ e^{-σ r} f r` is integrable on `(0, ∞)`, i.e. the Laplace
  integral converges absolutely at the real abscissa `σ`.

## Main results

* `LaplaceIntegrable.integrableOn`: absolute convergence on the closed half-plane `σ ≤ Re s`;
  `laplaceIntegrable_of_le_exp`: locally integrable functions with `‖f r‖ ≤ C e^{σ₀ r}` for
  large `r` are Laplace integrable at every `σ > σ₀`;
* linearity, `laplace_comp_comm` (commutation with bounded linear maps), `laplace_apply`;
* `tendsto_intervalIntegral_laplace`, `tendsto_setIntegral_Ioc_laplace`: the transform is the
  limit of the truncated integrals `∫₀ᵗ`;
* `hasDerivAt_laplace`, `differentiableOn_laplace`, `analyticOnNhd_laplace`: holomorphy on the
  open half-plane `σ < Re s`, with derivative `-𝓛(r f)`;
* `tendsto_laplace_atTop`: `𝓛 f x → 0` as the real variable `x → ∞`;
* uniqueness: `ae_eq_zero_of_integral_Ioi_cexp_smul_nat_eq_zero` (on any half-line `(a, ∞)`,
  vanishing at `σ + n` for all `n : ℕ`), `ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero`
  (vanishing at all large real abscissae), and for `laplace`:
  `ae_eq_zero_of_laplace_nat_eq_zero`, `ae_eq_zero_of_laplace_eventually_eq_zero`,
  `ae_eq_zero_of_laplace_eq_zero`, `ae_eq_zero_of_laplace_frequently_eq_zero` (zeros with an
  accumulation point in the half-plane), `ae_eq_of_laplace_eq`, and the weak forms
  `ae_eq_zero_of_laplace_comp_eq_zero`, `ae_eq_zero_of_laplace_inner_eq_zero`.

The uniqueness proof avoids any change of variables: with `x(r) = e^{-(r-a)}`, the hypothesis
says that `∫ p(x(r)) e^{-σ r} f r dr = 0` for every real polynomial `p`; a test function `g`
supported in `(a, ∞)` is `ψ ∘ x` for a continuous `ψ` on `[0, 1]`, which Weierstrass
approximates uniformly by polynomials, and the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) concludes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Complex Real InnerProductSpace

noncomputable section

set_option autoImplicit false

namespace DataDrivenControl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Definitions -/

/-- The **Laplace transform** `𝓛 f s = ∫₀^∞ e^{-s r} f r dr`, as a Bochner integral over
`(0, ∞)` (hence `0` when the integral does not converge absolutely).  This is the transform of
`eq:analytic-transfer-laplace` (`lem:transfer-laplace`). -/
def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ r in Ioi (0 : ℝ), cexp (-(s * r)) • f r

/-- Absolute convergence of the Laplace integral at the real abscissa `σ`:
`r ↦ e^{-σ r} f r` is integrable on `(0, ∞)`.  It implies absolute convergence on the closed
half-plane `σ ≤ Re s` (`LaplaceIntegrable.integrableOn`). -/
def LaplaceIntegrable (f : ℝ → E) (σ : ℝ) : Prop :=
  IntegrableOn (fun r : ℝ ↦ cexp (-(σ * r)) • f r) (Ioi 0)

/-! ### Convergence -/

/-- `‖e^{-s r}‖ = e^{-(Re s) r}` for real `r`. -/
private theorem norm_cexp_neg_mul (s : ℂ) (r : ℝ) :
    ‖cexp (-(s * r))‖ = Real.exp (-(s.re * r)) := by
  rw [Complex.norm_exp]
  simp

/-- The integrand at `s` is the integrand at `σ` times the bounded factor `e^{-(s - σ) r}`. -/
private theorem cexp_smul_eq (f : ℝ → E) (σ : ℝ) (s : ℂ) (r : ℝ) :
    cexp (-(s * r)) • f r = cexp (-((s - σ) * r)) • (cexp (-(σ * r)) • f r) := by
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  ring

/-- Integrability of `e^{-s r} f r` on `(a, ∞)` propagates from `Re s = σ` to `Re s ≥ σ`. -/
private theorem integrableOn_Ioi_cexp_smul_of_le {f : ℝ → E} {a σ : ℝ} {s : ℂ}
    (hf : IntegrableOn (fun r : ℝ ↦ cexp (-(σ * r)) • f r) (Ioi a)) (hs : σ ≤ s.re) :
    IntegrableOn (fun r : ℝ ↦ cexp (-(s * r)) • f r) (Ioi a) := by
  simp_rw [cexp_smul_eq f σ s]
  refine Integrable.bdd_smul (φ := fun r : ℝ ↦ cexp (-((s - σ) * r))) hf
    (Real.exp (-((s.re - σ) * a))) (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
  rw [norm_cexp_neg_mul, Complex.sub_re, Complex.ofReal_re, Real.exp_le_exp, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (le_of_lt hr) (sub_nonneg.2 hs)

/-- The Laplace integrand is integrable on `(0, ∞)` for every `s` with `σ ≤ Re s`. -/
theorem LaplaceIntegrable.integrableOn {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    IntegrableOn (fun r : ℝ ↦ cexp (-(s * r)) • f r) (Ioi 0) :=
  integrableOn_Ioi_cexp_smul_of_le hf hs

/-- Laplace integrability is inherited by larger abscissae. -/
theorem LaplaceIntegrable.mono {f : ℝ → E} {σ σ' : ℝ} (hf : LaplaceIntegrable f σ)
    (h : σ ≤ σ') : LaplaceIntegrable f σ' :=
  hf.integrableOn (s := σ') (by simpa using h)

/-- A function integrable on every `(0, T]` and bounded by `C e^{σ₀ r}` for large `r` is
Laplace integrable at every abscissa `σ > σ₀`.  (For `ψ_η` in `lem:transfer-laplace`:
`L²_loc` and `‖ψ_η r‖ = O(e^{σ r})`.) -/
theorem laplaceIntegrable_of_le_exp {f : ℝ → E} {σ₀ σ C : ℝ}
    (hloc : ∀ T : ℝ, IntegrableOn f (Ioc 0 T))
    (hbound : ∀ᶠ r in atTop, ‖f r‖ ≤ C * Real.exp (σ₀ * r)) (hσ : σ₀ < σ) :
    LaplaceIntegrable f σ := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hbound
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
    rw [← iUnion_Ioc_eq_Ioi_self_iff.2 fun x _ ↦ exists_nat_ge x]
    exact aestronglyMeasurable_iUnion_iff.2 fun n ↦ (hloc n).aestronglyMeasurable
  unfold LaplaceIntegrable
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.bdd_smul (φ := fun r : ℝ ↦ cexp (-(σ * r))) (hloc R)
      (Real.exp (|σ| * R)) (by fun_prop) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr ↦ ?_
    rw [norm_cexp_neg_mul, Complex.ofReal_re, Real.exp_le_exp]
    have h1 : -(σ * r) ≤ |σ| * r := by
      rw [neg_le, ← neg_mul]
      exact mul_le_mul_of_nonneg_right (neg_abs_le σ) hr.1.le
    exact h1.trans (mul_le_mul_of_nonneg_left hr.2 (abs_nonneg σ))
  · have hint : IntegrableOn (fun r : ℝ ↦ C * Real.exp (-(σ - σ₀) * r)) (Ioi R) :=
      (exp_neg_integrableOn_Ioi R (sub_pos.2 hσ)).const_mul C
    refine hint.mono' ?_ ?_
    · refine (Continuous.aestronglyMeasurable (by fun_prop)).smul ?_
      exact hmeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hR) le_rfl)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
      rw [norm_smul, norm_cexp_neg_mul, Complex.ofReal_re]
      calc Real.exp (-(σ * r)) * ‖f r‖ ≤ Real.exp (-(σ * r)) * (C * Real.exp (σ₀ * r)) :=
            mul_le_mul_of_nonneg_left (hR₀ r ((le_max_left _ _).trans hr.le)) (Real.exp_pos _).le
        _ = C * Real.exp (-(σ - σ₀) * r) := by
            rw [mul_left_comm, ← Real.exp_add]
            ring_nf

/-- Laplace integrability only depends on `f` a.e. on `(0, ∞)`. -/
theorem LaplaceIntegrable.congr_ae {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) : LaplaceIntegrable g σ :=
  Integrable.congr hf (hfg.mono fun r hr ↦ by simp only [hr])

/-- Laplace integrability is preserved by sums. -/
theorem LaplaceIntegrable.add {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hg : LaplaceIntegrable g σ) : LaplaceIntegrable (fun r ↦ f r + g r) σ := by
  refine (Integrable.add hf hg).congr (Eventually.of_forall fun r ↦ ?_)
  simp [smul_add]

/-- Laplace integrability is preserved by negation. -/
theorem LaplaceIntegrable.neg {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ) :
    LaplaceIntegrable (fun r ↦ -f r) σ := by
  refine (Integrable.neg hf).congr (Eventually.of_forall fun r ↦ ?_)
  simp [smul_neg]

/-- Laplace integrability is preserved by differences. -/
theorem LaplaceIntegrable.sub {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hg : LaplaceIntegrable g σ) : LaplaceIntegrable (fun r ↦ f r - g r) σ := by
  refine (Integrable.sub hf hg).congr (Eventually.of_forall fun r ↦ ?_)
  simp [smul_sub]

/-- Laplace integrability is preserved by scalar multiplication. -/
theorem LaplaceIntegrable.const_smul {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (c : ℂ) : LaplaceIntegrable (fun r ↦ c • f r) σ := by
  refine (Integrable.smul c hf).congr (Eventually.of_forall fun r ↦ ?_)
  simp [smul_comm c]

/-- Composition with a bounded linear map preserves Laplace integrability. -/
theorem LaplaceIntegrable.comp_clm {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (L : E →L[ℂ] F) : LaplaceIntegrable (fun r ↦ L (f r)) σ := by
  refine (L.integrable_comp hf).congr (Eventually.of_forall fun r ↦ ?_)
  simp [map_smul]

/-- `r e^{-δ r} ≤ δ⁻¹` for `δ > 0`. -/
private theorem mul_exp_neg_le_inv {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    r * Real.exp (-(δ * r)) ≤ δ⁻¹ := by
  have h := Real.add_one_le_exp (δ * r)
  have h2 : δ * r ≤ Real.exp (δ * r) := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), inv_mul_eq_div,
    le_div_iff₀ hδ, mul_comm]
  exact h2

/-- Multiplying by `r` costs an arbitrarily small amount of abscissa. -/
theorem LaplaceIntegrable.ofReal_smul {f : ℝ → E} {σ σ' : ℝ} (hf : LaplaceIntegrable f σ)
    (h : σ < σ') : LaplaceIntegrable (fun r ↦ (r : ℂ) • f r) σ' := by
  have heq : ∀ r : ℝ, cexp (-(σ' * r)) • ((r : ℂ) • f r)
      = ((r : ℂ) * cexp (-((σ' - σ : ℝ) * r))) • (cexp (-(σ * r)) • f r) := by
    intro r
    rw [smul_smul, smul_smul, mul_assoc, ← Complex.exp_add, mul_comm]
    congr 3
    push_cast
    ring
  unfold LaplaceIntegrable
  simp_rw [heq]
  refine Integrable.bdd_smul (φ := fun r : ℝ ↦ (r : ℂ) * cexp (-((σ' - σ : ℝ) * r))) hf
    (σ' - σ)⁻¹ (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
  rw [norm_mul, norm_cexp_neg_mul, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg
    (le_of_lt hr)]
  exact mul_exp_neg_le_inv (sub_pos.2 h) r

/-- A Laplace integrable function is a.e. strongly measurable on `(0, ∞)`, and so is its
product with any continuous scalar function. -/
private theorem LaplaceIntegrable.aestronglyMeasurable_smul {f : ℝ → E} {σ : ℝ}
    (hf : LaplaceIntegrable f σ) {φ : ℝ → ℂ} (hφ : Continuous φ) :
    AEStronglyMeasurable (fun r ↦ φ r • f r) (volume.restrict (Ioi 0)) := by
  have := (Continuous.aestronglyMeasurable (μ := volume.restrict (Ioi 0))
    (by fun_prop : Continuous fun r : ℝ ↦ φ r * cexp (σ * r))).smul hf.aestronglyMeasurable
  refine this.congr (Eventually.of_forall fun r ↦ ?_)
  simp only [Pi.smul_apply', smul_smul, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

/-! ### Algebraic properties -/

/-- The transform only depends on `f` a.e. on `(0, ∞)`. -/
theorem laplace_congr_ae {f g : ℝ → E} (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) :
    laplace f = laplace g := by
  funext s
  exact integral_congr_ae (hfg.mono fun r hr ↦ by simp only [hr])

/-- The transform is additive on Laplace integrable functions. -/
theorem laplace_add {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hg : LaplaceIntegrable g σ) {s : ℂ} (hs : σ ≤ s.re) :
    laplace (fun r ↦ f r + g r) s = laplace f s + laplace g s := by
  simp only [laplace, smul_add]
  exact integral_add (hf.integrableOn hs) (hg.integrableOn hs)

/-- The transform commutes with negation. -/
theorem laplace_neg (f : ℝ → E) (s : ℂ) : laplace (fun r ↦ -f r) s = -laplace f s := by
  simp only [laplace, smul_neg, integral_neg]

/-- The transform is subtractive on Laplace integrable functions. -/
theorem laplace_sub {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hg : LaplaceIntegrable g σ) {s : ℂ} (hs : σ ≤ s.re) :
    laplace (fun r ↦ f r - g r) s = laplace f s - laplace g s := by
  simp only [laplace, smul_sub]
  exact integral_sub (hf.integrableOn hs) (hg.integrableOn hs)

/-- The transform commutes with scalar multiplication. -/
theorem laplace_const_smul (c : ℂ) (f : ℝ → E) (s : ℂ) :
    laplace (fun r ↦ c • f r) s = c • laplace f s := by
  simp only [laplace, smul_comm _ c, integral_smul]

/-- The transform commutes with bounded linear maps (e.g. `⟨η, ·⟩` in
`eq:analytic-transfer-laplace`). -/
theorem laplace_comp_comm [CompleteSpace E] [CompleteSpace F] (L : E →L[ℂ] F) {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    {s : ℂ} (hs : σ ≤ s.re) : laplace (fun r ↦ L (f r)) s = L (laplace f s) := by
  simp only [laplace, ← L.integral_comp_comm (hf.integrableOn hs), map_smul]

/-- The operator-valued case: the transform of `f : ℝ → E →L[ℂ] F` acts pointwise. -/
theorem laplace_apply {f : ℝ → E →L[ℂ] F} {σ : ℝ} (hf : LaplaceIntegrable f σ) {s : ℂ}
    (hs : σ ≤ s.re) (v : E) : laplace f s v = laplace (fun r ↦ f r v) s := by
  rw [laplace, ContinuousLinearMap.integral_apply (hf.integrableOn hs) v]
  rfl

/-! ### Truncation -/

/-- The transform is the limit of the truncated integrals `∫₀ᵗ e^{-s r} f r dr`, `t → ∞`
(the last step of the proof of `lem:transfer-laplace`). -/
theorem tendsto_intervalIntegral_laplace {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    Tendsto (fun t : ℝ ↦ ∫ r in (0 : ℝ)..t, cexp (-(s * r)) • f r) atTop
      (𝓝 (laplace f s)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (hf.integrableOn hs) tendsto_id

/-- `tendsto_intervalIntegral_laplace` over the windows `(0, t]` of `μI t`. -/
theorem tendsto_setIntegral_Ioc_laplace {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    Tendsto (fun t : ℝ ↦ ∫ r in Ioc 0 t, cexp (-(s * r)) • f r) atTop
      (𝓝 (laplace f s)) := by
  refine (tendsto_intervalIntegral_laplace hf hs).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact intervalIntegral.integral_of_le ht

/-! ### Holomorphy -/

/-- Complex differentiability of the transform on the open half-plane `σ < Re s`, with
`(𝓛 f)' = -𝓛 (r ↦ r f r)`. -/
theorem hasDerivAt_laplace {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ) {s : ℂ}
    (hs : σ < s.re) :
    HasDerivAt (laplace f) (-laplace (fun r ↦ (r : ℂ) • f r) s) s := by
  set ε := (s.re - σ) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun r : ℝ ↦ cexp (-(z * r)) • f r)
      (volume.restrict (Ioi 0)) := fun z ↦ hf.aestronglyMeasurable_smul (by fun_prop)
  have hmeas' : AEStronglyMeasurable (fun r : ℝ ↦ -(cexp (-(s * r)) • ((r : ℂ) • f r)))
      (volume.restrict (Ioi 0)) := by
    refine (hf.aestronglyMeasurable_smul (φ := fun r : ℝ ↦ -(cexp (-(s * r)) * r))
      (by fun_prop)).congr (Eventually.of_forall fun r ↦ ?_)
    simp only [neg_smul, mul_smul]
  have hderiv : ∀ (r : ℝ) (z : ℂ), HasDerivAt (fun w : ℂ ↦ cexp (-(w * r)) • f r)
      (-(cexp (-(z * r)) • ((r : ℂ) • f r))) z := by
    intro r z
    have := (((hasDerivAt_id' z).mul_const (r : ℂ)).neg.cexp).smul_const (f r)
    convert this using 1
    rw [one_mul, mul_neg, neg_smul, mul_smul]
    rfl
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (w : ℂ) (r : ℝ) ↦ cexp (-(w * r)) • f r)
    (F' := fun (w : ℂ) (r : ℝ) ↦ -(cexp (-(w * r)) • ((r : ℂ) • f r)))
    (bound := fun r : ℝ ↦ ε⁻¹ * ‖cexp (-(σ * r)) • f r‖)
    (Metric.ball_mem_nhds s hε) (Eventually.of_forall hmeas) (hf.integrableOn hs.le)
    hmeas' ?_
    ((Integrable.norm hf).const_mul _) (ae_of_all _ fun r z _ ↦ hderiv r z)
  · have := key.2
    rw [integral_neg] at this
    exact this
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr z hz ↦ ?_
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    have hzre : σ + ε < z.re := by
      have h1 := Complex.abs_re_le_norm (z - s)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h2 : |(z - s).re| < ε := h1.trans_lt hz
      rw [Complex.sub_re, abs_lt] at h2
      rw [hε_def] at h2 ⊢
      linarith
    rw [norm_neg, norm_smul, norm_smul, norm_smul, norm_cexp_neg_mul, norm_cexp_neg_mul,
      Complex.norm_real, Real.norm_of_nonneg hr', Complex.ofReal_re]
    calc Real.exp (-(z.re * r)) * (r * ‖f r‖)
        ≤ Real.exp (-((σ + ε) * r)) * (r * ‖f r‖) := by
          gcongr
      _ = (r * Real.exp (-(ε * r))) * (Real.exp (-(σ * r)) * ‖f r‖) := by
          rw [show -((σ + ε) * r) = -(ε * r) + -(σ * r) by ring, Real.exp_add]
          ring
      _ ≤ ε⁻¹ * (Real.exp (-(σ * r)) * ‖f r‖) := by
          gcongr
          exact mul_exp_neg_le_inv hε r

/-- The transform is holomorphic on the open half-plane `σ < Re s`. -/
theorem differentiableOn_laplace {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ) :
    DifferentiableOn ℂ (laplace f) {s : ℂ | σ < s.re} :=
  fun _ hs ↦ (hasDerivAt_laplace hf hs).differentiableAt.differentiableWithinAt

/-- The transform is analytic on the open half-plane `σ < Re s`. -/
theorem analyticOnNhd_laplace [CompleteSpace E] {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ) :
    AnalyticOnNhd ℂ (laplace f) {s : ℂ | σ < s.re} :=
  (differentiableOn_laplace hf).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The transform tends to `0` along the real axis. -/
theorem tendsto_laplace_atTop {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ) :
    Tendsto (fun x : ℝ ↦ laplace f x) atTop (𝓝 0) := by
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (l := atTop) (F := fun (x : ℝ) (r : ℝ) ↦ cexp (-(x * r)) • f r) (f := fun _ ↦ (0 : E))
    (fun r ↦ ‖cexp (-(σ * r)) • f r‖) ?_ ?_ (Integrable.norm hf) ?_
  · simpa [laplace] using key
  · exact Eventually.of_forall fun x ↦ hf.aestronglyMeasurable_smul (by fun_prop)
  · filter_upwards [eventually_ge_atTop σ] with x hx
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
    rw [norm_smul, norm_smul, norm_cexp_neg_mul, norm_cexp_neg_mul, Complex.ofReal_re,
      Complex.ofReal_re]
    gcongr
    exact le_of_lt hr
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_smul, norm_cexp_neg_mul, Complex.ofReal_re]
    have : Tendsto (fun x : ℝ ↦ Real.exp (-(x * r))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.atTop_mul_const hr))
    simpa using this.mul_const ‖f r‖

/-! ### Uniqueness -/

section Uniqueness

variable [CompleteSpace E]

/-- **Uniqueness of the Laplace transform**, core form on a half-line `(a, ∞)`: if
`e^{-σ r} f r` is integrable on `(a, ∞)` and `∫_a^∞ e^{-(σ + n) r} f r dr = 0` for every
`n : ℕ`, then `f = 0` a.e. on `(a, ∞)`.  (The form used, with `a = -T`, in the window part of
`app:analytic-universal-sufficiency`.) -/
theorem ae_eq_zero_of_integral_Ioi_cexp_smul_nat_eq_zero {f : ℝ → E} {a σ : ℝ}
    (hf : IntegrableOn (fun r : ℝ ↦ cexp (-(σ * r)) • f r) (Ioi a))
    (h : ∀ n : ℕ, ∫ r in Ioi a, cexp (-((σ + n) * r)) • f r = 0) :
    f =ᵐ[volume.restrict (Ioi a)] 0 := by
  set G : ℝ → E := fun r ↦ cexp (-(σ * r)) • f r with hG_def
  have hG : IntegrableOn G (Ioi a) := hf
  -- the substitution variable `x(r) = e^{-(r - a)} ∈ (0, 1]`
  set x : ℝ → ℝ := fun r ↦ Real.exp (a - r) with hx_def
  have hx_mem : ∀ r ∈ Ioi a, x r ∈ Icc (0 : ℝ) 1 := fun r hr ↦
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by simp only [mem_Ioi] at hr; linarith)⟩
  have hint : ∀ φ : ℝ → ℝ, Continuous φ →
      IntegrableOn (fun r ↦ φ (x r) • G r) (Ioi a) := by
    intro φ hφ
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hφ.continuousOn (s := Icc (0 : ℝ) 1))
    exact Integrable.bdd_smul (φ := fun r ↦ φ (x r)) hG C
      (by fun_prop : Continuous fun r ↦ φ (x r)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ hC _ (hx_mem r hr))
  -- the moments `∫ x(r)^n e^{-σ r} f r dr` vanish
  have hmono : ∀ n : ℕ, ∫ r in Ioi a, (x r) ^ n • G r = 0 := by
    intro n
    have : ∀ r : ℝ, (x r) ^ n • G r = cexp (n * a) • (cexp (-((σ + n) * r)) • f r) := by
      intro r
      simp only [hx_def, hG_def]
      rw [← Complex.coe_smul, smul_smul, smul_smul]
      congr 1
      push_cast
      rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    simp_rw [this, integral_smul, h n, smul_zero]
  -- hence so do the polynomial moments
  have hpoly : ∀ p : Polynomial ℝ, ∫ r in Ioi a, p.eval (x r) • G r = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.eval_add, add_smul]
      rw [integral_add (hint _ p.continuous) (hint _ q.continuous), hp, hq, add_zero]
    | monomial n c =>
      simp only [Polynomial.eval_monomial, mul_smul]
      rw [integral_smul, hmono n, smul_zero]
  -- test functions supported in `(a, ∞)` are uniform limits of polynomials in `x`
  have key := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hG.locallyIntegrableOn ?_
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [key] with r hr hra
    have h0 : G r = 0 := hr hra
    simpa [hG_def, Complex.exp_ne_zero] using h0
  intro g hg hgc hgs
  have hg0 : ∀ y, y ∉ Ioi a → g y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun hmem ↦ hy (hgs hmem)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi a)
    fun y hy ↦ by simp [hg0 y hy]]
  obtain ⟨R, hR⟩ := hgc.isCompact.bddAbove
  set ψ : ℝ → ℝ := fun y ↦ g (a - Real.log y) with hψ_def
  have hψx : ∀ r, ψ (x r) = g r := fun r ↦ by simp [hψ_def, hx_def, Real.log_exp]
  have hψ : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y = 0
    · subst hy
      have hev : ψ =ᶠ[𝓝 0] fun _ ↦ 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (Real.exp_pos (a - R))] with y hy
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        simp only [hψ_def]
        by_cases hy0 : y = 0
        · subst hy0
          simpa using hg0 a (lt_irrefl a)
        · apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have h1 := hR hmem
          have h2 : Real.log y < a - R := by
            rw [← Real.log_abs]
            calc Real.log |y| < Real.log (Real.exp (a - R)) :=
                  Real.log_lt_log (abs_pos.2 hy0) hy
              _ = a - R := Real.log_exp _
          linarith
      exact continuousAt_const.congr hev.symm
    · exact hg.continuous.continuousAt.comp (continuousAt_const.sub (Real.continuousAt_log hy))
  set K := ∫ r in Ioi a, ‖G r‖ with hK_def
  have hK : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  have hgint : IntegrableOn (fun r ↦ g r • G r) (Ioi a) := by
    have := hint ψ hψ
    simp only [hψx] at this
    exact this
  have hbound : ∀ ε > 0, ‖∫ r in Ioi a, g r • G r‖ ≤ ε * K := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 ψ hψ.continuousOn ε hε
    have heq : ∫ r in Ioi a, g r • G r = ∫ r in Ioi a, (g r - p.eval (x r)) • G r := by
      simp_rw [sub_smul]
      rw [integral_sub hgint (hint _ p.continuous), hpoly p, sub_zero]
    rw [heq, hK_def, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hG.norm.const_mul ε) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ ?_
    rw [norm_smul, Real.norm_eq_abs]
    have := hp (x r) (hx_mem r hr)
    rw [hψx, abs_sub_comm] at this
    exact mul_le_mul_of_nonneg_right this.le (norm_nonneg _)
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  have hK1 : 0 < K + 1 := by linarith
  calc ‖∫ r in Ioi a, g r • G r‖ ≤ ε / (K + 1) * K := hbound _ (div_pos hε hK1)
    _ ≤ ε / (K + 1) * (K + 1) := by gcongr; linarith
    _ = 0 + ε := by rw [div_mul_cancel₀ _ hK1.ne', zero_add]

/-- Uniqueness on a half-line `(a, ∞)` from vanishing at all large real abscissae. -/
theorem ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero {f : ℝ → E} {a σ : ℝ}
    (hf : IntegrableOn (fun r : ℝ ↦ cexp (-(σ * r)) • f r) (Ioi a))
    (h : ∀ᶠ x : ℝ in atTop, ∫ r in Ioi a, cexp (-(x * r)) • f r = 0) :
    f =ᵐ[volume.restrict (Ioi a)] 0 := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  refine ae_eq_zero_of_integral_Ioi_cexp_smul_nat_eq_zero (σ := max σ X)
    (integrableOn_Ioi_cexp_smul_of_le hf (by simp)) fun n ↦ ?_
  have := hX (max σ X + n) (by
    have := le_max_right σ X
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith)
  push_cast at this
  exact this

/-- Uniqueness of the Laplace transform from its values at `σ + n`, `n : ℕ`. -/
theorem ae_eq_zero_of_laplace_nat_eq_zero {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (h : ∀ n : ℕ, laplace f (σ + n) = 0) : f =ᵐ[volume.restrict (Ioi 0)] 0 :=
  ae_eq_zero_of_integral_Ioi_cexp_smul_nat_eq_zero hf h

/-- Uniqueness of the Laplace transform: vanishing for all large real `s` forces `f = 0`
a.e. on `(0, ∞)`. -/
theorem ae_eq_zero_of_laplace_eventually_eq_zero {f : ℝ → E} {σ : ℝ}
    (hf : LaplaceIntegrable f σ) (h : ∀ᶠ x : ℝ in atTop, laplace f x = 0) :
    f =ᵐ[volume.restrict (Ioi 0)] 0 :=
  ae_eq_zero_of_integral_Ioi_cexp_smul_eventually_eq_zero hf h

/-- Uniqueness of the Laplace transform: vanishing on the half-plane `σ < Re s` forces `f = 0`
a.e. on `(0, ∞)` (`lem:transfer-laplace`). -/
theorem ae_eq_zero_of_laplace_eq_zero {f : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (h : ∀ s : ℂ, σ < s.re → laplace f s = 0) : f =ᵐ[volume.restrict (Ioi 0)] 0 :=
  ae_eq_zero_of_laplace_eventually_eq_zero hf
    ((eventually_gt_atTop σ).mono fun x hx ↦ h x (by simpa using hx))

/-- Uniqueness of the Laplace transform from zeros accumulating at a point of the half-plane
`σ < Re s` (identity theorem). -/
theorem ae_eq_zero_of_laplace_frequently_eq_zero {f : ℝ → E} {σ : ℝ}
    (hf : LaplaceIntegrable f σ) {z₀ : ℂ} (hz₀ : σ < z₀.re)
    (h : ∃ᶠ z in 𝓝[≠] z₀, laplace f z = 0) : f =ᵐ[volume.restrict (Ioi 0)] 0 := by
  have := (analyticOnNhd_laplace hf).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt σ).isPreconnected hz₀ h
  exact ae_eq_zero_of_laplace_eq_zero hf fun s hs ↦ this hs

/-- Injectivity of the Laplace transform: equal transforms for all large real `s` force
`f = g` a.e. on `(0, ∞)`. -/
theorem ae_eq_of_laplace_eq {f g : ℝ → E} {σ : ℝ} (hf : LaplaceIntegrable f σ)
    (hg : LaplaceIntegrable g σ) (h : ∀ᶠ x : ℝ in atTop, laplace f x = laplace g x) :
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  have := ae_eq_zero_of_laplace_eventually_eq_zero (hf.sub hg)
    ((h.and (eventually_ge_atTop σ)).mono fun x hx ↦ by
      rw [laplace_sub hf hg (by simpa using hx.2), hx.1, sub_self])
  exact this.mono fun r hr ↦ by simpa [sub_eq_zero] using hr

/-- Weak uniqueness: if every scalar transform `𝓛 (L ∘ f)`, `L ∈ E'`, vanishes on the
half-plane `σ < Re s`, then `f = 0` a.e. on `(0, ∞)`.  (No separability is needed.) -/
theorem ae_eq_zero_of_laplace_comp_eq_zero {f : ℝ → E} {σ : ℝ}
    (hf : LaplaceIntegrable f σ)
    (h : ∀ L : E →L[ℂ] ℂ, ∀ s : ℂ, σ < s.re → laplace (fun r ↦ L (f r)) s = 0) :
    f =ᵐ[volume.restrict (Ioi 0)] 0 :=
  ae_eq_zero_of_laplace_eq_zero hf fun s hs ↦
    SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun L ↦ by
      rw [← laplace_comp_comm L hf hs.le]
      exact h L s hs

/-- Weak uniqueness in a Hilbert space: if `𝓛 ⟪v, f ·⟫` vanishes on the half-plane
`σ < Re s` for every `v`, then `f = 0` a.e. on `(0, ∞)` (`lem:transfer-laplace`). -/
theorem ae_eq_zero_of_laplace_inner_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {f : ℝ → H} {σ : ℝ}
    (hf : LaplaceIntegrable f σ)
    (h : ∀ v : H, ∀ s : ℂ, σ < s.re → laplace (fun r ↦ ⟪v, f r⟫_ℂ) s = 0) :
    f =ᵐ[volume.restrict (Ioi 0)] 0 := by
  refine ae_eq_zero_of_laplace_eq_zero hf fun s hs ↦ ?_
  have h1 := laplace_comp_comm (innerSL ℂ (laplace f s)) hf hs.le
  simp only [innerSL_apply_apply] at h1
  rw [h (laplace f s) s hs] at h1
  exact inner_self_eq_zero.1 h1.symm

end Uniqueness

end DataDrivenControl
