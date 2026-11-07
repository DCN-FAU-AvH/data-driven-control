module

public import DataDrivenControl.System.Mild

/-!
# Fourier estimates for the wave frequencies

Paper: `ex:intro-wave` (`introduction.tex`): the two estimates behind `hyp:H1` and `hyp:H2` for
the wave equation with Dirichlet control.

The Dirichlet modes of `∂ₜₜw = c² ∂ξξ w` on `(0, 1)` oscillate with the frequencies
`ωₙ = c (n + 1) π`, `n ≥ 0` (`freq`; the paper's `ωₙ = c n π`, `n ≥ 1`, is `freq c (n - 1)`).
All of them are multiples of `c π`, so `cos(ωₙ ·)` and `sin(ωₙ ·)` are orthogonal families on
every interval of length `2/c`; on `(0, 2/c]` the families `√c cos(ωₙ ·)` and `√c sin(ωₙ ·)` are
orthonormal (`orthonormal_cos`, `orthonormal_sin`).  This gives the two inequalities:

* **Bessel** (for `hyp:H1`): `∑ₙ (∫₀^{2/c} cos(ωₙ r) g(r) dr)² ≤ ‖g‖² / c`, and the same
  for `sin` (`summable_sq_integral_cos`, `tsum_sq_integral_cos_le`, `summable_sq_integral_sin`,
  `tsum_sq_integral_sin_le`);
* **synthesis** (for `hyp:H2`): for absolutely summable `α, β`,
  `‖∑ₙ (αₙ cos(ωₙ ·) + βₙ sin(ωₙ ·))‖²_{L²(0, 2/c)} ≤ (2/c) ∑ₙ (αₙ² + βₙ²)` (`eLpNorm_tsum_le`).
  It follows from Bessel by duality: pairing the sum `f` with itself gives
  `‖f‖² = ∑ₙ (αₙ Aₙ + βₙ Bₙ)` with `Aₙ = ∫ cos(ωₙ ·) f`, `Bₙ = ∫ sin(ωₙ ·) f`, and
  `c (αₙ Aₙ + βₙ Bₙ) ≤ αₙ² + βₙ² + (c²/4) (Aₙ² + Bₙ²)`.

The cosine and sine families are used separately (no cross terms are needed), which costs a
factor `2` in both constants.

## Main declarations

* `freq`, `freq_pos`, `freq_mul_period`, `sin_freq_mul_period`, `cos_freq_mul_period`;
* `integral_cos_freq_mul_cos_freq`, `integral_sin_freq_mul_sin_freq`
  (`∫₀^{2/c} cos(ωₙ r) cos(ωₘ r) dr = δₙₘ / c`, and the same for `sin`);
* `famL2 φ hφ c n = √c φ(ωₙ ·) ∈ L²(0, 2/c)` for continuous `φ`, `inner_famL2`;
* `bessel`, and its instances listed above; `eLpNorm_tsum_le`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Wave

/-- The modal frequencies of the Dirichlet wave equation with speed `c`:
`ωₙ = c (n + 1) π`, `n ≥ 0` (the paper's `ωₙ = c n π`, `n ≥ 1`, is `freq c (n - 1)`). -/
def freq (c : ℝ) (n : ℕ) : ℝ := c * ((n : ℝ) + 1) * Real.pi

theorem freq_pos {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 < freq c n := by
  unfold freq; positivity

section Orth

variable {c : ℝ}

/-- `ωₙ · (2/c) = (n + 1) 2π`: every mode has period dividing `2/c`. -/
theorem freq_mul_period (hc : c ≠ 0) (n : ℕ) :
    freq c n * (2 / c) = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
  unfold freq; push_cast; field_simp

theorem sin_freq_mul_period (hc : c ≠ 0) (n : ℕ) : Real.sin (freq c n * (2 / c)) = 0 := by
  have h : freq c n * (2 / c) = ((2 * (n + 1) : ℕ) : ℝ) * Real.pi := by
    rw [freq_mul_period hc]; push_cast; ring
  rw [h, Real.sin_nat_mul_pi]

theorem cos_freq_mul_period (hc : c ≠ 0) (n : ℕ) : Real.cos (freq c n * (2 / c)) = 1 := by
  rw [freq_mul_period hc, Real.cos_nat_mul_two_pi]

/-! ### Orthogonality on `(0, 2/c)` -/

/-- `∫₀ᵀ cos(k r) dr = 0` if `k ≠ 0` and `sin(k T) = 0`. -/
theorem integral_cos_mul_eq_zero {k T : ℝ} (hk : k ≠ 0) (h : Real.sin (k * T) = 0) :
    ∫ r in (0 : ℝ)..T, Real.cos (k * r) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun r => Real.cos r) hk, integral_cos, mul_zero,
    Real.sin_zero, sub_zero, h, smul_zero]

private theorem sin_sub_freq_mul_period (hc : c ≠ 0) (n m : ℕ) :
    Real.sin ((freq c n - freq c m) * (2 / c)) = 0 := by
  have h : (freq c n - freq c m) * (2 / c) = ((2 * ((n : ℤ) - m) : ℤ) : ℝ) * Real.pi := by
    unfold freq; push_cast; field_simp; ring
  rw [h, Real.sin_int_mul_pi]

private theorem sin_add_freq_mul_period (hc : c ≠ 0) (n m : ℕ) :
    Real.sin ((freq c n + freq c m) * (2 / c)) = 0 := by
  have h : (freq c n + freq c m) * (2 / c) = ((2 * ((n : ℤ) + m + 2) : ℤ) : ℝ) * Real.pi := by
    unfold freq; push_cast; field_simp; ring
  rw [h, Real.sin_int_mul_pi]

private theorem freq_add_ne_zero (hc : 0 < c) (n m : ℕ) : freq c n + freq c m ≠ 0 :=
  (add_pos (freq_pos hc n) (freq_pos hc m)).ne'

private theorem freq_sub_ne_zero (hc : 0 < c) {n m : ℕ} (h : n ≠ m) :
    freq c n - freq c m ≠ 0 := by
  intro h0
  apply h
  have h1 : c * Real.pi * ((n : ℝ) - m) = 0 := by unfold freq at h0; linear_combination h0
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 (by positivity)
  · exact_mod_cast sub_eq_zero.1 h2

private theorem intervalIntegrable_cos_mul (k a b : ℝ) :
    IntervalIntegrable (fun r => Real.cos (k * r)) volume a b :=
  (by fun_prop : Continuous fun r => Real.cos (k * r)).intervalIntegrable a b

private theorem integral_cos_sub_self (n : ℕ) :
    ∫ r in (0 : ℝ)..(2 / c), Real.cos ((freq c n - freq c n) * r) = 2 / c := by
  simp

/-- `∫₀^{2/c} cos(ωₙ r) cos(ωₘ r) dr = δₙₘ / c`. -/
theorem integral_cos_freq_mul_cos_freq (hc : 0 < c) (n m : ℕ) :
    ∫ r in (0 : ℝ)..(2 / c), Real.cos (freq c n * r) * Real.cos (freq c m * r) =
      if n = m then 1 / c else 0 := by
  have e : ∀ r, Real.cos (freq c n * r) * Real.cos (freq c m * r) =
      (Real.cos ((freq c n - freq c m) * r) + Real.cos ((freq c n + freq c m) * r)) / 2 :=
    fun r => by rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (intervalIntegrable_cos_mul _ _ _) (intervalIntegrable_cos_mul _ _ _),
    integral_cos_mul_eq_zero (freq_add_ne_zero hc n m) (sin_add_freq_mul_period hc.ne' n m)]
  split_ifs with h
  · subst h
    rw [integral_cos_sub_self]
    ring
  · rw [integral_cos_mul_eq_zero (freq_sub_ne_zero hc h) (sin_sub_freq_mul_period hc.ne' n m)]
    simp

/-- `∫₀^{2/c} sin(ωₙ r) sin(ωₘ r) dr = δₙₘ / c`. -/
theorem integral_sin_freq_mul_sin_freq (hc : 0 < c) (n m : ℕ) :
    ∫ r in (0 : ℝ)..(2 / c), Real.sin (freq c n * r) * Real.sin (freq c m * r) =
      if n = m then 1 / c else 0 := by
  have e : ∀ r, Real.sin (freq c n * r) * Real.sin (freq c m * r) =
      (Real.cos ((freq c n - freq c m) * r) - Real.cos ((freq c n + freq c m) * r)) / 2 :=
    fun r => by rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (intervalIntegrable_cos_mul _ _ _) (intervalIntegrable_cos_mul _ _ _),
    integral_cos_mul_eq_zero (freq_add_ne_zero hc n m) (sin_add_freq_mul_period hc.ne' n m)]
  split_ifs with h
  · subst h
    rw [integral_cos_sub_self]
    ring
  · rw [integral_cos_mul_eq_zero (freq_sub_ne_zero hc h) (sin_sub_freq_mul_period hc.ne' n m)]
    simp

end Orth

/-! ### The orthonormal families and Bessel's inequality -/

section Family

variable (φ : ℝ → ℝ) (hφ : Continuous φ) (c : ℝ)
include hφ

theorem continuous_fam (n : ℕ) : Continuous fun r => Real.sqrt c * φ (freq c n * r) :=
  continuous_const.mul (hφ.comp (continuous_const.mul continuous_id))

theorem memLp_fam (n : ℕ) : MemLp (fun r => Real.sqrt c * φ (freq c n * r)) 2 (μI (2 / c)) :=
  memLp_μI_of_continuousOn (continuous_fam φ hφ c n).continuousOn

/-- `√c φ(ωₙ ·)` as an element of `L²(0, 2/c)` (used with `φ = cos` and `φ = sin`). -/
def famL2 (n : ℕ) : L2 ℝ (2 / c) := (memLp_fam φ hφ c n).toLp _

theorem coeFn_famL2 (n : ℕ) :
    ∀ᵐ r ∂(μI (2 / c)), famL2 φ hφ c n r = Real.sqrt c * φ (freq c n * r) :=
  (memLp_fam φ hφ c n).coeFn_toLp

/-- `⟪√c φ(ωₙ ·), g⟫ = √c ∫₀^{2/c} φ(ωₙ r) g(r) dr`. -/
theorem inner_famL2 (n : ℕ) (g : L2 ℝ (2 / c)) :
    ⟪famL2 φ hφ c n, g⟫_ℝ = Real.sqrt c * ∫ r in Ioc 0 (2 / c), φ (freq c n * r) * g r := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_famL2 φ hφ c n] with r hr
  rw [hr, RCLike.inner_apply, conj_trivial]
  ring

theorem inner_famL2_famL2 (hc : 0 < c) (n m : ℕ) :
    ⟪famL2 φ hφ c n, famL2 φ hφ c m⟫_ℝ =
      c * ∫ r in (0 : ℝ)..(2 / c), φ (freq c n * r) * φ (freq c m * r) := by
  rw [inner_famL2, intervalIntegral.integral_of_le (by positivity)]
  have h : ∫ r in Ioc 0 (2 / c), φ (freq c n * r) * famL2 φ hφ c m r =
      ∫ r in Ioc 0 (2 / c), Real.sqrt c * (φ (freq c n * r) * φ (freq c m * r)) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_famL2 φ hφ c m] with r hr
    rw [hr]
    ring
  rw [h, integral_const_mul, ← mul_assoc, Real.mul_self_sqrt hc.le]

/-- **Bessel's inequality** for an orthonormal family `√c φ(ωₙ ·)` in `L²(0, 2/c)`. -/
theorem bessel (hc : 0 < c) (hv : Orthonormal ℝ (famL2 φ hφ c)) (g : L2 ℝ (2 / c)) :
    Summable (fun n => (∫ r in Ioc 0 (2 / c), φ (freq c n * r) * g r) ^ 2) ∧
      ∑' n, (∫ r in Ioc 0 (2 / c), φ (freq c n * r) * g r) ^ 2 ≤ ‖g‖ ^ 2 / c := by
  have e : ∀ n, (∫ r in Ioc 0 (2 / c), φ (freq c n * r) * g r) ^ 2 =
      ‖⟪famL2 φ hφ c n, g⟫_ℝ‖ ^ 2 / c := fun n => by
    rw [inner_famL2, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hc.le]
    field_simp
  refine ⟨((hv.inner_products_summable g).div_const c).congr fun n => (e n).symm, ?_⟩
  rw [tsum_congr e, tsum_div_const]
  exact div_le_div_of_nonneg_right (hv.tsum_inner_products_le g) hc.le

end Family

section Bessel

variable {c : ℝ}

/-- `√c cos(ωₙ ·)`, `n ≥ 0`, is orthonormal in `L²(0, 2/c)`. -/
theorem orthonormal_cos (hc : 0 < c) : Orthonormal ℝ (famL2 Real.cos Real.continuous_cos c) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [inner_famL2_famL2 _ _ _ hc, integral_cos_freq_mul_cos_freq hc]
  split_ifs
  · field_simp
  · simp

/-- `√c sin(ωₙ ·)`, `n ≥ 0`, is orthonormal in `L²(0, 2/c)`. -/
theorem orthonormal_sin (hc : 0 < c) : Orthonormal ℝ (famL2 Real.sin Real.continuous_sin c) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [inner_famL2_famL2 _ _ _ hc, integral_sin_freq_mul_sin_freq hc]
  split_ifs
  · field_simp
  · simp

theorem summable_sq_integral_cos (hc : 0 < c) (g : L2 ℝ (2 / c)) :
    Summable fun n => (∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * g r) ^ 2 :=
  (bessel Real.cos Real.continuous_cos c hc (orthonormal_cos hc) g).1

/-- **Bessel** for the cosines: `∑ₙ (∫₀^{2/c} cos(ωₙ r) g(r) dr)² ≤ ‖g‖² / c`. -/
theorem tsum_sq_integral_cos_le (hc : 0 < c) (g : L2 ℝ (2 / c)) :
    ∑' n, (∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * g r) ^ 2 ≤ ‖g‖ ^ 2 / c :=
  (bessel Real.cos Real.continuous_cos c hc (orthonormal_cos hc) g).2

theorem summable_sq_integral_sin (hc : 0 < c) (g : L2 ℝ (2 / c)) :
    Summable fun n => (∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * g r) ^ 2 :=
  (bessel Real.sin Real.continuous_sin c hc (orthonormal_sin hc) g).1

/-- **Bessel** for the sines: `∑ₙ (∫₀^{2/c} sin(ωₙ r) g(r) dr)² ≤ ‖g‖² / c`. -/
theorem tsum_sq_integral_sin_le (hc : 0 < c) (g : L2 ℝ (2 / c)) :
    ∑' n, (∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * g r) ^ 2 ≤ ‖g‖ ^ 2 / c :=
  (bessel Real.sin Real.continuous_sin c hc (orthonormal_sin hc) g).2

/-! ### The synthesis inequality -/

/-- **The synthesis inequality** on `(0, 2/c]`: for absolutely summable `α, β`, the
trigonometric series `f(t) = ∑ₙ (αₙ cos(ωₙ t) + βₙ sin(ωₙ t))` satisfies
`‖f‖²_{L²(0, 2/c)} ≤ (2/c) ∑ₙ (αₙ² + βₙ²)` (Bessel's inequality and duality). -/
theorem eLpNorm_tsum_le (hc : 0 < c) {α β : ℕ → ℝ} (hα : Summable fun n => |α n|)
    (hβ : Summable fun n => |β n|) (hα2 : Summable fun n => α n ^ 2)
    (hβ2 : Summable fun n => β n ^ 2) :
    eLpNorm (fun t => ∑' n, (α n * Real.cos (freq c n * t) + β n * Real.sin (freq c n * t))) 2
        (μI (2 / c)) ≤
      ENNReal.ofReal (Real.sqrt (2 / c * ∑' n, (α n ^ 2 + β n ^ 2))) := by
  set φ : ℕ → ℝ → ℝ := fun n t => α n * Real.cos (freq c n * t) + β n * Real.sin (freq c n * t)
    with hφ
  set f : ℝ → ℝ := fun t => ∑' n, φ n t with hf
  have hφc : ∀ n, Continuous (φ n) := fun n => by simp only [hφ]; fun_prop
  have hφb : ∀ n t, ‖φ n t‖ ≤ |α n| + |β n| := fun n t => by
    simp only [hφ, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hfc : Continuous f := continuous_tsum hφc (hα.add hβ) hφb
  have hfm : MemLp f 2 (μI (2 / c)) := memLp_μI_of_continuousOn hfc.continuousOn
  set F : L2 ℝ (2 / c) := hfm.toLp f with hFdef
  have hFf : (F : ℝ → ℝ) =ᵐ[μI (2 / c)] f := hfm.coeFn_toLp
  have hintI : ∀ {g : ℝ → ℝ}, Continuous g → Integrable g (μI (2 / c)) := fun hg =>
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- The coefficients of `F` and Bessel's inequality.
  set A : ℕ → ℝ := fun n => ∫ r in Ioc 0 (2 / c), Real.cos (freq c n * r) * F r with hA
  set B : ℕ → ℝ := fun n => ∫ r in Ioc 0 (2 / c), Real.sin (freq c n * r) * F r with hB
  have hAs : Summable fun n => A n ^ 2 := summable_sq_integral_cos hc F
  have hBs : Summable fun n => B n ^ 2 := summable_sq_integral_sin hc F
  have hAle : (∑' n, A n ^ 2) * c ≤ ‖F‖ ^ 2 := (le_div_iff₀ hc).1 (tsum_sq_integral_cos_le hc F)
  have hBle : (∑' n, B n ^ 2) * c ≤ ‖F‖ ^ 2 := (le_div_iff₀ hc).1 (tsum_sq_integral_sin_le hc F)
  -- `‖F‖² = ∑ₙ (αₙ Aₙ + βₙ Bₙ)`.
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hfc.continuousOn (s := Icc 0 (2 / c)))
  have hint : ∀ n, Integrable (fun t => φ n t * f t) (μI (2 / c)) := fun n =>
    hintI ((hφc n).mul hfc)
  have hnorm : Summable fun n => ∫ t in Ioc 0 (2 / c), ‖φ n t * f t‖ := by
    refine ((hα.add hβ).mul_right (M * (μI (2 / c)).real univ)).of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) fun n => ?_
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← mul_assoc]
    refine norm_integral_le_of_norm_le_const ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_norm, norm_mul]
    exact mul_le_mul (hφb n t) (hM t (Ioc_subset_Icc_self ht)) (norm_nonneg _) (by positivity)
  have hs : Summable fun n => ∫ t in Ioc 0 (2 / c), φ n t * f t :=
    hnorm.of_norm_bounded fun n => norm_integral_le_integral_norm _
  have hF2 : ‖F‖ ^ 2 = ∫ t in Ioc 0 (2 / c), f t * f t := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hFf] with t ht
    rw [ht, RCLike.inner_apply, conj_trivial]
  have hexch : ∫ t in Ioc 0 (2 / c), f t * f t = ∑' n, ∫ t in Ioc 0 (2 / c), φ n t * f t := by
    rw [integral_tsum_of_summable_integral_norm hint hnorm]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show f t * f t = ∑' n, φ n t * f t
    rw [tsum_mul_right]
  have hcoef : ∀ n, ∫ t in Ioc 0 (2 / c), φ n t * f t = α n * A n + β n * B n := fun n => by
    have hA' : A n = ∫ t in Ioc 0 (2 / c), Real.cos (freq c n * t) * f t :=
      integral_congr_ae (hFf.mono fun t ht => by simp only [ht])
    have hB' : B n = ∫ t in Ioc 0 (2 / c), Real.sin (freq c n * t) * f t :=
      integral_congr_ae (hFf.mono fun t ht => by simp only [ht])
    rw [hA', hB', ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hintI (by fun_prop)) (hintI (by fun_prop))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hφ]
    ring
  have hsum : HasSum (fun n => α n * A n + β n * B n) (‖F‖ ^ 2) := by
    rw [hF2, hexch]
    convert hs.hasSum using 1
    funext n
    exact (hcoef n).symm
  -- `c (αₙ Aₙ + βₙ Bₙ) ≤ αₙ² + βₙ² + (c²/4) (Aₙ² + Bₙ²)`, summed.
  set S := ∑' n, (α n ^ 2 + β n ^ 2) with hSdef
  have hle : c * ‖F‖ ^ 2 ≤ S + c ^ 2 / 4 * (∑' n, A n ^ 2 + ∑' n, B n ^ 2) :=
    hasSum_le (fun n => by
        nlinarith [sq_nonneg (α n - c * A n / 2), sq_nonneg (β n - c * B n / 2)])
      (hsum.mul_left c) ((hα2.add hβ2).hasSum.add ((hAs.hasSum.add hBs.hasSum).mul_left _))
  have key : ‖F‖ ^ 2 ≤ 2 / c * S := by
    have h1 : c ^ 2 / 4 * (∑' n, A n ^ 2 + ∑' n, B n ^ 2) ≤ c / 2 * ‖F‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hAle (by positivity : (0 : ℝ) ≤ c / 4),
        mul_le_mul_of_nonneg_left hBle (by positivity : (0 : ℝ) ≤ c / 4)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  rw [eLpNorm_congr_ae hFf.symm, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.abs_le_sqrt key))

end Bessel

end Wave

end DataDrivenControl
