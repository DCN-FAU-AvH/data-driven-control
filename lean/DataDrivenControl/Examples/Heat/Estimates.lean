module

public import DataDrivenControl.Examples.Heat.Spaces

/-!
# Two estimates for the boundary-controlled heat system

The analytic estimates behind `Examples/Heat/System`.

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`): the point observation on
`W` and `eq:heat-control-X`.  The notation is that of `Examples/Heat/Spaces`: modal data
`d : ModalData` (eigenvalues `λₙ ≤ 0`, `wₙ = 1 - λₙ`, `∑ 1/wₙ < ∞`, bounded `cₙ`), a Hilbert
basis `e` of `X`, the free output `d.obs a t = ∑ₙ cₙ wₙ e^{λₙ t} aₙ` of `a ∈ X₋₁ = ℓ²`, the
embedding `d.toXm1 e x = (⟪eₙ, x⟫ / wₙ)ₙ` and `A_{X,-1} = d.genXm1 e`, `x ↦ (λₙ ⟪eₙ, x⟫ / wₙ)ₙ`.
For `t > 0`: `d.obs (d.toXm1 e x) t = ∑ₙ cₙ e^{λₙ t} ⟪eₙ, x⟫` (`hasSum_obs_toXm1`) and
`d.obs (d.genXm1 e x) t = ∑ₙ cₙ λₙ e^{λₙ t} ⟪eₙ, x⟫` (`hasSum_obs_genXm1`).

## Main statements

* `ModalData.hasSum_trace`: **the trace formula in time** behind `C ∈ L(W, ℝ)`.  For `x ∈ D(A)`
  (`∑ (λₙ xₙ)² < ∞`), `g = C S(·) x` and `g' = C S(·) A x` satisfy
  `∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds = ∑ₙ cₙ xₙ` (`= g(0)`).
* `ModalData.exists_control_bound`: **`eq:heat-control-X`** and the `V`-bound of
  `A_{X,-1} L_T u`.  For bounded control coefficients `bₙ` whose kernel derivative
  `h'(t) = ∑ₙ cₙ bₙ λₙ e^{λₙ t}` is bounded on `(0, ∞)`, the vector `x = L_T u` with coordinates
  `xₙ = bₙ ∫₀ᵀ e^{λₙ (T - r)} u(r) dr` lies in `X` with `‖x‖ ≤ C ‖u‖`, and the free output of
  `A_{X,-1} x`, `s ↦ ∫₀ᵀ h'(s + T - r) u(r) dr`, is square integrable on `(0, 1]` with
  `L²`-norm at most `C ‖u‖`.

## Auxiliary results

`integral_trace_kernel` (`∫₀¹ (e^{λ s} - λ (1 - s) e^{λ s}) ds = 1`), `sq_integral_mul_le`
(Cauchy–Schwarz in `L²(0, T)`), `ModalData.setIntegral_exp_le` (`∫₀¹ e^{λₙ s} ds ≤ 2/wₙ`),
`ModalData.setIntegral_exp_sq_le` (`∫₀ᵀ e^{2λₙ (T - r)} dr ≤ (T + 1)/wₙ`),
`ModalData.summable_abs_div_wt`.

## Proofs

* `hasSum_trace`: exchange `∫` and `∑ₙ` in both integrals
  (`integral_tsum_of_summable_integral_norm`; `∫₀¹ e^{λₙ s} ds ≤ 2/wₙ`
  (`setIntegral_exp_neg_mul_le`), `∑ₙ |xₙ|/wₙ < ∞` and `∑ₙ |λₙ xₙ|/wₙ < ∞` by Cauchy–Schwarz or
  AM–GM, `|cₙ| ≤ K`), then use `∫₀¹ e^{λ s} ds - λ ∫₀¹ (1 - s) e^{λ s} ds = 1` (FTC for
  `s ↦ -(1 - s) e^{λ s}`).
* `exists_control_bound`: Cauchy–Schwarz in `L²(0, T)` gives
  `xₙ² ≤ K² ‖u‖² ∫₀ᵀ e^{2λₙ s} ds ≤ K² (T + 1) ‖u‖² / wₙ` (`setIntegral_exp_neg_mul_le`), so
  `∑ xₙ² ≤ K² (T + 1) (∑ 1/wₙ) ‖u‖²`; take `x = toX e (mkL2 xs _)` (or
  `Diagonal.exists_inner_eq`).  For `s > 0`, `d.obs (d.genXm1 e x) s = ∫₀ᵀ h'(s + T - r) u(r) dr`
  (exchange with `integral_tsum_of_summable_integral_norm`, using
  `|λₙ| e^{λₙ s} ≤ wₙ e^{λₙ s} ≤ (2 eˢ/s²)/wₙ` from `wt_pow_mul_exp_le`), hence
  `|d.obs (d.genXm1 e x) s| ≤ M √T ‖u‖`; measurability from `aestronglyMeasurable_obs`, then
  `MemLp.of_bound` and `Lp.norm_le_of_ae_bound` (`μI 1` has mass `1`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

/-- `∫₀¹ (e^{λ s} - λ (1 - s) e^{λ s}) ds = 1`. -/
theorem integral_trace_kernel (l : ℝ) :
    ∫ s in Ioc 0 1, (Real.exp (l * s) - (1 - s) * (l * Real.exp (l * s))) = 1 := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => -((1 - s) * Real.exp (l * s))) (fun s _ => ?_)
      ((by fun_prop : Continuous fun s : ℝ =>
        Real.exp (l * s) - (1 - s) * (l * Real.exp (l * s))).intervalIntegrable _ _)]
  · simp
  · have h1 : HasDerivAt (fun s : ℝ => l * s) l s := by
      simpa using (hasDerivAt_id' s).const_mul l
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id' s).const_sub 1
    have := (h2.mul h1.exp).neg
    convert this using 1
    ring

/-- Cauchy–Schwarz in `L²(0, T)`: `(∫₀ᵀ g u)² ≤ (∫₀ᵀ g²) ‖u‖²`. -/
theorem sq_integral_mul_le {T : ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 (μI T)) (u : L2 ℝ T) :
    (∫ r in Ioc 0 T, g r * u r) ^ 2 ≤ (∫ r in Ioc 0 T, g r ^ 2) * ‖u‖ ^ 2 := by
  set G := hg.toLp g
  have h1 : ⟪G, u⟫_ℝ = ∫ r in Ioc 0 T, g r * u r := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with r hr
    rw [hr, RCLike.inner_apply, conj_trivial, mul_comm]
  have h2 : ‖G‖ ^ 2 = ∫ r in Ioc 0 T, g r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with r hr
    rw [hr, RCLike.inner_apply, conj_trivial, sq]
  rw [← h1, ← h2, ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm G u) 2

namespace ModalData

variable (d : ModalData) {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] (e : HilbertBasis ℕ ℝ X)

/-- `∫₀¹ e^{λₙ s} ds ≤ 2/wₙ`. -/
theorem setIntegral_exp_le (n : ℕ) : ∫ s in Ioc 0 1, Real.exp (d.lam n * s) ≤ 2 / d.wt n := by
  have h := setIntegral_exp_neg_mul_le (y := -d.lam n) (by linarith [d.lam_nonpos n]) zero_le_one
  have e1 : ∀ s : ℝ, -(-d.lam n * s) = d.lam n * s := fun s => by ring
  simp only [e1] at h
  refine h.trans (le_of_eq ?_)
  unfold wt; ring

/-- `∑ₙ |aₙ|/wₙ < ∞` for square-summable `a`. -/
theorem summable_abs_div_wt {a : ℕ → ℝ} (ha : Summable fun n => a n ^ 2) :
    Summable fun n => |a n| / d.wt n := by
  refine (ha.add d.summable_inv_wt).of_nonneg_of_le
    (fun n => div_nonneg (abs_nonneg _) (d.wt_pos n).le) fun n => ?_
  have hw := d.wt_pos n
  have h1 := d.one_le_wt n
  show |a n| / d.wt n ≤ a n ^ 2 + (d.wt n)⁻¹
  rw [div_eq_mul_inv]
  have hi : (d.wt n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hi0 : 0 ≤ (d.wt n)⁻¹ := inv_nonneg.2 hw.le
  nlinarith [two_mul_le_add_sq |a n| (d.wt n)⁻¹, sq_abs (a n), abs_nonneg (a n)]

/-- `∫₀ᵀ e^{2λₙ (T - r)} dr ≤ (T + 1)/wₙ`. -/
theorem setIntegral_exp_sq_le (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) ^ 2 ≤ (T + 1) / d.wt n := by
  set y := -(2 * d.lam n) with hy
  have hy0 : 0 ≤ y := by linarith [d.lam_nonpos n]
  have he : ∀ r, Real.exp (d.lam n * (T - r)) ^ 2 = Real.exp (-(y * (T - r))) := fun r => by
    rw [← Real.exp_nat_mul]; congr 1; rw [hy]; push_cast; ring
  simp only [he]
  rw [← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_comp_sub_left (fun s => Real.exp (-(y * s))) T, sub_self,
    sub_zero, intervalIntegral.integral_of_le hT]
  refine (setIntegral_exp_neg_mul_le hy0 hT).trans ?_
  have hw := d.wt_pos n
  refine div_le_div_of_nonneg_left (by linarith) hw ?_
  unfold wt; rw [hy]; linarith [d.lam_nonpos n]

/-- **The trace formula in time** (`app:boundary-heat-informative`, point observation on `W`):
for `x ∈ D(A)`, i.e. `∑ₙ (λₙ ⟪eₙ, x⟫)² < ∞`, the free outputs `g = C S(·) x` and
`g' = C S(·) A x = C S(·) A_{X,-1} x` satisfy `∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds = ∑ₙ cₙ ⟪eₙ, x⟫`. -/
theorem hasSum_trace (x : X) (hx : Summable fun n => (d.lam n * ⟪e n, x⟫_ℝ) ^ 2) :
    HasSum (fun n => d.c n * ⟪e n, x⟫_ℝ)
      ((∫ s in Ioc 0 1, d.obs (d.toXm1 e x) s) -
        ∫ s in Ioc 0 1, (1 - s) * d.obs (d.genXm1 e x) s) := by
  obtain ⟨K, hK⟩ := d.exists_abs_c_le
  set xs : ℕ → ℝ := fun n => ⟪e n, x⟫_ℝ with hxs
  have hxs2 : Summable fun n => xs n ^ 2 := Diagonal.summable_inner_sq e x
  set F₁ : ℕ → ℝ → ℝ := fun n s => d.c n * Real.exp (d.lam n * s) * xs n with hF₁
  set F₂ : ℕ → ℝ → ℝ := fun n s => (1 - s) * (d.c n * d.lam n * Real.exp (d.lam n * s) * xs n)
    with hF₂
  have hI : ∀ n, ∫ s in Ioc 0 1, Real.exp (d.lam n * s) ≤ 2 / d.wt n := d.setIntegral_exp_le
  have hexpi : ∀ n, IntegrableOn (fun s => Real.exp (d.lam n * s)) (Ioc 0 1) := fun n =>
    (by fun_prop : Continuous fun s => Real.exp (d.lam n * s)).integrableOn_Ioc
  have hint₁ : ∀ n, Integrable (F₁ n) (volume.restrict (Ioc 0 1)) := fun n =>
    (by fun_prop : Continuous (F₁ n)).integrableOn_Ioc
  have hint₂ : ∀ n, Integrable (F₂ n) (volume.restrict (Ioc 0 1)) := fun n =>
    (by fun_prop : Continuous (F₂ n)).integrableOn_Ioc
  -- bounds on the integrals of the norms
  have hb₁ : ∀ n, ∫ s in Ioc 0 1, ‖F₁ n s‖ ≤ 2 * K * (|xs n| / d.wt n) := by
    intro n
    calc ∫ s in Ioc 0 1, ‖F₁ n s‖
        ≤ ∫ s in Ioc 0 1, K * |xs n| * Real.exp (d.lam n * s) := by
          refine setIntegral_mono_on (hint₁ n).norm ((hexpi n).const_mul _) measurableSet_Ioc
            fun s _ => ?_
          rw [Real.norm_eq_abs, hF₁]
          simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |d.c n| * Real.exp (d.lam n * s) * |xs n|
              = |d.c n| * (|xs n| * Real.exp (d.lam n * s)) := by ring
            _ ≤ K * (|xs n| * Real.exp (d.lam n * s)) :=
                mul_le_mul_of_nonneg_right (hK n) (by positivity)
            _ = K * |xs n| * Real.exp (d.lam n * s) := by ring
      _ = K * |xs n| * ∫ s in Ioc 0 1, Real.exp (d.lam n * s) := integral_const_mul _ _
      _ ≤ K * |xs n| * (2 / d.wt n) := by
          gcongr
          · exact mul_nonneg ((abs_nonneg _).trans (hK 0)) (abs_nonneg _)
          · exact hI n
      _ = 2 * K * (|xs n| / d.wt n) := by ring
  have hb₂ : ∀ n, ∫ s in Ioc 0 1, ‖F₂ n s‖ ≤ 2 * K * (|d.lam n * xs n| / d.wt n) := by
    intro n
    calc ∫ s in Ioc 0 1, ‖F₂ n s‖
        ≤ ∫ s in Ioc 0 1, K * |d.lam n * xs n| * Real.exp (d.lam n * s) := by
          refine setIntegral_mono_on (hint₂ n).norm ((hexpi n).const_mul _) measurableSet_Ioc
            fun s hs => ?_
          rw [Real.norm_eq_abs, hF₂]
          have h1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
          simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
          have h0 : 0 ≤ |d.c n| * |d.lam n| * Real.exp (d.lam n * s) * |xs n| := by positivity
          calc |1 - s| * (|d.c n| * |d.lam n| * Real.exp (d.lam n * s) * |xs n|)
              ≤ 1 * (|d.c n| * |d.lam n| * Real.exp (d.lam n * s) * |xs n|) :=
                mul_le_mul_of_nonneg_right h1 h0
            _ = |d.c n| * (|d.lam n| * |xs n| * Real.exp (d.lam n * s)) := by ring
            _ ≤ K * (|d.lam n| * |xs n| * Real.exp (d.lam n * s)) :=
                mul_le_mul_of_nonneg_right (hK n) (by positivity)
            _ = K * (|d.lam n| * |xs n|) * Real.exp (d.lam n * s) := by ring
      _ = K * |d.lam n * xs n| * ∫ s in Ioc 0 1, Real.exp (d.lam n * s) := integral_const_mul _ _
      _ ≤ K * |d.lam n * xs n| * (2 / d.wt n) := by
          gcongr
          · exact mul_nonneg ((abs_nonneg _).trans (hK 0)) (abs_nonneg _)
          · exact hI n
      _ = 2 * K * (|d.lam n * xs n| / d.wt n) := by ring
  have hs₁ : Summable fun n => ∫ s in Ioc 0 1, ‖F₁ n s‖ :=
    ((d.summable_abs_div_wt hxs2).mul_left (2 * K)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) hb₁
  have hs₂ : Summable fun n => ∫ s in Ioc 0 1, ‖F₂ n s‖ :=
    ((d.summable_abs_div_wt hx).mul_left (2 * K)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) hb₂
  have h₁ := hasSum_integral_of_summable_integral_norm hint₁ hs₁
  have h₂ := hasSum_integral_of_summable_integral_norm hint₂ hs₂
  have he₁ : ∫ s in Ioc 0 1, d.obs (d.toXm1 e x) s = ∫ s in Ioc 0 1, ∑' n, F₁ n s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs =>
      ((d.hasSum_obs_toXm1 e hs.1 x).tsum_eq).symm
  have he₂ : ∫ s in Ioc 0 1, (1 - s) * d.obs (d.genXm1 e x) s = ∫ s in Ioc 0 1, ∑' n, F₂ n s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by
      rw [← (d.hasSum_obs_genXm1 e hs.1 x).tsum_eq, ← tsum_mul_left]
  rw [he₁, he₂]
  convert h₁.sub h₂ using 1
  funext n
  rw [← integral_sub (hint₁ n) (hint₂ n)]
  have : ∀ s, F₁ n s - F₂ n s =
      d.c n * xs n * (Real.exp (d.lam n * s) - (1 - s) * (d.lam n * Real.exp (d.lam n * s))) :=
    fun s => by simp only [hF₁, hF₂]; ring
  simp only [this, integral_const_mul, integral_trace_kernel, mul_one]
  rfl

/-- **`eq:heat-control-X`** and the `V`-bound of `A_{X,-1} L_T u`
(`app:boundary-heat-informative`): for bounded `bₙ` with `h'(t) = ∑ₙ cₙ bₙ λₙ e^{λₙ t}` bounded on
`(0, ∞)`, the vector `x` with coordinates `bₙ ∫₀ᵀ e^{λₙ (T - r)} u(r) dr` lies in `X` with
`‖x‖ ≤ C ‖u‖`, and the free output of `A_{X,-1} x` is square integrable on `(0, 1]` with norm at
most `C ‖u‖`. -/
theorem exists_control_bound {b : ℕ → ℝ} (hb : ∃ K, ∀ n, |b n| ≤ K)
    (hk : ∃ M, ∀ t > 0, |∑' n, d.c n * b n * d.lam n * Real.exp (d.lam n * t)| ≤ M)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ u : L2 ℝ T, ∃ x : X,
      (∀ n, ⟪e n, x⟫_ℝ = b n * ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r) ∧
      ‖x‖ ≤ C * ‖u‖ ∧
      ∃ h : MemLp (d.obs (d.genXm1 e x)) 2 (μI 1), ‖h.toLp _‖ ≤ C * ‖u‖ := by
  obtain ⟨Kb, hKb⟩ := hb
  obtain ⟨Kc, hKc⟩ := d.exists_abs_c_le
  obtain ⟨M, hM⟩ := hk
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 one_pos)
  have hKb0 : 0 ≤ Kb := (abs_nonneg _).trans (hKb 0)
  have hKc0 : 0 ≤ Kc := (abs_nonneg _).trans (hKc 0)
  set S := ∑' n, (d.wt n)⁻¹ with hSdef
  have hS : HasSum (fun n => (d.wt n)⁻¹) S := d.summable_inv_wt.hasSum
  have hS0 : 0 ≤ S := tsum_nonneg fun n => inv_nonneg.2 (d.wt_pos n).le
  set C₁ := Real.sqrt (Kb ^ 2 * (T + 1) * S) with hC₁
  set C₂ := M * Real.sqrt T with hC₂
  refine ⟨max C₁ C₂, fun u => ?_⟩
  have hu0 := norm_nonneg u
  set I : ℕ → ℝ := fun n => ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r with hIdef
  set xs : ℕ → ℝ := fun n => b n * I n with hxsdef
  have hmemg : ∀ n, MemLp (fun r => Real.exp (d.lam n * (T - r))) 2 (μI T) := fun n =>
    MemLp.of_bound
      (by fun_prop : Continuous fun r => Real.exp (d.lam n * (T - r))).aestronglyMeasurable
      1 (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (d.lam_nonpos n) (by linarith [hr.2]))
  have hxs2 : ∀ n, xs n ^ 2 ≤ Kb ^ 2 * (T + 1) * ‖u‖ ^ 2 * (d.wt n)⁻¹ := by
    intro n
    have h1 := (sq_integral_mul_le (hmemg n) u).trans
      (mul_le_mul_of_nonneg_right (d.setIntegral_exp_sq_le n hT.le) (sq_nonneg _))
    have hb2 : b n ^ 2 ≤ Kb ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKb n) 2
    rw [hxsdef]
    dsimp only
    rw [mul_pow]
    calc b n ^ 2 * I n ^ 2 ≤ Kb ^ 2 * ((T + 1) / d.wt n * ‖u‖ ^ 2) :=
          mul_le_mul hb2 h1 (sq_nonneg _) (sq_nonneg _)
      _ = Kb ^ 2 * (T + 1) * ‖u‖ ^ 2 * (d.wt n)⁻¹ := by ring
  have hsum : Summable fun n => xs n ^ 2 :=
    (d.summable_inv_wt.mul_left (Kb ^ 2 * (T + 1) * ‖u‖ ^ 2)).of_nonneg_of_le
      (fun n => sq_nonneg _) hxs2
  set a := mkL2 xs hsum with ha
  set x : X := toX e a with hx
  have hxe : ∀ n, ⟪e n, x⟫_ℝ = xs n := fun n => by
    rw [hx, toX, Diagonal.inner_diagMap, inner_stdBasis, ha, mkL2_apply, one_mul]
  -- the bound on `x`
  have hnorm_a : ‖a‖ ^ 2 ≤ (C₁ * ‖u‖) ^ 2 := by
    rw [mul_pow, hC₁, Real.sq_sqrt (by positivity)]
    calc ‖a‖ ^ 2 ≤ Kb ^ 2 * (T + 1) * ‖u‖ ^ 2 * S :=
          hasSum_le (fun n => hxs2 n) (by simpa [ha] using hasSum_sq a)
            (hS.mul_left (Kb ^ 2 * (T + 1) * ‖u‖ ^ 2))
      _ = Kb ^ 2 * (T + 1) * S * ‖u‖ ^ 2 := by ring
  have hnorm_x : ‖x‖ ≤ C₁ * ‖u‖ := by
    have h1 : ‖x‖ ≤ ‖a‖ := by
      rw [hx]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _)
          ((Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)))
    exact h1.trans ((pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hu0) two_ne_zero).1 hnorm_a)
  -- the free output of `A_{X,-1} x`
  have hpt : ∀ s : ℝ, 0 < s → |d.obs (d.genXm1 e x) s| ≤ C₂ * ‖u‖ := by
    intro s hs
    set kd : ℝ → ℝ := fun τ => ∑' n, d.c n * b n * d.lam n * Real.exp (d.lam n * τ) with hkd
    set B : ℕ → ℝ := fun n => |d.c n * b n * d.lam n| * Real.exp (d.lam n * s) with hB
    have hBs : Summable B := by
      refine (d.summable_inv_wt.mul_left (Kc * Kb * (2 * Real.exp s / s ^ 2))).of_nonneg_of_le
        (fun n => by positivity) fun n => ?_
      have hw := d.wt_pos n
      have h2 := d.wt_pow_mul_exp_le 2 hs n
      simp only [Nat.factorial_two, Nat.cast_ofNat] at h2
      have hl := d.abs_lam_le_wt n
      have hE := Real.exp_pos (d.lam n * s)
      show |d.c n * b n * d.lam n| * Real.exp (d.lam n * s) ≤
        Kc * Kb * (2 * Real.exp s / s ^ 2) * (d.wt n)⁻¹
      rw [abs_mul, abs_mul]
      have h3 : d.wt n * Real.exp (d.lam n * s) ≤ 2 * Real.exp s / s ^ 2 * (d.wt n)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hw]; nlinarith
      calc |d.c n| * |b n| * |d.lam n| * Real.exp (d.lam n * s)
          ≤ Kc * Kb * (d.wt n * Real.exp (d.lam n * s)) := by
            have := mul_le_mul (hKc n) (hKb n) (abs_nonneg _) hKc0
            have h4 : |d.lam n| * Real.exp (d.lam n * s) ≤ d.wt n * Real.exp (d.lam n * s) :=
              mul_le_mul_of_nonneg_right hl hE.le
            calc |d.c n| * |b n| * |d.lam n| * Real.exp (d.lam n * s)
                = (|d.c n| * |b n|) * (|d.lam n| * Real.exp (d.lam n * s)) := by ring
              _ ≤ (Kc * Kb) * (d.wt n * Real.exp (d.lam n * s)) :=
                  mul_le_mul this h4 (by positivity) (by positivity)
        _ ≤ Kc * Kb * (2 * Real.exp s / s ^ 2 * (d.wt n)⁻¹) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    -- `kd` is continuous on `[s, ∞)` and bounded by `M` there
    have hkdc : ContinuousOn kd (Ici s) := by
      refine continuousOn_tsum (fun n => by fun_prop) hBs fun n τ hτ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hB]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      exact mul_le_mul_of_nonpos_left hτ (d.lam_nonpos n)
    have hu1 : Integrable (u : ℝ → ℝ) (μI T) := (Lp.memLp u).integrable one_le_two
    set F : ℕ → ℝ → ℝ := fun n r =>
      (d.c n * b n * d.lam n * Real.exp (d.lam n * (s + T - r))) * u r with hF
    have hFb : ∀ n, ∀ r ∈ Ioc 0 T,
        ‖d.c n * b n * d.lam n * Real.exp (d.lam n * (s + T - r))‖ ≤ B n :=
      fun n r hr => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hB]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
        exact mul_le_mul_of_nonpos_left (by linarith [hr.2]) (d.lam_nonpos n)
    have hFi : ∀ n, Integrable (F n) (μI T) := fun n =>
      hu1.bdd_mul (by fun_prop : Continuous fun r =>
          d.c n * b n * d.lam n * Real.exp (d.lam n * (s + T - r))).aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioc (hFb n))
    have hFn : ∀ n, ∫ r in Ioc 0 T, ‖F n r‖ ≤ B n * ∫ r in Ioc 0 T, ‖(u : ℝ → ℝ) r‖ := by
      intro n
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hFi n).norm (hu1.norm.const_mul _) measurableSet_Ioc
        fun r hr => ?_
      rw [hF]; dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hFb n r hr) (norm_nonneg _)
    have hFs : Summable fun n => ∫ r in Ioc 0 T, ‖F n r‖ :=
      (hBs.mul_right _).of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hFn
    have hH := hasSum_integral_of_summable_integral_norm hFi hFs
    have hobs := d.hasSum_obs_genXm1 e hs x
    have heq : (fun n => d.c n * d.lam n * Real.exp (d.lam n * s) * ⟪e n, x⟫_ℝ) =
        fun n => ∫ r in Ioc 0 T, F n r := by
      funext n
      rw [hxe, hxsdef, hIdef]
      dsimp only
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      rw [hF]; dsimp only
      rw [show d.lam n * (s + T - r) = d.lam n * s + d.lam n * (T - r) by ring, Real.exp_add]
      ring
    rw [heq] at hobs
    have hval : d.obs (d.genXm1 e x) s = ∫ r in Ioc 0 T, kd (s + T - r) * u r := by
      rw [hobs.unique hH]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      rw [hkd]; dsimp only
      rw [← tsum_mul_right]
    have hmemk : MemLp (fun r => kd (s + T - r)) 2 (μI T) := by
      refine MemLp.of_bound ?_ M (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        refine hkdc.comp (by fun_prop) fun r hr => ?_
        show s ≤ s + T - r
        linarith [hr.2]
      · rw [Real.norm_eq_abs]; exact hM _ (by linarith [hr.2])
    have hk2 : ∫ r in Ioc 0 T, kd (s + T - r) ^ 2 ≤ M ^ 2 * T := by
      calc ∫ r in Ioc 0 T, kd (s + T - r) ^ 2 ≤ ∫ _ in Ioc 0 T, M ^ 2 := by
            refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Ioc
              fun r hr => ?_
            · exact (memLp_two_iff_integrable_sq hmemk.aestronglyMeasurable).1 hmemk
            · rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hM _ (by linarith [hr.2])) 2
        _ = M ^ 2 * T := by simp [hT.le, mul_comm]
    have hcs := (sq_integral_mul_le hmemk u).trans
      (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _))
    rw [hval]
    refine (Real.abs_le_sqrt hcs).trans (le_of_eq ?_)
    rw [hC₂, show M ^ 2 * T * ‖u‖ ^ 2 = (M * Real.sqrt T * ‖u‖) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]]
    exact Real.sqrt_sq (by positivity)
  have hmem : MemLp (d.obs (d.genXm1 e x)) 2 (μI 1) :=
    MemLp.of_bound (d.aestronglyMeasurable_obs _ measurableSet_Ioc fun t ht => ht.1) (C₂ * ‖u‖)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        rw [Real.norm_eq_abs]; exact hpt t ht.1)
  refine ⟨x, fun n => hxe n, hnorm_x.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0), hmem, ?_⟩
  have hC₂0 : 0 ≤ C₂ * ‖u‖ := by positivity
  have hb := Lp.norm_le_of_ae_bound (μ := μI 1) (p := 2) (f := hmem.toLp _) hC₂0
    (by
      filter_upwards [hmem.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t h1 h2
      rw [h1, Real.norm_eq_abs]; exact hpt t h2.1)
  have hμ : measureUnivNNReal (μI 1) = 1 := by
    simp [measureUnivNNReal]
  rw [hμ, NNReal.coe_one, Real.one_rpow, one_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hu0)

end ModalData

end BoundaryHeat

end DataDrivenControl
