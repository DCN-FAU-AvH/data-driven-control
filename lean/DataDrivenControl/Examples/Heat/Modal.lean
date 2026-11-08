module

public import DataDrivenControl.Semigroup.Modal
public import DataDrivenControl.Examples.Heat.Kernel

/-!
# Modal coordinates of the heat equation: `X₋₁`, the embeddings and two estimates

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`): the extrapolation space
`E = X₋₁` with `‖z‖_E = ‖(id - A)⁻¹ z‖_X`, `eq:heat-control-X`, and the point observation on `W`.

`ModalData` bundles eigenvalues `λₙ ≤ 0` with `∑ₙ 1/(1 - λₙ) < ∞`; `heatModal` has the Neumann
eigenvalues `λₙ = -(nπ)²`.  For a real Hilbert space `X` with a Hilbert basis `e`, `A` generates
`S_X = diagSemigroup e λ` (`ModalData.SX`).  Indices start at `0`, as in the paper.

## Main declarations

* `Xm1 = ℓ²(ℕ, ℝ)`, the space `X₋₁` in the coordinates `aₙ = zₙ / wₙ`, `wₙ = 1 - λₙ`;
  `d.toXm1 e : X →L[ℝ] Xm1`, `A_{X,-1} = d.genXm1 e`, the semigroup `d.Sm` on `X₋₁`
  (`Sm_generator_toXm1`: `A_{X₋₁} = A_{X,-1}` on `X`), the smoothing `d.smoothing e : X₋₁ →L[ℝ] X`
  (`S(s)` for `s > 0`), and the isometry `toX e : ℓ² → X`.
* `ModalData.hasSum_trace`: **the trace formula in time** behind `C ∈ L(W, ℝ)`: for `x ∈ D(A)`,
  `g(s) = ∑ₙ cₙ e^{λₙ s} xₙ` and `g'(s) = ∑ₙ cₙ λₙ e^{λₙ s} xₙ`,
  `∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds = ∑ₙ cₙ xₙ` (`= g(0)`).
* `ModalData.exists_control_bound`: **`eq:heat-control-X`**: for bounded `bₙ`, the state with
  coordinates `bₙ ∫₀ᵀ e^{λₙ (T - r)} u(r) dr` lies in `X` with norm at most `C ‖u‖`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace lp

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

/-! ### `ℓ²` -/

/-- The extrapolation space `X₋₁`, modelled as `ℓ²(ℕ, ℝ)` in the coordinates `aₙ = zₙ / wₙ`
(`‖z‖_{X₋₁} = ‖(1 - A)⁻¹ z‖_X`, `app:boundary-heat-informative`). -/
abbrev Xm1 : Type := ℓ²(ℕ, ℝ)

/-- The standard Hilbert basis of `ℓ²`. -/
def stdBasis : HilbertBasis ℕ ℝ Xm1 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ Xm1)

/-- Coordinates in the standard basis: `⟪δₙ, a⟫ = aₙ`. -/
theorem inner_stdBasis (a : Xm1) (n : ℕ) : ⟪stdBasis n, a⟫_ℝ = a n := by
  rw [← HilbertBasis.repr_apply_apply]; rfl

/-- The element of `ℓ²` with the given square-summable coordinates. -/
def mkL2 (f : ℕ → ℝ) (hf : Summable fun n => f n ^ 2) : Xm1 :=
  ⟨f, show Memℓp f 2 from (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
    (by simpa [Real.norm_eq_abs, sq_abs] using hf)⟩

/-- Coordinates of `mkL2`. -/
@[simp] theorem mkL2_apply (f : ℕ → ℝ) (hf : Summable fun n => f n ^ 2) (n : ℕ) :
    mkL2 f hf n = f n := rfl

/-- Parseval in `ℓ²`: `∑ₙ aₙ² = ‖a‖²`. -/
theorem hasSum_sq (a : Xm1) : HasSum (fun n => a n ^ 2) (‖a‖ ^ 2) := by
  simpa [inner_stdBasis] using Diagonal.hasSum_inner_sq stdBasis a

/-- The coordinates of `a ∈ ℓ²` are square summable. -/
theorem summable_sq (a : Xm1) : Summable fun n => a n ^ 2 := (hasSum_sq a).summable

/-- Elements of `ℓ²` are determined by their coordinates. -/
theorem ext_Xm1 {a b : Xm1} (h : ∀ n, a n = b n) : a = b := lp.ext (funext h)

/-! ### Elementary integrals -/

/-- `∫₀ᵀ e^{-y s} ds ≤ (T + 1)/(1 + y)` for `y, T ≥ 0`. -/
theorem setIntegral_exp_neg_mul_le {y T : ℝ} (hy : 0 ≤ y) (hT : 0 ≤ T) :
    ∫ s in Ioc 0 T, Real.exp (-(y * s)) ≤ (T + 1) / (1 + y) := by
  set I := ∫ s in Ioc 0 T, Real.exp (-(y * s)) with hI
  have hc : Continuous fun s : ℝ => Real.exp (-(y * s)) := by fun_prop
  have h1 : I ≤ T := by
    calc I ≤ ∫ _ in Ioc 0 T, (1 : ℝ) :=
          setIntegral_mono_on hc.integrableOn_Ioc (integrableOn_const (by simp))
            measurableSet_Ioc fun s hs => by
              rw [Real.exp_le_one_iff]; nlinarith [hs.1]
      _ = T := by simp [hT]
  have h2 : y * I = 1 - Real.exp (-(y * T)) := by
    rw [hI, ← integral_const_mul, ← intervalIntegral.integral_of_le hT,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s => -Real.exp (-(y * s))) (f' := fun s => y * Real.exp (-(y * s)))
        (fun s _ => ?_)
        ((by fun_prop : Continuous fun s => y * Real.exp (-(y * s))).intervalIntegrable _ _)]
    · simp; ring
    · have h1 : HasDerivAt (fun s => -(y * s)) (-y) s := by
        simpa using (hasDerivAt_id' s).const_mul (-y)
      have := h1.exp.neg
      convert this using 1
      ring
  have h3 : y * I ≤ 1 := by rw [h2]; linarith [Real.exp_pos (-(y * T))]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

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

/-! ### Modal data -/

/-- **Modal data**: eigenvalues `λₙ ≤ 0` with `∑ₙ 1/(1 - λₙ) < ∞`. -/
structure ModalData where
  /-- The eigenvalues `λₙ`. -/
  lam : ℕ → ℝ
  lam_nonpos : ∀ n, lam n ≤ 0
  summable_inv_wt : Summable fun n => (1 - lam n)⁻¹

namespace ModalData

variable (d : ModalData)

/-- The weights `wₙ = 1 - λₙ ≥ 1` of `X₋₁`. -/
def wt (n : ℕ) : ℝ := 1 - d.lam n

/-- `wₙ = 1 - λₙ ≥ 1`. -/
theorem one_le_wt (n : ℕ) : 1 ≤ d.wt n := by unfold wt; linarith [d.lam_nonpos n]

/-- `wₙ > 0`. -/
theorem wt_pos (n : ℕ) : 0 < d.wt n := lt_of_lt_of_le one_pos (d.one_le_wt n)

/-- `|λₙ| ≤ wₙ`. -/
theorem abs_lam_le_wt (n : ℕ) : |d.lam n| ≤ d.wt n := by
  unfold wt; rw [abs_of_nonpos (d.lam_nonpos n)]; linarith

/-- `|1/wₙ| ≤ 1`. -/
theorem abs_inv_wt_le (n : ℕ) : |(d.wt n)⁻¹| ≤ 1 := by
  rw [abs_inv, abs_of_pos (d.wt_pos n)]
  exact inv_le_one_of_one_le₀ (d.one_le_wt n)

/-- The eigenvalues are bounded above (by `0`). -/
theorem bddAbove_lam : BddAbove (Set.range d.lam) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact d.lam_nonpos n⟩

/-- Smoothing estimate: `wₙᵏ e^{λₙ t} ≤ k! eᵗ / tᵏ` for `t > 0` (from `yᵏ/k! ≤ eʸ`). -/
theorem wt_pow_mul_exp_le (k : ℕ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    d.wt n ^ k * Real.exp (d.lam n * t) ≤ k.factorial * Real.exp t / t ^ k := by
  have hw := d.wt_pos n
  have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg ht.le hw.le) k
  have hE : 0 < Real.exp (t * d.wt n) := Real.exp_pos _
  have h2 : Real.exp (d.lam n * t) = Real.exp t / Real.exp (t * d.wt n) := by
    rw [← Real.exp_sub]; congr 1; unfold wt; ring
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : t ^ k * d.wt n ^ k ≤ k.factorial * Real.exp (t * d.wt n) := by
    rw [← mul_pow]
    rw [div_le_iff₀ hf] at h1
    linarith
  have htk : 0 < t ^ k := pow_pos ht k
  rw [h2, mul_div_assoc', div_le_div_iff₀ hE htk]
  calc d.wt n ^ k * Real.exp t * t ^ k = (t ^ k * d.wt n ^ k) * Real.exp t := by ring
    _ ≤ (k.factorial * Real.exp (t * d.wt n)) * Real.exp t := by gcongr
    _ = _ := by ring

/-- `∑ₙ e^{λₙ t} < ∞` for `t > 0`. -/
theorem summable_exp {t : ℝ} (ht : 0 < t) : Summable fun n => Real.exp (d.lam n * t) := by
  refine (d.summable_inv_wt.mul_left (Real.exp t / t)).of_nonneg_of_le
    (fun n => (Real.exp_pos _).le) (fun n => ?_)
  have h := d.wt_pow_mul_exp_le 1 ht n
  have hw := d.wt_pos n
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
  show Real.exp (d.lam n * t) ≤ Real.exp t / t * (d.wt n)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_comm]
  exact h

/-- The extended (diagonal) semigroup `S(t) a = (e^{λₙ t} aₙ)ₙ` on `X₋₁`. -/
abbrev Sm : C0Semigroup ℝ Xm1 := diagSemigroup stdBasis d.lam d.bddAbove_lam

/-- Coordinates of the diagonal semigroup on `X₋₁`: `(S(t) a)ₙ = e^{λₙ t} aₙ`. -/
theorem Sm_apply {t : ℝ} (ht : 0 ≤ t) (a : Xm1) (n : ℕ) :
    d.Sm.real t a n = Real.exp (d.lam n * t) * a n := by
  rw [← inner_stdBasis, inner_diagSemigroup_real _ _ _ ht, inner_stdBasis]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (e : HilbertBasis ℕ ℝ X)

/-- The state-space semigroup `S_X`, diagonal in `e`. -/
abbrev SX : C0Semigroup ℝ X := diagSemigroup e d.lam d.bddAbove_lam

/-- The embedding `X ↪ X₋₁`, `x ↦ (⟪eₙ, x⟫ / wₙ)ₙ`. -/
def toXm1 : X →L[ℝ] Xm1 := Diagonal.diagMap e stdBasis (fun n => (d.wt n)⁻¹) 1 d.abs_inv_wt_le

/-- Coordinates of `X ↪ X₋₁`: `(toXm1 x)ₙ = ⟪eₙ, x⟫ / wₙ`. -/
theorem toXm1_apply (x : X) (n : ℕ) : d.toXm1 e x n = (d.wt n)⁻¹ * ⟪e n, x⟫_ℝ := by
  rw [← inner_stdBasis, toXm1, Diagonal.inner_diagMap]

omit [CompleteSpace X] in
/-- `X ↪ X₋₁` is injective. -/
theorem toXm1_injective : Function.Injective (d.toXm1 e) :=
  Diagonal.injective_diagMap e stdBasis d.abs_inv_wt_le fun n => inv_ne_zero (d.wt_pos n).ne'

/-- `X ↪ X₋₁` is consistent with the semigroups. -/
theorem consistent_toXm1 : C0Semigroup.Consistent (d.toXm1 e) (d.SX e) d.Sm :=
  Diagonal.consistent_diagMap e stdBasis d.abs_inv_wt_le d.lam d.bddAbove_lam

/-- The smoothing `S(s) : X₋₁ → X`, `a ↦ ∑ₙ wₙ e^{λₙ s} aₙ eₙ` (`s > 0`). -/
def smoothing {s : ℝ} (hs : 0 < s) : Xm1 →L[ℝ] X :=
  Diagonal.diagMap stdBasis e (fun n => d.wt n * Real.exp (d.lam n * s)) (Real.exp s / s)
    fun n => by
      have h := d.wt_pow_mul_exp_le 1 hs n
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
      rw [abs_of_pos (mul_pos (d.wt_pos n) (Real.exp_pos _))]
      exact h

/-- `smoothing s a` is `S(s) a`, read in `X`. -/
theorem toXm1_smoothing {s : ℝ} (hs : 0 < s) (a : Xm1) :
    d.toXm1 e (d.smoothing e hs a) = d.Sm.real s a := by
  refine ext_Xm1 fun n => ?_
  rw [toXm1_apply, smoothing, Diagonal.inner_diagMap, inner_stdBasis, Sm_apply _ hs.le]
  field_simp [(d.wt_pos n).ne']

/-- The isometry `ℓ² → X`, `a ↦ ∑ₙ aₙ eₙ`. -/
def toX : Xm1 →L[ℝ] X := Diagonal.diagMap stdBasis e (fun _ => 1) 1 fun _ => by simp

/-- The extension `A_{X,-1} : X → X₋₁` of `A`, `x ↦ (λₙ ⟪eₙ, x⟫ / wₙ)ₙ`. -/
def genXm1 : X →L[ℝ] Xm1 :=
  Diagonal.diagMap e stdBasis (fun n => d.lam n / d.wt n) 1 fun n => by
    rw [abs_div, abs_of_pos (d.wt_pos n), div_le_one (d.wt_pos n)]
    exact d.abs_lam_le_wt n

/-- Coordinates of `A_{X,-1} x`: `λₙ ⟪eₙ, x⟫ / wₙ`. -/
theorem genXm1_apply (x : X) (n : ℕ) : d.genXm1 e x n = d.lam n / d.wt n * ⟪e n, x⟫_ℝ := by
  rw [← inner_stdBasis, genXm1, Diagonal.inner_diagMap]

/-- `X ⊆ D(A_{X₋₁})`. -/
theorem toXm1_mem_generator_domain (x : X) : d.toXm1 e x ∈ d.Sm.generator.domain := by
  rw [mem_generator_domain_diag_iff]
  refine (Diagonal.summable_inner_sq e x).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  rw [inner_stdBasis, toXm1_apply, ← sq_abs, ← sq_abs ⟪e n, x⟫_ℝ]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  rw [abs_mul, abs_mul, ← mul_assoc]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [abs_inv, abs_of_pos (d.wt_pos n), ← div_eq_mul_inv, div_le_one (d.wt_pos n)]
  exact d.abs_lam_le_wt n

/-- `A_{X₋₁} x = A_{X,-1} x` for `x ∈ X`. -/
theorem Sm_generator_toXm1 (x : X) :
    d.Sm.generator ⟨d.toXm1 e x, d.toXm1_mem_generator_domain e x⟩ = d.genXm1 e x := by
  refine ext_Xm1 fun n => ?_
  rw [← inner_stdBasis, inner_generator_diag, inner_stdBasis, toXm1_apply, genXm1_apply]
  ring

/-! ### The trace formula in time and `eq:heat-control-X` -/

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
for `x ∈ D(A)` (`∑ₙ xₙ² < ∞`, `∑ₙ (λₙ xₙ)² < ∞`) and bounded `cₙ`, the free outputs
`g(s) = ∑ₙ cₙ e^{λₙ s} xₙ` of `x` and `g'(s) = ∑ₙ cₙ λₙ e^{λₙ s} xₙ` of `A x` satisfy
`∫₀¹ g - ∫₀¹ (1 - s) g'(s) ds = ∑ₙ cₙ xₙ`. -/
theorem hasSum_trace {c x : ℕ → ℝ} {K : ℝ} (hK : ∀ n, |c n| ≤ K)
    (hx : Summable fun n => x n ^ 2) (hAx : Summable fun n => (d.lam n * x n) ^ 2)
    {g g' : ℝ → ℝ}
    (hg : ∀ s ∈ Ioc (0 : ℝ) 1, HasSum (fun n => c n * Real.exp (d.lam n * s) * x n) (g s))
    (hg' : ∀ s ∈ Ioc (0 : ℝ) 1,
      HasSum (fun n => c n * d.lam n * Real.exp (d.lam n * s) * x n) (g' s)) :
    HasSum (fun n => c n * x n) ((∫ s in Ioc 0 1, g s) - ∫ s in Ioc 0 1, (1 - s) * g' s) := by
  set F₁ : ℕ → ℝ → ℝ := fun n s => c n * Real.exp (d.lam n * s) * x n with hF₁
  set F₂ : ℕ → ℝ → ℝ := fun n s => (1 - s) * (c n * d.lam n * Real.exp (d.lam n * s) * x n)
    with hF₂
  have hI : ∀ n, ∫ s in Ioc 0 1, Real.exp (d.lam n * s) ≤ 2 / d.wt n := d.setIntegral_exp_le
  have hexpi : ∀ n, IntegrableOn (fun s => Real.exp (d.lam n * s)) (Ioc 0 1) := fun n =>
    (by fun_prop : Continuous fun s => Real.exp (d.lam n * s)).integrableOn_Ioc
  have hint₁ : ∀ n, Integrable (F₁ n) (volume.restrict (Ioc 0 1)) := fun n =>
    (by fun_prop : Continuous (F₁ n)).integrableOn_Ioc
  have hint₂ : ∀ n, Integrable (F₂ n) (volume.restrict (Ioc 0 1)) := fun n =>
    (by fun_prop : Continuous (F₂ n)).integrableOn_Ioc
  -- bounds on the integrals of the norms
  have hb₁ : ∀ n, ∫ s in Ioc 0 1, ‖F₁ n s‖ ≤ 2 * K * (|x n| / d.wt n) := by
    intro n
    calc ∫ s in Ioc 0 1, ‖F₁ n s‖
        ≤ ∫ s in Ioc 0 1, K * |x n| * Real.exp (d.lam n * s) := by
          refine setIntegral_mono_on (hint₁ n).norm ((hexpi n).const_mul _) measurableSet_Ioc
            fun s _ => ?_
          rw [Real.norm_eq_abs, hF₁]
          simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |c n| * Real.exp (d.lam n * s) * |x n|
              = |c n| * (|x n| * Real.exp (d.lam n * s)) := by ring
            _ ≤ K * (|x n| * Real.exp (d.lam n * s)) :=
                mul_le_mul_of_nonneg_right (hK n) (by positivity)
            _ = K * |x n| * Real.exp (d.lam n * s) := by ring
      _ = K * |x n| * ∫ s in Ioc 0 1, Real.exp (d.lam n * s) := integral_const_mul _ _
      _ ≤ K * |x n| * (2 / d.wt n) := by
          gcongr
          · exact mul_nonneg ((abs_nonneg _).trans (hK 0)) (abs_nonneg _)
          · exact hI n
      _ = 2 * K * (|x n| / d.wt n) := by ring
  have hb₂ : ∀ n, ∫ s in Ioc 0 1, ‖F₂ n s‖ ≤ 2 * K * (|d.lam n * x n| / d.wt n) := by
    intro n
    calc ∫ s in Ioc 0 1, ‖F₂ n s‖
        ≤ ∫ s in Ioc 0 1, K * |d.lam n * x n| * Real.exp (d.lam n * s) := by
          refine setIntegral_mono_on (hint₂ n).norm ((hexpi n).const_mul _) measurableSet_Ioc
            fun s hs => ?_
          rw [Real.norm_eq_abs, hF₂]
          have h1 : |1 - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
          simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
          have h0 : 0 ≤ |c n| * |d.lam n| * Real.exp (d.lam n * s) * |x n| := by positivity
          calc |1 - s| * (|c n| * |d.lam n| * Real.exp (d.lam n * s) * |x n|)
              ≤ 1 * (|c n| * |d.lam n| * Real.exp (d.lam n * s) * |x n|) :=
                mul_le_mul_of_nonneg_right h1 h0
            _ = |c n| * (|d.lam n| * |x n| * Real.exp (d.lam n * s)) := by ring
            _ ≤ K * (|d.lam n| * |x n| * Real.exp (d.lam n * s)) :=
                mul_le_mul_of_nonneg_right (hK n) (by positivity)
            _ = K * (|d.lam n| * |x n|) * Real.exp (d.lam n * s) := by ring
      _ = K * |d.lam n * x n| * ∫ s in Ioc 0 1, Real.exp (d.lam n * s) := integral_const_mul _ _
      _ ≤ K * |d.lam n * x n| * (2 / d.wt n) := by
          gcongr
          · exact mul_nonneg ((abs_nonneg _).trans (hK 0)) (abs_nonneg _)
          · exact hI n
      _ = 2 * K * (|d.lam n * x n| / d.wt n) := by ring
  have hs₁ : Summable fun n => ∫ s in Ioc 0 1, ‖F₁ n s‖ :=
    ((d.summable_abs_div_wt hx).mul_left (2 * K)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) hb₁
  have hs₂ : Summable fun n => ∫ s in Ioc 0 1, ‖F₂ n s‖ :=
    ((d.summable_abs_div_wt hAx).mul_left (2 * K)).of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) hb₂
  have h₁ := hasSum_integral_of_summable_integral_norm hint₁ hs₁
  have h₂ := hasSum_integral_of_summable_integral_norm hint₂ hs₂
  have he₁ : ∫ s in Ioc 0 1, g s = ∫ s in Ioc 0 1, ∑' n, F₁ n s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => (hg s hs).tsum_eq.symm
  have he₂ : ∫ s in Ioc 0 1, (1 - s) * g' s = ∫ s in Ioc 0 1, ∑' n, F₂ n s :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by
      rw [← (hg' s hs).tsum_eq, ← tsum_mul_left]
  rw [he₁, he₂]
  convert h₁.sub h₂ using 1
  funext n
  rw [← integral_sub (hint₁ n) (hint₂ n)]
  have : ∀ s, F₁ n s - F₂ n s =
      c n * x n * (Real.exp (d.lam n * s) - (1 - s) * (d.lam n * Real.exp (d.lam n * s))) :=
    fun s => by simp only [hF₁, hF₂]; ring
  simp only [this, integral_const_mul, integral_trace_kernel, mul_one]

/-- **`eq:heat-control-X`** (`app:boundary-heat-informative`): for bounded `bₙ`, the state `x`
with coordinates `bₙ ∫₀ᵀ e^{λₙ (T - r)} u(r) dr` lies in `X` with `‖x‖ ≤ C ‖u‖` (Cauchy–Schwarz
in each coordinate: `xₙ² ≤ K² (T + 1) ‖u‖² / wₙ`). -/
theorem exists_control_bound {b : ℕ → ℝ} (hb : ∃ K, ∀ n, |b n| ≤ K) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, ∀ u : L2 ℝ T, ∃ x : X,
      (∀ n, ⟪e n, x⟫_ℝ = b n * ∫ r in Ioc 0 T, Real.exp (d.lam n * (T - r)) * u r) ∧
      ‖x‖ ≤ C * ‖u‖ := by
  obtain ⟨Kb, hKb⟩ := hb
  set S := ∑' n, (d.wt n)⁻¹ with hSdef
  have hS : HasSum (fun n => (d.wt n)⁻¹) S := d.summable_inv_wt.hasSum
  have hS0 : 0 ≤ S := tsum_nonneg fun n => inv_nonneg.2 (d.wt_pos n).le
  set C₁ := Real.sqrt (Kb ^ 2 * (T + 1) * S) with hC₁
  refine ⟨C₁, fun u => ?_⟩
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
  refine ⟨toX e a, fun n => ?_, ?_⟩
  · rw [toX, Diagonal.inner_diagMap, inner_stdBasis, ha, mkL2_apply, one_mul]
  have hnorm_a : ‖a‖ ^ 2 ≤ (C₁ * ‖u‖) ^ 2 := by
    rw [mul_pow, hC₁, Real.sq_sqrt (by positivity)]
    calc ‖a‖ ^ 2 ≤ Kb ^ 2 * (T + 1) * ‖u‖ ^ 2 * S :=
          hasSum_le (fun n => hxs2 n) (by simpa [ha] using hasSum_sq a)
            (hS.mul_left (Kb ^ 2 * (T + 1) * ‖u‖ ^ 2))
      _ = Kb ^ 2 * (T + 1) * S * ‖u‖ ^ 2 := by ring
  have h1 : ‖toX e a‖ ≤ ‖a‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)))
  exact h1.trans ((pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hu0) two_ne_zero).1 hnorm_a)

end ModalData

/-! ### The heat equation -/

/-- `∑ₙ 1/(1 + n²π²) < ∞`. -/
theorem summable_inv_one_sub_eig : Summable fun n => (1 - eig n)⁻¹ := by
  have hs : Summable fun n : ℕ => 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left 2
  refine hs.of_nonneg_of_le (fun n => ?_) fun n => ?_
  · have := eig_nonpos n
    exact inv_nonneg.2 (by linarith)
  · have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have h1 : 1 - eig n = 1 + ((n : ℝ) * Real.pi) ^ 2 := by unfold eig; ring
    rw [h1, Nat.cast_add, Nat.cast_one, ← div_eq_mul_inv]
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h2 : (n : ℝ) ^ 2 ≤ ((n : ℝ) * Real.pi) ^ 2 := by
      rw [mul_pow]; exact le_mul_of_one_le_right (sq_nonneg _) (by nlinarith)
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- The Neumann eigenvalues are bounded above by `λ₀ = 0`. -/
theorem bddAbove_eig : BddAbove (Set.range eig) := ⟨0, by rintro _ ⟨n, rfl⟩; exact eig_nonpos n⟩

/-- **The modal data of the heat equation**: `λₙ = -(nπ)²` (`app:boundary-heat-informative`). -/
def heatModal : ModalData where
  lam := eig
  lam_nonpos := eig_nonpos
  summable_inv_wt := summable_inv_one_sub_eig

/-- The eigenvalues `λₙ`. -/
theorem heatModal_lam : heatModal.lam = eig := rfl

/-- The weights `wₙ = 1 - λₙ`. -/
theorem heatModal_wt (n : ℕ) : heatModal.wt n = 1 - eig n := rfl

end BoundaryHeat

end DataDrivenControl
