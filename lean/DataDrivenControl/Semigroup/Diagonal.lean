module

public import DataDrivenControl.Semigroup.Analytic
public import DataDrivenControl.System.Controllability
public import DataDrivenControl.Analysis.ExpSums
public import DataDrivenControl.Analysis.BohrMean

/-!
# Diagonal semigroups

A real Hilbert basis `(eₙ)` and real eigenvalues `λₙ` bounded above define the self-adjoint
diagonal semigroup `S t eₙ = e^{λₙ t} eₙ`.  Approximate controllability of `(A, B)` with bounded
`B` is proved directly when the `λₙ` are distinct and `B† eₙ ≠ 0`; this replaces the paper's
appeal to `prop:fattorini-hautus` for the explicit systems of `prop:hilbert-pe-necessary`
(Step 3) and `prop:infinite-pe-insufficient` (with `Semigroup/Perturbation`).

## Main declarations

* `diagSemigroup e lam hlam : C0Semigroup ℝ X`, chosen from `exists_diagSemigroup` (built from
  the bounded diagonal operators `Diagonal.diagOp`, strong continuity by dominated convergence
  on the coordinates); `diagSemigroup_apply_basis`,
  `diagSemigroup_real_apply_basis`, `inner_diagSemigroup`, `inner_diagSemigroup_real`,
  `norm_diagSemigroup_le`;
* self-adjointness: `isSelfAdjoint_diagSemigroup`, `adjoint_diagSemigroup`,
  `generator_adjoint_diag`;
* generator: `mem_generator_domain_diag_iff` (`∑ |λₙ xₙ|² < ∞`), `inner_generator_diag`,
  `basis_mem_generator_domain`, `generator_basis`;
* `isAnalytic_diagSemigroup` (`|λₙ| e^{λₙ t} ≤ C/t` on `(0, 1]`);
* `inner_mild_diag`: the coordinates of the mild solution of `System.bounded`,
  `xₙ(t) = e^{λₙ t} xₙ(0) + ∫₀ᵗ e^{λₙ (t - r)} ⟪B† eₙ, u r⟫ dr`;
* `approxControllable_diag`: distinct `λₙ` and `B† eₙ ≠ 0` give approximate controllability in
  every time `T > 0`.

## Auxiliary results

* coordinates in a real Hilbert basis (`Diagonal.hasSum_inner_sq` (Parseval), `ext_inner`,
  `exists_inner_eq`, `norm_le_of_abs_inner_le`, `tendsto_of_inner`);
* `Diagonal.coeff_eq_zero_of_tsum_eq_zero`: uniqueness for Dirichlet series `∑ᵢ aᵢ e^{μᵢ t}` with
  distinct exponents **bounded above** (no discreteness), absolutely summable coefficients,
  vanishing on an interval: holomorphic continuation to `Re z > 0` (identity theorem), then the
  Bohr coefficients on the line `Re z = 1` (`Analysis/BohrMean`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

variable {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

namespace Diagonal

/-! ### Coordinates in a real Hilbert basis -/

section Coord

variable (e : HilbertBasis ι ℝ X)

omit [CompleteSpace X] in
/-- Parseval's identity in a real Hilbert basis: `‖x‖² = ∑ₙ ⟪eₙ, x⟫²`. -/
theorem hasSum_inner_sq (x : X) : HasSum (fun n => ⟪e n, x⟫_ℝ ^ 2) (‖x‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext n
  rw [sq, real_inner_comm (e n) x]

omit [CompleteSpace X] in
theorem summable_inner_sq (x : X) : Summable fun n => ⟪e n, x⟫_ℝ ^ 2 :=
  (hasSum_inner_sq e x).summable

omit [CompleteSpace X] in
/-- A vector is determined by its coordinates. -/
theorem ext_inner {x y : X} (h : ∀ n, ⟪e n, x⟫_ℝ = ⟪e n, y⟫_ℝ) : x = y := by
  refine e.repr.injective (lp.ext (funext fun n => ?_))
  rw [e.repr_apply_apply, e.repr_apply_apply, h]

omit [CompleteSpace X] in
/-- Every square-summable coordinate sequence comes from a vector. -/
theorem exists_inner_eq (c : ι → ℝ) (hc : Summable fun n => c n ^ 2) :
    ∃ y : X, ∀ n, ⟪e n, y⟫_ℝ = c n := by
  have hmem : Memℓp c 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    convert hc using 2 with n
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨e.repr.symm ⟨c, hmem⟩, fun n => ?_⟩
  rw [← e.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

omit [CompleteSpace X] in
/-- A norm bound from coordinatewise bounds. -/
theorem norm_le_of_abs_inner_le {x y : X} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ n, |⟪e n, y⟫_ℝ| ≤ K * |⟪e n, x⟫_ℝ|) : ‖y‖ ≤ K * ‖x‖ := by
  have h1 : ‖y‖ ^ 2 ≤ (K * ‖x‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n => ?_) (hasSum_inner_sq e y) ((hasSum_inner_sq e x).mul_left (K ^ 2))
    rw [← sq_abs, ← sq_abs ⟪e n, x⟫_ℝ, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (h n) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

omit [CompleteSpace X] in
/-- Convergence from coordinatewise convergence with a summable bound on the squared
coordinate errors (dominated convergence for series). -/
theorem tendsto_of_inner {α : Type*} {l : Filter α} {F : α → X} {y : X} {g : ι → ℝ}
    (hg : Summable g) (hlim : ∀ n, Tendsto (fun a => ⟪e n, F a⟫_ℝ) l (𝓝 ⟪e n, y⟫_ℝ))
    (hb : ∀ᶠ a in l, ∀ n, (⟪e n, F a⟫_ℝ - ⟪e n, y⟫_ℝ) ^ 2 ≤ g n) : Tendsto F l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun a => ∑' n, (⟪e n, F a⟫_ℝ - ⟪e n, y⟫_ℝ) ^ 2) l
      (𝓝 (∑' _n : ι, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hg (fun n => ?_) (hb.mono fun a ha n => ?_)
    · simpa using ((hlim n).sub_const ⟪e n, y⟫_ℝ).pow 2
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact ha n
  rw [tsum_zero] at h1
  have h2 : ∀ a, ∑' n, (⟪e n, F a⟫_ℝ - ⟪e n, y⟫_ℝ) ^ 2 = ‖F a - y‖ ^ 2 := fun a => by
    rw [← (hasSum_inner_sq e (F a - y)).tsum_eq]
    simp only [inner_sub_right]
  simp only [h2] at h1
  simpa [Real.sqrt_sq (norm_nonneg _)] using h1.sqrt

/-- The coordinates of a bounded operator that is diagonal on the basis. -/
theorem inner_apply_of_apply_basis (T : X →L[ℝ] X) (c : ι → ℝ) (hT : ∀ m, T (e m) = c m • e m)
    (x : X) (n : ι) : ⟪e n, T x⟫_ℝ = c n * ⟪e n, x⟫_ℝ := by
  classical
  have h1 : ContinuousLinearMap.adjoint T (e n) = c n • e n := by
    refine ext_inner e fun m => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, hT, real_inner_smul_left, real_inner_smul_right,
      orthonormal_iff_ite.1 e.orthonormal]
    split_ifs with h
    · subst h; rfl
    · simp
  rw [← ContinuousLinearMap.adjoint_inner_left, h1, real_inner_smul_left]

omit [CompleteSpace X] in
theorem summable_mul_inner_sq {m : ι → ℝ} {C : ℝ} (hm : ∀ n, |m n| ≤ C) (x : X) :
    Summable fun n => (m n * ⟪e n, x⟫_ℝ) ^ 2 := by
  refine ((summable_inner_sq e x).mul_left (C ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _)
    fun n => ?_
  rw [mul_pow, ← sq_abs (m n)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hm n) 2) (sq_nonneg _)

omit [CompleteSpace X] in
/-- The vector with coordinates `mₙ ⟪eₙ, x⟫` (bounded multiplier `m`). -/
def diagFun (m : ι → ℝ) (C : ℝ) (hm : ∀ n, |m n| ≤ C) (x : X) : X :=
  (exists_inner_eq e _ (summable_mul_inner_sq e hm x)).choose

omit [CompleteSpace X] in
theorem inner_diagFun {m : ι → ℝ} {C : ℝ} (hm : ∀ n, |m n| ≤ C) (x : X) (n : ι) :
    ⟪e n, diagFun e m C hm x⟫_ℝ = m n * ⟪e n, x⟫_ℝ :=
  (exists_inner_eq e _ (summable_mul_inner_sq e hm x)).choose_spec n

omit [CompleteSpace X] in
/-- The bounded diagonal operator `x ↦ ∑ₙ mₙ ⟪eₙ, x⟫ eₙ`, `|mₙ| ≤ C`. -/
def diagOp (m : ι → ℝ) (C : ℝ) (hm : ∀ n, |m n| ≤ C) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := diagFun e m C hm
      map_add' := fun x y => ext_inner e fun n => by
        simp only [inner_add_right, inner_diagFun]
        ring
      map_smul' := fun c x => ext_inner e fun n => by
        simp only [real_inner_smul_right, RingHom.id_apply, inner_diagFun]
        ring }
    |C| fun x => norm_le_of_abs_inner_le e (abs_nonneg C) fun n => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, inner_diagFun, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hm n).trans (le_abs_self C)) (abs_nonneg _)

omit [CompleteSpace X] in
theorem inner_diagOp {m : ι → ℝ} {C : ℝ} (hm : ∀ n, |m n| ≤ C) (x : X) (n : ι) :
    ⟪e n, diagOp e m C hm x⟫_ℝ = m n * ⟪e n, x⟫_ℝ :=
  inner_diagFun e hm x n

end Coord

/-! ### Elementary estimates for exponentials -/

theorem mul_le_max_of_le_one {l ω t : ℝ} (hl : l ≤ ω) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    l * t ≤ max ω 0 := by
  rcases le_total 0 l with h | h
  · nlinarith [le_max_left ω 0]
  · nlinarith [le_max_right ω 0]

theorem abs_exp_sub_one_le {a c : ℝ} (ha : a ≤ c) (hc : 0 ≤ c) : |Real.exp a - 1| ≤ Real.exp c := by
  have h1 := Real.exp_pos a
  have h2 := Real.exp_le_exp.2 ha
  have h3 := Real.one_le_exp hc
  rw [abs_le]
  constructor <;> linarith

/-- `|h⁻¹ (e^{l h} - 1) - l| ≤ e^{max ω 0} |l|` for `0 < h ≤ 1` and `l ≤ ω`. -/
theorem abs_inv_mul_exp_sub_one_sub_le {l ω h : ℝ} (hl : l ≤ ω) (hh : 0 < h) (hh1 : h ≤ 1) :
    |h⁻¹ * (Real.exp (l * h) - 1) - l| ≤ Real.exp (max ω 0) * |l| := by
  set a := l * h with ha
  have e1 : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have e2 : -a + 1 ≤ Real.exp (-a) := Real.add_one_le_exp (-a)
  have e3 : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hpos := Real.exp_pos a
  have e4 : Real.exp a - 1 ≤ a * Real.exp a := by
    nlinarith [mul_le_mul_of_nonneg_left e2 hpos.le]
  have hq1 : 0 ≤ h⁻¹ * (Real.exp a - 1) - l := by
    have : l * h ≤ Real.exp a - 1 := by linarith
    have h2 : l ≤ h⁻¹ * (Real.exp a - 1) := by
      rw [le_inv_mul_iff₀ hh]; linarith
    linarith
  have hq2 : h⁻¹ * (Real.exp a - 1) - l ≤ l * (Real.exp a - 1) := by
    have : h⁻¹ * (Real.exp a - 1) ≤ l * Real.exp a := by
      rw [inv_mul_le_iff₀ hh]; nlinarith
    linarith
  have hb := abs_exp_sub_one_le (mul_le_max_of_le_one hl hh.le hh1) (le_max_right ω 0)
  rw [abs_of_nonneg hq1]
  calc _ ≤ l * (Real.exp a - 1) := hq2
    _ ≤ |l * (Real.exp a - 1)| := le_abs_self _
    _ = |l| * |Real.exp a - 1| := abs_mul _ _
    _ ≤ |l| * Real.exp (max ω 0) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- `|l e^{l t}| t ≤ 1 + max ω 0 e^{max ω 0}` for `0 < t ≤ 1` and `l ≤ ω`. -/
theorem abs_mul_exp_mul_le {l ω t : ℝ} (hl : l ≤ ω) (ht : 0 < t) (ht1 : t ≤ 1) :
    |l * Real.exp (l * t)| * t ≤ 1 + max ω 0 * Real.exp (max ω 0) := by
  have hK : 0 ≤ max ω 0 * Real.exp (max ω 0) :=
    mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rcases le_total l 0 with h | h
  · rw [abs_of_nonpos h]
    set b := -l * t with hb
    have hb0 : 0 ≤ b := by nlinarith
    have e1 : b + 1 ≤ Real.exp b := Real.add_one_le_exp b
    have e2 : Real.exp (l * t) * Real.exp b = 1 := by
      rw [← Real.exp_add, hb]
      ring_nf
      exact Real.exp_zero
    have hpos := Real.exp_pos (l * t)
    have : -l * Real.exp (l * t) * t = b * Real.exp (l * t) := by rw [hb]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left e1 hpos.le]
  · rw [abs_of_nonneg h]
    have h1 : l ≤ max ω 0 := hl.trans (le_max_left _ _)
    have h2 : Real.exp (l * t) ≤ Real.exp (max ω 0) :=
      Real.exp_le_exp.2 (mul_le_max_of_le_one hl ht.le ht1)
    calc l * Real.exp (l * t) * t ≤ l * Real.exp (l * t) * 1 :=
          mul_le_mul_of_nonneg_left ht1 (mul_nonneg h (Real.exp_pos _).le)
      _ ≤ max ω 0 * Real.exp (max ω 0) := by
          rw [mul_one]; exact mul_le_mul h1 h2 (Real.exp_pos _).le (le_max_right _ _)
      _ ≤ _ := le_add_of_nonneg_left zero_le_one

/-! ### Uniqueness for Dirichlet series with exponents bounded above -/

/-- Holomorphy of a Dirichlet series on a right half-plane (as in `Analysis/ExpSums`). -/
theorem differentiableOn_dirichlet {ι : Type*} {μ : ι → ℝ} {d : ι → ℂ} {t₀ : ℝ}
    (hsum : ∀ t, t₀ < t → Summable fun i => ‖d i‖ * Real.exp (μ i * t)) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, Complex.exp (μ i * z) * d i) {z | t₀ < z.re} := by
  intro z hz
  have hz' : t₀ < z.re := hz
  set t₁ := (t₀ + z.re) / 2 with ht₁
  set t₂ := z.re + 1 with ht₂
  set V := {w : ℂ | t₁ < w.re ∧ w.re < t₂} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hzV : z ∈ V := ⟨by rw [ht₁]; linarith, by rw [ht₂]; linarith⟩
  have h1 : t₀ < t₁ := by rw [ht₁]; linarith
  have h2 : t₀ < t₂ := by rw [ht₂]; linarith
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' i, Complex.exp (μ i * z) * d i) V := by
    refine Complex.differentiableOn_tsum_of_summable_norm ((hsum t₁ h1).add (hsum t₂ h2))
      (fun i => Differentiable.differentiableOn (by fun_prop)) hVo (fun i w hw => ?_)
    rw [norm_mul, Complex.norm_exp, mul_comm]
    have hre : ((μ i : ℂ) * w).re = μ i * w.re := by simp
    rw [hre]
    have hle : Real.exp (μ i * w.re) ≤ Real.exp (μ i * t₁) + Real.exp (μ i * t₂) := by
      rcases le_total 0 (μ i) with hμ | hμ
      · exact le_add_of_nonneg_of_le (Real.exp_pos _).le
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hw.2.le hμ))
      · exact le_add_of_le_of_nonneg
          (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hw.1.le hμ)) (Real.exp_pos _).le
    calc ‖d i‖ * Real.exp (μ i * w.re)
        ≤ ‖d i‖ * (Real.exp (μ i * t₁) + Real.exp (μ i * t₂)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖d i‖ * Real.exp (μ i * t₁) + ‖d i‖ * Real.exp (μ i * t₂) := by ring
  exact (hd.differentiableAt (hVo.mem_nhds hzV)).differentiableWithinAt

/-- Countable-index case of `coeff_eq_zero_of_tsum_eq_zero`. -/
theorem coeff_eq_zero_of_tsum_eq_zero_of_countable {ι : Type*} [Countable ι] {μ : ι → ℝ}
    (hμ : Function.Injective μ) {ω : ℝ} (hω : ∀ i, μ i ≤ ω) {a : ι → ℝ}
    (ha : Summable fun i => |a i|) {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Ioo 0 T, ∑' i, a i * Real.exp (μ i * t) = 0) (i : ι) : a i = 0 := by
  set d : ι → ℂ := fun i => (a i : ℂ) with hd
  have hsum : ∀ t, 0 < t → Summable fun i => ‖d i‖ * Real.exp (μ i * t) := fun t ht =>
    (ha.mul_right (Real.exp (ω * t))).of_nonneg_of_le (fun i => by positivity) fun i => by
      simp only [hd, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hω i) ht.le)) (abs_nonneg _)
  set G := fun z : ℂ => ∑' i, Complex.exp (μ i * z) * d i with hG
  have hGd : DifferentiableOn ℂ G {z | 0 < z.re} := differentiableOn_dirichlet hsum
  have hP : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hzero : EqOn G 0 {z : ℂ | 0 < z.re} := by
    refine eqOn_zero_of_ae_Ioo_real (hGd.analyticOnNhd hP)
      (convex_halfSpace_re_gt 0).isPreconnected hT (fun t ht => by simpa using ht.1) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    have e1 : G t = ((∑' i, a i * Real.exp (μ i * t) : ℝ) : ℂ) := by
      simp only [hG, hd]
      rw [Complex.ofReal_tsum]
      congr 1
      funext i
      push_cast
      ring
    rw [e1, h t ht, Complex.ofReal_zero]
  set v : ι → ℂ := fun i => ((Real.exp (μ i) * a i : ℝ) : ℂ) with hv
  have hvs : Summable fun i => ‖v i‖ :=
    (ha.mul_left (Real.exp ω)).of_nonneg_of_le (fun _ => norm_nonneg _) fun i => by
      simp only [hv, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hω i)) (abs_nonneg _)
  have hbohr : ∀ y : ℝ, bohrSeries μ v y = 0 := fun y => by
    have h1 := hzero (show (1 + y * Complex.I) ∈ {z : ℂ | 0 < z.re} by simp)
    simp only [Pi.zero_apply, hG] at h1
    rw [bohrSeries_apply, ← h1]
    congr 1
    funext i
    simp only [hv, hd, smul_eq_mul]
    rw [show (μ i : ℂ) * (1 + y * Complex.I) = μ i + μ i * y * Complex.I by ring, Complex.exp_add]
    push_cast
    ring
  have hv0 := eq_zero_of_bohrSeries_ae_eq_zero hvs hμ (Eventually.of_forall fun y => hbohr y)
  have hvi : v i = 0 := congrFun hv0 i
  simp only [hv, Complex.ofReal_eq_zero, mul_eq_zero] at hvi
  exact hvi.resolve_left (Real.exp_pos _).ne'

/-- **Uniqueness for Dirichlet series with exponents bounded above.**  If the real exponents
`μᵢ ≤ ω` are distinct, `∑ᵢ |aᵢ| < ∞` and `∑ᵢ aᵢ e^{μᵢ t} = 0` for `t ∈ (0, T)`, every `aᵢ`
vanishes.  (No discreteness of the exponents is needed.) -/
theorem coeff_eq_zero_of_tsum_eq_zero {ι : Type*} {μ : ι → ℝ} (hμ : Function.Injective μ)
    {ω : ℝ} (hω : ∀ i, μ i ≤ ω) {a : ι → ℝ} (ha : Summable fun i => |a i|) {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Ioo 0 T, ∑' i, a i * Real.exp (μ i * t) = 0) (i : ι) : a i = 0 := by
  by_contra hai
  set s := Function.support a with hs
  have hsc : s.Countable := (summable_abs_iff.1 ha).countable_support
  have : Countable s := hsc.to_subtype
  refine hai (coeff_eq_zero_of_tsum_eq_zero_of_countable (ι := s) (μ := fun j => μ j)
    (hμ.comp Subtype.val_injective) (fun j => hω j) (a := fun j => a j) (ha.subtype s) hT
    (fun t ht => ?_) ⟨i, hai⟩)
  rw [← h t ht]
  refine tsum_subtype_eq_of_support_subset (f := fun i => a i * Real.exp (μ i * t)) ?_
  intro j hj
  exact left_ne_zero_of_mul hj

end Diagonal

open Diagonal

-- `diagSemigroup` is defined by choice from this existence theorem.
/-- A Hilbert basis and eigenvalues bounded above define a C₀-semigroup with
`S t eₙ = e^{λₙ t} eₙ` (unique, by density of the span of the basis). -/
theorem exists_diagSemigroup (e : HilbertBasis ι ℝ X) (lam : ι → ℝ)
    (hlam : BddAbove (Set.range lam)) :
    ∃ S : C0Semigroup ℝ X, ∀ (t : ℝ≥0) (n : ι), S t (e n) = Real.exp (lam n * t) • e n := by
  classical
  obtain ⟨ω, hω⟩ := hlam
  have hω' : ∀ n, lam n ≤ ω := fun n => hω ⟨n, rfl⟩
  have hb : ∀ (t : ℝ≥0) n, |Real.exp (lam n * t)| ≤ Real.exp (ω * t) := fun t n => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hω' n) t.2)
  let f : ℝ≥0 → X →L[ℝ] X := fun t => diagOp e (fun n => Real.exp (lam n * t)) _ (hb t)
  have hf : ∀ t x n, ⟪e n, f t x⟫_ℝ = Real.exp (lam n * t) * ⟪e n, x⟫_ℝ := fun t x n =>
    inner_diagOp e (hb t) x n
  have h0 : f 0 = 1 := ContinuousLinearMap.ext fun x => ext_inner e fun n => by simp [hf]
  have hadd : ∀ s t, f (s + t) = (f s).comp (f t) := fun s t =>
    ContinuousLinearMap.ext fun x => ext_inner e fun n => by
      simp only [hf, ContinuousLinearMap.comp_apply, NNReal.coe_add, mul_add, Real.exp_add]
      ring
  have hcont : ∀ x, Tendsto (fun t => f t x) (𝓝 0) (𝓝 x) := by
    intro x
    refine tendsto_of_inner e (g := fun n => Real.exp (max ω 0) ^ 2 * ⟪e n, x⟫_ℝ ^ 2)
      ((summable_inner_sq e x).mul_left _) (fun n => ?_) ?_
    · simp only [hf]
      have : Tendsto (fun t : ℝ≥0 => Real.exp (lam n * t)) (𝓝 0) (𝓝 1) := by
        have hc : Continuous fun t : ℝ≥0 => Real.exp (lam n * t) := by fun_prop
        simpa using hc.tendsto 0
      simpa using this.mul_const ⟪e n, x⟫_ℝ
    · filter_upwards [Iio_mem_nhds (zero_lt_one' ℝ≥0)] with t ht n
      rw [hf, show Real.exp (lam n * t) * ⟪e n, x⟫_ℝ - ⟪e n, x⟫_ℝ =
        (Real.exp (lam n * t) - 1) * ⟪e n, x⟫_ℝ by ring, mul_pow, ← sq_abs (Real.exp _ - 1)]
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ?_ 2) (sq_nonneg _)
      exact abs_exp_sub_one_le (mul_le_max_of_le_one (hω' n) t.2 (le_of_lt ht))
        (le_max_right _ _)
  refine ⟨C0Semigroup.ofTendsto f h0 hadd hcont, fun t n => ?_⟩
  rw [C0Semigroup.ofTendsto_apply]
  refine ext_inner e fun m => ?_
  rw [hf, real_inner_smul_right, orthonormal_iff_ite.1 e.orthonormal]
  split_ifs with h
  · subst h; rfl
  · simp

/-- The **diagonal semigroup** `S t eₙ = e^{λₙ t} eₙ` on the Hilbert basis `e`, for eigenvalues
`λₙ` bounded above. -/
def diagSemigroup (e : HilbertBasis ι ℝ X) (lam : ι → ℝ) (hlam : BddAbove (Set.range lam)) :
    C0Semigroup ℝ X :=
  (exists_diagSemigroup e lam hlam).choose

variable (e : HilbertBasis ι ℝ X) (lam : ι → ℝ) (hlam : BddAbove (Set.range lam))

theorem diagSemigroup_apply_basis (t : ℝ≥0) (n : ι) :
    diagSemigroup e lam hlam t (e n) = Real.exp (lam n * t) • e n :=
  (exists_diagSemigroup e lam hlam).choose_spec t n

theorem diagSemigroup_real_apply_basis {t : ℝ} (ht : 0 ≤ t) (n : ι) :
    (diagSemigroup e lam hlam).real t (e n) = Real.exp (lam n * t) • e n := by
  rw [C0Semigroup.real, diagSemigroup_apply_basis, Real.coe_toNNReal t ht]

/-- Coordinates: `⟪eₙ, S t x⟫ = e^{λₙ t} ⟪eₙ, x⟫`. -/
theorem inner_diagSemigroup (t : ℝ≥0) (x : X) (n : ι) :
    ⟪e n, diagSemigroup e lam hlam t x⟫_ℝ = Real.exp (lam n * t) * ⟪e n, x⟫_ℝ :=
  inner_apply_of_apply_basis e _ (fun m => Real.exp (lam m * t))
    (fun m => diagSemigroup_apply_basis e lam hlam t m) x n

/-- Coordinates at real times `t ≥ 0`. -/
theorem inner_diagSemigroup_real {t : ℝ} (ht : 0 ≤ t) (x : X) (n : ι) :
    ⟪e n, (diagSemigroup e lam hlam).real t x⟫_ℝ = Real.exp (lam n * t) * ⟪e n, x⟫_ℝ := by
  rw [C0Semigroup.real, inner_diagSemigroup, Real.coe_toNNReal t ht]

/-- `‖S t‖ ≤ e^{ω t}` when `λₙ ≤ ω` for all `n`. -/
theorem norm_diagSemigroup_le {ω : ℝ} (hω : ∀ n, lam n ≤ ω) (t : ℝ≥0) :
    ‖diagSemigroup e lam hlam t‖ ≤ Real.exp (ω * t) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x =>
    norm_le_of_abs_inner_le e (Real.exp_pos _).le fun n => by
      rw [inner_diagSemigroup, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hω n) t.2)) (abs_nonneg _)

/-- Each `S t` is self-adjoint. -/
theorem isSelfAdjoint_diagSemigroup (t : ℝ≥0) : IsSelfAdjoint (diagSemigroup e lam hlam t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext fun x => ext_inner e fun n => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, diagSemigroup_apply_basis, real_inner_smul_left,
    inner_diagSemigroup]

/-- The adjoint of `S t` at real times. -/
theorem adjoint_diagSemigroup_real (t : ℝ) :
    ContinuousLinearMap.adjoint ((diagSemigroup e lam hlam).real t) =
      (diagSemigroup e lam hlam).real t :=
  ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_diagSemigroup e lam hlam _)

/-- The diagonal semigroup is its own adjoint semigroup. -/
theorem adjoint_diagSemigroup : (diagSemigroup e lam hlam).adjoint = diagSemigroup e lam hlam := by
  ext t x
  rw [C0Semigroup.adjoint_apply, ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_diagSemigroup e lam hlam t).star_eq]

/-- Coordinates of the difference quotient. -/
theorem inner_diffQuot_diag (x : X) {h : ℝ} (hh : 0 ≤ h) (n : ι) :
    ⟪e n, (diagSemigroup e lam hlam).diffQuot x h⟫_ℝ =
      h⁻¹ * (Real.exp (lam n * h) - 1) * ⟪e n, x⟫_ℝ := by
  rw [C0Semigroup.diffQuot, real_inner_smul_right, inner_sub_right,
    inner_diagSemigroup_real e lam hlam hh]
  ring

theorem tendsto_inner_diffQuot_diag (x : X) (n : ι) :
    Tendsto (fun h => ⟪e n, (diagSemigroup e lam hlam).diffQuot x h⟫_ℝ) (𝓝[>] 0)
      (𝓝 (lam n * ⟪e n, x⟫_ℝ)) := by
  have hd : HasDerivAt (fun h => Real.exp (lam n * h)) (lam n) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (lam n)).exp
  refine (hd.tendsto_slope_zero_right.mul_const ⟪e n, x⟫_ℝ).congr'
    (eventually_nhdsWithin_of_forall fun h hh => ?_)
  dsimp only
  rw [inner_diffQuot_diag e lam hlam x (le_of_lt hh)]
  simp [smul_eq_mul]

/-- The generator acts diagonally: `⟪eₙ, A x⟫ = λₙ ⟪eₙ, x⟫`. -/
theorem inner_generator_diag (x : (diagSemigroup e lam hlam).generator.domain) (n : ι) :
    ⟪e n, (diagSemigroup e lam hlam).generator x⟫_ℝ = lam n * ⟪e n, (x : X)⟫_ℝ := by
  have h1 : Tendsto (fun h => ⟪e n, (diagSemigroup e lam hlam).diffQuot x h⟫_ℝ) (𝓝[>] 0)
      (𝓝 ⟪e n, (diagSemigroup e lam hlam).generator x⟫_ℝ) :=
    (((innerSL ℝ (e n)).continuous.tendsto _).comp
      ((diagSemigroup e lam hlam).tendsto_generator x))
  exact tendsto_nhds_unique h1 (tendsto_inner_diffQuot_diag e lam hlam x n)

/-- The generator domain is `{x | ∑ |λₙ ⟪eₙ, x⟫|² < ∞}`. -/
theorem mem_generator_domain_diag_iff (x : X) :
    x ∈ (diagSemigroup e lam hlam).generator.domain ↔
      Summable fun n => (lam n * ⟪e n, x⟫_ℝ) ^ 2 := by
  constructor
  · intro hx
    have := summable_inner_sq e ((diagSemigroup e lam hlam).generator ⟨x, hx⟩)
    simpa only [inner_generator_diag] using this
  · intro hs
    obtain ⟨y, hy⟩ := exists_inner_eq e _ hs
    obtain ⟨ω, hω⟩ := id hlam
    refine (diagSemigroup e lam hlam).mem_generator_domain_of_tendsto (y := y) ?_
    refine tendsto_of_inner e (g := fun n => Real.exp (max ω 0) ^ 2 * (lam n * ⟪e n, x⟫_ℝ) ^ 2)
      (hs.mul_left _) (fun n => by rw [hy n]; exact tendsto_inner_diffQuot_diag e lam hlam x n) ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with h hh n
    rw [inner_diffQuot_diag e lam hlam x hh.1.le, hy n]
    have hq := abs_inv_mul_exp_sub_one_sub_le (hω ⟨n, rfl⟩) hh.1 hh.2
    calc (h⁻¹ * (Real.exp (lam n * h) - 1) * ⟪e n, x⟫_ℝ - lam n * ⟪e n, x⟫_ℝ) ^ 2
        = |h⁻¹ * (Real.exp (lam n * h) - 1) - lam n| ^ 2 * ⟪e n, x⟫_ℝ ^ 2 := by
          rw [sq_abs]; ring
      _ ≤ (Real.exp (max ω 0) * |lam n|) ^ 2 * ⟪e n, x⟫_ℝ ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, sq_abs]; ring

theorem basis_mem_generator_domain (n : ι) :
    e n ∈ (diagSemigroup e lam hlam).generator.domain :=
  (((diagSemigroup e lam hlam).eigen_iff_real (e n) (lam n)).1
    (diagSemigroup_apply_basis e lam hlam · n)).1

/-- `A eₙ = λₙ eₙ`. -/
theorem generator_basis (n : ι) :
    (diagSemigroup e lam hlam).generator ⟨e n, basis_mem_generator_domain e lam hlam n⟩ =
      lam n • e n :=
  (((diagSemigroup e lam hlam).eigen_iff_real (e n) (lam n)).1
    (diagSemigroup_apply_basis e lam hlam · n)).2

/-- The generator is self-adjoint: `A† = A`. -/
theorem generator_adjoint_diag :
    (diagSemigroup e lam hlam).generator.adjoint = (diagSemigroup e lam hlam).generator := by
  rw [← C0Semigroup.generator_adjoint, adjoint_diagSemigroup]

/-- Diagonal semigroups with eigenvalues bounded above are analytic. -/
theorem isAnalytic_diagSemigroup : (diagSemigroup e lam hlam).IsAnalytic := by
  obtain ⟨ω, hω⟩ := id hlam
  have hω' : ∀ n, lam n ≤ ω := fun n => hω ⟨n, rfl⟩
  set K := 1 + max ω 0 * Real.exp (max ω 0) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max ω 0 * Real.exp (max ω 0) := mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    linarith
  refine ⟨K, fun t ht ht1 x => ?_⟩
  have hcoef : ∀ n, |lam n * Real.exp (lam n * t)| ≤ K / t := fun n => by
    rw [le_div_iff₀ ht]; exact abs_mul_exp_mul_le (hω' n) ht ht1
  have hmem : (diagSemigroup e lam hlam).real t x ∈ (diagSemigroup e lam hlam).generator.domain := by
    rw [mem_generator_domain_diag_iff]
    refine ((summable_inner_sq e x).mul_left ((K / t) ^ 2)).of_nonneg_of_le
      (fun n => sq_nonneg _) fun n => ?_
    rw [inner_diagSemigroup_real e lam hlam ht.le, ← mul_assoc, mul_pow,
      ← sq_abs (lam n * _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hcoef n) 2) (sq_nonneg _)
  refine ⟨hmem, norm_le_of_abs_inner_le e (div_nonneg hK0 ht.le) fun n => ?_⟩
  simp only [inner_generator_diag]
  rw [inner_diagSemigroup_real e lam hlam ht.le, ← mul_assoc, abs_mul]
  exact mul_le_mul_of_nonneg_right (hcoef n) (abs_nonneg _)

section System

variable {U Y : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- For bounded systems the control convolution is the `X`-valued integral. -/
private theorem bounded_L_eq (S : C0Semigroup ℝ X) (B : U →L[ℝ] X) (C : X →L[ℝ] Y) (t : ℝ)
    (u : ℝ → U) :
    (System.bounded S B C).L t u = ∫ r in Ioc 0 t, S.real (t - r) (B (u r)) :=
  System.L_eq_of_ιWV rfl

/-- Coordinates of the mild solution of the diagonal system with bounded `B`:
`⟪eₙ, x t⟫ = e^{λₙ t} ⟪eₙ, x₀⟫ + ∫₀ᵗ e^{λₙ (t - r)} ⟪B† eₙ, u r⟫ dr`. -/
theorem inner_mild_diag (B : U →L[ℝ] X) (C : X →L[ℝ] Y) {t : ℝ} (ht : 0 ≤ t) {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) (x₀ : X) (n : ι) :
    ⟪e n, (System.bounded (diagSemigroup e lam hlam) B C).mild x₀ u t⟫_ℝ =
      Real.exp (lam n * t) * ⟪e n, x₀⟫_ℝ +
        ∫ r in Ioc 0 t, Real.exp (lam n * (t - r)) * ⟪ContinuousLinearMap.adjoint B (e n), u r⟫_ℝ := by
  have hint : IntegrableOn (fun r => (diagSemigroup e lam hlam).real (t - r) (B (u r))) (Ioc 0 t) :=
    (diagSemigroup e lam hlam).integrableOn_conv (B.integrable_comp (hu.integrable one_le_two))
  simp only [System.mild, System.bounded_SX, System.bounded_ιW, ContinuousLinearMap.id_apply,
    bounded_L_eq, inner_add_right]
  rw [inner_diagSemigroup_real e lam hlam ht, ← integral_inner hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  rw [inner_diagSemigroup_real e lam hlam (sub_nonneg.2 hr.2),
    ContinuousLinearMap.adjoint_inner_left]

/-- **Direct approximate controllability** of diagonal systems: if the eigenvalues are
distinct and `B† eₙ ≠ 0` for every `n`, then `(A, B)` is approximately controllable in every
time `T > 0` (uniqueness of exponential series; replaces `prop:fattorini-hautus` for the
explicit examples). -/
theorem approxControllable_diag (hinj : Function.Injective lam) (B : U →L[ℝ] X)
    (hB : ∀ n, ContinuousLinearMap.adjoint B (e n) ≠ 0) (C : X →L[ℝ] Y) {T : ℝ} (hT : 0 < T) :
    (System.bounded (diagSemigroup e lam hlam) B C).ApproxControllable T := by
  set S := diagSemigroup e lam hlam with hS
  obtain ⟨ω, hω⟩ := id hlam
  have hH1 := System.bounded_H1 S B C T
  rw [System.approxControllable_iff hH1 hT]
  intro η hη
  set f : ℝ → U := fun r => ContinuousLinearMap.adjoint B (S.real (T - r) η) with hf
  have hfc : Continuous f := (ContinuousLinearMap.adjoint B).continuous.comp
    ((S.continuous_real_apply η).comp (continuous_const.sub continuous_id))
  have hfm : MemLp f 2 (μI T) := memLp_μI_of_continuousOn hfc.continuousOn
  have h1 := hη (hfm.toLp f)
  rw [System.Lop_apply hH1 hT, System.L_congr_ae hfm.coeFn_toLp] at h1
  simp only [System.bounded_ιW, ContinuousLinearMap.id_apply, bounded_L_eq] at h1
  have hint : IntegrableOn (fun r => S.real (T - r) (B (f r))) (Ioc 0 T) :=
    S.integrableOn_conv (B.integrable_comp (hfm.integrable one_le_two))
  rw [← integral_inner hint] at h1
  have h2 : ∀ r, ⟪η, S.real (T - r) (B (f r))⟫_ℝ = ‖f r‖ ^ 2 := fun r => by
    rw [← ContinuousLinearMap.adjoint_inner_left (S.real (T - r)),
      adjoint_diagSemigroup_real e lam hlam, ← ContinuousLinearMap.adjoint_inner_left B,
      real_inner_self_eq_norm_sq]
  simp only [h2] at h1
  have hsq : Continuous fun r => ‖f r‖ ^ 2 := hfc.norm.pow 2
  have h3 : (fun r => ‖f r‖ ^ 2) =ᵐ[volume.restrict (Ioc 0 T)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg _)
      (hsq.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).1 h1
  have h4 : EqOn (fun r => ‖f r‖ ^ 2) 0 (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self h3)
      isOpen_Ioo hsq.continuousOn continuousOn_const
  have h5 : ∀ s ∈ Ioo 0 T, ContinuousLinearMap.adjoint B (S.real s η) = 0 := fun s hs => by
    have := h4 (show T - s ∈ Ioo 0 T from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      norm_eq_zero, hf, sub_sub_cancel] at this
    exact this
  have h6 : ∀ n, ⟪e n, η⟫_ℝ = 0 := by
    intro n
    set v := ContinuousLinearMap.adjoint B (e n) with hv
    set a : ι → ℝ := fun m => ⟪e m, η⟫_ℝ * ⟪e m, B v⟫_ℝ with ha
    have has : Summable fun m => |a m| :=
      ((summable_inner_sq e η).add (summable_inner_sq e (B v))).of_nonneg_of_le
        (fun m => abs_nonneg _) fun m => by
          simp only [ha, abs_mul]
          nlinarith [two_mul_le_add_sq |⟪e m, η⟫_ℝ| |⟪e m, B v⟫_ℝ|, sq_abs ⟪e m, η⟫_ℝ,
            sq_abs ⟪e m, B v⟫_ℝ, abs_nonneg ⟪e m, η⟫_ℝ, abs_nonneg ⟪e m, B v⟫_ℝ,
            mul_nonneg (abs_nonneg ⟪e m, η⟫_ℝ) (abs_nonneg ⟪e m, B v⟫_ℝ)]
    have hzero : ∀ s ∈ Ioo 0 T, ∑' m, a m * Real.exp (lam m * s) = 0 := fun s hs => by
      have h7 : ⟪S.real s η, B v⟫_ℝ = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left, h5 s hs, inner_zero_left]
      rw [← (e.hasSum_inner_mul_inner (S.real s η) (B v)).tsum_eq] at h7
      rw [← h7]
      congr 1
      funext m
      rw [real_inner_comm (e m) (S.real s η), inner_diagSemigroup_real e lam hlam hs.1.le]
      simp only [ha]
      ring
    have hcoef := coeff_eq_zero_of_tsum_eq_zero hinj (fun m => hω ⟨m, rfl⟩) has hT hzero n
    have hv0 : ⟪e n, B v⟫_ℝ ≠ 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← hv, real_inner_self_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hB n))
    exact (mul_eq_zero.1 hcoef).resolve_right hv0
  exact ext_inner e fun n => by rw [h6 n, inner_zero_right]

end System

end DataDrivenControl
