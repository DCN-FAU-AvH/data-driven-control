module

public import DataDrivenControl.Semigroup.Resolvent
public import DataDrivenControl.Semigroup.Adjoint
public import DataDrivenControl.System.Setting

/-!
# Analytic semigroups

**Definition.**  `IsAnalytic S` is the scalar-agnostic
characterisation (Pazy, Thm 2.5.2 (d), local form; Engel–Nagel, Thm II.4.6): `S t` maps into
`D(A)` for `t > 0` and `‖A S(t) x‖ ≤ C/t ‖x‖` for `0 < t ≤ 1`.  It is equivalent to the
holomorphic extension of `S` to a sector, and needs no complexification.

## Main declarations

* `C0Semigroup.IsAnalytic`;
* `IsAnalytic.mem_generator_domain`: `S t x ∈ D(A)` for every `t > 0`;
* `IsAnalytic.analyticOnNhd`, `IsAnalytic.contDiffOn`: `t ↦ S t x` is real analytic (hence
  smooth) on `(0, ∞)`; `IsAnalytic.hasDerivAt`: `d/dt S t x = A S(t) x` for `t > 0`;
* `IsAnalytic.adjoint`: the adjoint semigroup of an analytic semigroup is analytic;
* system level, under `hyp:compat`: `System.exists_smoothing` (`S δ ∈ L(X, W)` for `δ > 0`)
  and `System.exists_growth_W` (`eq:analytic-W-growth-bound`).

## Proof API (no completeness needed for the generic part)

* `IsAnalytic.gen hS t : E →L[𝕜] E` is `A S(t)` for `t > 0` (`gen_apply`), with
  `‖A S(t)‖ ≤ C/t` on `(0, 1]` (`norm_gen_le_of_le_one`), `gen_add_apply`
  (`A S(a + r) = A S(a) S(r)`), `real_gen_apply` (`S(r)` commutes with `A S(a)`),
  `commute_gen`;
* `IsAnalytic.iter hS k t = Aᵏ S(t)` as a bounded operator; `gen_pow_mul_real`/`iter_eq`
  (`(A S(c))ᵏ S(r)` depends only on `k c + r`), `hasDerivAt_iter` (`d/dt Aᵏ S(t) = Aᵏ⁺¹ S(t)`),
  `norm_iter_apply_le` (`‖Aⁿ S(y) x‖ ≤ (C n/τ)ⁿ ‖S(y - τ) x‖`, from `S(τ) = S(τ/n)ⁿ`);
* `hasDerivAt_of_hasDerivWithinAt_Ici` (continuous right derivative ⇒ derivative, by the mean
  value inequality), `IsAnalytic.hasDerivAt_real_apply`;
* `IsAnalytic.norm_sub_taylor_le` (Taylor bound) and `IsAnalytic.analyticAt_real_apply`: the
  series `∑ (t - t₀)ⁿ/n! Aⁿ S(t₀) x` converges to `S t x` for `|t - t₀| < ρ`, since
  `‖Aⁿ S(y) x‖ / n! ≤ K (C e/τ)ⁿ`; `IsAnalytic.analyticAt_gen_apply` (`t ↦ A S(t) x`);
* `IsAnalytic.adjoint_real_mem_adjoint_domain`: `(S t)† η ∈ D(A†)` with
  `A† (S t)† η = (A S(t))† η`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace DataDrivenControl

/-- A continuous function with a right derivative `g y` at every point of a neighbourhood of
`t`, `g` continuous at `t`, has derivative `g t` at `t` (no completeness needed). -/
theorem hasDerivAt_of_hasDerivWithinAt_Ici {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {t : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 t) (hf : ContinuousOn f U)
    (hd : ∀ y ∈ U, HasDerivWithinAt f (g y) (Ici y) y) (hg : ContinuousAt g t) :
    HasDerivAt f (g t) t := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.1 hg ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.mem_nhds_iff.1 hU
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hball : Metric.ball t δ ⊆ U := (Metric.ball_subset_ball (min_le_right _ _)).trans h₂
  have hgε : ∀ y ∈ Metric.ball t δ, ‖g y - g t‖ ≤ ε := fun y hy => by
    rw [← dist_eq_norm]; exact (h₁ (lt_of_lt_of_le hy (min_le_left _ _))).le
  set φ : ℝ → F := fun s => f s - s • g t
  have hφc : ContinuousOn φ (Metric.ball t δ) :=
    (hf.mono hball).sub (continuous_id.smul continuous_const).continuousOn
  have hφd : ∀ y ∈ Metric.ball t δ, HasDerivWithinAt φ (g y - g t) (Ici y) y := fun y hy => by
    have h2 : HasDerivWithinAt (fun s : ℝ => s • g t) (g t) (Ici y) y := by
      simpa using (hasDerivWithinAt_id y (Ici y)).smul_const (g t)
    exact (hd y (hball hy)).sub h2
  have key : ∀ a b, a ∈ Metric.ball t δ → b ∈ Metric.ball t δ → a ≤ b →
      ‖φ b - φ a‖ ≤ ε * (b - a) := by
    intro a b ha hb hab
    have hsub : Icc a b ⊆ Metric.ball t δ := (convex_ball t δ).ordConnected.out ha hb
    exact norm_image_sub_le_of_norm_deriv_right_le_segment (hφc.mono hsub)
      (fun y hy => hφd y (hsub (Ico_subset_Icc_self hy)))
      (fun y hy => hgε y (hsub (Ico_subset_Icc_self hy))) b (right_mem_Icc.2 hab)
  filter_upwards [Metric.ball_mem_nhds t hδ] with y hy
  have ht : t ∈ Metric.ball t δ := Metric.mem_ball_self hδ
  have e : f y - f t - (y - t) • g t = φ y - φ t := by simp only [φ, sub_smul]; abel
  rw [e, Real.norm_eq_abs]
  rcases le_total t y with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key t y ht hy h
  · rw [abs_of_nonpos (sub_nonpos.2 h), norm_sub_rev, neg_sub]; exact key y t hy ht h

namespace C0Semigroup

section Generic

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

variable (S : C0Semigroup 𝕜 E)

/-- `S` is an **analytic semigroup**: `S t` maps into `D(A)` for `t > 0`, and
`‖A S(t) x‖ ≤ C/t ‖x‖` for `0 < t ≤ 1` (Pazy, Thm 2.5.2 (d), local form). -/
def IsAnalytic : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : E,
    ∃ h : S.real t x ∈ S.generator.domain, ‖S.generator ⟨S.real t x, h⟩‖ ≤ C / t * ‖x‖

variable {S}

/-- An analytic semigroup maps into `D(A)` at every positive time. -/
theorem IsAnalytic.mem_generator_domain (hS : S.IsAnalytic) {t : ℝ} (ht : 0 < t) (x : E) :
    S.real t x ∈ S.generator.domain := by
  obtain ⟨C, hC⟩ := hS
  rcases le_total t 1 with h1 | h1
  · exact (hC t ht h1 x).1
  · have := S.mem_generator_domain_apply (hC 1 one_pos le_rfl (S.real (t - 1) x)).1
      (Real.toNNReal 0)
    have e : S.real t x = S.real 1 (S.real (t - 1) x) := by
      rw [← S.real_add_apply zero_le_one (by linarith)]; ring_nf
    rw [e]
    simpa using this

/-- Congruence for the generator. -/
private theorem generator_congr {x y : E} (hx : x ∈ S.generator.domain) (hy : y ∈ S.generator.domain)
    (h : x = y) : S.generator ⟨x, hx⟩ = S.generator ⟨y, hy⟩ := by
  subst h; rfl

namespace IsAnalytic

variable (hS : S.IsAnalytic)
include hS

/-- `x ↦ A S(t) x` as a linear map, `t > 0`. -/
def genLin {t : ℝ} (ht : 0 < t) : E →ₗ[𝕜] E :=
  S.generator.toFun ∘ₗ
    ((S.real t : E →ₗ[𝕜] E).codRestrict S.generator.domain (hS.mem_generator_domain ht))

/-- `genLin` is `x ↦ A S(t) x`. -/
theorem genLin_apply {t : ℝ} (ht : 0 < t) (x : E) :
    hS.genLin ht x = S.generator ⟨S.real t x, hS.mem_generator_domain ht x⟩ := rfl

/-- The analyticity constant can be taken nonnegative. -/
theorem exists_nonneg_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 < t, t ≤ 1 → ∀ x : E,
    ‖S.generator ⟨S.real t x, hS.mem_generator_domain ht x⟩‖ ≤ C / t * ‖x‖ := by
  obtain ⟨C, hC⟩ := id hS
  refine ⟨max C 0, le_max_right _ _, fun t ht ht1 x => ?_⟩
  obtain ⟨h, hle⟩ := hC t ht ht1 x
  refine hle.trans ?_
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) ht.le)
    (norm_nonneg _)

/-- A bound for `genLin` at every positive time. -/
theorem exists_bound_genLin {t : ℝ} (ht : 0 < t) :
    ∃ K, ∀ x, ‖hS.genLin ht x‖ ≤ K * ‖x‖ := by
  obtain ⟨C, hC0, hC⟩ := hS.exists_nonneg_bound
  rcases le_total t 1 with h1 | h1
  · exact ⟨C / t, fun x => hC t ht h1 x⟩
  · refine ⟨C / 1 * ‖S.real (t - 1)‖, fun x => ?_⟩
    have e : S.real t x = S.real 1 (S.real (t - 1) x) := by
      rw [← S.real_add_apply zero_le_one (by linarith)]; ring_nf
    rw [genLin_apply, S.generator_congr _ (hS.mem_generator_domain one_pos _) e]
    refine (hC 1 one_pos le_rfl _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((S.real (t - 1)).le_opNorm x) (by positivity)

/-- `A S(t)` as a bounded operator (`t > 0`; junk `0` for `t ≤ 0`). -/
def gen (t : ℝ) : E →L[𝕜] E :=
  if ht : 0 < t then (hS.genLin ht).mkContinuousOfExistsBound (hS.exists_bound_genLin ht)
  else 0

/-- `gen t x = A S(t) x` for `t > 0`. -/
theorem gen_apply {t : ℝ} (ht : 0 < t) (x : E) :
    hS.gen t x = S.generator ⟨S.real t x, hS.mem_generator_domain ht x⟩ := by
  simp only [gen, ht, ↓reduceDIte]; rfl

/-- `‖A S(t)‖ ≤ C/t` for `0 < t ≤ 1`, with `C ≥ 0`. -/
theorem norm_gen_le_of_le_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ‖hS.gen t‖ ≤ C / t := by
  obtain ⟨C, hC0, hC⟩ := hS.exists_nonneg_bound
  refine ⟨C, hC0, fun t ht ht1 => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [hS.gen_apply ht]; exact hC t ht ht1 x

/-- `A S(a + r) x = A S(a) S(r) x`. -/
theorem gen_add_apply {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (x : E) :
    hS.gen (a + r) x = hS.gen a (S.real r x) := by
  rw [hS.gen_apply (by linarith), hS.gen_apply ha]
  exact S.generator_congr _ _ (S.real_add_apply ha.le hr x)

/-- `S(r)` commutes with `A S(a)`. -/
theorem real_gen_apply {a : ℝ} (ha : 0 < a) (r : ℝ) (x : E) :
    S.real r (hS.gen a x) = hS.gen a (S.real r x) := by
  rw [hS.gen_apply ha, hS.gen_apply ha, ← S.generator_real_apply (hS.mem_generator_domain ha x) r]
  exact S.generator_congr _ _ (S.real_comm_apply r a x)

/-- `A S(a)` and `A S(b)` commute. -/
theorem gen_gen_apply {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : E) :
    hS.gen a (hS.gen b x) = hS.gen b (hS.gen a x) := by
  have e : hS.gen b (S.real a x) = hS.gen a (S.real b x) := by
    rw [hS.gen_apply hb, hS.gen_apply ha]
    exact S.generator_congr _ _ (S.real_comm_apply b a x)
  rw [hS.gen_apply ha (hS.gen b x), hS.gen_apply hb (hS.gen a x)]
  exact S.generator_congr _ _ (by rw [hS.real_gen_apply hb a x, hS.real_gen_apply ha b x, e])

/-- `A S(a)` and `A S(b)` commute (as elements of the ring `E →L[𝕜] E`). -/
theorem commute_gen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Commute (hS.gen a) (hS.gen b) :=
  ContinuousLinearMap.ext fun x => hS.gen_gen_apply ha hb x

private theorem gen_pow_mul_real_aux (k : ℕ) {c c' : ℝ} (hc' : 0 < c') (hcc : c' ≤ c) :
    ∀ {r r' : ℝ}, 0 ≤ r → 0 ≤ r' → k * c + r = k * c' + r' →
      hS.gen c ^ k * S.real r = hS.gen c' ^ k * S.real r' := by
  have hc : 0 < c := hc'.trans_le hcc
  induction k with
  | zero =>
    intro r r' _ _ h
    simp only [CharP.cast_eq_zero, zero_mul, zero_add] at h
    simp [h]
  | succ k ih =>
    intro r r' hr hr' h
    have h1 : hS.gen c * S.real r = hS.gen c' * S.real (c - c' + r) := by
      ext x
      simp only [mul_apply_eq_comp]
      rw [← hS.gen_add_apply hc hr, ← hS.gen_add_apply hc' (by linarith),
        show c' + (c - c' + r) = c + r by ring]
    have h2 := ih (r := c - c' + r) (r' := r') (by linarith) hr' (by push_cast at h; linarith)
    rw [pow_succ, mul_assoc, h1, ← mul_assoc, ((hS.commute_gen hc hc').pow_left k).eq,
      mul_assoc, h2, ← mul_assoc, ← pow_succ']

/-- `(A S(c))ᵏ S(r)` depends only on `k c + r` (it is `Aᵏ S(k c + r)`). -/
theorem gen_pow_mul_real (k : ℕ) {c c' r r' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hr : 0 ≤ r)
    (hr' : 0 ≤ r') (h : k * c + r = k * c' + r') :
    hS.gen c ^ k * S.real r = hS.gen c' ^ k * S.real r' := by
  rcases le_total c' c with hcc | hcc
  · exact hS.gen_pow_mul_real_aux k hc' hcc hr hr' h
  · exact (hS.gen_pow_mul_real_aux k hc hcc hr' hr h.symm).symm

/-- `Aᵏ S(t)` as a bounded operator, written `(A S(t/(k+1)))ᵏ S(t/(k+1))`. -/
def iter (k : ℕ) (t : ℝ) : E →L[𝕜] E := hS.gen (t / (k + 1)) ^ k * S.real (t / (k + 1))

/-- `A⁰ S(t) = S(t)`. -/
@[simp] theorem iter_zero (t : ℝ) : hS.iter 0 t = S.real t := by simp [iter]

/-- `Aᵏ S(k c + r) = (A S(c))ᵏ S(r)`. -/
theorem iter_eq (k : ℕ) {t c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (h : t = k * c + r) :
    hS.iter k t = hS.gen c ^ k * S.real r := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [h]
  have hkc : 0 < (k : ℝ) * c := mul_pos (by exact_mod_cast hk) hc
  have ht : 0 < t := by linarith
  refine hS.gen_pow_mul_real k (by positivity) hc (by positivity) hr ?_
  rw [h]; field_simp

/-- The right derivative of `s ↦ S s x` at `t > 0` is `A S(t) x`. -/
theorem hasDerivWithinAt_real_apply {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivWithinAt (fun s => S.real s x) (hS.gen t x) (Ici t) t := by
  have h0 := S.hasDerivWithinAt_real_apply ⟨S.real t x, hS.mem_generator_domain ht x⟩
    (le_refl (0 : ℝ))
  simp only [real_zero, one_apply_eq_self] at h0
  have h1 := h0.scomp_of_eq t ((hasDerivWithinAt_id t (Ici t)).sub_const t)
    (fun s hs => sub_nonneg.2 hs) (by simp)
  rw [one_smul, ← hS.gen_apply ht] at h1
  refine h1.congr_of_mem (fun s hs => ?_) self_mem_Ici
  simp only [Function.comp_apply, id_eq]
  rw [← S.real_add_apply (sub_nonneg.2 hs) ht.le, sub_add_cancel]

/-- `t ↦ A S(t) x` is continuous at every `t > 0`. -/
theorem continuousAt_gen_apply {t : ℝ} (ht : 0 < t) (x : E) :
    ContinuousAt (fun s => hS.gen s x) t := by
  have hc : Continuous fun s => hS.gen (t / 2) (S.real (s - t / 2) x) :=
    (hS.gen (t / 2)).continuous.comp ((S.continuous_real_apply x).comp (continuous_sub_right _))
  refine hc.continuousAt.congr ?_
  filter_upwards [lt_mem_nhds (half_lt_self ht)] with s hs
  rw [← hS.gen_add_apply (half_pos ht) (sub_nonneg.2 hs.le), add_sub_cancel]

/-- `d/dt S t x = A S(t) x` for `t > 0` (no completeness needed). -/
theorem hasDerivAt_real_apply {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => S.real s x) (hS.gen t x) t :=
  hasDerivAt_of_hasDerivWithinAt_Ici (Ioi_mem_nhds ht) (S.continuous_real_apply x).continuousOn
    (fun _ hy => hS.hasDerivWithinAt_real_apply hy x) (hS.continuousAt_gen_apply ht x)

/-- `d/dt Aᵏ S(t) x = Aᵏ⁺¹ S(t) x` for `t > 0`. -/
theorem hasDerivAt_iter (k : ℕ) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => hS.iter k s x) (hS.iter (k + 1) t x) t := by
  set c := t / (k + 2) with hc_def
  have hc : 0 < c := by positivity
  have hkc : (k : ℝ) * c < t := by
    rw [hc_def, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hrest : 0 < t - (k + 1) * c := by
    rw [hc_def]; field_simp; ring_nf; positivity
  have hD := (hS.hasDerivAt_real_apply (sub_pos.2 hkc) x).comp_sub_const t (k * c)
  have hL := ((hS.gen c ^ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hD
  refine HasDerivAt.congr_of_eventuallyEq (f := fun s => (hS.gen c ^ k) (S.real (s - k * c) x))
    ?_ ?_
  · have e : hS.iter (k + 1) t x = ((hS.gen c ^ k).restrictScalars ℝ) (hS.gen (t - k * c) x) := by
      rw [hS.iter_eq (k + 1) hc hrest.le (by push_cast; ring)]
      rw [ContinuousLinearMap.coe_restrictScalars', show t - k * c = c + (t - (k + 1) * c) by ring,
        hS.gen_add_apply hc hrest.le, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
    rw [e]; exact hL
  · filter_upwards [lt_mem_nhds hkc] with s hs
    rw [hS.iter_eq k hc (sub_nonneg.2 hs.le) (by ring)]
    rfl

/-- `‖Aⁿ S(y) x‖ ≤ (C n / τ)ⁿ ‖S(y - τ) x‖` for `n ≥ 1`, `0 < τ ≤ 1`, `τ ≤ y` (split
`S(τ) = S(τ/n)ⁿ`). -/
theorem norm_iter_apply_le {C : ℝ} (hC : ∀ t, 0 < t → t ≤ 1 → ‖hS.gen t‖ ≤ C / t) {τ y : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hy : τ ≤ y) {n : ℕ} (hn : 0 < n) (x : E) :
    ‖hS.iter n y x‖ ≤ (C * n / τ) ^ n * ‖S.real (y - τ) x‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hS.iter_eq n (c := τ / n) (r := y - τ) (by positivity) (sub_nonneg.2 hy)
    (by field_simp; ring), mul_apply_eq_comp]
  refine ((hS.gen (τ / n) ^ n).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (norm_pow_le' _ hn).trans ?_
  have h1 : τ / n ≤ 1 := div_le_one_of_le₀ (hτ1.trans (by exact_mod_cast hn)) hn'.le
  have := hC (τ / n) (by positivity) h1
  rw [div_div_eq_mul_div] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this n

/-- Derivative of the Taylor sums `∑_{k ≤ n} (t - y)ᵏ / k! • Aᵏ S(y) x` in `y`. -/
theorem hasDerivAt_taylor (x : E) (t : ℝ) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => ∑ k ∈ Finset.range (n + 1), ((t - y) ^ k / k.factorial) • hS.iter k y x)
      (((t - y) ^ n / n.factorial) • hS.iter (n + 1) y x) y := by
  induction n with
  | zero =>
    simpa using hS.hasDerivAt_iter 0 hy x
  | succ n ih =>
    have hp : HasDerivAt (fun y => (t - y) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-((t - y) ^ n / n.factorial)) y := by
      have h1 : HasDerivAt (fun y : ℝ => (t - y) ^ (n + 1))
          (((n + 1 : ℕ) : ℝ) * (t - y) ^ n * (-1)) y := by
        have := (hasDerivAt_pow (n + 1) (t - y)).comp y ((hasDerivAt_id y).const_sub t)
        simpa [Function.comp_def] using this
      refine (h1.div_const ((n + 1).factorial : ℝ)).congr_deriv ?_
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have h := ih.add (hp.smul (hS.hasDerivAt_iter (n + 1) hy x))
    have e : (fun y => ∑ k ∈ Finset.range (n + 1 + 1),
        ((t - y) ^ k / k.factorial) • hS.iter k y x) = fun y =>
        (∑ k ∈ Finset.range (n + 1), ((t - y) ^ k / k.factorial) • hS.iter k y x) +
          ((t - y) ^ (n + 1) / ((n + 1).factorial : ℝ)) • hS.iter (n + 1) y x := by
      ext y; rw [Finset.sum_range_succ]
    rw [e]
    convert h using 1
    rw [neg_smul]; abel

/-- **Taylor bound** for the orbit: the remainder after the terms of order `≤ n` is at most
`|t - t₀|ⁿ⁺¹ / n! · M`, where `M` bounds `‖Aⁿ⁺¹ S(y) x‖` between `t₀` and `t`. -/
theorem norm_sub_taylor_le (x : E) {t₀ t : ℝ} (n : ℕ) {M : ℝ} (hpos : ∀ y ∈ uIcc t₀ t, 0 < y)
    (hM : ∀ y ∈ uIcc t₀ t, ‖hS.iter (n + 1) y x‖ ≤ M) :
    ‖S.real t x - ∑ k ∈ Finset.range (n + 1), ((t - t₀) ^ k / k.factorial) • hS.iter k t₀ x‖ ≤
      |t - t₀| ^ n / n.factorial * M * |t - t₀| := by
  set φ := fun y => ∑ k ∈ Finset.range (n + 1), ((t - y) ^ k / k.factorial) • hS.iter k y x
  have hφt : φ t = S.real t x := by
    simp only [φ, sub_self]
    rw [Finset.sum_range_succ']
    simp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ left_mem_uIcc)
  have h := (convex_uIcc t₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ)
    (fun y hy => (hS.hasDerivAt_taylor x t n (hpos y hy)).hasDerivWithinAt)
    (C := |t - t₀| ^ n / n.factorial * M) (fun y hy => ?_) left_mem_uIcc right_mem_uIcc
  · rw [hφt, Real.norm_eq_abs] at h
    exact h
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    refine mul_le_mul ?_ (hM y hy) (norm_nonneg _) (by positivity)
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_right_of_mem_uIcc hy) n) (by positivity)

/-- Orbits of an analytic semigroup are real analytic at every `t₀ > 0`: the Taylor series
`∑ (t - t₀)ⁿ / n! • Aⁿ S(t₀) x` converges to `S t x` for `|t - t₀| < ρ`. -/
theorem analyticAt_real_apply (x : E) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    AnalyticAt ℝ (fun t => S.real t x) t₀ := by
  obtain ⟨C₀, hC₀, hC₀'⟩ := hS.norm_gen_le_of_le_one
  set C := C₀ + 1 with hC_def
  have hC : 0 < C := by linarith
  have hgen : ∀ t, 0 < t → t ≤ 1 → ‖hS.gen t‖ ≤ C / t := fun t ht ht1 =>
    (hC₀' t ht ht1).trans (div_le_div_of_nonneg_right (by linarith) ht.le)
  set τ := min (t₀ / 2) 1 with hτ_def
  have hτ : 0 < τ := lt_min (half_pos ht₀) one_pos
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτt : τ ≤ t₀ / 2 := min_le_left _ _
  set L := C * Real.exp 1 / τ with hL_def
  have hL : 0 < L := by positivity
  set ρ := min (t₀ / 2) (1 / (2 * L)) with hρ_def
  have hρ : 0 < ρ := lt_min (half_pos ht₀) (by positivity)
  have hρt : ρ ≤ t₀ / 2 := min_le_left _ _
  have hρL : L * ρ ≤ 1 / 2 := by
    have : ρ ≤ 1 / (2 * L) := min_le_right _ _
    calc L * ρ ≤ L * (1 / (2 * L)) := mul_le_mul_of_nonneg_left this hL.le
      _ = 1 / 2 := by field_simp
  set J := Icc (t₀ - ρ) (t₀ + ρ) with hJ_def
  have ht₀J : t₀ ∈ J := ⟨by linarith, by linarith⟩
  have hJτ : ∀ y ∈ J, τ ≤ y := fun y hy => by linarith [hy.1]
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t₀ - ρ) (b := t₀ + ρ)).exists_bound_of_continuousOn
    (f := fun y => ‖S.real (y - τ) x‖ + ‖S.real y x‖)
    (((S.continuous_real_apply x).comp (continuous_sub_right τ)).norm.add
      (S.continuous_real_apply x).norm).continuousOn
  have hK' : ∀ y ∈ J, ‖S.real (y - τ) x‖ + ‖S.real y x‖ ≤ K := fun y hy => by
    have := hK y hy
    rwa [Real.norm_of_nonneg (by positivity)] at this
  have hK0 : 0 ≤ K := (by positivity : (0 : ℝ) ≤ ‖S.real (t₀ - τ) x‖ + ‖S.real t₀ x‖).trans
    (hK' t₀ ht₀J)
  -- bound on the derivatives `Aⁿ S(y) x`, `y ∈ J`
  have hB : ∀ n : ℕ, ∀ y ∈ J, ‖hS.iter n y x‖ ≤ K * (L ^ n * n.factorial) := by
    intro n y hy
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [iter_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
      linarith [hK' y hy, norm_nonneg (S.real (y - τ) x)]
    · refine (hS.norm_iter_apply_le hgen hτ hτ1 (hJτ y hy) hn x).trans ?_
      have h1 : ‖S.real (y - τ) x‖ ≤ K := by linarith [hK' y hy, norm_nonneg (S.real y x)]
      have hfac : (n : ℝ) ^ n ≤ Real.exp 1 ^ n * n.factorial := by
        have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
        rw [div_le_iff₀ (by positivity),
          show Real.exp (n : ℝ) = Real.exp 1 ^ n by rw [← Real.exp_nat_mul, mul_one]] at this
        exact this
      have h2 : (C * n / τ) ^ n ≤ L ^ n * n.factorial := by
        calc (C * n / τ) ^ n = (C / τ) ^ n * (n : ℝ) ^ n := by rw [mul_div_right_comm, mul_pow]
          _ ≤ (C / τ) ^ n * (Real.exp 1 ^ n * n.factorial) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
          _ = L ^ n * n.factorial := by rw [hL_def, mul_div_right_comm, mul_pow]; ring
      calc (C * n / τ) ^ n * ‖S.real (y - τ) x‖ ≤ (L ^ n * n.factorial) * K :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = K * (L ^ n * n.factorial) := by ring
  -- the power series
  set p : FormalMultilinearSeries ℝ ℝ E := fun n =>
    ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (((n.factorial : ℝ)⁻¹) • hS.iter n t₀ x)
    with hp_def
  have hp_apply : ∀ (n : ℕ) (s : ℝ),
      (p n fun _ => s) = ((t₀ + s - t₀) ^ n / n.factorial) • hS.iter n t₀ x := by
    intro n s
    simp only [hp_def, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_smul, add_sub_cancel_left, div_eq_mul_inv]
  have hpn : ∀ n, ‖p n‖ ≤ K * L ^ n := by
    intro n
    rw [hp_def, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, norm_inv, RCLike.norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖hS.iter n t₀ x‖
        ≤ (n.factorial : ℝ)⁻¹ * (K * (L ^ n * n.factorial)) := by
          gcongr; exact hB n t₀ ht₀J
      _ = K * L ^ n := by field_simp
  clear_value p L τ C
  refine ⟨p, ENNReal.ofReal ρ, ?_, ENNReal.ofReal_pos.2 hρ, ?_⟩
  · refine p.le_radius_of_bound K (r := ρ.toNNReal) fun n => ?_
    rw [Real.coe_toNNReal _ hρ.le]
    calc ‖p n‖ * ρ ^ n ≤ K * L ^ n * ρ ^ n := by gcongr; exact hpn n
      _ = K * (L * ρ) ^ n := by ring
      _ ≤ K * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) (by linarith)
      _ = K := mul_one K
  · intro s hs
    rw [Metric.eball_ofReal, mem_ball_zero_iff, Real.norm_eq_abs] at hs
    set q := L * |s| with hq_def
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      calc q ≤ L * ρ := mul_le_mul_of_nonneg_left hs.le hL.le
        _ < 1 := by linarith
    have hterm : ∀ n, ‖p n fun _ => s‖ ≤ K * q ^ n := by
      intro n
      rw [hp_apply, norm_smul, Real.norm_eq_abs, add_sub_cancel_left, abs_div, abs_pow,
        Nat.abs_cast]
      calc |s| ^ n / n.factorial * ‖hS.iter n t₀ x‖
          ≤ |s| ^ n / n.factorial * (K * (L ^ n * n.factorial)) := by
            gcongr; exact hB n t₀ ht₀J
        _ = K * q ^ n := by rw [hq_def, mul_pow]; field_simp
    have hsum : Summable fun n => ‖p n fun _ => s‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left K)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum, ← tendsto_add_atTop_iff_nat 1,
      tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => K * ((n + 1 : ℝ) * q ^ (n + 1))) atTop (𝓝 0) := by
      have := ((tendsto_add_atTop_iff_nat 1).2 (tendsto_self_mul_const_pow_of_lt_one hq0 hq1))
      simpa using this.const_mul K
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
    have hsJ : t₀ + s ∈ J := by
      rcases abs_lt.1 hs with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    have hsub : uIcc t₀ (t₀ + s) ⊆ J := uIcc_subset_Icc ht₀J hsJ
    have hT := hS.norm_sub_taylor_le x (t₀ := t₀) (t := t₀ + s) n
      (M := K * (L ^ (n + 1) * (n + 1).factorial))
      (fun y hy => hτ.trans_le (hJτ y (hsub hy))) (fun y hy => hB (n + 1) y (hsub hy))
    rw [norm_sub_rev]
    simp_rw [hp_apply]
    refine hT.trans (le_of_eq ?_)
    rw [add_sub_cancel_left, hq_def, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `t ↦ A S(t) x` is real analytic at every `t₀ > 0`. -/
theorem analyticAt_gen_apply (x : E) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    AnalyticAt ℝ (fun t => hS.gen t x) t₀ := by
  have h1 : AnalyticAt ℝ (fun t => S.real (t - t₀ / 2) x) t₀ := by
    have h := hS.analyticAt_real_apply x (by linarith : (0 : ℝ) < t₀ - t₀ / 2)
    exact h.comp_of_eq (analyticAt_id.sub analyticAt_const) rfl
  have h2 := ((hS.gen (t₀ / 2)).restrictScalars ℝ).analyticAt _ |>.comp h1
  refine h2.congr ?_
  filter_upwards [lt_mem_nhds (half_lt_self ht₀)] with s hs
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [← hS.gen_add_apply (half_pos ht₀) (sub_nonneg.2 hs.le), add_sub_cancel]

end IsAnalytic

/-- Orbits of an analytic semigroup are real analytic on `(0, ∞)`. -/
theorem IsAnalytic.analyticOnNhd (hS : S.IsAnalytic) (x : E) :
    AnalyticOnNhd ℝ (fun t => S.real t x) (Ioi 0) :=
  fun _ ht₀ => hS.analyticAt_real_apply x ht₀

/-- Orbits of an analytic semigroup are smooth on `(0, ∞)`. -/
theorem IsAnalytic.contDiffOn (hS : S.IsAnalytic) (x : E) :
    ContDiffOn ℝ ⊤ (fun t => S.real t x) (Ioi 0) :=
  (hS.analyticOnNhd x).contDiffOn isOpen_Ioi.uniqueDiffOn

/-- `d/dt S t x = A S(t) x` for `t > 0` and every `x` (analytic semigroups). -/
theorem IsAnalytic.hasDerivAt (hS : S.IsAnalytic) (x : E) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => S.real s x)
      (S.generator ⟨S.real t x, hS.mem_generator_domain ht x⟩) t := by
  rw [← hS.gen_apply ht]
  exact hS.hasDerivAt_real_apply ht x

end Generic

section Hilbert

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- For an analytic semigroup and `t > 0`, `(S t)† η ∈ D(A†)` and `A† (S t)† η = (A S(t))† η`. -/
theorem IsAnalytic.adjoint_real_mem_adjoint_domain {S : C0Semigroup 𝕜 E} (hS : S.IsAnalytic)
    {t : ℝ} (ht : 0 < t) (η : E) :
    ∃ h : S.adjoint.real t η ∈ S.generator.adjoint.domain,
      S.generator.adjoint ⟨_, h⟩ = ContinuousLinearMap.adjoint (hS.gen t) η := by
  rw [S.adjoint_real]
  have key : ∀ x : S.generator.domain, ⟪ContinuousLinearMap.adjoint (hS.gen t) η, (x : E)⟫_𝕜 =
      ⟪ContinuousLinearMap.adjoint (S.real t) η, S.generator x⟫_𝕜 := by
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      hS.gen_apply ht, S.generator_real_apply x.2 t]
  have hmem := LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, key⟩
  exact ⟨hmem, LinearPMap.adjoint_apply_eq S.dense_generator_domain ⟨_, hmem⟩ key⟩

/-- The adjoint semigroup of an analytic semigroup on a Hilbert space is analytic. -/
theorem IsAnalytic.adjoint {S : C0Semigroup 𝕜 E} (hS : S.IsAnalytic) : S.adjoint.IsAnalytic := by
  obtain ⟨C, -, hC⟩ := hS.norm_gen_le_of_le_one
  refine ⟨C, fun t ht ht1 η => ?_⟩
  obtain ⟨hmem, hval⟩ := hS.adjoint_real_mem_adjoint_domain ht η
  refine ⟨S.mem_adjoint_generator_domain hmem, ?_⟩
  rw [S.adjoint_generator_apply hmem, hval]
  calc ‖ContinuousLinearMap.adjoint (hS.gen t) η‖
      ≤ ‖ContinuousLinearMap.adjoint (hS.gen t)‖ * ‖η‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖hS.gen t‖ * ‖η‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ C / t * ‖η‖ := by gcongr; exact hC t ht ht1

end Hilbert

end C0Semigroup

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {sys : System U W X V Y}

omit [InnerProductSpace ℝ W] [CompleteSpace W] [InnerProductSpace ℝ X] [CompleteSpace X] in
/-- A bounded operator `f` on `X` whose values lie in `ι(W)`, with `‖ι⁻¹ f x‖ ≤ K ‖x‖`, factors
through a bounded operator `X → W`. -/
private theorem exists_clm_lift [NormedSpace ℝ W] [NormedSpace ℝ X] (ι : W →L[ℝ] X)
    (hι : Function.Injective ι) (f : X →L[ℝ] X) (K : ℝ)
    (h : ∀ x, ∃ w, ι w = f x ∧ ‖w‖ ≤ K * ‖x‖) : ∃ T : X →L[ℝ] W, ∀ x, ι (T x) = f x := by
  choose g hg using h
  have hadd : ∀ x y, g (x + y) = g x + g y := fun x y =>
    hι (by rw [map_add, (hg _).1, (hg _).1, (hg _).1, map_add])
  have hsmul : ∀ (c : ℝ) x, g (c • x) = c • g x := fun c x =>
    hι (by rw [map_smul, (hg _).1, (hg _).1, map_smul])
  let gl : X →ₗ[ℝ] W := { toFun := g, map_add' := hadd, map_smul' := hsmul }
  exact ⟨gl.mkContinuous K fun x => (hg x).2, fun x => (hg x).1⟩

set_option linter.unusedSectionVars false in
/-- **Smoothing into `W`** (`app:analytic-universal-sufficiency`): if `S` is analytic on `X`
and `hyp:compat` holds, then `S δ ∈ L(X, W)` for every `δ > 0`
(`D(A) ↪ D_V(A) ↪ W`). -/
theorem exists_smoothing (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : X →L[ℝ] W, ∀ x : X, sys.ιW (K x) = sys.SX.real δ x := by
  obtain ⟨c, hc⟩ := hc.1
  refine exists_clm_lift sys.ιW sys.ιW_injective (sys.SX.real δ)
    (|c| * ‖sys.ιV‖ * (‖sys.SX.real δ‖ + ‖hA.gen δ‖)) fun x => ?_
  have hmem := hA.mem_generator_domain hδ x
  have hV := sys.consistentV.mem_generator_domain sys.SV hmem
  obtain ⟨w, hw, hwn⟩ := hc _ hV
  refine ⟨w, sys.ιV_injective (by rw [← sys.ιWV_apply, hw]), hwn.trans ?_⟩
  rw [sys.consistentV.generator_apply sys.SV hmem, ← hA.gen_apply hδ]
  have h1 : ‖sys.ιV (sys.SX.real δ x)‖ ≤ ‖sys.ιV‖ * (‖sys.SX.real δ‖ * ‖x‖) :=
    (sys.ιV.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((sys.SX.real δ).le_opNorm x)
      (norm_nonneg _))
  have h2 : ‖sys.ιV (hA.gen δ x)‖ ≤ ‖sys.ιV‖ * (‖hA.gen δ‖ * ‖x‖) :=
    (sys.ιV.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((hA.gen δ).le_opNorm x)
      (norm_nonneg _))
  calc c * (‖sys.ιV (sys.SX.real δ x)‖ + ‖sys.ιV (hA.gen δ x)‖)
      ≤ |c| * (‖sys.ιV (sys.SX.real δ x)‖ + ‖sys.ιV (hA.gen δ x)‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (‖sys.ιV‖ * (‖sys.SX.real δ‖ * ‖x‖) + ‖sys.ιV‖ * (‖hA.gen δ‖ * ‖x‖)) := by
        gcongr
    _ = |c| * ‖sys.ιV‖ * (‖sys.SX.real δ‖ + ‖hA.gen δ‖) * ‖x‖ := by ring

set_option linter.unusedSectionVars false in
/-- **`eq:analytic-W-growth-bound`**: under analyticity and `hyp:compat`, a growth bound
`‖S t‖_{L(X)} ≤ M e^{σ t}` transfers to `W`: `‖S t‖_{L(W)} ≤ M_W e^{σ t}`
(`S(t)|_W = S(1) S(t - 1)|_W` for `t ≥ 1`, local boundedness on `W` for `t ≤ 1`). -/
theorem exists_growth_W (hA : sys.SX.IsAnalytic) (hc : sys.Compat) {M σ : ℝ}
    (hS : ∀ t : ℝ≥0, ‖sys.SX t‖ ≤ M * Real.exp (σ * t)) :
    ∃ MW : ℝ, 1 ≤ MW ∧ ∀ t : ℝ≥0, ‖sys.SW t‖ ≤ MW * Real.exp (σ * t) := by
  obtain ⟨K, hK⟩ := exists_smoothing hA hc one_pos
  obtain ⟨M₁, hM₁0, hM₁⟩ := sys.SW.exists_norm_real_le 1
  have hM0 : 0 ≤ M := by
    have := hS 0
    rw [NNReal.coe_zero, mul_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set MW := max 1 (max (M₁ * Real.exp |σ|) (‖K‖ * M * Real.exp (-σ) * ‖sys.ιW‖)) with hMW
  have hMW0 : 0 ≤ MW := zero_le_one.trans (le_max_left _ _)
  refine ⟨MW, le_max_left _ _, fun t => ?_⟩
  rcases le_total (t : ℝ) 1 with ht | ht
  · have h1 : ‖sys.SW t‖ ≤ M₁ := by simpa using hM₁ t ht
    have h2 : 1 ≤ Real.exp |σ| * Real.exp (σ * t) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have h0 : (0 : ℝ) ≤ t := t.2
      have : -(|σ| * t) ≤ σ * t := by
        rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le σ) h0
      nlinarith [abs_nonneg σ]
    calc ‖sys.SW t‖ ≤ M₁ := h1
      _ ≤ M₁ * (Real.exp |σ| * Real.exp (σ * t)) := le_mul_of_one_le_right hM₁0 h2
      _ = (M₁ * Real.exp |σ|) * Real.exp (σ * t) := by ring
      _ ≤ MW * Real.exp (σ * t) := by
          gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    have e : sys.SW t w = K (sys.SX.real (t - 1) (sys.ιW w)) := by
      apply sys.ιW_injective
      rw [hK, ← sys.SX.real_add_apply zero_le_one (by linarith), add_sub_cancel,
        ← sys.SW.real_coe t, sys.ιW_SW]
    rw [e]
    have hX : ‖sys.SX.real (t - 1)‖ ≤ M * Real.exp (σ * (t - 1)) := by
      rw [sys.SX.real_of_nonneg (by linarith)]; exact hS _
    calc ‖K (sys.SX.real (t - 1) (sys.ιW w))‖
        ≤ ‖K‖ * (‖sys.SX.real (t - 1)‖ * (‖sys.ιW‖ * ‖w‖)) :=
          (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (((sys.SX.real (t - 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left
              (sys.ιW.le_opNorm w) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ ‖K‖ * (M * Real.exp (σ * (t - 1)) * (‖sys.ιW‖ * ‖w‖)) := by gcongr
      _ = (‖K‖ * M * Real.exp (-σ) * ‖sys.ιW‖) * Real.exp (σ * t) * ‖w‖ := by
          rw [show σ * ((t : ℝ) - 1) = -σ + σ * t by ring, Real.exp_add]; ring
      _ ≤ MW * Real.exp (σ * t) * ‖w‖ := by
          gcongr; exact (le_max_right _ _).trans (le_max_right _ _)

end System

end DataDrivenControl
