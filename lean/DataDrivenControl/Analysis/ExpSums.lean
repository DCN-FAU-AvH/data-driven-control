module

public import Mathlib

/-!
# Uniqueness for exponential sums and series

Uniqueness tools for exponential sums and series, all through
the identity theorem.  Used by `ex:window-strictly-stronger` (`app:window-strictly-stronger`),
`prop:infinite-pe-insufficient` (`app:infinite-pe-insufficient`), `lem:harmonic-pe-implies-pe`
(`app:harmonic-pe`), `lem:bohr-annihilator` (`app:analytic-universal-sufficiency`) and diagonal
controllability (`Semigroup/Diagonal`, through `eqOn_zero_of_ae_Ioo_real`).

Coefficients live in a Banach space `E`; Hilbert-valued coefficients are the case of interest.
"For a.e. `t` in an interval" is `∀ᵐ t ∂(volume.restrict (Ioo a b))`; windows `Ioc 0 T` reduce to
it by `ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self`.

## Accumulation points and the identity theorem
* `accPt_Ioo_inter_of_ae`: a property holding a.e. on `Ioo a b` holds on a set accumulating at
  every point of `Ioo a b`; `accPt_ofReal_image`: accumulation points of real sets persist in `ℂ`;
* `eqOn_zero_of_accPt`: an analytic function on a preconnected set vanishing
  on a set with an accumulation point in it vanishes (identity theorem);
* `eqOn_zero_of_ae_Ioo`: the same for a real-analytic function vanishing a.e. on an interval;
  `eqOn_zero_of_accPt_real`, `eqOn_zero_of_ae_Ioo_real`: a holomorphic function vanishing on real
  points accumulating in its domain, or a.e. on a real interval in it, vanishes;
* `analyticOnNhd_comp_ofReal`: a holomorphic function is real analytic along the real line.

## Trigonometric series
* `fourierSeries_coeff_eq_zero`: an absolutely convergent series `∑ₙ e^{int} cₙ` vanishing on `ℝ`
  has zero coefficients;
* `trigSeries_coeff_eq_zero`: `∑ₙ (cos (n t) aₙ + sin (n t) bₙ)` with geometrically decaying
  coefficients vanishing on a set with an accumulation point has `aₙ = 0` and `bₙ = 0` (`n ≥ 1`)
  (`app:window-strictly-stronger`); the series is continued analytically as a Laurent series in
  `e^{it}` and its coefficients are recovered by `fourierSeries_coeff_eq_zero`.

## Exponential sums
* `coeff_eq_zero_of_sum_cexp_eq_zero`, `coeff_eq_zero_of_sum_rexp_eq_zero`: finite sums
  `∑ᵢ e^{μᵢ t} cᵢ` with distinct exponents (complex, resp. real) vanishing on a set with an
  accumulation point have zero coefficients (the real case is used in
  `app:window-strictly-stronger`);
* `coeff_eq_zero_of_tsum_rexp_eq_zero` (and the a.e. version `…_ae_eq_zero`): a Dirichlet series
  `∑ᵢ e^{μᵢ t} cᵢ` with distinct real exponents, finitely many above each level, converging
  absolutely on `(t₀, ∞)`, vanishing on a set accumulating in `(t₀, ∞)`, has zero coefficients
  (identity theorem on a half-plane and the leading term; the a.e. version is used in
  `app:infinite-pe-insufficient`, where it replaces the paper's power series in `q = e^{-t}`).

## Harmonic signals
* `differentiable_tsum_cexp_smul`: `z ↦ ∑ᵢ e^{μᵢ z} dᵢ` with bounded `μᵢ` and summable `‖dᵢ‖` is
  entire; `analyticOnNhd_tsum_cexp_smul_ofReal`: it is real analytic on `ℝ`;
* `tsum_cexp_smul_eq_zero_of_ae`: vanishing a.e. on an interval forces vanishing on `ℂ`;
* `analyticOnNhd_harmonic`, `harmonic_eq_zero_of_ae`: the specialisation to harmonic signals
  `t ↦ ∑ₗ e^{i ωₗ t} vₗ` with bounded frequencies (`harmonic_eq_zero_of_ae` in `app:harmonic-pe`,
  `analyticOnNhd_harmonic` in `lem:bohr-annihilator`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace DataDrivenControl

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Accumulation points -/

/-- A property that holds for almost every point of an open interval holds on a subset of the
interval that accumulates at every point of it. -/
theorem accPt_Ioo_inter_of_ae {P : ℝ → Prop} {a b : ℝ}
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) :
    AccPt t₀ (𝓟 (Ioo a b ∩ {t | P t})) := by
  rw [accPt_iff_nhds]
  intro U hU
  by_contra hcon
  push Not at hcon
  have hU' : U ∩ Ioo a b ∈ 𝓝 t₀ := Filter.inter_mem hU (isOpen_Ioo.mem_nhds ht₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  rw [Real.ball_eq_Ioo] at hball
  have hsub : Ioo t₀ (t₀ + ε) ⊆ Ioo a b := fun t ht =>
    (hball ⟨by linarith [ht.1], ht.2⟩).2
  have h' : ∀ᵐ t ∂(volume.restrict (Ioo t₀ (t₀ + ε))), False := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h,
      ae_restrict_mem measurableSet_Ioo] with t hPt ht
    have hmem := hball ⟨by linarith [ht.1], ht.2⟩
    exact ht.1.ne' (hcon t ⟨hmem.1, hmem.2, hPt⟩)
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero,
    Real.volume_Ioo] at h'
  simp at h'
  linarith

/-- Accumulation points of a set of reals persist in `ℂ`. -/
theorem accPt_ofReal_image {S : Set ℝ} {t₀ : ℝ} (h : AccPt t₀ (𝓟 S)) :
    AccPt (t₀ : ℂ) (𝓟 (((↑) : ℝ → ℂ) '' S)) := by
  have := h.map Complex.continuous_ofReal.continuousAt Complex.ofReal_injective
  rwa [Filter.map_principal] at this

/-! ### The identity theorem -/

section Identity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/-- **Identity theorem.**  A function analytic on a preconnected set `U` that vanishes on a set
`S` with an accumulation point in `U` vanishes on `U`. -/
theorem eqOn_zero_of_accPt {f : 𝕜 → E} {U S : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) {z₀ : 𝕜} (hz₀ : z₀ ∈ U) (hacc : AccPt z₀ (𝓟 S))
    (hS : ∀ z ∈ S, f z = 0) : EqOn f 0 U := by
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz₀
    ((accPt_iff_frequently_nhdsNE.1 hacc).mono hS)

end Identity

/-- A real-analytic function on a preconnected set `U ⊇ (a, b)`, `a < b`, that vanishes a.e. on
`(a, b)` vanishes on `U`. -/
theorem eqOn_zero_of_ae_Ioo [NormedSpace ℝ E] {f : ℝ → E} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U) {a b : ℝ} (hab : a < b)
    (hsub : Ioo a b ⊆ U) (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), f t = 0) : EqOn f 0 U := by
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact eqOn_zero_of_accPt hf hU (hsub ht₀) (accPt_Ioo_inter_of_ae h ht₀) fun t ht => ht.2

/-- A holomorphic function on a preconnected set `U` that vanishes on a set of reals with an
accumulation point `t₀ ∈ U` vanishes on `U`. -/
theorem eqOn_zero_of_accPt_real [NormedSpace ℂ E] {f : ℂ → E} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) {S : Set ℝ} {t₀ : ℝ}
    (ht₀ : (t₀ : ℂ) ∈ U) (hacc : AccPt t₀ (𝓟 S)) (hS : ∀ t ∈ S, f t = 0) : EqOn f 0 U := by
  refine eqOn_zero_of_accPt hf hU ht₀ (accPt_ofReal_image hacc) ?_
  rintro _ ⟨t, ht, rfl⟩
  exact hS t ht

/-- A holomorphic function on a preconnected set `U` containing the real interval `(a, b)`,
`a < b`, that vanishes at a.e. point of `(a, b)` vanishes on `U`. -/
theorem eqOn_zero_of_ae_Ioo_real [NormedSpace ℂ E] {f : ℂ → E} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) {a b : ℝ} (hab : a < b)
    (hsub : ∀ t ∈ Ioo a b, (t : ℂ) ∈ U) (h : ∀ᵐ t : ℝ ∂(volume.restrict (Ioo a b)), f t = 0) :
    EqOn f 0 U := by
  have ht₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact eqOn_zero_of_accPt_real hf hU (hsub _ ht₀) (accPt_Ioo_inter_of_ae h ht₀)
    fun t ht => ht.2

/-- A function holomorphic on an open set `U ⊆ ℂ` is real analytic along the real points of
`U`. -/
theorem analyticOnNhd_comp_ofReal [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    AnalyticOnNhd ℝ (fun t : ℝ => f t) {t : ℝ | (t : ℂ) ∈ U} := by
  intro t ht
  have h1 : AnalyticAt ℂ f t := hf.analyticAt (hU.mem_nhds ht)
  exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)

/-! ### Power, Laurent and trigonometric series -/

/-- `∫₀^{2π} e^{ikt} dt = 2π δ_{k0}`. -/
private theorem integral_cexp_int_mul_I (k : ℤ) :
    ∫ t in (0 : ℝ)..2 * Real.pi, Complex.exp (k * t * Complex.I) =
      if k = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hk) Complex.I_ne_zero
    have e1 : (fun t : ℝ => Complex.exp (k * t * Complex.I)) =
        fun t : ℝ => Complex.exp (k * Complex.I * t) := by
      funext t
      ring_nf
    rw [e1, integral_exp_mul_complex hc]
    have : Complex.exp (k * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = k * (2 * Real.pi * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [this]
    simp

/-- **Uniqueness of Fourier coefficients.**  An absolutely convergent series
`∑ₙ e^{int} cₙ` (`n ∈ ℤ`) that vanishes for every real `t` has zero coefficients. -/
theorem fourierSeries_coeff_eq_zero [NormedSpace ℂ E] [CompleteSpace E] {c : ℤ → E}
    (hc : Summable fun n => ‖c n‖)
    (h : ∀ t : ℝ, ∑' n : ℤ, Complex.exp (n * t * Complex.I) • c n = 0) (n : ℤ) : c n = 0 := by
  have hsum : ∀ t : ℝ, Summable fun k : ℤ => Complex.exp (k * t * Complex.I) • c k := by
    intro t
    refine hc.of_norm_bounded fun k => le_of_eq ?_
    rw [norm_smul, show (k : ℂ) * t * Complex.I = ((k * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  set F : ℤ → ℝ → E := fun k t => Complex.exp ((k - n : ℤ) * t * Complex.I) • c k with hFdef
  have hF : ∀ t : ℝ, HasSum (fun k => F k t) 0 := by
    intro t
    have h1 := ((hsum t).hasSum).const_smul (Complex.exp (-(n * t * Complex.I)))
    rw [h t, smul_zero] at h1
    convert h1 using 1
    funext k
    simp only [hFdef, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hint : HasSum (fun k => ∫ t in (0 : ℝ)..2 * Real.pi, F k t)
      (∫ _ in (0 : ℝ)..2 * Real.pi, (0 : E)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖c k‖)
      (fun k => (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun k => ae_of_all _ fun t _ => le_of_eq ?_) (ae_of_all _ fun t _ => hc)
      intervalIntegrable_const (ae_of_all _ fun t _ => hF t)
    rw [hFdef, norm_smul, show ((k - n : ℤ) : ℂ) * t * Complex.I =
      (((k - n : ℤ) * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hval : ∀ k, ∫ t in (0 : ℝ)..2 * Real.pi, F k t =
      if k = n then (2 * (Real.pi : ℂ)) • c n else 0 := by
    intro k
    rw [hFdef]
    simp only
    rw [intervalIntegral.integral_smul_const, integral_cexp_int_mul_I]
    by_cases hkn : k = n
    · subst hkn
      simp
    · have : k - n ≠ 0 := sub_ne_zero.2 hkn
      simp [this, hkn]
  simp only [hval, intervalIntegral.integral_zero] at hint
  have h2 := hasSum_ite_eq n ((2 * (Real.pi : ℂ)) • c n)
  have h3 := hint.unique h2
  rcases smul_eq_zero.1 h3.symm with h | h
  · exfalso
    have : (2 * (Real.pi : ℂ)) ≠ 0 := by
      have := Real.pi_pos
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
    exact this h
  · exact h

/-- A Laurent series with `∑ₙ ‖aₙ‖ ρⁿ < ∞` for `r < ρ < R` is holomorphic on the annulus. -/
private theorem differentiableOn_laurent [NormedSpace ℂ E] [CompleteSpace E] {a : ℤ → E}
    {r R : ℝ} (hr : 0 ≤ r)
    (ha : ∀ ρ : ℝ, r < ρ → ρ < R → Summable fun n : ℤ => ‖a n‖ * ρ ^ n) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℤ, z ^ n • a n) {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
  rintro z ⟨hz1, hz2⟩
  obtain ⟨ρ₁, h1, h1'⟩ := exists_between hz1
  obtain ⟨ρ₂, h2, h2'⟩ := exists_between hz2
  set V := {w : ℂ | ρ₁ < ‖w‖ ∧ ‖w‖ < ρ₂} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hρ₁ : 0 < ρ₁ := lt_of_le_of_lt hr h1
  have hzV : z ∈ V := ⟨h1', h2⟩
  have hd : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℤ, z ^ n • a n) V := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((ha ρ₁ h1 (h1'.trans hz2)).add (ha ρ₂ (hz1.trans h2) h2')) (fun n => ?_) hVo
      (fun n w hw => ?_)
    · intro w hw
      have hw0 : w ≠ 0 := by
        intro h0
        have := hw.1
        rw [h0, norm_zero] at this
        linarith
      exact ((differentiableAt_zpow.2 (Or.inl hw0)).smul_const (a n)).differentiableWithinAt
    · rw [norm_smul, norm_zpow, mul_comm]
      have hw1 : ρ₁ ≤ ‖w‖ := hw.1.le
      have hw2 : ‖w‖ ≤ ρ₂ := hw.2.le
      have hle : ‖w‖ ^ n ≤ ρ₁ ^ n + ρ₂ ^ n := by
        rcases le_or_gt 0 n with hn | hn
        · exact le_add_of_nonneg_of_le (zpow_pos hρ₁ _).le
            (zpow_le_zpow_left₀ hn (norm_nonneg _) hw2)
        · have hn' : 0 ≤ -n := by omega
          have : ‖w‖ ^ n ≤ ρ₁ ^ n := by
            have h := inv_anti₀ (zpow_pos hρ₁ (-n)) (zpow_le_zpow_left₀ hn' hρ₁.le hw1)
            rwa [← zpow_neg, ← zpow_neg, neg_neg] at h
          exact le_add_of_le_of_nonneg this (zpow_pos (hρ₁.trans (h1'.trans h2)) _).le
      calc ‖a n‖ * ‖w‖ ^ n ≤ ‖a n‖ * (ρ₁ ^ n + ρ₂ ^ n) :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖a n‖ * ρ₁ ^ n + ‖a n‖ * ρ₂ ^ n := by ring
  exact (hd.differentiableAt (hVo.mem_nhds hzV)).differentiableWithinAt

/-- The scalar case of `trigSeries_coeff_eq_zero`. -/
private theorem trigSeries_coeff_eq_zero_real {α β : ℕ → ℝ} {ρ : ℝ} (hρ : 1 < ρ)
    (hα : Summable fun n => |α n| * ρ ^ n) (hβ : Summable fun n => |β n| * ρ ^ n)
    {S : Set ℝ} {t₀ : ℝ} (hacc : AccPt t₀ (𝓟 S))
    (hS : ∀ t ∈ S, ∑' n : ℕ, (Real.cos (n * t) * α n + Real.sin (n * t) * β n) = 0) :
    (∀ n, α n = 0) ∧ ∀ n, n ≠ 0 → β n = 0 := by
  have hρ0 : 0 < ρ := by linarith
  -- the Laurent coefficients
  set d : ℤ → ℂ := fun k => if 0 < k then ((α k.natAbs : ℂ) - β k.natAbs * Complex.I) / 2
    else if k < 0 then ((α k.natAbs : ℂ) + β k.natAbs * Complex.I) / 2 else (α 0 : ℂ) with hd
  have hd_pos : ∀ m : ℕ, 0 < m → d m = ((α m : ℂ) - β m * Complex.I) / 2 := by
    intro m hm
    have h1 : (0 : ℤ) < m := by exact_mod_cast hm
    simp only [hd, h1, ↓reduceIte, Int.natAbs_natCast]
  have hd_neg : ∀ m : ℕ, 0 < m → d (-m) = ((α m : ℂ) + β m * Complex.I) / 2 := by
    intro m hm
    have h1 : ¬ (0 : ℤ) < -m := by omega
    have h2 : (-m : ℤ) < 0 := by omega
    simp only [hd, h1, h2, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  have hd_zero : d 0 = α 0 := by simp [hd]
  have hd_norm : ∀ k : ℤ, ‖d k‖ ≤ |α k.natAbs| + |β k.natAbs| := by
    intro k
    have key : ∀ (x y : ℝ) (s : ℝ), s = 1 ∨ s = -1 →
        ‖((x : ℂ) + s * y * Complex.I) / 2‖ ≤ |x| + |y| := by
      intro x y s hs
      rw [norm_div, Complex.norm_two]
      have : ‖(x : ℂ) + s * y * Complex.I‖ ≤ |x| + |y| := by
        refine (norm_add_le _ _).trans ?_
        rcases hs with rfl | rfl <;> simp [Complex.norm_real]
      linarith [norm_nonneg ((x : ℂ) + s * y * Complex.I)]
    rcases lt_trichotomy 0 k with hk | hk | hk
    · have := key (α k.natAbs) (β k.natAbs) (-1) (Or.inr rfl)
      simp only [hd, ite_eq_left hk]
      convert this using 2
      push_cast
      ring
    · subst hk
      simp [hd]
    · have := key (α k.natAbs) (β k.natAbs) 1 (Or.inl rfl)
      simp only [hd, ite_eq_right (not_lt.2 hk.le), ite_eq_left hk]
      convert this using 2
      push_cast
      ring
  -- summability on the annulus
  have hg : Summable fun m : ℕ => (|α m| + |β m|) * ρ ^ m := by
    simpa [add_mul] using hα.add hβ
  have hdsum : ∀ ρ' : ℝ, 1 / ρ < ρ' → ρ' < ρ → Summable fun k : ℤ => ‖d k‖ * ρ' ^ k := by
    intro ρ' h1 h2
    have hρ'0 : 0 < ρ' := lt_trans (by positivity) h1
    have hgZ : Summable fun k : ℤ => (|α k.natAbs| + |β k.natAbs|) * ρ ^ k.natAbs :=
      Summable.of_nat_of_neg (by simpa using hg) (by simpa using hg)
    refine hgZ.of_nonneg_of_le (fun k => by positivity) fun k => ?_
    refine mul_le_mul (hd_norm k) ?_ (by positivity) (by positivity)
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      simp only [zpow_natCast, Int.natAbs_natCast]
      exact pow_le_pow_left₀ hρ'0.le h2.le m
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -m := ⟨k.natAbs, by omega⟩
      subst hm
      simp only [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      rw [← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [inv_le_comm₀ hρ'0 hρ0]
      rw [one_div] at h1
      exact h1.le
  -- the holomorphic extension and its real-analytic restriction
  set G : ℂ → ℂ := fun z => ∑' k : ℤ, z ^ k • d k with hG
  set A := {z : ℂ | 1 / ρ < ‖z‖ ∧ ‖z‖ < ρ} with hA
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hGd : DifferentiableOn ℂ G A := differentiableOn_laurent (by positivity) hdsum
  have h1ρ : 1 / ρ < 1 := by rw [div_lt_one hρ0]; exact hρ
  set U := {z : ℂ | Complex.exp (z * Complex.I) ∈ A} with hU
  have hUo : IsOpen U := hAo.preimage (by fun_prop)
  have hUd : DifferentiableOn ℂ (fun z : ℂ => G (Complex.exp (z * Complex.I))) U :=
    hGd.comp (Differentiable.differentiableOn (by fun_prop)) fun z hz => hz
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ U := by
    intro t
    show Complex.exp (t * Complex.I) ∈ A
    refine ⟨?_, ?_⟩ <;> rw [Complex.norm_exp_ofReal_mul_I]
    · exact h1ρ
    · exact hρ
  have hHan : AnalyticOnNhd ℝ (fun t : ℝ => G (Complex.exp (t * Complex.I))) univ := by
    have := analyticOnNhd_comp_ofReal hUd hUo
    simpa [hreal] using this
  -- summability of the coefficients
  have hd1 : Summable fun k : ℤ => ‖d k‖ := by
    simpa using hdsum 1 h1ρ hρ
  -- the extension equals the trigonometric series on the real line
  have htrig_sum : ∀ t : ℝ,
      Summable fun n : ℕ => Real.cos (n * t) * α n + Real.sin (n * t) * β n := by
    intro t
    refine (hg.of_nonneg_of_le (fun n => by positivity) fun n => ?_)
      |>.of_norm_bounded fun n => le_rfl
    have hρn : 1 ≤ ρ ^ n := one_le_pow₀ hρ.le
    have hc := Real.abs_cos_le_one (n * t)
    have hs := Real.abs_sin_le_one (n * t)
    rw [Real.norm_eq_abs]
    calc |Real.cos (n * t) * α n + Real.sin (n * t) * β n|
        ≤ |Real.cos (n * t) * α n| + |Real.sin (n * t) * β n| := abs_add_le _ _
      _ ≤ |α n| + |β n| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hc)
            (mul_le_of_le_one_left (abs_nonneg _) hs)
      _ ≤ (|α n| + |β n|) * ρ ^ n := le_mul_of_one_le_right (by positivity) hρn
  have hGt : ∀ t : ℝ, G (Complex.exp (t * Complex.I)) =
      ((∑' n : ℕ, (Real.cos (n * t) * α n + Real.sin (n * t) * β n) : ℝ) : ℂ) := by
    intro t
    set f : ℤ → ℂ := fun k => Complex.exp (k * t * Complex.I) * d k with hf
    have hfG : G (Complex.exp (t * Complex.I)) = ∑' k, f k := by
      show ∑' k : ℤ, (Complex.exp (t * Complex.I)) ^ k • d k = ∑' k, f k
      congr 1
      funext k
      rw [hf, smul_eq_mul, ← Complex.exp_int_mul]
      congr 2
      ring
    have hfs : Summable f := by
      refine hd1.of_norm_bounded fun k => le_of_eq ?_
      rw [hf, norm_mul, show (k : ℂ) * t * Complex.I = ((k * t : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h1 := hfs.hasSum.nat_add_neg
    have hterm : ∀ m : ℕ, f m + f (-m) =
        ((Real.cos (m * t) * α m + Real.sin (m * t) * β m : ℝ) : ℂ) +
          (if m = 0 then (α 0 : ℂ) else 0) := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp [hf, hd_zero]
      · have h0 : (if m = 0 then (α 0 : ℂ) else 0) = 0 := by simp [hm.ne']
        rw [h0, add_zero, hf]
        simp only
        rw [hd_pos m hm, hd_neg m hm]
        have e1 : Complex.exp (((m : ℤ) : ℂ) * t * Complex.I) =
            Complex.cos (m * t) + Complex.sin (m * t) * Complex.I := by
          rw [Complex.cos_add_sin_I]
          push_cast
          ring_nf
        have e2 : Complex.exp (((-m : ℤ) : ℂ) * t * Complex.I) =
            Complex.cos (m * t) - Complex.sin (m * t) * Complex.I := by
          rw [Complex.cos_sub_sin_I]
          push_cast
          ring_nf
        rw [e1, e2]
        push_cast
        linear_combination (-(Complex.sin (m * t) * β m)) * Complex.I_sq
    simp only [hterm] at h1
    have h2 := ((Complex.hasSum_ofReal.2 (htrig_sum t).hasSum)).add (hasSum_ite_eq 0 (α 0 : ℂ))
    have h3 := h1.unique h2
    rw [hfG]
    have hf0 : f 0 = α 0 := by simp [hf, hd_zero]
    rw [hf0] at h3
    simpa using h3
  -- identity theorem on ℝ, then uniqueness of Fourier coefficients
  have hzero : EqOn (fun t : ℝ => G (Complex.exp (t * Complex.I))) 0 univ := by
    refine eqOn_zero_of_accPt hHan isPreconnected_univ (mem_univ t₀) hacc fun t ht => ?_
    show G (Complex.exp (t * Complex.I)) = 0
    rw [hGt t, hS t ht, Complex.ofReal_zero]
  have hdz : ∀ k, d k = 0 := by
    refine fourierSeries_coeff_eq_zero hd1 fun t => ?_
    have := hzero (mem_univ t)
    simp only [Pi.zero_apply] at this
    rw [← this]
    show _ = ∑' k : ℤ, (Complex.exp (t * Complex.I)) ^ k • d k
    congr 1
    funext k
    rw [← Complex.exp_int_mul]
    congr 2
    ring
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have := hdz 0
      rw [hd_zero] at this
      exact_mod_cast this
    · have := hdz n
      rw [hd_pos n hn] at this
      have := congrArg Complex.re this
      simpa using this
  · have := hdz n
    rw [hd_pos n (Nat.pos_of_ne_zero hn)] at this
    have := congrArg Complex.im this
    simpa using this

/-- **Uniqueness for trigonometric series with geometric decay** (`app:window-strictly-stronger`).
If `∑ ‖aₙ‖ ρⁿ` and `∑ ‖bₙ‖ ρⁿ` converge for some `ρ > 1` and
`∑ₙ (cos (n t) aₙ + sin (n t) bₙ) = 0` on a set of reals with an accumulation point, then
`aₙ = 0` for every `n` and `bₙ = 0` for every `n ≠ 0`. -/
theorem trigSeries_coeff_eq_zero [NormedSpace ℝ E] [CompleteSpace E] {a b : ℕ → E} {ρ : ℝ}
    (hρ : 1 < ρ) (ha : Summable fun n => ‖a n‖ * ρ ^ n) (hb : Summable fun n => ‖b n‖ * ρ ^ n)
    {S : Set ℝ} {t₀ : ℝ} (hacc : AccPt t₀ (𝓟 S))
    (hS : ∀ t ∈ S, ∑' n : ℕ, (Real.cos (n * t) • a n + Real.sin (n * t) • b n) = 0) :
    (∀ n, a n = 0) ∧ ∀ n, n ≠ 0 → b n = 0 := by
  have key : ∀ φ : StrongDual ℝ E, (∀ n, φ (a n) = 0) ∧ ∀ n, n ≠ 0 → φ (b n) = 0 := by
    intro φ
    have hbd : ∀ x : E, |φ x| ≤ ‖φ‖ * ‖x‖ := fun x => by
      rw [← Real.norm_eq_abs]
      exact φ.le_opNorm x
    have hα : Summable fun n => |φ (a n)| * ρ ^ n := by
      refine (ha.mul_left ‖φ‖).of_nonneg_of_le (fun n => by positivity) fun n => ?_
      calc |φ (a n)| * ρ ^ n ≤ ‖φ‖ * ‖a n‖ * ρ ^ n :=
            mul_le_mul_of_nonneg_right (hbd _) (by positivity)
        _ = ‖φ‖ * (‖a n‖ * ρ ^ n) := mul_assoc _ _ _
    have hβ : Summable fun n => |φ (b n)| * ρ ^ n := by
      refine (hb.mul_left ‖φ‖).of_nonneg_of_le (fun n => by positivity) fun n => ?_
      calc |φ (b n)| * ρ ^ n ≤ ‖φ‖ * ‖b n‖ * ρ ^ n :=
            mul_le_mul_of_nonneg_right (hbd _) (by positivity)
        _ = ‖φ‖ * (‖b n‖ * ρ ^ n) := mul_assoc _ _ _
    have hsumE : ∀ t : ℝ,
        Summable fun n : ℕ => Real.cos (n * t) • a n + Real.sin (n * t) • b n := by
      intro t
      refine (ha.add hb).of_norm_bounded fun n => ?_
      have hρn : 1 ≤ ρ ^ n := one_le_pow₀ hρ.le
      have hc := Real.abs_cos_le_one (n * t)
      have hs := Real.abs_sin_le_one (n * t)
      calc ‖Real.cos (n * t) • a n + Real.sin (n * t) • b n‖
          ≤ ‖Real.cos (n * t) • a n‖ + ‖Real.sin (n * t) • b n‖ := norm_add_le _ _
        _ ≤ ‖a n‖ + ‖b n‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hc)
              (mul_le_of_le_one_left (norm_nonneg _) hs)
        _ ≤ ‖a n‖ * ρ ^ n + ‖b n‖ * ρ ^ n := by
            nlinarith [norm_nonneg (a n), norm_nonneg (b n)]
    have hS' : ∀ t ∈ S,
        ∑' n : ℕ, (Real.cos (n * t) * φ (a n) + Real.sin (n * t) * φ (b n)) = 0 := by
      intro t ht
      have := congrArg φ (hS t ht)
      rw [φ.map_tsum (hsumE t), map_zero] at this
      simpa [map_add, map_smul, smul_eq_mul] using this
    exact trigSeries_coeff_eq_zero_real hρ hα hβ hacc hS'
  exact ⟨fun n => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => (key φ).1 n,
    fun n hn => SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => (key φ).2 n hn⟩

/-! ### Exponential sums -/

/-- The character `x ↦ e^{μ x}` of the additive group of `ℂ`. -/
private def cexpHom (μ : ℂ) : Multiplicative ℂ →* ℂ where
  toFun x := Complex.exp (μ * x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, Complex.exp_add]

private theorem cexpHom_injective : Function.Injective cexpHom := by
  intro μ ν h
  by_contra hne
  have hsub : μ - ν ≠ 0 := sub_ne_zero.2 hne
  have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (1 / (μ - ν)))
  simp only [cexpHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h1
  have h2 : Complex.exp ((μ - ν) * (1 / (μ - ν))) = 1 := by
    rw [sub_mul, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  rw [mul_one_div_cancel hsub, Complex.exp_eq_one_iff] at h2
  obtain ⟨n, hn⟩ := h2
  have := congrArg Complex.re hn
  simp at this

/-- **Finite exponential sums, complex exponents.**  If `∑ᵢ e^{μᵢ z} cᵢ = 0` on a set with an
accumulation point and the `μᵢ` are distinct, every `cᵢ` vanishes. -/
theorem coeff_eq_zero_of_sum_cexp_eq_zero [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    {μ : ι → ℂ} (hμ : Function.Injective μ) {c : ι → E} {S : Set ℂ} {z₀ : ℂ}
    (hacc : AccPt z₀ (𝓟 S)) (hS : ∀ z ∈ S, ∑ i, Complex.exp (μ i * z) • c i = 0) (i : ι) :
    c i = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ => ?_
  set g : ℂ → ℂ := fun z => ∑ j, φ (c j) * Complex.exp (μ j * z) with hg
  have hgd : Differentiable ℂ g := by
    rw [hg]
    fun_prop
  have hzero : EqOn g 0 univ := by
    refine eqOn_zero_of_accPt (hgd.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ
      (mem_univ z₀) hacc fun z hz => ?_
    have := congrArg φ (hS z hz)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [hg]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hli := (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).comp (fun j => cexpHom (μ j))
    (cexpHom_injective.comp hμ)
  refine Fintype.linearIndependent_iff.1 hli (fun j => φ (c j)) ?_ i
  funext x
  have := hzero (mem_univ x.toAdd)
  simp only [hg, Pi.zero_apply] at this
  simpa [cexpHom, Finset.sum_apply] using this

/-- **Finite exponential sums, real exponents** (linear independence of the `e^{μᵢ t}`; used in
`app:window-strictly-stronger`).  If `∑ᵢ e^{μᵢ t} cᵢ = 0` on a set of reals with an
accumulation point and the `μᵢ` are distinct, every `cᵢ` vanishes. -/
theorem coeff_eq_zero_of_sum_rexp_eq_zero [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    {μ : ι → ℝ} (hμ : Function.Injective μ) {c : ι → E} {S : Set ℝ} {t₀ : ℝ}
    (hacc : AccPt t₀ (𝓟 S)) (hS : ∀ t ∈ S, ∑ i, Real.exp (μ i * t) • c i = 0) (i : ι) :
    c i = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
  have h := coeff_eq_zero_of_sum_cexp_eq_zero (E := ℂ) (μ := fun j => (μ j : ℂ))
    (fun j k hjk => hμ (Complex.ofReal_injective hjk)) (c := fun j => (φ (c j) : ℂ))
    (accPt_ofReal_image hacc) ?_ i
  · exact_mod_cast h
  · rintro _ ⟨t, ht, rfl⟩
    have := congrArg φ (hS t ht)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    have := congrArg (fun x : ℝ => (x : ℂ)) this
    push_cast at this
    simpa [smul_eq_mul] using this

/-- A Dirichlet series `∑ᵢ e^{μᵢ z} dᵢ` converging absolutely for real `z > t₀` is holomorphic on
the half-plane `re z > t₀`. -/
private theorem differentiableOn_dirichlet {ι : Type*} {μ : ι → ℝ} {d : ι → ℂ} {t₀ : ℝ}
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

/-- **Uniqueness for Dirichlet series.**  Let the real exponents `μᵢ` be distinct with only
finitely many above each level, and let `∑ᵢ ‖cᵢ‖ e^{μᵢ t} < ∞` for every `t > t₀`.  If
`∑ᵢ e^{μᵢ t} cᵢ = 0` on a set accumulating at some `s₀ > t₀`, every `cᵢ` vanishes. -/
theorem coeff_eq_zero_of_tsum_rexp_eq_zero [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*}
    {μ : ι → ℝ} (hμ : Function.Injective μ) (hfin : ∀ M : ℝ, {i | M ≤ μ i}.Finite)
    {c : ι → E} {t₀ : ℝ} (hsum : ∀ t, t₀ < t → Summable fun i => ‖c i‖ * Real.exp (μ i * t))
    {S : Set ℝ} {s₀ : ℝ} (hs₀ : t₀ < s₀) (hacc : AccPt s₀ (𝓟 S))
    (hS : ∀ t ∈ S, t₀ < t → ∑' i, Real.exp (μ i * t) • c i = 0) (i : ι) : c i = 0 := by
  classical
  have hsE : ∀ t, t₀ < t → Summable fun j => Real.exp (μ j * t) • c j := by
    intro t ht
    refine (hsum t ht).of_norm_bounded fun j => le_of_eq ?_
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  -- Step 1: the series vanishes on `(t₀, ∞)`
  have hF : ∀ t, t₀ < t → ∑' j, Real.exp (μ j * t) • c j = 0 := by
    intro t ht
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun φ => ?_
    have hsumφ : ∀ t, t₀ < t →
        Summable fun j => ‖((φ (c j) : ℝ) : ℂ)‖ * Real.exp (μ j * t) := by
      intro t ht
      refine ((hsum t ht).mul_left ‖φ‖).of_nonneg_of_le (fun j => by positivity) fun j => ?_
      rw [Complex.norm_real, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (φ.le_opNorm _) (Real.exp_pos _).le
    set g := fun z : ℂ => ∑' j, Complex.exp (μ j * z) * (φ (c j) : ℂ) with hg
    have hgd := differentiableOn_dirichlet hsumφ
    have hP : IsOpen {z : ℂ | t₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hPc : IsPreconnected {z : ℂ | t₀ < z.re} := (convex_halfSpace_re_gt t₀).isPreconnected
    have hgreal : ∀ t, t₀ < t → g t = (φ (∑' j, Real.exp (μ j * t) • c j) : ℂ) := by
      intro t ht
      rw [φ.map_tsum (hsE t ht), Complex.ofReal_tsum]
      simp only [hg]
      congr 1
      funext j
      simp [smul_eq_mul, Complex.ofReal_exp]
    have hzero : EqOn g 0 {z : ℂ | t₀ < z.re} := by
      refine eqOn_zero_of_accPt_real (hgd.analyticOnNhd hP) hPc (t₀ := s₀) (by simpa using hs₀)
        (hacc.nhds_inter (Ioi_mem_nhds hs₀)) ?_
      rintro t ⟨htI, htS⟩
      rw [hgreal t htI, hS t htS htI, map_zero, Complex.ofReal_zero]
    have := hzero (show (t : ℂ) ∈ {z : ℂ | t₀ < z.re} by simpa using ht)
    rw [Pi.zero_apply, hgreal t ht] at this
    exact_mod_cast this
  -- Step 2: the leading coefficient vanishes
  by_contra hci
  obtain ⟨j, hjT, hjmax⟩ := ((hfin (μ i)).toFinset.filter fun j => c j ≠ 0).exists_max_image μ
    ⟨i, by simp [hci]⟩
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hjT hjmax
  have hmax : ∀ k, c k ≠ 0 → μ k ≤ μ j := by
    intro k hk
    by_cases hik : μ i ≤ μ k
    · exact hjmax k ⟨hik, hk⟩
    · exact (not_le.1 hik).le.trans hjT.1
  have hlt : ∀ k, k ≠ j → c k ≠ 0 → μ k < μ j := fun k hkj hk =>
    lt_of_le_of_ne (hmax k hk) fun h => hkj (hμ h)
  set L := μ j with hL
  have hG0 : ∀ t, t₀ < t → ∑' k, Real.exp ((μ k - L) * t) • c k = 0 := by
    intro t ht
    have h1 := ((hsE t ht).hasSum.const_smul (Real.exp (-(L * t)))).tsum_eq
    rw [hF t ht, smul_zero] at h1
    rw [← h1]
    congr 1
    funext k
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  have hlim : Tendsto (fun t => ∑' k, Real.exp ((μ k - L) * t) • c k) atTop
      (𝓝 (∑' k, if k = j then c j else 0)) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun t k => Real.exp ((μ k - L) * t) • c k) (g := fun k => if k = j then c j else 0)
      (bound := fun k => ‖c k‖ * Real.exp ((μ k - L) * (t₀ + 1))) ?_ (fun k => ?_) ?_
    · refine ((hsum (t₀ + 1) (by linarith)).mul_left (Real.exp (-(L * (t₀ + 1))))).congr
        fun k => ?_
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    · by_cases hkj : k = j
      · have hconst : ∀ t : ℝ, Real.exp ((μ k - L) * t) • c k = c j := by
          intro t
          rw [hkj, ← hL, sub_self, zero_mul, Real.exp_zero, one_smul]
        simp only [hconst]
        rw [ite_eq_left hkj]
        exact tendsto_const_nhds
      · simp only [hkj, ite_false]
        by_cases hck : c k = 0
        · simp only [hck, smul_zero]
          exact tendsto_const_nhds
        · have hneg : μ k - L < 0 := sub_neg.2 (hlt k hkj hck)
          have : Tendsto (fun t => Real.exp ((μ k - L) * t)) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
          simpa using this.smul_const (c k)
    · filter_upwards [eventually_ge_atTop (t₀ + 1)] with t ht k
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      by_cases hck : c k = 0
      · simp [hck]
      · have hle : μ k - L ≤ 0 := sub_nonpos.2 (hmax k hck)
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left ht hle)) (norm_nonneg _)
  rw [tsum_ite_eq] at hlim
  have hG : Tendsto (fun t => ∑' k, Real.exp ((μ k - L) * t) • c k) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((eventually_gt_atTop t₀).mono fun t ht => (hG0 t ht).symm)
  exact hjT.2 (tendsto_nhds_unique hlim hG)

/-- **Uniqueness for Dirichlet series**, a.e. version: vanishing a.e. on an interval
`(a, b) ⊆ (t₀, ∞)` suffices. -/
theorem coeff_eq_zero_of_tsum_rexp_ae_eq_zero [NormedSpace ℝ E] [CompleteSpace E] {ι : Type*}
    {μ : ι → ℝ} (hμ : Function.Injective μ) (hfin : ∀ M : ℝ, {i | M ≤ μ i}.Finite)
    {c : ι → E} {t₀ : ℝ} (hsum : ∀ t, t₀ < t → Summable fun i => ‖c i‖ * Real.exp (μ i * t))
    {a b : ℝ} (ha : t₀ ≤ a) (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∑' i, Real.exp (μ i * t) • c i = 0) (i : ι) :
    c i = 0 := by
  have hs : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact coeff_eq_zero_of_tsum_rexp_eq_zero hμ hfin hsum (by linarith [hs.1] : t₀ < (a + b) / 2)
    (accPt_Ioo_inter_of_ae h hs) (fun t ht _ => ht.2) i

/-! ### Exponential series with bounded exponents; harmonic signals -/

section Bounded

variable [NormedSpace ℂ E] [CompleteSpace E] {ι : Type*}

/-- An exponential series `z ↦ ∑ᵢ e^{μᵢ z} dᵢ` with bounded exponents and absolutely summable
coefficients is entire (`app:harmonic-pe`). -/
theorem differentiable_tsum_cexp_smul {μ : ι → ℂ} {M : ℝ} (hμ : ∀ i, ‖μ i‖ ≤ M) {d : ι → E}
    (hd : Summable fun i => ‖d i‖) :
    Differentiable ℂ fun z : ℂ => ∑' i, Complex.exp (μ i * z) • d i := by
  have hR : ∀ R : ℝ, DifferentiableOn ℂ (fun z : ℂ => ∑' i, Complex.exp (μ i * z) • d i)
      (Metric.ball 0 R) := by
    intro R
    refine Complex.differentiableOn_tsum_of_summable_norm (hd.mul_right (Real.exp (max M 0 * R)))
      (fun i => Differentiable.differentiableOn (by fun_prop)) Metric.isOpen_ball
      (fun i w hw => ?_)
    rw [norm_smul, Complex.norm_exp, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    calc (μ i * w).re ≤ ‖μ i * w‖ := Complex.re_le_norm _
      _ = ‖μ i‖ * ‖w‖ := norm_mul _ _
      _ ≤ max M 0 * R := mul_le_mul (le_max_of_le_left (hμ i)) (mem_ball_zero_iff.1 hw).le
          (norm_nonneg _) (le_max_right _ _)
  intro z
  exact (hR (‖z‖ + 1)).differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))

/-- An exponential series with bounded exponents and absolutely summable coefficients is real
analytic on `ℝ`. -/
theorem analyticOnNhd_tsum_cexp_smul_ofReal {μ : ι → ℂ} {M : ℝ} (hμ : ∀ i, ‖μ i‖ ≤ M)
    {d : ι → E} (hd : Summable fun i => ‖d i‖) :
    AnalyticOnNhd ℝ (fun t : ℝ => ∑' i, Complex.exp (μ i * t) • d i) univ := by
  have := analyticOnNhd_comp_ofReal (differentiable_tsum_cexp_smul hμ hd).differentiableOn
    isOpen_univ
  simpa using this

/-- An exponential series with bounded exponents and absolutely summable coefficients that
vanishes a.e. on a real interval `(a, b)`, `a < b`, vanishes on `ℂ` (`app:harmonic-pe`:
identities on the window propagate to the whole line). -/
theorem tsum_cexp_smul_eq_zero_of_ae {μ : ι → ℂ} {M : ℝ} (hμ : ∀ i, ‖μ i‖ ≤ M) {d : ι → E}
    (hd : Summable fun i => ‖d i‖) {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t : ℝ ∂(volume.restrict (Ioo a b)), ∑' i, Complex.exp (μ i * t) • d i = 0) (z : ℂ) :
    ∑' i, Complex.exp (μ i * z) • d i = 0 := by
  have hA := (differentiable_tsum_cexp_smul hμ hd).differentiableOn.analyticOnNhd isOpen_univ
  exact eqOn_zero_of_ae_Ioo_real hA isPreconnected_univ hab (fun _ _ => mem_univ _) h
    (mem_univ z)

private theorem norm_ofReal_mul_I_le {ω : ι → ℝ} {Ω : ℝ} (hω : ∀ l, |ω l| ≤ Ω) (l : ι) :
    ‖(ω l : ℂ) * Complex.I‖ ≤ Ω := by
  simpa [Complex.norm_real] using hω l

private theorem harmonic_mul_comm (ω : ℝ) (t : ℝ) :
    (ω : ℂ) * t * Complex.I = (ω * Complex.I) * t := mul_right_comm _ _ _

/-- A harmonic signal `t ↦ ∑ₗ e^{i ωₗ t} vₗ` with bounded frequencies and absolutely summable
coefficients is real analytic (`def:harmonic-signal`, `app:harmonic-pe`; used in
`lem:bohr-annihilator`). -/
theorem analyticOnNhd_harmonic {ω : ι → ℝ} {Ω : ℝ} (hω : ∀ l, |ω l| ≤ Ω) {v : ι → E}
    (hv : Summable fun l => ‖v l‖) :
    AnalyticOnNhd ℝ (fun t : ℝ => ∑' l, Complex.exp (ω l * t * Complex.I) • v l) univ := by
  simp only [harmonic_mul_comm]
  exact analyticOnNhd_tsum_cexp_smul_ofReal (norm_ofReal_mul_I_le hω) hv

/-- A harmonic signal `t ↦ ∑ₗ e^{i ωₗ t} vₗ` with bounded frequencies and absolutely summable
coefficients that vanishes a.e. on an interval `(a, b)`, `a < b`, vanishes on `ℝ`
(`app:harmonic-pe`, `lem:harmonic-pe-implies-pe`). -/
theorem harmonic_eq_zero_of_ae {ω : ι → ℝ} {Ω : ℝ} (hω : ∀ l, |ω l| ≤ Ω) {v : ι → E}
    (hv : Summable fun l => ‖v l‖) {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t : ℝ ∂(volume.restrict (Ioo a b)),
      ∑' l, Complex.exp (ω l * t * Complex.I) • v l = 0)
    (t : ℝ) : ∑' l, Complex.exp (ω l * t * Complex.I) • v l = 0 := by
  simp only [harmonic_mul_comm] at h ⊢
  exact tsum_cexp_smul_eq_zero_of_ae (norm_ofReal_mul_I_le hω) hv hab h t

end Bounded

end DataDrivenControl
