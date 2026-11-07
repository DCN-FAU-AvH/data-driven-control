module

public import DataDrivenControl.Signal.TestFunction

/-!
# Weak derivatives and constant-coefficient ODEs

Paper: `x ∈ H¹(I; V₋₁)` and `-∫ φ̇ x = ∫ φ ẋ` (`app:willems-gramian`, `eq:record-dynamics`),
the `H¹` scalar function `t ↦ ⟪η, x̄ t⟫` (`app:data-fattorini-hautus`, `eq:weak-mild-diff`),
the weak ODE arguments of `app:pe-necessity` (Step 4) and `app:window-pe-necessity`.

## Conventions

* `HasWeakDeriv T x g` is `x ∈ H¹(I; E)` with weak derivative `g`, in integral form:
  `g ∈ L²(0, T; E)` and `x t = x 0 + ∫₀ᵗ g` for every `t ∈ [0, T]`.  It
  pins down the continuous representative of `x` on `[0, T]`.
* Weak forms use the test functions of `Signal.TestFunction`.

## Main statements

* `HasWeakDeriv.integral_deriv_smul`: `∫ φ' • x = -∫ φ • g` for test functions `φ`, and its
  converse `hasWeakDeriv_iff` (for `x` continuous on `[0, T]`); `HasWeakDeriv.derivMoment_succ`;
* `HasWeakDeriv.ae_eq`: uniqueness of the weak derivative;
* `HasWeakDeriv.smul`: product rule with a `C¹` scalar function;
* `exists_ae_eq_const_of_integral_deriv_smul_eq_zero`: du Bois-Reymond;
* variation of constants for `ẋ = a x + f`, real (`HasWeakDeriv.eq_exp_smul_add_integral`) and
  complex (`HasWeakDeriv.eq_cexp_smul_add_integral`), and the converse;
* `ae_eq_sum_exp_of_polyDerivMoment_eq_zero`: a weak solution of `p(D) w = 0`, `p` with distinct
  real roots `ρₙ`, is `∑ κₙ e^{ρₙ t}`;
* `eq_zero_of_sum_iteratedDeriv_smul_eq_zero`: a compactly supported smooth solution of a
  nontrivial constant-coefficient ODE vanishes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Polynomial
open scoped ContDiff InnerProductSpace ENNReal

noncomputable section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace DataDrivenControl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `x ∈ H¹(I; E)` with weak derivative `g`, in integral form: `g ∈ L²(0, T; E)`
and `x t = x 0 + ∫₀ᵗ g` for `t ∈ [0, T]` (the paper's `x ∈ H¹(I; V₋₁)`, `ẋ = g`). -/
structure HasWeakDeriv (T : ℝ) (x g : ℝ → E) : Prop where
  /-- The weak derivative is square integrable on the window. -/
  memLp_deriv : MemLp g 2 (μI T)
  /-- Integral form: `x t = x 0 + ∫₀ᵗ g` on `[0, T]`. -/
  eq_add_integral : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in 0..t, g s

section CompleteSpace

variable [CompleteSpace E] [CompleteSpace F] {T : ℝ} {x y g g' : ℝ → E} {φ : ℝ → ℝ}

/-! ### Auxiliary lemmas -/

/-- Continuous functions on `[0, T]` are in every `Lᵖ` of the window. -/
private theorem memLp_of_continuousOn {G : Type*} [NormedAddCommGroup G] {f : ℝ → G}
    {p : ℝ≥0∞} (hf : ContinuousOn f (Icc 0 T)) : MemLp f p (μI T) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hC t (Ioc_subset_Icc_self ht))

/-- A function continuous on `[0, T]` times an `L²` signal is an `L²` signal. -/
private theorem memLp_smul_of_continuousOn {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    {c : ℝ → 𝕜} (hc : ContinuousOn c (Icc 0 T)) {f : ℝ → E} (hf : MemLp f 2 (μI T)) :
    MemLp (fun t => c t • f t) 2 (μI T) :=
  (memLp_of_continuousOn (p := ∞) hc).smul hf

private theorem intervalIntegrable_of_integrable {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : ℝ → G} (hf : Integrable f (μI T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable f volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
    (IntegrableOn.mono_set (hf : IntegrableOn f (Ioc 0 T) volume) (Ioc_subset_Ioc_right ht.2))

private theorem continuousOn_primitive {f : ℝ → E} (hf : Integrable f (μI T)) :
    ContinuousOn (fun t => ∫ s in 0..t, f s) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (not_le.2 hT)]
    exact continuousOn_empty _
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (f := f) (by rw [uIcc_of_le hT, integrableOn_Icc_iff_integrableOn_Ioc]; exact hf)
  rwa [uIcc_of_le hT] at this

/-- Fubini on the triangle `0 < r ≤ s < t`, followed by the fundamental theorem of calculus:
`∫₀ᵗ a' s • (∫₀ˢ g) ds = ∫₀ᵗ (a t - a r) • g r dr`. -/
private theorem integral_smul_primitive {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]
    [IsScalarTower ℝ 𝕜 E] {a a' : ℝ → 𝕜} (ha : ∀ t, HasDerivAt a (a' t) t)
    (ha' : Continuous a') {g : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hg : IntegrableOn g (Ioc 0 t)) :
    ∫ s in 0..t, a' s • ∫ r in 0..s, g r = ∫ r in 0..t, (a t - a r) • g r := by
  set μ := volume.restrict (Ioc (0 : ℝ) t) with hμ
  let F : ℝ → ℝ → E := fun s r => (Iic s).indicator (fun r => a' s • g r) r
  have hFdef : ∀ s r, F s r = (Iic s).indicator (fun r => a' s • g r) r := fun _ _ => rfl
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := by
    have h1 : Integrable (fun z : ℝ × ℝ => a' z.1 • g z.2) (μ.prod μ) :=
      Integrable.smul_prod (ha'.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hg
    have h2 := h1.indicator (measurableSet_le measurable_snd measurable_fst)
    refine h2.congr (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, hFdef, Set.indicator_apply, mem_Iic, mem_ofPred_eq]
  have key := integral_integral_swap hF
  have hL : ∫ s in 0..t, a' s • ∫ r in 0..s, g r = ∫ s, ∫ r, F s r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [hFdef]
    have e : Iic s ∩ Ioc 0 t = Ioc 0 s := by
      ext r
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hs.2⟩
    rw [integral_indicator measurableSet_Iic, hμ, Measure.restrict_restrict measurableSet_Iic, e,
      integral_smul, intervalIntegral.integral_of_le hs.1.le]
  have hR : ∫ r in 0..t, (a t - a r) • g r = ∫ r, ∫ s, F s r ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have e1 : (fun s => F s r) = (Ici r).indicator (fun s => a' s • g r) := by
      ext s
      simp only [hFdef, Set.indicator_apply, mem_Iic, mem_Ici]
    have e2 : Ici r ∩ Ioc 0 t = Icc r t := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hr.1.trans_le h1, h2⟩
    rw [e1, integral_indicator measurableSet_Ici, hμ, Measure.restrict_restrict measurableSet_Ici,
      integral_smul_const, e2, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr.2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => ha s)
        (ha'.intervalIntegrable r t)]
  rw [hL, hR, key]

/-- On an empty window, every test function vanishes. -/
private theorem IsTestFunction.eq_zero_of_nonpos (hφ : IsTestFunction T φ) (hT : T ≤ 0) :
    φ = 0 :=
  funext fun t => hφ.apply_eq_zero fun h => by linarith [h.1, h.2]

/-- `∫ φ' = 0` for a test function `φ`. -/
private theorem IsTestFunction.integral_deriv_eq_zero (hφ : IsTestFunction T φ) :
    ∫ t, deriv φ t = 0 := by
  rcases le_or_gt T 0 with hT | hT
  · simp [hφ.eq_zero_of_nonpos hT]
  have h := (hφ.deriv).integral_smul_eq_setIntegral (fun _ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [h, ← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => (hφ.differentiable t).hasDerivAt)
      (hφ.deriv.continuous.intervalIntegrable 0 T),
    hφ.apply_eq_zero (fun h => lt_irrefl T h.2), hφ.apply_eq_zero (fun h => lt_irrefl 0 h.1),
    sub_self]

/-- Integration by parts for the primitive of an integrable signal:
`∫ φ' • (∫₀ᵗ g) = -∫ φ • g`. -/
private theorem integral_deriv_smul_primitive {g : ℝ → E} (hg : Integrable g (μI T))
    (hφ : IsTestFunction T φ) :
    ∫ t, deriv φ t • ∫ s in 0..t, g s = -∫ t, φ t • g t := by
  rcases le_or_gt T 0 with hT | hT
  · simp [hφ.eq_zero_of_nonpos hT]
  rw [(hφ.deriv).integral_smul_eq_setIntegral, hφ.integral_smul_eq_setIntegral,
    ← intervalIntegral.integral_of_le hT.le, ← intervalIntegral.integral_of_le hT.le,
    integral_smul_primitive (𝕜 := ℝ) (fun t => (hφ.differentiable t).hasDerivAt)
      hφ.deriv.continuous hT.le hg,
    hφ.apply_eq_zero (fun h => lt_irrefl T h.2), ← intervalIntegral.integral_neg]
  simp

/-- The range of `η ↦ η' + ρ η` on test functions: if `∫ e^{ρ t} χ t dt = 0`, then
`χ = η' + ρ η` for a test function `η` (`η t = e^{-ρ t} ∫₀ᵗ e^{ρ s} χ s ds`). -/
theorem IsTestFunction.exists_deriv_add_mul_eq {χ : ℝ → ℝ} (hχ : IsTestFunction T χ) (ρ : ℝ)
    (h : ∫ t, Real.exp (ρ * t) * χ t = 0) :
    ∃ η, IsTestFunction T η ∧ ∀ t, deriv η t + ρ * η t = χ t := by
  rcases (tsupport χ).eq_empty_or_nonempty with he | hne
  · refine ⟨0, IsTestFunction.zero, fun t => ?_⟩
    have : χ = 0 := tsupport_eq_empty_iff.1 he
    simp [this]
  obtain ⟨a, b, ha, hab, hb, hsub⟩ := hχ.exists_Ioo hne
  have hχ0 : ∀ t ∉ Ioo a b, χ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (hsub h)
  set f : ℝ → ℝ := fun t => Real.exp (ρ * t) * χ t with hf
  have hfs : ContDiff ℝ ∞ f := (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
    hχ.contDiff
  have hfc : Continuous f := hfs.continuous
  set P : ℝ → ℝ := fun t => ∫ s in 0..t, f s with hP
  have hPd : ∀ t, HasDerivAt P (f t) t := fun t => (hfc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hPs : ContDiff ℝ ∞ P := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hPd t).differentiableAt, ?_⟩
    have : deriv P = f := funext fun t => (hPd t).deriv
    rw [this]; exact hfs
  have hP0 : ∀ t ∉ Ioo a b, P t = 0 := by
    intro t ht
    rcases le_or_gt t a with hta | hta
    · simp only [hP]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
      · simp
      · simp only [hf]
        rw [hχ0 s fun h' => ?_, mul_zero]
        have : s ≤ a := hs.2.trans (sup_le ha.le hta)
        linarith [h'.1]
    · have htb : b ≤ t := by
        by_contra hcon
        exact ht ⟨hta, not_le.1 hcon⟩
      have e1 : ∫ s in 0..t, f s = ∫ s, f s := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
        simp only [hf]
        rw [hχ0 s fun h' => hs ⟨by linarith [h'.1], by linarith [h'.2]⟩, mul_zero]
      simp only [hP]
      rw [e1]
      exact h
  refine ⟨fun t => Real.exp (-ρ * t) * P t, ⟨?_, ?_⟩, fun t => ?_⟩
  · exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hPs
  · refine (closure_mono (s := Function.support fun t => Real.exp (-ρ * t) * P t)
      (t := Ioo a b) ?_).trans ?_
    · intro t ht
      by_contra hcon
      exact ht (by simp [hP0 t hcon])
    · rw [closure_Ioo hab.ne]
      exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · have hd : HasDerivAt (fun t => Real.exp (-ρ * t) * P t)
        (Real.exp (-ρ * t) * (-ρ) * P t + Real.exp (-ρ * t) * f t) t := by
      have h1 : HasDerivAt (fun t => Real.exp (-ρ * t)) (Real.exp (-ρ * t) * (-ρ)) t := by
        have := ((hasDerivAt_id t).const_mul (-ρ)).exp
        simpa using this
      exact h1.mul (hPd t)
    rw [hd.deriv]
    simp only [hf]
    rw [← mul_assoc, ← Real.exp_add]
    have : -ρ * t + ρ * t = 0 := by ring
    rw [this, Real.exp_zero]
    ring

namespace HasWeakDeriv

theorem integrable_deriv (h : HasWeakDeriv T x g) : Integrable g (μI T) :=
  h.memLp_deriv.integrable one_le_two

theorem continuousOn (h : HasWeakDeriv T x g) : ContinuousOn x (Icc 0 T) :=
  (continuousOn_const.add (continuousOn_primitive h.integrable_deriv)).congr
    fun t ht => h.eq_add_integral t ht

/-- An `H¹` function is square integrable on the window. -/
theorem memLp (h : HasWeakDeriv T x g) : MemLp x 2 (μI T) :=
  memLp_of_continuousOn h.continuousOn

theorem integrable (h : HasWeakDeriv T x g) : Integrable x (μI T) :=
  h.memLp.integrable one_le_two

theorem intervalIntegrable_deriv (h : HasWeakDeriv T x g) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable g volume 0 t :=
  intervalIntegrable_of_integrable h.integrable_deriv ht

/-- `C¹` functions on `[0, T]` are `H¹`, with their classical derivative. -/
theorem of_hasDerivWithinAt {x' : ℝ → E}
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (x' t) (Icc 0 T) t)
    (hx' : ContinuousOn x' (Icc 0 T)) : HasWeakDeriv T x x' := by
  have hcont : ContinuousOn x (Icc 0 T) := fun t ht => (hx t ht).continuousWithinAt
  refine ⟨memLp_of_continuousOn hx', fun t ht => ?_⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hcont.mono hsub)
    (fun s hs => ((hx s (Ioo_subset_Icc_self.trans hsub hs)).hasDerivAt
      (Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2, ht.2]))).hasDerivWithinAt)
    ((hx'.mono hsub).intervalIntegrable_of_Icc ht.1)]
  abel

theorem of_hasDerivAt {x' : ℝ → E} (hx : ∀ t, HasDerivAt x (x' t) t) (hx' : Continuous x') :
    HasWeakDeriv T x x' :=
  of_hasDerivWithinAt (fun t _ => (hx t).hasDerivWithinAt) hx'.continuousOn

theorem const (c : E) : HasWeakDeriv T (fun _ => c) 0 :=
  ⟨MemLp.zero, fun t _ => by simp⟩

theorem add (hx : HasWeakDeriv T x g) (hy : HasWeakDeriv T y g') :
    HasWeakDeriv T (fun t => x t + y t) (fun t => g t + g' t) :=
  ⟨hx.memLp_deriv.add hy.memLp_deriv, fun t ht => by
    rw [hx.eq_add_integral t ht, hy.eq_add_integral t ht,
      intervalIntegral.integral_add (hx.intervalIntegrable_deriv ht)
        (hy.intervalIntegrable_deriv ht)]
    abel⟩

theorem neg (hx : HasWeakDeriv T x g) : HasWeakDeriv T (fun t => -x t) (fun t => -g t) :=
  ⟨hx.memLp_deriv.neg, fun t ht => by
    rw [hx.eq_add_integral t ht, intervalIntegral.integral_neg]
    abel⟩

theorem sub (hx : HasWeakDeriv T x g) (hy : HasWeakDeriv T y g') :
    HasWeakDeriv T (fun t => x t - y t) (fun t => g t - g' t) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem const_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    (hx : HasWeakDeriv T x g) (c : 𝕜) :
    HasWeakDeriv T (fun t => c • x t) (fun t => c • g t) :=
  ⟨hx.memLp_deriv.const_smul c, fun t ht => by
    rw [hx.eq_add_integral t ht, intervalIntegral.integral_smul, smul_add]⟩

/-- Bounded operators preserve `H¹` and commute with the weak derivative. -/
theorem map (hx : HasWeakDeriv T x g) (L : E →L[ℝ] F) :
    HasWeakDeriv T (fun t => L (x t)) (fun t => L (g t)) :=
  ⟨L.comp_memLp' hx.memLp_deriv, fun t ht => by
    rw [hx.eq_add_integral t ht, L.intervalIntegral_comp_comm (hx.intervalIntegrable_deriv ht),
      map_add]⟩

/-- The scalar function `t ↦ ⟪η, x t⟫` of an `H¹` function is `H¹`
(`app:data-fattorini-hautus`). -/
theorem inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {x g : ℝ → H} (hx : HasWeakDeriv T x g) (η : H) :
    HasWeakDeriv T (fun t => ⟪η, x t⟫_ℝ) (fun t => ⟪η, g t⟫_ℝ) := by
  simpa only [innerSL_apply_apply] using hx.map (innerSL ℝ η)

/-- Product rule with a `C¹` scalar function `a`: `(a • x)' = a' • x + a • x'`. -/
theorem smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    (hx : HasWeakDeriv T x g) {a a' : ℝ → 𝕜} (ha : ∀ t, HasDerivAt a (a' t) t)
    (ha' : Continuous a') :
    HasWeakDeriv T (fun t => a t • x t) (fun t => a' t • x t + a t • g t) := by
  have hxc := hx.continuousOn
  have hacont : Continuous a := continuous_iff_continuousAt.2 fun t => (ha t).continuousAt
  refine ⟨(memLp_smul_of_continuousOn ha'.continuousOn hx.memLp).add
    (memLp_smul_of_continuousOn hacont.continuousOn hx.memLp_deriv), fun t ht => ?_⟩
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hgt : IntegrableOn g (Ioc 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1 (hx.intervalIntegrable_deriv ht)
  have i1 : IntervalIntegrable (fun s => a' s • x s) volume 0 t :=
    (ha'.continuousOn.smul (hxc.mono hsub)).intervalIntegrable_of_Icc ht.1
  have i2 : IntervalIntegrable (fun s => a s • g s) volume 0 t :=
    (hx.intervalIntegrable_deriv ht).continuousOn_smul hacont.continuousOn
  have i2' : IntervalIntegrable (fun s => a t • g s) volume 0 t :=
    (hx.intervalIntegrable_deriv ht).continuousOn_smul continuousOn_const
  have i3 : IntervalIntegrable (fun s => a' s • x 0) volume 0 t :=
    (ha'.smul continuous_const).intervalIntegrable 0 t
  have i4 : IntervalIntegrable (fun s => a' s • ∫ r in 0..s, g r) volume 0 t :=
    (ha'.continuousOn.smul ((continuousOn_primitive hx.integrable_deriv).mono hsub)).intervalIntegrable_of_Icc
      ht.1
  have e1 : ∫ s in 0..t, a' s • x s = ∫ s in 0..t, (a' s • x 0 + a' s • ∫ r in 0..s, g r) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hx.eq_add_integral s (hsub hs), smul_add]
  have e2 : ∫ r in 0..t, (a t - a r) • g r =
      (a t • ∫ r in 0..t, g r) - ∫ r in 0..t, a r • g r := by
    simp only [sub_smul]
    rw [intervalIntegral.integral_sub i2' i2, intervalIntegral.integral_smul]
  rw [intervalIntegral.integral_add i1 i2, e1, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_smul_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => ha s) (ha'.intervalIntegrable 0 t),
    integral_smul_primitive ha ha' ht.1 hgt, e2, hx.eq_add_integral t ht]
  simp only [smul_add, sub_smul]
  abel

theorem congr (hx : HasWeakDeriv T x g) (hxy : EqOn x y (Icc 0 T)) (hg : g =ᵐ[μI T] g') :
    HasWeakDeriv T y g' := by
  refine ⟨hx.memLp_deriv.ae_eq hg, fun t ht => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  rw [← hxy ht, ← hxy h0, hx.eq_add_integral t ht]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hg' : ∀ᵐ s, s ∈ Ioc 0 T → g s = g' s := (ae_restrict_iff' measurableSet_Ioc).1 hg
  filter_upwards [hg'] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  exact hs (Ioc_subset_Ioc_right ht.2 hsI)

/-- Restriction of an `H¹` function to a shorter window. -/
theorem mono (hx : HasWeakDeriv T x g) {T' : ℝ} (hT : T' ≤ T) : HasWeakDeriv T' x g :=
  ⟨hx.memLp_deriv.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hT) le_rfl),
    fun t ht => hx.eq_add_integral t ⟨ht.1, ht.2.trans hT⟩⟩

/-- Weak form: `-∫ φ' • x = ∫ φ • g` for every test function `φ` (`app:willems-gramian`). -/
theorem integral_deriv_smul (hx : HasWeakDeriv T x g) (hφ : IsTestFunction T φ) :
    ∫ t, deriv φ t • x t = -∫ t, φ t • g t := by
  have hG : Integrable (fun t => ∫ s in 0..t, g s) (μI T) :=
    (memLp_of_continuousOn (p := 1) (continuousOn_primitive hx.integrable_deriv)).integrable le_rfl
  have e : (fun t => deriv φ t • x t) = fun t => deriv φ t • x 0 + deriv φ t • ∫ s in 0..t, g s := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · rw [hx.eq_add_integral t (Ioo_subset_Icc_self ht), smul_add]
    · rw [(hφ.deriv).apply_eq_zero ht]
      simp
  rw [e, integral_add (hφ.deriv.integrable.smul_const _) ((hφ.deriv).integrable_smul hG),
    integral_smul_const, hφ.integral_deriv_eq_zero, zero_smul, zero_add,
    integral_deriv_smul_primitive hx.integrable_deriv hφ]

/-- `⟨Dᵏ⁺¹ x, φ⟩ = ⟨Dᵏ x', φ⟩` for `x ∈ H¹` with weak derivative `x'`. -/
theorem derivMoment_succ (hx : HasWeakDeriv T x g) (hφ : IsTestFunction T φ) (k : ℕ) :
    derivMoment (k + 1) x φ = derivMoment k g φ := by
  have := hx.integral_deriv_smul (hφ.iteratedDeriv k)
  simp only [derivMoment, iteratedDeriv_succ, this, pow_succ, mul_neg_one, neg_smul, smul_neg,
    neg_neg]

/-- Uniqueness of the weak derivative. -/
theorem ae_eq (hx : HasWeakDeriv T x g) (hx' : HasWeakDeriv T x g') : g =ᵐ[μI T] g' :=
  ae_eq_of_integral_smul_eq hx.integrable_deriv hx'.integrable_deriv fun φ hφ => by
    have h1 := hx.integral_deriv_smul hφ
    rw [hx'.integral_deriv_smul hφ] at h1
    exact (neg_injective h1).symm

/-- If `ẋ = a x + f` weakly, then `⟨((X - a) q)(D) x, φ⟩ = ⟨q(D) f, φ⟩`. -/
theorem polyDerivMoment_X_sub_C_mul {a : ℝ} {f : ℝ → E}
    (hx : HasWeakDeriv T x (fun t => a • x t + f t)) (hφ : IsTestFunction T φ) (q : ℝ[X]) :
    polyDerivMoment ((X - C a) * q) x φ = polyDerivMoment q f φ := by
  have hf : Integrable f (μI T) := by
    have := hx.integrable_deriv.sub (hx.integrable.smul a)
    refine this.congr (ae_of_all _ fun t => ?_)
    simp
  have hk : ∀ k, derivMoment k f φ = -derivMoment k x (deriv φ) - a • derivMoment k x φ := by
    intro k
    have h1 := hx.derivMoment_succ hφ k
    rw [derivMoment_add (u := fun t => a • x t) hφ (hx.integrable.smul a) hf, derivMoment_smul,
      DataDrivenControl.derivMoment_succ k x φ] at h1
    rw [h1]
    abel
  have e : (X - C a) * q = X * q + C (-a) * q := by
    rw [sub_mul, C_neg, neg_mul, sub_eq_add_neg]
  rw [e, polyDerivMoment_add_left, polyDerivMoment_X_mul, polyDerivMoment_C_mul]
  simp only [polyDerivMoment, Polynomial.sum_def, hk, smul_sub, smul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, Finset.smul_sum, neg_smul]
  have e2 : ∀ n, a • q.coeff n • derivMoment n x φ = q.coeff n • a • derivMoment n x φ :=
    fun n => smul_comm _ _ _
  simp only [e2, sub_eq_add_neg]

end HasWeakDeriv

/-- For `v 0 ∈ Hᵏ` with successive weak derivatives `v 1, …, v k`, `⟨Dᵏ (v 0), φ⟩ = ∫ φ • v k`
(the remark on regular inputs after `def:PE`). -/
theorem derivMoment_eq_integral_of_hasWeakDeriv (hφ : IsTestFunction T φ) {v : ℕ → ℝ → E}
    (k : ℕ) (hv : ∀ j < k, HasWeakDeriv T (v j) (v (j + 1))) :
    derivMoment k (v 0) φ = ∫ t, φ t • v k t := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [(hv 0 (Nat.succ_pos k)).derivMoment_succ hφ k]
    exact ih (v := fun j => v (j + 1)) fun j hj => hv (j + 1) (by omega)

/-- du Bois-Reymond: a signal with zero weak derivative is a.e. constant on the window. -/
theorem exists_ae_eq_const_of_integral_deriv_smul_eq_zero (hx : Integrable x (μI T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, deriv φ t • x t = 0) :
    ∃ c : E, ∀ᵐ t ∂(μI T), x t = c := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, ?_⟩
    have : μI T = 0 := by simp [μI, Ioc_eq_empty (not_lt.2 hT)]
    simp [this]
  obtain ⟨θ, hθ, -, hθ1⟩ := exists_isTestFunction_integral_eq_one hT
  refine ⟨∫ t, θ t • x t, ?_⟩
  have key : ∀ χ, IsTestFunction T χ → ∫ t, χ t • x t = (∫ t, χ t) • ∫ t, θ t • x t := by
    intro χ hχ
    obtain ⟨η, hη, hηeq⟩ := (hχ.sub (hθ.const_smul (∫ t, χ t))).exists_deriv_add_mul_eq 0 (by
      simp only [zero_mul, Real.exp_zero, one_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_sub hχ.integrable (hθ.integrable.const_mul _), integral_const_mul, hθ1, mul_one,
        sub_self])
    have h1 := h η hη
    have e : (fun t => deriv η t • x t) = fun t => χ t • x t - (∫ s, χ s) • (θ t • x t) := by
      funext t
      have := hηeq t
      simp only [zero_mul, add_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, sub_smul, mul_smul]
    have i2 : Integrable (fun t => (∫ s, χ s) • (θ t • x t)) := (hθ.integrable_smul hx).smul _
    rw [e, integral_sub (hχ.integrable_smul hx) i2, integral_smul] at h1
    exact sub_eq_zero.1 h1
  have := ae_eq_zero_of_integral_smul_eq_zero (u := fun t => x t - ∫ s, θ s • x s)
    (hx.sub (integrable_const _)) fun χ hχ => by
      simp only [smul_sub]
      rw [integral_sub (hχ.integrable_smul hx) (hχ.integrable.smul_const _), integral_smul_const,
        key χ hχ, sub_self]
  filter_upwards [this] with t ht using sub_eq_zero.1 ht

/-- A signal whose distributional derivative is an integrable `g` is a.e. equal to
`c + ∫₀ᵗ g`. -/
theorem exists_ae_eq_of_integral_deriv_smul (hx : Integrable x (μI T))
    (hg : Integrable g (μI T))
    (h : ∀ φ, IsTestFunction T φ → ∫ t, deriv φ t • x t = -∫ t, φ t • g t) :
    ∃ c : E, ∀ᵐ t ∂(μI T), x t = c + ∫ s in 0..t, g s := by
  have hG : Integrable (fun t => ∫ s in 0..t, g s) (μI T) :=
    (memLp_of_continuousOn (p := 1) (continuousOn_primitive hg)).integrable le_rfl
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_smul_eq_zero
    (x := fun t => x t - ∫ s in 0..t, g s) (hx.sub hG) fun φ hφ => by
      simp only [smul_sub]
      rw [integral_sub ((hφ.deriv).integrable_smul hx) ((hφ.deriv).integrable_smul hG), h φ hφ,
        integral_deriv_smul_primitive hg hφ, sub_self]
  refine ⟨c, ?_⟩
  filter_upwards [hc] with t ht
  rw [← ht]
  abel

/-- For `x` continuous on `[0, T]` and `g ∈ L²`, the integral form of `H¹` is equivalent to the
weak form `-∫ φ' • x = ∫ φ • g` for all test functions (`app:willems-gramian`, Step 3). -/
theorem hasWeakDeriv_iff (hx : ContinuousOn x (Icc 0 T)) (hg : MemLp g 2 (μI T)) :
    HasWeakDeriv T x g ↔ ∀ φ, IsTestFunction T φ → ∫ t, deriv φ t • x t = -∫ t, φ t • g t := by
  refine ⟨fun hxg φ hφ => hxg.integral_deriv_smul hφ, fun h => ⟨hg, fun t ht => ?_⟩⟩
  have hgi : Integrable g (μI T) := hg.integrable one_le_two
  have hxi : Integrable x (μI T) := (memLp_of_continuousOn (p := 1) hx).integrable le_rfl
  obtain ⟨c, hc⟩ := exists_ae_eq_of_integral_deriv_smul hxi hgi h
  have hT : 0 ≤ T := ht.1.trans ht.2
  rcases hT.eq_or_lt with hT0 | hT0
  · have : t = 0 := by
      have := ht.2
      rw [← hT0] at this
      exact le_antisymm this ht.1
    subst this
    simp
  have hEq : EqOn x (fun t => c + ∫ s in 0..t, g s) (Icc 0 T) := by
    have hc' : x =ᵐ[volume.restrict (Icc 0 T)] fun t => c + ∫ s in 0..t, g s := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
      exact hc
    exact Measure.eqOn_of_ae_eq hc' hx (continuousOn_const.add (continuousOn_primitive hgi))
      (by simp [interior_Icc, closure_Ioo hT0.ne])
  have h0 := hEq ⟨le_rfl, hT0.le⟩
  simp only [intervalIntegral.integral_same, add_zero] at h0
  rw [hEq ht, h0]

/-! ### Scalar constant-coefficient ODEs -/

private theorem hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun t => Real.exp (c * t)) (Real.exp (c * t) * c) t := by
  simpa using ((hasDerivAt_id t).const_mul c).exp

private theorem hasDerivAt_cexp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Complex.exp (c * (t : ℂ)) * c) t := by
  simpa using (((hasDerivAt_id t).ofReal_comp).const_mul c).cexp

/-- Variation of constants (real): an `H¹` solution of `ẋ = a x + f` is
`x t = e^{a t} x 0 + ∫₀ᵗ e^{a (t - s)} f s ds` on `[0, T]`. -/
theorem HasWeakDeriv.eq_exp_smul_add_integral {a : ℝ} {f : ℝ → E}
    (hx : HasWeakDeriv T x (fun t => a • x t + f t)) :
    ∀ t ∈ Icc 0 T,
      x t = Real.exp (a * t) • x 0 + ∫ s in 0..t, Real.exp (a * (t - s)) • f s := by
  have hz := hx.smul (𝕜 := ℝ) (a := fun t => Real.exp (-a * t))
    (a' := fun t => Real.exp (-a * t) * (-a)) (hasDerivAt_exp_mul (-a)) (by fun_prop)
  intro t ht
  have h1 := hz.eq_add_integral t ht
  have e : ∀ s, (Real.exp (-a * s) * (-a)) • x s + Real.exp (-a * s) • (a • x s + f s) =
      Real.exp (-a * s) • f s := fun s => by module
  simp only [e, mul_zero, Real.exp_zero, one_smul] at h1
  have hx' : x t = Real.exp (a * t) • (Real.exp (-a * t) • x t) := by
    rw [smul_smul, ← Real.exp_add, show a * t + -a * t = 0 by ring, Real.exp_zero, one_smul]
  rw [hx', h1, smul_add, ← intervalIntegral.integral_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [smul_smul, ← Real.exp_add]
  ring_nf

/-- Variation of constants (real), converse: the formula defines an `H¹` solution of
`ẋ = a x + f`. -/
theorem hasWeakDeriv_exp_smul_add_integral {a : ℝ} {f : ℝ → E} (hf : MemLp f 2 (μI T))
    (x₀ : E) :
    HasWeakDeriv T (fun t => Real.exp (a * t) • x₀ + ∫ s in 0..t, Real.exp (a * (t - s)) • f s)
      (fun t => a • (Real.exp (a * t) • x₀ + ∫ s in 0..t, Real.exp (a * (t - s)) • f s) + f t) := by
  have hz : HasWeakDeriv T (fun t => x₀ + ∫ s in 0..t, Real.exp (-a * s) • f s)
      (fun t => Real.exp (-a * t) • f t) :=
    ⟨memLp_smul_of_continuousOn (by fun_prop : Continuous fun t => Real.exp (-a * t)).continuousOn
      hf, fun t _ => by simp⟩
  have h2 := hz.smul (𝕜 := ℝ) (a := fun t => Real.exp (a * t))
    (a' := fun t => Real.exp (a * t) * a) (hasDerivAt_exp_mul a) (by fun_prop)
  have hid : ∀ t, Real.exp (a * t) • (x₀ + ∫ s in 0..t, Real.exp (-a * s) • f s) =
      Real.exp (a * t) • x₀ + ∫ s in 0..t, Real.exp (a * (t - s)) • f s := by
    intro t
    rw [smul_add, ← intervalIntegral.integral_smul]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [smul_smul, ← Real.exp_add]
    ring_nf
  refine h2.congr (fun t _ => hid t) (ae_of_all _ fun t => ?_)
  simp only
  rw [mul_comm, mul_smul, hid, smul_smul, ← Real.exp_add,
    show a * t + -a * t = 0 by ring, Real.exp_zero, one_smul]

/-- An `H¹` solution of `ẋ = a x` is `e^{a t} x 0` on `[0, T]`. -/
theorem HasWeakDeriv.eq_exp_smul {a : ℝ} (hx : HasWeakDeriv T x (fun t => a • x t)) :
    ∀ t ∈ Icc 0 T, x t = Real.exp (a * t) • x 0 := by
  have hx' : HasWeakDeriv T x (fun t => a • x t + (fun _ => (0 : E)) t) :=
    hx.congr (fun _ _ => rfl) (ae_of_all _ fun t => by simp)
  intro t ht
  simpa using hx'.eq_exp_smul_add_integral (f := fun _ => (0 : E)) t ht

/-- Variation of constants (complex `a`). -/
theorem HasWeakDeriv.eq_cexp_smul_add_integral [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a : ℂ} {f : ℝ → E} (hx : HasWeakDeriv T x (fun t => a • x t + f t)) :
    ∀ t ∈ Icc 0 T, x t = Complex.exp (a * (t : ℂ)) • x 0 +
      ∫ s in 0..t, Complex.exp (a * ((t - s : ℝ) : ℂ)) • f s := by
  have hz := hx.smul (𝕜 := ℂ) (a := fun t : ℝ => Complex.exp (-a * (t : ℂ)))
    (a' := fun t : ℝ => Complex.exp (-a * (t : ℂ)) * (-a)) (hasDerivAt_cexp_mul (-a))
    (by fun_prop)
  intro t ht
  have h1 := hz.eq_add_integral t ht
  have e : ∀ s : ℝ, (Complex.exp (-a * (s : ℂ)) * (-a)) • x s +
      Complex.exp (-a * (s : ℂ)) • (a • x s + f s) = Complex.exp (-a * (s : ℂ)) • f s :=
    fun s => by module
  simp only [e, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at h1
  have hx' : x t = Complex.exp (a * (t : ℂ)) • (Complex.exp (-a * (t : ℂ)) • x t) := by
    rw [smul_smul, ← Complex.exp_add, show a * (t : ℂ) + -a * (t : ℂ) = 0 by ring,
      Complex.exp_zero, one_smul]
  rw [hx', h1, smul_add, ← intervalIntegral.integral_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [smul_smul, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Variation of constants (complex `a`), converse. -/
theorem hasWeakDeriv_cexp_smul_add_integral [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a : ℂ} {f : ℝ → E} (hf : MemLp f 2 (μI T)) (x₀ : E) :
    HasWeakDeriv T
      (fun t => Complex.exp (a * (t : ℂ)) • x₀ +
        ∫ s in 0..t, Complex.exp (a * ((t - s : ℝ) : ℂ)) • f s)
      (fun t => a • (Complex.exp (a * (t : ℂ)) • x₀ +
        ∫ s in 0..t, Complex.exp (a * ((t - s : ℝ) : ℂ)) • f s) + f t) := by
  have hz : HasWeakDeriv T (fun t => x₀ + ∫ s in 0..t, Complex.exp (-a * (s : ℂ)) • f s)
      (fun t => Complex.exp (-a * (t : ℂ)) • f t) :=
    ⟨memLp_smul_of_continuousOn
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-a * (t : ℂ))).continuousOn hf,
      fun t _ => by simp⟩
  have h2 := hz.smul (𝕜 := ℂ) (a := fun t : ℝ => Complex.exp (a * (t : ℂ)))
    (a' := fun t : ℝ => Complex.exp (a * (t : ℂ)) * a) (hasDerivAt_cexp_mul a) (by fun_prop)
  have hid : ∀ t : ℝ, Complex.exp (a * (t : ℂ)) •
      (x₀ + ∫ s in 0..t, Complex.exp (-a * (s : ℂ)) • f s) =
      Complex.exp (a * (t : ℂ)) • x₀ +
        ∫ s in 0..t, Complex.exp (a * ((t - s : ℝ) : ℂ)) • f s := by
    intro t
    rw [smul_add, ← intervalIntegral.integral_smul]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [smul_smul, ← Complex.exp_add]
    push_cast
    ring_nf
  refine h2.congr (fun t _ => hid t) (ae_of_all _ fun t => ?_)
  simp only
  rw [mul_comm, mul_smul, hid, smul_smul, ← Complex.exp_add,
    show a * (t : ℂ) + -a * (t : ℂ) = 0 by ring, Complex.exp_zero, one_smul]

/-- A complex `H¹` solution of `ẏ = a y` is `e^{a t} y 0` on `[0, T]`
(`app:data-fattorini-hautus`, `eq:data-fh-exponential`). -/
theorem HasWeakDeriv.eq_cexp_mul {y : ℝ → ℂ} {a : ℂ} (hy : HasWeakDeriv T y (fun t => a * y t)) :
    ∀ t ∈ Icc 0 T, y t = Complex.exp (a * (t : ℂ)) * y 0 := by
  have hy' : HasWeakDeriv T y (fun t => a • y t + (fun _ => (0 : ℂ)) t) :=
    hy.congr (fun _ _ => rfl) (ae_of_all _ fun t => by simp)
  intro t ht
  simpa using hy'.eq_cexp_smul_add_integral (f := fun _ => (0 : ℂ)) t ht

end CompleteSpace

private theorem polyDerivMoment_add_right {T : ℝ} {u : ℝ → E} {φ ψ : ℝ → ℝ} (p : ℝ[X])
    (hφ : IsTestFunction T φ) (hψ : IsTestFunction T ψ) (hu : Integrable u (μI T)) :
    polyDerivMoment p u (φ + ψ) = polyDerivMoment p u φ + polyDerivMoment p u ψ := by
  simp only [polyDerivMoment, Polynomial.sum_def, derivMoment_add_right hφ hψ hu, smul_add,
    Finset.sum_add_distrib]

private theorem polyDerivMoment_smul_right {T : ℝ} {u : ℝ → E} {φ : ℝ → ℝ} (p : ℝ[X])
    (hφ : IsTestFunction T φ) (c : ℝ) :
    polyDerivMoment p u (c • φ) = c • polyDerivMoment p u φ := by
  simp only [polyDerivMoment, Polynomial.sum_def, derivMoment_smul_right hφ, Finset.smul_sum,
    smul_comm c]

/-- `⟨q(D) e^{λ ·}, χ⟩ = q(λ) ∫ e^{λ t} χ t dt`. -/
private theorem polyDerivMoment_exp {T : ℝ} {χ : ℝ → ℝ} (hχ : IsTestFunction T χ) (q : ℝ[X])
    (l : ℝ) :
    polyDerivMoment q (fun t => Real.exp (l * t)) χ =
      q.eval l * ∫ t, Real.exp (l * t) * χ t := by
  have hk : ∀ k, derivMoment k (fun t => Real.exp (l * t)) χ =
      l ^ k * ∫ t, Real.exp (l * t) * χ t := by
    intro k
    have h := derivMoment_eq_integral_of_hasDerivAt hχ (v := fun j t => l ^ j * Real.exp (l * t))
      k (fun j _ t _ => by
        have := (hasDerivAt_exp_mul l t).const_mul (l ^ j)
        convert this using 1
        ring)
      (fun j _ => by fun_prop)
    simp only [pow_zero, one_mul, smul_eq_mul] at h
    rw [h, ← integral_const_mul]
    congr 1
    funext t
    ring
  rw [polyDerivMoment, Polynomial.sum_def, eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hk, smul_eq_mul]
  ring

/-- `p(D) w = 0` in `𝒟'(I)` for `p = ∏ₙ (X - ρₙ)` with distinct real roots forces
`w = ∑ₙ κₙ e^{ρₙ t}` a.e. on the window (`app:pe-necessity`, Step 4). -/
theorem ae_eq_sum_exp_of_polyDerivMoment_eq_zero {T : ℝ} {r : ℕ} (ρ : Fin r → ℝ)
    (hρ : Function.Injective ρ) {w : ℝ → ℝ} (hw : Integrable w (μI T))
    (h : ∀ φ, IsTestFunction T φ → polyDerivMoment (∏ n, (X - C (ρ n))) w φ = 0) :
    ∃ κ : Fin r → ℝ, ∀ᵐ t ∂(μI T), w t = ∑ n, κ n * Real.exp (ρ n * t) := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, ?_⟩
    have : μI T = 0 := by simp [μI, Ioc_eq_empty (not_lt.2 hT)]
    simp [this]
  have hexpi : ∀ l : ℝ, Integrable (fun t => Real.exp (l * t)) (μI T) := fun l =>
    (memLp_of_continuousOn (p := 1)
      (by fun_prop : Continuous fun t => Real.exp (l * t)).continuousOn).integrable le_rfl
  induction r generalizing w with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty] at h ⊢
    exact ae_eq_zero_of_integral_smul_eq_zero hw fun φ hφ => by
      have := h φ hφ
      rwa [← C_1, polyDerivMoment_C, one_smul] at this
  | succ r ih =>
    set l := ρ (Fin.last r) with hl
    set q := ∏ n : Fin r, (X - C (ρ (Fin.castSucc n))) with hq
    have hp : ∏ n, (X - C (ρ n)) = (X - C l) * q := by
      rw [Fin.prod_univ_castSucc, mul_comm]
    -- `ℓ = ⟨q(D) w, ·⟩` annihilates `η' + l η`
    have h1 : ∀ η, IsTestFunction T η →
        polyDerivMoment q w (deriv η + l • η) = 0 := by
      intro η hη
      have := h η hη
      rw [hp, sub_eq_add_neg, add_mul, polyDerivMoment_add_left, polyDerivMoment_X_mul, ← C_neg,
        polyDerivMoment_C_mul] at this
      rw [polyDerivMoment_add_right q hη.deriv (hη.const_smul l) hw,
        polyDerivMoment_smul_right q hη]
      simp only [smul_eq_mul] at this ⊢
      linarith
    -- a test function `θ` with `∫ e^{l t} θ = 1`
    obtain ⟨θ₀, hθ₀, -, hθ₀1⟩ := exists_isTestFunction_integral_eq_one hT
    have hθ := hθ₀.mul_left (g := fun t => Real.exp (-l * t))
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
    have hθ1 : ∫ t, Real.exp (l * t) * (Real.exp (-l * t) * θ₀ t) = 1 := by
      rw [← hθ₀1]
      congr 1
      funext t
      rw [← mul_assoc, ← Real.exp_add, show l * t + -l * t = 0 by ring, Real.exp_zero, one_mul]
    set θ := fun t => Real.exp (-l * t) * θ₀ t with hθdef
    have hexpχ : ∀ χ, IsTestFunction T χ → Integrable fun t => Real.exp (l * t) * χ t :=
      fun χ hχ => (hχ.mul_left (g := fun t => Real.exp (l * t))
        (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).integrable
    -- `ℓ χ = (∫ e^{l t} χ) ℓ θ`
    have h2 : ∀ χ, IsTestFunction T χ →
        polyDerivMoment q w χ = (∫ t, Real.exp (l * t) * χ t) * polyDerivMoment q w θ := by
      intro χ hχ
      set m := ∫ t, Real.exp (l * t) * χ t with hm
      have hχ' := hχ.add (hθ.const_smul (-m))
      obtain ⟨η, hη, hηeq⟩ := hχ'.exists_deriv_add_mul_eq l (by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
        rw [integral_add (hexpχ χ hχ) ?_]
        · have : (fun t => Real.exp (l * t) * (-m * θ t)) =
              fun t => -m * (Real.exp (l * t) * θ t) := by funext t; ring
          rw [this, integral_const_mul, hθdef, hθ1, ← hm]
          ring
        · have : (fun t => Real.exp (l * t) * (-m * θ t)) =
              fun t => -m * (Real.exp (l * t) * θ t) := by funext t; ring
          rw [this]
          exact (hexpχ θ hθ).const_mul _)
      have e : deriv η + l • η = χ + (-m) • θ := by
        funext t
        simpa using hηeq t
      have := h1 η hη
      rw [e, polyDerivMoment_add_right q hχ (hθ.const_smul (-m)) hw,
        polyDerivMoment_smul_right q hθ] at this
      simp only [smul_eq_mul] at this
      linarith
    -- `q(l) ≠ 0`
    have hql : q.eval l ≠ 0 := by
      rw [hq, eval_prod, Finset.prod_ne_zero_iff]
      intro i _
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero, hl]
      exact fun h' => (Fin.castSucc_lt_last i).ne (hρ h').symm
    set c := polyDerivMoment q w θ / q.eval l with hc
    set w' : ℝ → ℝ := fun t => w t + (-c) * Real.exp (l * t) with hw'
    have hw'i : Integrable w' (μI T) := hw.add ((hexpi l).const_mul _)
    have h3 : ∀ χ, IsTestFunction T χ →
        polyDerivMoment (∏ n : Fin r, (X - C ((ρ ∘ Fin.castSucc) n))) w' χ = 0 := by
      intro χ hχ
      change polyDerivMoment q w' χ = 0
      have : w' = fun t => w t + (-c) • Real.exp (l * t) := rfl
      rw [this, polyDerivMoment_add (v := fun t => (-c) • Real.exp (l * t)) q hχ hw
          ((hexpi l).smul (-c)),
        polyDerivMoment_smul q, polyDerivMoment_exp hχ q l, h2 χ hχ, hc]
      simp only [smul_eq_mul]
      field_simp
      ring
    obtain ⟨κ', hκ'⟩ := ih (ρ ∘ Fin.castSucc) (hρ.comp (Fin.castSucc_injective r)) hw'i h3
    refine ⟨Fin.snoc (α := fun _ => ℝ) κ' c, ?_⟩
    filter_upwards [hκ'] with t ht
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply] at ht ⊢
    rw [← ht, hw', ← hl]
    ring

private theorem tsupport_iteratedDeriv_subset' (ψ : ℝ → ℝ) (k : ℕ) :
    tsupport (iteratedDeriv k ψ) ⊆ tsupport ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Scalar core: a compactly supported smooth `ψ` with `ψ⁽ⁿ⁾ = ∑_{k<n} bₖ ψ⁽ᵏ⁾` vanishes
(uniqueness for the first-order system of `(ψ, ψ', …, ψ⁽ⁿ⁻¹⁾)`). -/
private theorem eq_zero_of_iteratedDeriv_eq_sum {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) (b : ℕ → ℝ)
    (h : ∀ t, iteratedDeriv n ψ t = ∑ k ∈ Finset.range n, b k * iteratedDeriv k ψ t) :
    ψ = 0 := by
  rcases n with _ | n
  · funext t
    simpa using h t
  have hdiff : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m ψ) := fun m =>
    hψ.differentiable_iteratedDeriv m (by exact_mod_cast ENat.natCast_lt_top m)
  let M : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := LinearMap.pi fun i : Fin (n + 1) =>
    if hi : (i : ℕ) + 1 < n + 1 then LinearMap.proj ⟨i + 1, hi⟩
    else ∑ k : Fin (n + 1), b k • LinearMap.proj k
  let Mc := LinearMap.toContinuousLinearMap M
  let Y : ℝ → Fin (n + 1) → ℝ := fun t i => iteratedDeriv i ψ t
  have hY : ∀ t, HasDerivAt Y (Mc (Y t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have hd : HasDerivAt (iteratedDeriv i ψ) (iteratedDeriv (i + 1) ψ t) t := by
      rw [iteratedDeriv_succ]
      exact (hdiff i t).hasDerivAt
    convert hd using 1
    simp only [Mc, LinearMap.coe_toContinuousLinearMap', M, LinearMap.pi_apply]
    split_ifs with hi
    · simp [Y]
    · have hin : (i : ℕ) + 1 = n + 1 := by omega
      rw [hin, h t, ← Fin.sum_univ_eq_sum_range (fun k => b k * iteratedDeriv k ψ t)]
      simp [Y, LinearMap.sum_apply]
  have h0 : ∀ t, HasDerivAt (fun _ : ℝ => (0 : Fin (n + 1) → ℝ)) (Mc 0) t := fun t => by
    simpa using hasDerivAt_const t (0 : Fin (n + 1) → ℝ)
  obtain ⟨B, hB⟩ := hc.isCompact.bddAbove
  have ht₀ : B + 1 ∉ tsupport ψ := fun hmem => by linarith [hB hmem]
  have hY0 : Y (B + 1) = 0 := by
    funext i
    exact image_eq_zero_of_notMem_tsupport (f := iteratedDeriv i ψ) fun hmem =>
      ht₀ (tsupport_iteratedDeriv_subset' ψ i hmem)
  have := ODE_solution_unique_univ (v := fun _ => Mc) (s := fun _ => univ) (K := ‖Mc‖₊)
    (f := Y) (g := fun _ => 0) (t₀ := B + 1) (fun _ => Mc.lipschitzWith.lipschitzOnWith)
    (fun t => ⟨hY t, trivial⟩) (fun t => ⟨h0 t, trivial⟩) hY0
  funext t
  have := congrFun (congrFun this t) 0
  simpa [Y] using this

/-- A compactly supported smooth solution of a nontrivial linear constant-coefficient ODE
`∑ₖ ψ⁽ᵏ⁾ ζₖ = 0` (coefficients `ζₖ` in a normed space, not all zero) vanishes
(`app:window-pe-necessity`). -/
theorem eq_zero_of_sum_iteratedDeriv_smul_eq_zero {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {L : ℕ} (ζ : Fin L → E) (hζ : ζ ≠ 0)
    (h : ∀ t, ∑ k : Fin L, iteratedDeriv k ψ t • ζ k = 0) : ψ = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, ζ j ≠ 0 := by
    by_contra hcon
    exact hζ (funext fun k => not_not.1 fun hk => hcon ⟨k, hk⟩)
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ (ζ j) (norm_ne_zero_iff.2 hj)
  let c : ℕ → ℝ := fun k => if hk : k < L then ℓ (ζ ⟨k, hk⟩) else 0
  have hcj : c j ≠ 0 := by
    simp [c, hℓ, hj]
  have hsum : ∀ t, ∑ k ∈ Finset.range L, c k * iteratedDeriv k ψ t = 0 := by
    intro t
    have := congrArg ℓ (h t)
    rw [map_sum, map_zero] at this
    rw [← Fin.sum_univ_eq_sum_range (fun k => c k * iteratedDeriv k ψ t)]
    simpa [c, mul_comm] using this
  set n := Nat.findGreatest (fun k => c k ≠ 0) L with hn
  have hcn : c n ≠ 0 := Nat.findGreatest_spec (P := fun k => c k ≠ 0) j.2.le hcj
  have hzero : ∀ k, n < k → c k = 0 := fun k hk => by
    by_cases hkL : k ≤ L
    · exact not_not.1 (Nat.findGreatest_is_greatest hk hkL)
    · simp [c, show ¬ k < L by omega]
  have hnL : n < L := by
    by_contra hcon
    exact hcn (by simp [c, show ¬ n < L by omega])
  apply eq_zero_of_iteratedDeriv_eq_sum hψ hc n (fun k => -c k / c n)
  intro t
  have h1 : ∑ k ∈ Finset.range (n + 1), c k * iteratedDeriv k ψ t = 0 := by
    rw [← hsum t]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hk hk' => ?_
    simp only [Finset.mem_range] at hk hk'
    rw [hzero k (by omega), zero_mul]
  rw [Finset.sum_range_succ] at h1
  have e : ∑ k ∈ Finset.range n, -c k / c n * iteratedDeriv k ψ t =
      -(∑ k ∈ Finset.range n, c k * iteratedDeriv k ψ t) / c n := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, eq_div_iff hcn]
  linarith

/-- Test-function form of `eq_zero_of_sum_iteratedDeriv_smul_eq_zero`. -/
theorem IsTestFunction.eq_zero_of_sum_iteratedDeriv_smul_eq_zero {T : ℝ} {ψ : ℝ → ℝ}
    (hψ : IsTestFunction T ψ) {L : ℕ} (ζ : Fin L → E) (hζ : ζ ≠ 0)
    (h : ∀ t, ∑ k : Fin L, iteratedDeriv k ψ t • ζ k = 0) : ψ = 0 :=
  DataDrivenControl.eq_zero_of_sum_iteratedDeriv_smul_eq_zero hψ.contDiff hψ.hasCompactSupport
    ζ hζ h

end DataDrivenControl
