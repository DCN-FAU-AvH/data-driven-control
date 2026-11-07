module

public import DataDrivenControl.Semigroup.Adjoint

/-!
# Inhomogeneous equations and Ball's theorem

Real Hilbert spaces only (complex statements go through `Analysis/Complexification`).  The
equation is `ẋ = A x + f`, `x(0) = x₀`, with `f ∈ L¹(0, τ; E)`.

## Main declarations

* `C0Semigroup.mildSol S x₀ f t = S t x₀ + ∫₀ᵗ S (t - r) (f r) dr`, `continuousOn_mildSol`
  (dominated convergence, `continuousOn_conv`);
* `C0Semigroup.IsWeakSol S τ x₀ f x`: `x ∈ C([0, τ]; E)`, `x 0 = x₀` and, for `η ∈ D(A†)`,
  `⟪η, x t⟫ = ⟪η, x₀⟫ + ∫₀ᵗ (⟪A† η, x s⟫ + ⟪η, f s⟫) ds`;
* **Ball's theorem** (J. M. Ball, Proc. AMS 63 (1977)): `isWeakSol_mildSol` (mild ⇒ weak, by
  the Fubini computation `integral_inner_generator_adjoint_conv`), `IsWeakSol.eq_mildSol`
  (weak ⇒ mild, hence uniqueness of weak solutions, via `eq_zero_of_isWeakSol_zero`: test the
  primitive `w = ∫₀ᵗ y` with `S(t - s)† ζ`, `ζ ∈ D(A†)`, and use density of `D(A†)`),
  `isWeakSol_iff`;
* `eq_mildSol_of_strong`: the variation-of-constants formula for strong solutions
  (`x t ∈ D(A)`, `x t = x 0 + ∫₀ᵗ (A x + f)`).  Not used elsewhere: Steps 1 and 4 of
  `app:willems-gramian` go through Ball's theorem on `V` instead.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (S : C0Semigroup ℝ E)

/-- The **mild solution** of `ẋ = A x + f`, `x(0) = x₀`:
`x t = S t x₀ + ∫₀ᵗ S (t - r) (f r) dr`. -/
def mildSol (x₀ : E) (f : ℝ → E) (t : ℝ) : E :=
  S.real t x₀ + ∫ r in Ioc 0 t, S.real (t - r) (f r)

/-- A **weak solution** of `ẋ = A x + f`, `x(0) = x₀` on `[0, τ]` (Ball 1977): `x` is
continuous, `x 0 = x₀`, and for every `η ∈ D(A†)` and `t ∈ [0, τ]`,
`⟪η, x t⟫ = ⟪η, x₀⟫ + ∫₀ᵗ (⟪A† η, x s⟫ + ⟪η, f s⟫) ds`. -/
def IsWeakSol (τ : ℝ) (x₀ : E) (f : ℝ → E) (x : ℝ → E) : Prop :=
  ContinuousOn x (Icc 0 τ) ∧ x 0 = x₀ ∧
    ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain), ∀ t ∈ Icc 0 τ,
      ⟪η, x t⟫_ℝ = ⟪η, x₀⟫_ℝ +
        ∫ s in (0 : ℝ)..t, (⟪S.generator.adjoint ⟨η, hη⟩, x s⟫_ℝ + ⟪η, f s⟫_ℝ)

omit [CompleteSpace E] in
@[simp] theorem mildSol_zero_time (x₀ : E) (f : ℝ → E) : S.mildSol x₀ f 0 = x₀ := by
  simp [mildSol]

/-- `∫ ⟪c, f⟫ = ⟪c, ∫ f⟫` for interval integrals. -/
private theorem intervalIntegral_inner_aux {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (c : E) :
    ∫ s in a..b, ⟪c, f s⟫_ℝ = ⟪c, ∫ s in a..b, f s⟫_ℝ :=
  (innerSL ℝ c).intervalIntegral_comp_comm hf

/-- Continuity of the convolution `t ↦ ∫_{(0,t]} S (t - r) f r dr` on `[0, τ]`. -/
theorem continuousOn_conv {τ : ℝ} {f : ℝ → E} (hf : IntegrableOn f (Ioc 0 τ)) :
    ContinuousOn (fun t => ∫ r in Ioc 0 t, S.real (t - r) (f r)) (Icc 0 τ) := by
  set F : ℝ → ℝ → E := fun t => (Iic t).indicator fun r => S.real (t - r) (f r) with hFdef
  have hF : ∀ t ≤ τ, ∫ r in Ioc 0 t, S.real (t - r) (f r) = ∫ r in Ioc 0 τ, F t r := by
    intro t ht
    rw [hFdef, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, inf_eq_right.2 ht]
  have hcont : ∀ t₀, ContinuousAt (fun t => ∫ r in Ioc 0 τ, F t r) t₀ := by
    intro t₀
    obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le (t₀ + 1)
    refine continuousAt_of_dominated (bound := fun r => M * ‖f r‖) ?_ ?_ (hf.norm.const_mul M) ?_
    · exact Eventually.of_forall fun t =>
        (S.aestronglyMeasurable_conv hf.aestronglyMeasurable t).indicator measurableSet_Iic
    · filter_upwards [eventually_lt_nhds (lt_add_one t₀)] with t ht
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      by_cases hrt : r ∈ Iic t
      · simp only [hFdef, indicator_of_mem hrt]
        exact ((S.real _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hM _ (by linarith [hr.1])) (norm_nonneg _))
      · simp only [hFdef, indicator_of_notMem hrt, norm_zero]
        positivity
    · filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume t₀)] with r hr
      rcases hr.lt_or_gt with h | h
      · have : (fun t => S.real (t - r) (f r)) =ᶠ[𝓝 t₀] fun t => F t r := by
          filter_upwards [eventually_gt_nhds h] with t ht
          simp only [hFdef, indicator_of_mem (show r ∈ Iic t from ht.le)]
        exact (((S.continuous_real_apply (f r)).comp
          (continuous_id.sub continuous_const)).continuousAt).congr this
      · have : (fun _ => (0 : E)) =ᶠ[𝓝 t₀] fun t => F t r := by
          filter_upwards [eventually_lt_nhds h] with t ht
          simp only [hFdef, indicator_of_notMem (show r ∉ Iic t from not_le.2 ht)]
        exact continuousAt_const.congr this
  intro t ht
  exact (hcont t).continuousWithinAt.congr (fun s hs => hF s hs.2) (hF t ht.2)

/-- The mild solution is continuous on `[0, τ]` for `f ∈ L¹(0, τ)`. -/
theorem continuousOn_mildSol {τ : ℝ} {f : ℝ → E} (hf : IntegrableOn f (Ioc 0 τ)) (x₀ : E) :
    ContinuousOn (S.mildSol x₀ f) (Icc 0 τ) :=
  (S.continuous_real_apply x₀).continuousOn.add (S.continuousOn_conv hf)

/-- The Fubini computation behind Ball's theorem:
`∫₀ᵗ ⟪A† η, ∫₀ˢ S (s - r) f r dr⟫ ds = ⟪η, ∫₀ᵗ S (t - r) f r dr⟫ - ∫₀ᵗ ⟪η, f r⟫ dr`. -/
theorem integral_inner_generator_adjoint_conv {η : E} (hη : η ∈ S.generator.adjoint.domain)
    {f : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hf : IntegrableOn f (Ioc 0 t)) :
    ∫ s in (0 : ℝ)..t,
        ⟪S.generator.adjoint ⟨η, hη⟩, ∫ r in Ioc 0 s, S.real (s - r) (f r)⟫_ℝ =
      ⟪η, ∫ r in Ioc 0 t, S.real (t - r) (f r)⟫_ℝ - ∫ r in Ioc 0 t, ⟪η, f r⟫_ℝ := by
  set ζ := S.generator.adjoint ⟨η, hη⟩
  set G : ℝ → ℝ → ℝ := fun s r => ⟪ζ, S.real (s - r) (f r)⟫_ℝ with hG
  set H : ℝ → ℝ → ℝ := fun s r => if r ≤ s then G s r else 0 with hH
  obtain ⟨M, hM0, hM⟩ := S.exists_norm_real_le t
  have h1 : ∫ s in (0 : ℝ)..t, ⟪ζ, ∫ r in Ioc 0 s, S.real (s - r) (f r)⟫_ℝ =
      ∫ s in Ioc 0 t, ∫ r in Ioc 0 t, H s r := by
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hfs : IntegrableOn f (Ioc 0 s) := hf.mono_set (Ioc_subset_Ioc_right hs.2)
    rw [← integral_inner (S.integrableOn_conv hfs)]
    have : (fun r => H s r) = (Iic s).indicator (G s) := by
      ext r; simp only [hH, indicator_apply, mem_Iic]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, inf_eq_right.2 hs.2]
  have hint : Integrable (Function.uncurry H)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry H)
        ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
      have : Function.uncurry H = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
          (fun p => ⟪ζ, S.real (p.1 - p.2) (f p.2)⟫_ℝ) := by
        ext p; simp only [Function.uncurry, hH, hG, indicator_apply, mem_ofPred_eq]
      rw [this]
      refine AEStronglyMeasurable.indicator ?_ (measurableSet_le measurable_snd measurable_fst)
      exact aestronglyMeasurable_const.inner
        (Continuous.comp_aestronglyMeasurable₂ (g := fun s x => S.real s x)
          S.continuous_real_apply₂ (continuous_fst.sub continuous_snd).aestronglyMeasurable
          hf.aestronglyMeasurable.comp_snd)
    have hb : Integrable (fun z : ℝ × ℝ => (fun _ : ℝ => ‖ζ‖ * M) z.1 * (fun r => ‖f r‖) z.2)
        ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) :=
      (integrable_const _).mul_prod hf.norm
    refine Integrable.mono' hb hmeas ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
    refine Eventually.of_forall fun p hp => ?_
    simp only [mem_prod, mem_Ioc] at hp
    simp only [Function.uncurry, hH, hG]
    split_ifs with h
    · calc ‖⟪ζ, S.real (p.1 - p.2) (f p.2)⟫_ℝ‖ ≤ ‖ζ‖ * ‖S.real (p.1 - p.2) (f p.2)‖ :=
            norm_inner_le_norm _ _
        _ ≤ ‖ζ‖ * (M * ‖f p.2‖) := by
            gcongr
            exact ((S.real _).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hM _ (by linarith)) (norm_nonneg _))
        _ = ‖ζ‖ * M * ‖f p.2‖ := by ring
    · rw [norm_zero]; positivity
  rw [h1, integral_integral_swap hint]
  have h4 : EqOn (fun r => ∫ s in Ioc 0 t, H s r)
      (fun r => ⟪η, S.real (t - r) (f r)⟫_ℝ - ⟪η, f r⟫_ℝ) (Ioc 0 t) := by
    intro r hr
    have hind : (fun s => H s r) = (Ici r).indicator (fun s => G s r) := by
      ext s; simp only [hH, indicator_apply, mem_Ici]
    have hset : Ioc 0 t ∩ Ici r = Icc r t := by
      ext s; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h2, h3⟩; exact ⟨⟨hr.1.trans_le h2, h3⟩, h2⟩
    simp only
    rw [hind, setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr.2]
    have hsub := intervalIntegral.integral_comp_sub_right
      (fun u => ⟪ζ, S.real u (f r)⟫_ℝ) (a := r) (b := t) r
    simp only [sub_self] at hsub
    rw [hG]
    simp only
    rw [hsub, S.inner_real_apply_eq_add_integral hη (f r) (sub_nonneg.2 hr.2)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc h4,
    integral_sub ((S.integrableOn_conv hf).const_inner η) (hf.const_inner η),
    integral_inner (S.integrableOn_conv hf)]

/-- **Ball's theorem, mild ⇒ weak**: the mild solution is a weak solution. -/
theorem isWeakSol_mildSol {τ : ℝ} {f : ℝ → E} (hf : IntegrableOn f (Ioc 0 τ)) (x₀ : E) :
    S.IsWeakSol τ x₀ f (S.mildSol x₀ f) := by
  refine ⟨S.continuousOn_mildSol hf x₀, S.mildSol_zero_time x₀ f, fun η hη t ht => ?_⟩
  have hft : IntegrableOn f (Ioc 0 t) := hf.mono_set (Ioc_subset_Ioc_right ht.2)
  set ζ := S.generator.adjoint ⟨η, hη⟩
  have hc1 : IntervalIntegrable (fun s => ⟪ζ, S.real s x₀⟫_ℝ) volume 0 t :=
    (continuous_const.inner (S.continuous_real_apply x₀)).intervalIntegrable _ _
  have hc2 : IntervalIntegrable
      (fun s => ⟪ζ, ∫ r in Ioc 0 s, S.real (s - r) (f r)⟫_ℝ) volume 0 t :=
    (continuousOn_const.inner (S.continuousOn_conv hft)).intervalIntegrable_of_Icc ht.1
  have hc3 : IntervalIntegrable (fun s => ⟪η, f s⟫_ℝ) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hft.const_inner η)
  simp only [mildSol, inner_add_right]
  rw [intervalIntegral.integral_add (hc1.add hc2) hc3, intervalIntegral.integral_add hc1 hc2,
    S.inner_real_apply_eq_add_integral hη x₀ ht.1, S.integral_inner_generator_adjoint_conv hη ht.1 hft,
    intervalIntegral.integral_of_le ht.1 (f := fun r => ⟪η, f r⟫_ℝ)]
  ring

/-- `A† (S t)† η = (S t)† A† η` for `η ∈ D(A†)` (real-time version). -/
theorem generator_adjoint_apply_adjoint_real {η : E} (hη : η ∈ S.generator.adjoint.domain)
    (t : ℝ) :
    S.generator.adjoint ⟨S.adjoint.real t η, S.adjoint_real_mem_adjoint_domain hη t⟩ =
      S.adjoint.real t (S.generator.adjoint ⟨η, hη⟩) :=
  S.generator_adjoint_apply_adjoint hη _

/-- Uniqueness for the homogeneous weak problem: a continuous `y` with
`⟪η, y t⟫ = ∫₀ᵗ ⟪A† η, y s⟫ ds` for all `η ∈ D(A†)` and `t ∈ [0, τ]` vanishes on `[0, τ]`.
Proof: with `w t = ∫₀ᵗ y`, `⟪η, y t⟫ = ⟪A† η, w t⟫`, so `s ↦ ⟪S(t - s)† ζ, w s⟫` has zero
derivative; hence `⟪ζ, w t⟫ = 0` for `ζ ∈ D(A†)`, `w t = 0`, and `y t = 0` by density. -/
theorem eq_zero_of_isWeakSol_zero {τ : ℝ} {y : ℝ → E} (hy : Continuous y)
    (h : ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain), ∀ t ∈ Icc 0 τ,
      ⟪η, y t⟫_ℝ = ∫ s in (0 : ℝ)..t, ⟪S.generator.adjoint ⟨η, hη⟩, y s⟫_ℝ) :
    ∀ t ∈ Icc 0 τ, y t = 0 := by
  set w : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, y s with hw
  have hwd : ∀ t, HasDerivAt w (y t) t := fun t => (hy.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t => (hwd t).continuousAt
  have hw0 : w 0 = 0 := by simp [hw]
  have key : ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain), ∀ t ∈ Icc 0 τ,
      ⟪η, y t⟫_ℝ = ⟪S.generator.adjoint ⟨η, hη⟩, w t⟫_ℝ := by
    intro η hη t ht
    rw [h η hη t ht, hw]
    exact intervalIntegral_inner_aux (hy.intervalIntegrable _ _) _
  have hw_zero : ∀ t ∈ Icc 0 τ, w t = 0 := by
    intro t ht
    refine S.dense_adjoint_domain.eq_zero_of_inner_left ℝ fun ζ hζ => ?_
    rw [real_inner_comm]
    set ψ : ℝ → ℝ := fun s => ⟪S.adjoint.real (t - s) ζ, w s⟫_ℝ with hψ
    have hψc : ContinuousOn ψ (Icc 0 t) :=
      (((S.adjoint.continuous_real_apply ζ).comp (continuous_const.sub continuous_id)).inner
        hwc).continuousOn
    have hψd : ∀ s ∈ Ico 0 t, HasDerivWithinAt ψ 0 (Ici s) s := by
      intro s hs
      have h1 := S.adjoint.hasDerivAt_real_apply ⟨ζ, S.mem_adjoint_generator_domain hζ⟩
        (sub_pos.2 hs.2)
      rw [S.adjoint_generator_apply hζ] at h1
      have h2 : HasDerivAt (fun s => S.adjoint.real (t - s) ζ)
          (-(S.adjoint.real (t - s) (S.generator.adjoint ⟨ζ, hζ⟩))) s := by
        simpa [Function.comp_def] using h1.scomp s ((hasDerivAt_id s).const_sub t)
      have h3 := h2.inner ℝ (hwd s)
      convert h3.hasDerivWithinAt using 1
      rw [key _ (S.adjoint_real_mem_adjoint_domain hζ (t - s)) s
        ⟨hs.1, hs.2.le.trans ht.2⟩, S.generator_adjoint_apply_adjoint_real hζ, inner_neg_left,
        add_neg_cancel]
    have := constant_of_has_deriv_right_zero hψc hψd t ⟨ht.1, le_rfl⟩
    simpa only [hψ, sub_self, S.adjoint.real_zero, one_apply_eq_self, hw0, inner_zero_right]
      using this
  intro t ht
  refine S.dense_adjoint_domain.eq_zero_of_inner_left ℝ fun η hη => ?_
  rw [real_inner_comm, key η hη t ht, hw_zero t ht, inner_zero_right]

/-- **Ball's theorem, weak ⇒ mild**: a weak solution is the mild solution; in particular weak
solutions are unique. -/
theorem IsWeakSol.eq_mildSol {τ : ℝ} {x₀ : E} {f x : ℝ → E} (hf : IntegrableOn f (Ioc 0 τ))
    (hx : S.IsWeakSol τ x₀ f x) : ∀ t ∈ Icc 0 τ, x t = S.mildSol x₀ f t := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hτ)
  obtain ⟨hxc, -, hxw⟩ := hx
  obtain ⟨hmc, -, hmw⟩ := S.isWeakSol_mildSol hf x₀
  set g : ℝ → E := fun s => x s - S.mildSol x₀ f s with hg
  set y : ℝ → E := fun s => g (projIcc 0 τ hτ s) with hy
  have hyc : Continuous y := (hxc.sub hmc).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 τ hτ s).2
  have hyeq : ∀ s ∈ Icc 0 τ, y s = x s - S.mildSol x₀ f s := fun s hs => by
    simp only [hy, hg, projIcc_of_mem hτ hs]
  have hyw : ∀ (η : E) (hη : η ∈ S.generator.adjoint.domain), ∀ t ∈ Icc 0 τ,
      ⟪η, y t⟫_ℝ = ∫ s in (0 : ℝ)..t, ⟪S.generator.adjoint ⟨η, hη⟩, y s⟫_ℝ := by
    intro η hη t ht
    have hft : IntegrableOn f (Ioc 0 t) := hf.mono_set (Ioc_subset_Ioc_right ht.2)
    have hsub : Icc 0 t ⊆ Icc 0 τ := Icc_subset_Icc_right ht.2
    have i1 : IntervalIntegrable (fun s => ⟪S.generator.adjoint ⟨η, hη⟩, x s⟫_ℝ) volume 0 t :=
      (continuousOn_const.inner (hxc.mono hsub)).intervalIntegrable_of_Icc ht.1
    have i2 : IntervalIntegrable
        (fun s => ⟪S.generator.adjoint ⟨η, hη⟩, S.mildSol x₀ f s⟫_ℝ) volume 0 t :=
      (continuousOn_const.inner (hmc.mono hsub)).intervalIntegrable_of_Icc ht.1
    have i3 : IntervalIntegrable (fun s => ⟪η, f s⟫_ℝ) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hft.const_inner η)
    have hcongr : ∫ s in (0 : ℝ)..t, ⟪S.generator.adjoint ⟨η, hη⟩, y s⟫_ℝ =
        ∫ s in (0 : ℝ)..t, (⟪S.generator.adjoint ⟨η, hη⟩, x s⟫_ℝ -
          ⟪S.generator.adjoint ⟨η, hη⟩, S.mildSol x₀ f s⟫_ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [hyeq s (hsub hs), inner_sub_right]
    rw [hyeq t ht, inner_sub_right, hxw η hη t ht, hmw η hη t ht, hcongr,
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_add i1 i3,
      intervalIntegral.integral_add i2 i3]
    ring
  intro t ht
  rw [← sub_eq_zero, ← hyeq t ht]
  exact S.eq_zero_of_isWeakSol_zero hyc hyw t ht

/-- Ball's theorem: weak solutions are exactly the mild solution. -/
theorem isWeakSol_iff {τ : ℝ} (hτ : 0 ≤ τ) {x₀ : E} {f x : ℝ → E}
    (hf : IntegrableOn f (Ioc 0 τ)) :
    S.IsWeakSol τ x₀ f x ↔ ∀ t ∈ Icc 0 τ, x t = S.mildSol x₀ f t := by
  refine ⟨fun hx => hx.eq_mildSol S hf, fun h => ?_⟩
  obtain ⟨hc, -, hw⟩ := S.isWeakSol_mildSol hf x₀
  refine ⟨hc.congr h, ?_, fun η hη t ht => ?_⟩
  · rw [h 0 ⟨le_rfl, hτ⟩, mildSol_zero_time]
  · rw [h t ht, hw η hη t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [h s ⟨hs.1, hs.2.trans ht.2⟩]

/-- **Variation of constants for strong solutions**: if `x s ∈ D(A)` with `A x s = g s` and
`x t = x 0 + ∫₀ᵗ (g s + f s) ds` on `[0, τ]`, then `x` is the mild solution. -/
theorem eq_mildSol_of_strong {τ : ℝ} {x g f : ℝ → E}
    (hx : ∀ s ∈ Icc 0 τ, x s ∈ S.generator.domain)
    (hg : ∀ (s : ℝ) (h : s ∈ Icc 0 τ), S.generator ⟨x s, hx s h⟩ = g s)
    (hgi : IntegrableOn g (Ioc 0 τ)) (hfi : IntegrableOn f (Ioc 0 τ))
    (hint : ∀ t ∈ Icc 0 τ, x t = x 0 + ∫ s in (0 : ℝ)..t, (g s + f s)) :
    ∀ t ∈ Icc 0 τ, x t = S.mildSol (x 0) f t := by
  rcases lt_or_ge τ 0 with hτ | hτ
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.2 hτ)
  have hgf : IntegrableOn (fun s => g s + f s) (Ioc 0 τ) := hgi.add hfi
  refine IsWeakSol.eq_mildSol S hfi ⟨?_, rfl, fun η hη t ht => ?_⟩
  · have hp := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := τ)
      (f := fun s => g s + f s)
      (by rw [uIcc_of_le hτ]; exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).2 hgf)
    rw [uIcc_of_le hτ] at hp
    exact (continuousOn_const.add hp).congr hint
  · have hgft : IntervalIntegrable (fun s => g s + f s) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2
        (hgf.mono_set (Ioc_subset_Ioc_right ht.2))
    rw [hint t ht, inner_add_right, ← intervalIntegral_inner_aux hgft]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [inner_add_right]
    rw [← hg s hs', ← LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain ⟨η, hη⟩
      ⟨x s, hx s hs'⟩]

end C0Semigroup

end DataDrivenControl
