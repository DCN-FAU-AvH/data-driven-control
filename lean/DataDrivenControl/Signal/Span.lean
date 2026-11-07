module

public import DataDrivenControl.Signal.Basic
public import DataDrivenControl.Analysis.BoundedBelow

/-!
# Annihilators and closed spans of signals

For a signal `z : α → E` into an inner product space over `𝕜` (`RCLike`: real for most of the
paper, complex in Sections 3.5 and 5) and an arbitrary measure `μ` on the time axis `α`
(typically `μI T`):

* `annihilator 𝕜 μ z = {ζ | ∀ᵐ t ∂μ, ⟪ζ, z t⟫ = 0}`, a closed submodule
  (`isClosed_annihilator`);
* `cspan 𝕜 μ z := (annihilator 𝕜 μ z)ᗮ`, the paper's `\cspan z`
  (`introduction.tex`: the smallest closed subspace containing `z t` for a.e. `t`).
  `isLeast_cspan` proves that characterisation for a.e. strongly measurable `z` in a Hilbert
  space, via `ae_mem_cspan` (which uses separability of the essential range) and
  `cspan_le_of_ae_mem`;
* `cspan_eq_top_iff`: `cspan = ⊤ ↔ annihilator = ⊥` (the form of informativity used in
  `def:hilbert-informative`);
* monotonicity in the measure and the window: `annihilator_mono_measure`,
  `annihilator_restrict_mono`, `annihilator_μI_mono` and the `cspan_…` versions; invariance under
  a.e. equality (`annihilator_congr`, `cspan_congr`);
* Bochner integrals: `integral_mem_of_ae_mem` (an integral of a function with values a.e. in a
  closed subspace lies in it) and `integral_smul_mem_cspan` (`∫ φ z ∈ cspan z`);
* images under continuous linear maps: `orthogonal_map_eq_comap_adjoint`
  (`(T K)ᗮ = (T†)⁻¹ Kᗮ`), `annihilator_comp` (`ζ` annihilates `T ∘ z` iff `T† ζ` annihilates
  `z`), `cspan_comp` (`cspan (T ∘ z) = closure (T (cspan z))`) and, for bounded-below `T`,
  `cspan_comp_of_isBoundedBelow` (`cspan (T ∘ z) = T (cspan z)`) and `cspan_comp_eq_range`
  (Step 2 of `app:willems-gramian`);
* pairs in `WithLp 2 (E × F)`: `mem_annihilator_prod`, `toLp_mem_annihilator_pair`,
  `annihilator_pair_eq_bot_iff`, `cspan_pair_eq_top_iff` (the "equivalently" clause of
  `def:hilbert-informative`).

The field `𝕜` is an explicit argument (`annihilator 𝕜 μ z`), as in `Submodule.span 𝕜`: a complex
space is also a real inner product space, so `𝕜` cannot be inferred from `z`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

namespace DataDrivenControl

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {α : Type*} {mα : MeasurableSpace α}

section Def

variable (𝕜)

/-- The **annihilator** of a signal: the vectors `ζ` with `⟪ζ, z t⟫ = 0` for `μ`-a.e. `t`. -/
def annihilator (μ : Measure α) (z : α → E) : Submodule 𝕜 E where
  carrier := {ζ | ∀ᵐ t ∂μ, ⟪ζ, z t⟫_𝕜 = 0}
  add_mem' {a b} ha hb := by
    change ∀ᵐ t ∂μ, ⟪a, z t⟫_𝕜 = 0 at ha
    change ∀ᵐ t ∂μ, ⟪b, z t⟫_𝕜 = 0 at hb
    change ∀ᵐ t ∂μ, ⟪a + b, z t⟫_𝕜 = 0
    filter_upwards [ha, hb] with t ha hb
    simp [inner_add_left, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    change ∀ᵐ t ∂μ, ⟪a, z t⟫_𝕜 = 0 at ha
    change ∀ᵐ t ∂μ, ⟪c • a, z t⟫_𝕜 = 0
    filter_upwards [ha] with t ha
    simp [inner_smul_left, ha]

/-- The **closed span** of a signal, `cspan z = (annihilator z)ᗮ` (the paper's `\cspan z`, see
`isLeast_cspan` for the "smallest closed subspace containing `z t` a.e." characterisation). -/
def cspan (μ : Measure α) (z : α → E) : Submodule 𝕜 E :=
  (annihilator 𝕜 μ z)ᗮ

end Def

variable {μ ν : Measure α} {z w : α → E}

theorem mem_annihilator {ζ : E} : ζ ∈ annihilator 𝕜 μ z ↔ ∀ᵐ t ∂μ, ⟪ζ, z t⟫_𝕜 = 0 :=
  Iff.rfl

theorem mem_annihilator' {ζ : E} : ζ ∈ annihilator 𝕜 μ z ↔ ∀ᵐ t ∂μ, ⟪z t, ζ⟫_𝕜 = 0 :=
  ⟨fun h => (mem_annihilator.1 h).mono fun _ ht => inner_eq_zero_symm.1 ht,
    fun h => mem_annihilator.2 (h.mono fun _ ht => inner_eq_zero_symm.1 ht)⟩

theorem cspan_def : cspan 𝕜 μ z = (annihilator 𝕜 μ z)ᗮ :=
  rfl

theorem mem_cspan {v : E} : v ∈ cspan 𝕜 μ z ↔ ∀ ζ ∈ annihilator 𝕜 μ z, ⟪ζ, v⟫_𝕜 = 0 :=
  Submodule.mem_orthogonal _ _

/-- The annihilator is closed. -/
theorem isClosed_annihilator : IsClosed (annihilator 𝕜 μ z : Set E) := by
  refine isSeqClosed_iff_isClosed.1 fun ζ ζ₀ hζ hlim => ?_
  have h : ∀ᵐ t ∂μ, ∀ n, ⟪ζ n, z t⟫_𝕜 = 0 := ae_all_iff.2 fun n => hζ n
  change ∀ᵐ t ∂μ, ⟪ζ₀, z t⟫_𝕜 = 0
  filter_upwards [h] with t ht
  have hlim' : Tendsto (fun n => ⟪ζ n, z t⟫_𝕜) atTop (𝓝 ⟪ζ₀, z t⟫_𝕜) :=
    hlim.inner tendsto_const_nhds
  simp only [ht] at hlim'
  exact tendsto_nhds_unique hlim' tendsto_const_nhds

/-- The closed span is closed. -/
theorem isClosed_cspan : IsClosed (cspan 𝕜 μ z : Set E) :=
  Submodule.isClosed_orthogonal _

/-- `(cspan z)ᗮ = annihilator z` (`eq:gramian-kernel` reads `ker 𝒢 = (cspan z)ᗮ`). -/
theorem orthogonal_cspan [CompleteSpace E] : (cspan 𝕜 μ z)ᗮ = annihilator 𝕜 μ z := by
  rw [cspan_def, Submodule.orthogonal_orthogonal_eq_closure,
    isClosed_annihilator.submodule_topologicalClosure_eq]

/-- `cspan z = ⊤` iff only `0` annihilates `z`. -/
theorem cspan_eq_top_iff : cspan 𝕜 μ z = ⊤ ↔ annihilator 𝕜 μ z = ⊥ :=
  (annihilator 𝕜 μ z).orthogonal_eq_top_iff

theorem annihilator_eq_bot_iff :
    annihilator 𝕜 μ z = ⊥ ↔ ∀ ζ : E, (∀ᵐ t ∂μ, ⟪ζ, z t⟫_𝕜 = 0) → ζ = 0 :=
  Submodule.eq_bot_iff _

theorem annihilator_congr (h : z =ᵐ[μ] w) : annihilator 𝕜 μ z = annihilator 𝕜 μ w := by
  ext ζ
  simp only [mem_annihilator]
  constructor <;> intro hζ <;> filter_upwards [h, hζ] with t ht h2
  · rwa [← ht]
  · rwa [ht]

theorem cspan_congr (h : z =ᵐ[μ] w) : cspan 𝕜 μ z = cspan 𝕜 μ w := by
  rw [cspan, cspan, annihilator_congr h]

/-- Annihilating on a larger measure (e.g. a longer window) is harder. -/
theorem annihilator_mono_measure (h : ν ≪ μ) : annihilator 𝕜 μ z ≤ annihilator 𝕜 ν z :=
  fun _ hζ => h.ae_le hζ

/-- The closed span grows with the measure (e.g. with the window). -/
theorem cspan_mono_measure (h : ν ≪ μ) : cspan 𝕜 ν z ≤ cspan 𝕜 μ z :=
  Submodule.orthogonal_le (annihilator_mono_measure h)

/-- Restricting to a smaller set makes annihilating easier. -/
theorem annihilator_restrict_mono {s s' : Set α} (hs : s ⊆ s') :
    annihilator 𝕜 (μ.restrict s') z ≤ annihilator 𝕜 (μ.restrict s) z :=
  annihilator_mono_measure (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hs le_rfl))

/-- Restricting to a smaller set shrinks the closed span. -/
theorem cspan_restrict_mono {s s' : Set α} (hs : s ⊆ s') :
    cspan 𝕜 (μ.restrict s) z ≤ cspan 𝕜 (μ.restrict s') z :=
  Submodule.orthogonal_le (annihilator_restrict_mono hs)

/-- Annihilating on a longer window `(0, T']` is harder. -/
theorem annihilator_μI_mono {z : ℝ → E} {T T' : ℝ} (h : T ≤ T') :
    annihilator 𝕜 (μI T') z ≤ annihilator 𝕜 (μI T) z :=
  annihilator_restrict_mono (Ioc_subset_Ioc_right h)

/-- The closed span grows with the window. -/
theorem cspan_μI_mono {z : ℝ → E} {T T' : ℝ} (h : T ≤ T') :
    cspan 𝕜 (μI T) z ≤ cspan 𝕜 (μI T') z :=
  Submodule.orthogonal_le (annihilator_μI_mono h)

/-! ### The closed span is the smallest closed subspace containing the signal a.e. -/

/-- An a.e. strongly measurable signal lies in its closed span for a.e. `t`.  The proof uses
the separability of the essential range of `z`. -/
theorem ae_mem_cspan (hz : AEStronglyMeasurable z μ) : ∀ᵐ t ∂μ, z t ∈ cspan 𝕜 μ z := by
  obtain ⟨S, ⟨D, hDc, hSD⟩, hzS⟩ := hz.isSeparable_ae_range
  -- the null sets `{t | z t ∈ ball d (1 / (n + 1))}` with `d ∈ D` (countably many)
  let B : E → ℕ → Set α := fun d n => z ⁻¹' Metric.ball d (1 / (n + 1))
  have hbad : ∀ᵐ t ∂μ, ∀ d ∈ D, ∀ n : ℕ, μ (B d n) = 0 → t ∉ B d n := by
    rw [ae_ball_iff hDc]
    intro d _
    rw [ae_all_iff]
    intro n
    by_cases h0 : μ (B d n) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with t ht _ using ht
    · exact Eventually.of_forall fun _ h => absurd h h0
  filter_upwards [hzS, hbad] with t htS htbad
  rw [mem_cspan]
  intro ζ hζ
  by_contra hne
  have hcont : ContinuousAt (fun v => ⟪ζ, v⟫_𝕜) (z t) :=
    (continuous_const.inner continuous_id).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hcont.eventually_ne hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hSD htS) (1 / (n + 1)) (by positivity)
  have hsub : B d n ⊆ {s | ⟪ζ, z s⟫_𝕜 ≠ 0} := by
    intro s hs
    apply hball
    have hs' : dist (z s) d < 1 / (n + 1) := hs
    rw [Metric.mem_ball]
    calc dist (z s) (z t) ≤ dist (z s) d + dist d (z t) := dist_triangle _ _ _
      _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add hs' (by rwa [dist_comm])
      _ < ε := by linarith
  have h0 : μ (B d n) = 0 := measure_mono_null hsub (ae_iff.1 hζ)
  exact htbad d hdD n h0 hd

/-- Any closed subspace containing `z t` for a.e. `t` contains the closed span. -/
theorem cspan_le_of_ae_mem [CompleteSpace E] {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (h : ∀ᵐ t ∂μ, z t ∈ K) : cspan 𝕜 μ z ≤ K := by
  have h1 : Kᗮ ≤ annihilator 𝕜 μ z := fun ζ hζ => by
    change ∀ᵐ t ∂μ, ⟪ζ, z t⟫_𝕜 = 0
    filter_upwards [h] with t ht
    exact Submodule.inner_left_of_mem_orthogonal ht hζ
  calc cspan 𝕜 μ z ≤ Kᗮᗮ := Submodule.orthogonal_le h1
    _ = K := by rw [Submodule.orthogonal_orthogonal_eq_closure, hK.submodule_topologicalClosure_eq]

/-- The paper's definition of `\cspan z` (`introduction.tex`): for an a.e. strongly measurable
signal in a Hilbert space, `cspan z` is the smallest closed subspace containing `z t` for
a.e. `t`. -/
theorem isLeast_cspan [CompleteSpace E] (hz : AEStronglyMeasurable z μ) :
    IsLeast {K : Submodule 𝕜 E | IsClosed (K : Set E) ∧ ∀ᵐ t ∂μ, z t ∈ K} (cspan 𝕜 μ z) :=
  ⟨⟨isClosed_cspan, ae_mem_cspan hz⟩, fun _ hK => cspan_le_of_ae_mem hK.1 hK.2⟩

/-! ### Bochner integrals stay in closed subspaces -/

section Integral

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The Bochner integral of a function with values a.e. in a closed subspace lies in that
subspace. -/
theorem integral_mem_of_ae_mem {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E)) {f : α → E}
    (hf : ∀ᵐ t ∂μ, f t ∈ K) : ∫ t, f t ∂μ ∈ K := by
  by_cases hfi : Integrable f μ
  · rw [← hK.submodule_topologicalClosure_eq, ← Submodule.orthogonal_orthogonal_eq_closure,
      Submodule.mem_orthogonal]
    intro ζ hζ
    rw [← integral_inner hfi]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf] with t ht
    exact Submodule.inner_left_of_mem_orthogonal ht hζ
  · rw [integral_undef hfi]
    exact K.zero_mem

/-- Weighted averages of an a.e. strongly measurable signal lie in its closed span. -/
theorem integral_smul_mem_cspan (hz : AEStronglyMeasurable z μ) (φ : α → 𝕜) :
    ∫ t, φ t • z t ∂μ ∈ cspan 𝕜 μ z := by
  refine integral_mem_of_ae_mem isClosed_cspan ?_
  filter_upwards [ae_mem_cspan (𝕜 := 𝕜) hz] with t ht
  exact Submodule.smul_mem _ _ ht

end Integral

/-! ### Images under continuous linear maps -/

section Image

variable [CompleteSpace E] [CompleteSpace F]

/-- `(T K)ᗮ = (T†)⁻¹ Kᗮ` for a continuous linear `T` between Hilbert spaces. -/
theorem orthogonal_map_eq_comap_adjoint (T : E →L[𝕜] F) (K : Submodule 𝕜 E) :
    (K.map (T : E →ₗ[𝕜] F))ᗮ = Kᗮ.comap (T† : F →ₗ[𝕜] E) := by
  ext ζ
  simp only [Submodule.mem_orthogonal, Submodule.mem_comap, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_right]

/-- `ζ` annihilates `T ∘ z` iff `T† ζ` annihilates `z`. -/
theorem annihilator_comp (T : E →L[𝕜] F) :
    annihilator 𝕜 μ (fun t => T (z t)) = (annihilator 𝕜 μ z).comap (T† : F →ₗ[𝕜] E) := by
  ext ζ
  simp only [Submodule.mem_comap, mem_annihilator, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_left]

/-- `cspan (T ∘ z) = closure (T (cspan z))` for a continuous linear `T`. -/
theorem cspan_comp (T : E →L[𝕜] F) :
    cspan 𝕜 μ (fun t => T (z t)) =
      ((cspan 𝕜 μ z).map (T : E →ₗ[𝕜] F)).topologicalClosure := by
  rw [cspan_def (z := fun t => T (z t)), annihilator_comp, ← orthogonal_cspan,
    ← orthogonal_map_eq_comap_adjoint, Submodule.orthogonal_orthogonal_eq_closure]

/-- For bounded-below `T`, `cspan (T ∘ z) = T (cspan z)` (Step 2 of `app:willems-gramian`). -/
theorem cspan_comp_of_isBoundedBelow {T : E →L[𝕜] F} (hT : IsBoundedBelow T) :
    cspan 𝕜 μ (fun t => T (z t)) = (cspan 𝕜 μ z).map (T : E →ₗ[𝕜] F) := by
  rw [cspan_comp, (hT.isClosed_map isClosed_cspan).submodule_topologicalClosure_eq]

/-- For bounded-below `T` and `cspan z = ⊤`, `cspan (T ∘ z) = range T` (Step 2 of
`app:willems-gramian`: `cspan (Γ z̄) = Γ (U × W) = im Γ`). -/
theorem cspan_comp_eq_range {T : E →L[𝕜] F} (hT : IsBoundedBelow T)
    (hz : cspan 𝕜 μ z = ⊤) : cspan 𝕜 μ (fun t => T (z t)) = T.range := by
  rw [cspan_comp_of_isBoundedBelow hT, hz, Submodule.map_top]

end Image

/-! ### Pairs: `WithLp 2 (E × F)` -/

section Prod

/-- On `WithLp 2 (E × F)` the inner product splits: `ζ` annihilates `z` iff
`⟪ζ.1, (z t).1⟫ + ⟪ζ.2, (z t).2⟫ = 0` a.e. -/
theorem mem_annihilator_prod {z : α → WithLp 2 (E × F)} {ζ : WithLp 2 (E × F)} :
    ζ ∈ annihilator 𝕜 μ z ↔
      ∀ᵐ t ∂μ, ⟪ζ.fst, (z t).fst⟫_𝕜 + ⟪ζ.snd, (z t).snd⟫_𝕜 = 0 :=
  Iff.rfl

/-- `(a, b)` annihilates `t ↦ (u t, x t)` iff `⟪a, u t⟫ + ⟪b, x t⟫ = 0` a.e.
(`def:hilbert-informative`). -/
theorem toLp_mem_annihilator_pair {u : α → E} {x : α → F} {a : E} {b : F} :
    WithLp.toLp 2 (a, b) ∈ annihilator 𝕜 μ (fun t => WithLp.toLp 2 (u t, x t)) ↔
      ∀ᵐ t ∂μ, ⟪a, u t⟫_𝕜 + ⟪b, x t⟫_𝕜 = 0 :=
  Iff.rfl

/-- Only `0` annihilates `t ↦ (u t, x t)` iff `⟪a, u t⟫ + ⟪b, x t⟫ = 0` a.e. forces
`a = 0` and `b = 0`. -/
theorem annihilator_pair_eq_bot_iff {u : α → E} {x : α → F} :
    annihilator 𝕜 μ (fun t => WithLp.toLp 2 (u t, x t)) = ⊥ ↔
      ∀ (a : E) (b : F), (∀ᵐ t ∂μ, ⟪a, u t⟫_𝕜 + ⟪b, x t⟫_𝕜 = 0) → a = 0 ∧ b = 0 := by
  rw [annihilator_eq_bot_iff]
  constructor
  · intro h a b hab
    simpa using h (WithLp.toLp 2 (a, b)) hab
  · intro h ζ hζ
    obtain ⟨ha, hb⟩ := h ζ.fst ζ.snd hζ
    rw [WithLp.ext_iff]
    exact Prod.ext ha hb

/-- The "equivalently" clause of `def:hilbert-informative`: `cspan (u, x) = U × H` iff
`⟪α, u t⟫ + ⟪β, x t⟫ = 0` a.e. forces `(α, β) = 0`. -/
theorem cspan_pair_eq_top_iff {u : α → E} {x : α → F} :
    cspan 𝕜 μ (fun t => WithLp.toLp 2 (u t, x t)) = ⊤ ↔
      ∀ (a : E) (b : F), (∀ᵐ t ∂μ, ⟪a, u t⟫_𝕜 + ⟪b, x t⟫_𝕜 = 0) → a = 0 ∧ b = 0 := by
  rw [cspan_eq_top_iff, annihilator_pair_eq_bot_iff]

end Prod

end DataDrivenControl
