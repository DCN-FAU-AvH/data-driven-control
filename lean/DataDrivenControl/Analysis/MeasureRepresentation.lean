module

public import Mathlib

/-!
# Measure representation of bounded maps on continuous histories

Paper: `ex:intro-delay` takes `L`, `M`, `C` to be arbitrary bounded linear maps on
`C([-h, 0]; ℝⁿ)` and assumes that the measure representing `M` has no mass at `0`.  This file
passes from such bounded maps to finite sums of integrals against finite positive measures, the
delay functionals of `Examples/Delay` (`Delay.exists_model`).

## Main results

* `exists_le_nnrealLinear`: a functional on `C_c(X, ℝ≥0)` that is bounded above on order
  intervals is dominated by the positive functional `Λ⁺ u = sup {Λ g : g ≤ u}` (additive by the
  Riesz decomposition `g = g ⊓ u + (g - g ⊓ u)`);
* `exists_eq_integral_sub_integral` (Riesz): for `X` compact Hausdorff, every bounded
  `Λ : C(X, ℝ) → ℝ` is `f ↦ ∫ f dμ - ∫ f dν` with finite measures `μ`, `ν` (the
  Riesz–Markov–Kakutani theorem `RealRMK.integral_rieszMeasure` applied to `Λ⁺` and `Λ⁺ - Λ`);
* `exists_eq_sum_integral`: for finite-dimensional real inner product spaces `E`, `F`, every
  bounded `T : C(X, E) → F` is `φ ↦ ∑ₖ Pₖ ∫ φ dμₖ` with `Pₖ : E →L[ℝ] F` and finite measures `μₖ`
  (coordinates in orthonormal bases);
* `exists_eq_sum_integral_delay`: on histories, `T φ = ∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ)` with finite measures
  `μₖ` on `ℝ` carried by the delays `[0, h]`, where `φ(-δ)` is `IccExtend _ φ (-δ)`.  On the
  history `ψ(s) = φ(s - h)` this reads `∑ₖ Pₖ ∫ ψ(h - δ) dμₖ(δ)`;
* `NoMassAtZero T`: `T` is uniformly small on histories that vanish before `-η`, as `η → 0`;
  `noMassAtZero_iff`: this holds iff `T` has a representation as above with `μₖ {0} = 0` for
  all `k`, so it is exactly the condition that the representing measure has no atom at `0`.

Mathlib provides the Riesz–Markov–Kakutani theorem for positive functionals; the decomposition of
a bounded functional into positive ones is `exists_le_nnrealLinear`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology CompactlySupportedContinuousMap
open scoped NNReal CompactlySupported InnerProductSpace

noncomputable section

namespace DataDrivenControl

/-! ### Domination by a positive functional -/

section Domination

variable {X : Type*} [TopologicalSpace X] (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ)

/-- `u ↦ sup {Λ g : g ≤ u}`: the positive part of `Λ` on nonnegative functions. -/
def supBelow (u : C_c(X, ℝ≥0)) : ℝ := sSup (Λ '' Iic u)

variable {Λ}

/-- Every `Λ g` with `g ≤ u` is below `supBelow Λ u`. -/
theorem le_supBelow (hΛ : ∀ u, BddAbove (Λ '' Iic u)) {g u : C_c(X, ℝ≥0)} (hg : g ≤ u) :
    Λ g ≤ supBelow Λ u :=
  le_csSup (hΛ u) (mem_image_of_mem _ hg)

/-- `supBelow Λ u` is the least upper bound of the `Λ g` with `g ≤ u`. -/
theorem supBelow_le {u : C_c(X, ℝ≥0)} {c : ℝ} (h : ∀ g ≤ u, Λ g ≤ c) : supBelow Λ u ≤ c :=
  csSup_le ⟨_, mem_image_of_mem _ (le_refl u)⟩ (forall_mem_image.2 h)

/-- `supBelow Λ` is additive (Riesz decomposition). -/
theorem supBelow_add (hΛ : ∀ u, BddAbove (Λ '' Iic u)) (u v : C_c(X, ℝ≥0)) :
    supBelow Λ (u + v) = supBelow Λ u + supBelow Λ v := by
  refine le_antisymm (supBelow_le fun g hg => ?_) ?_
  · obtain ⟨g₂, hg₂⟩ :=
      CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ u ≤ g)
    have h₂ : g₂ ≤ v := fun x => by
      have h1 : ((g x ⊓ u x : ℝ≥0) : ℝ) + g₂ x = g x := by exact_mod_cast congr($hg₂ x)
      have h2 : (g x : ℝ) ≤ u x + v x := by exact_mod_cast hg x
      rw [← NNReal.coe_le_coe]
      rcases le_total (g x) (u x) with h | h
      · rw [inf_of_le_left h] at h1
        linarith [(v x).2]
      · rw [inf_of_le_right h] at h1
        linarith
    rw [← hg₂, map_add]
    exact add_le_add (le_supBelow hΛ inf_le_right) (le_supBelow hΛ h₂)
  · rw [← le_sub_iff_add_le]
    refine supBelow_le fun g hg => ?_
    rw [le_sub_comm]
    refine supBelow_le fun g' hg' => ?_
    rw [le_sub_iff_add_le', ← map_add]
    exact le_supBelow hΛ (add_le_add hg hg')

/-- `supBelow Λ` is positively homogeneous. -/
theorem supBelow_smul (hΛ : ∀ u, BddAbove (Λ '' Iic u)) (c : ℝ≥0) (u : C_c(X, ℝ≥0)) :
    supBelow Λ (c • u) = c * supBelow Λ u := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine le_antisymm (supBelow_le fun g hg => ?_) ?_
    · rw [show g = 0 from le_antisymm (by simpa using hg) fun _ => zero_le]
      simp
    · rw [zero_smul, NNReal.coe_zero, zero_mul, ← map_zero Λ]
      exact le_supBelow hΛ le_rfl
  have hc' : (0 : ℝ) < c := by positivity
  refine le_antisymm (supBelow_le fun g hg => ?_) ?_
  · have hg' : c⁻¹ • g ≤ u := fun x => by
      have := hg x
      simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
      rwa [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
    calc Λ g = c * Λ (c⁻¹ • g) := by
          rw [map_smul, NNReal.smul_def, smul_eq_mul, ← mul_assoc, NNReal.coe_inv,
            mul_inv_cancel₀ hc'.ne', one_mul]
      _ ≤ c * supBelow Λ u := mul_le_mul_of_nonneg_left (le_supBelow hΛ hg') hc'.le
  · rw [← le_div_iff₀' hc']
    refine supBelow_le fun g hg => ?_
    rw [le_div_iff₀' hc', ← smul_eq_mul, ← NNReal.smul_def, ← map_smul]
    refine le_supBelow hΛ fun x => ?_
    simpa using mul_le_mul_of_nonneg_left (hg x) (zero_le (a := c))

/-- An `ℝ≥0`-linear functional on `C_c(X, ℝ≥0)` that is bounded above on order intervals is
dominated by a positive one. -/
theorem exists_le_nnrealLinear (hΛ : ∀ u, BddAbove (Λ '' Iic u)) :
    ∃ P : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0, ∀ u, Λ u ≤ P u :=
  ⟨{ toFun := fun u => ⟨supBelow Λ u, by
        simpa using le_supBelow hΛ (show (0 : C_c(X, ℝ≥0)) ≤ u from fun _ => zero_le)⟩
     map_add' := fun u v => NNReal.eq (supBelow_add hΛ u v)
     map_smul' := fun c u => NNReal.eq (supBelow_smul hΛ c u) },
    fun u => le_supBelow hΛ le_rfl⟩

end Domination

/-! ### Representation on a compact space -/

section Compact

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- **Riesz representation** of a bounded functional on `C(X, ℝ)`, `X` compact Hausdorff, as the
difference of the integrals against two finite measures. -/
theorem exists_eq_integral_sub_integral (Λ : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ μ ν : Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
      ∀ f : C(X, ℝ), Λ f = ∫ x, f x ∂μ - ∫ x, f x ∂ν := by
  let L : C_c(X, ℝ) →ₗ[ℝ] ℝ := Λ.toLinearMap ∘ₗ
    { toFun := fun f => f.toContinuousMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hbdd : ∀ u : C_c(X, ℝ≥0), BddAbove ((L.restrictScalars ℝ≥0 ∘ₗ toRealLinearMap) '' Iic u) :=
    fun u => ⟨‖Λ‖ * ‖u.toReal.toContinuousMap‖, forall_mem_image.2 fun g hg => by
      refine (Real.le_norm_self _).trans ((Λ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_)
          (norm_nonneg _)))
      refine le_trans ?_ (u.toReal.toContinuousMap.norm_coe_le_norm x)
      simpa using hg x⟩
  obtain ⟨P, hP⟩ := exists_le_nnrealLinear hbdd
  let P' := toRealPositiveLinear P
  have hP' (f : C_c(X, ℝ)) (hf : 0 ≤ f) : L f ≤ P' f := by
    have hf' : (nnrealPart f).toReal = f := by ext x; simpa using hf x
    rw [toRealPositiveLinear_apply, nnrealPart_neg_eq_zero_of_nonneg hf, map_zero,
      NNReal.coe_zero, sub_zero]
    simpa [hf'] using hP (nnrealPart f)
  let N : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ (P'.toLinearMap - L) fun f hf => sub_nonneg.2 (hP' f hf)
  refine ⟨RealRMK.rieszMeasure P', RealRMK.rieszMeasure N, inferInstance, inferInstance,
    fun f => ?_⟩
  have h₁ : ∫ x, f x ∂RealRMK.rieszMeasure P' = P' (continuousMapEquiv f) :=
    RealRMK.integral_rieszMeasure P' (continuousMapEquiv f)
  have h₂ : ∫ x, f x ∂RealRMK.rieszMeasure N = N (continuousMapEquiv f) :=
    RealRMK.integral_rieszMeasure N (continuousMapEquiv f)
  rw [h₁, h₂]
  exact (sub_sub_cancel _ _).symm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Riesz representation** of a bounded linear map `C(X, E) → F` between finite-dimensional
spaces: `T φ = ∑ₖ Pₖ ∫ φ dμₖ` with finitely many finite measures `μₖ`. -/
theorem exists_eq_sum_integral (T : C(X, E) →L[ℝ] F) :
    ∃ (N : ℕ) (P : Fin N → E →L[ℝ] F) (μ : Fin N → Measure X), (∀ k, IsFiniteMeasure (μ k)) ∧
      ∀ φ : C(X, E), T φ = ∑ k, P k (∫ x, φ x ∂μ k) := by
  let b := stdOrthonormalBasis ℝ E
  let c := stdOrthonormalBasis ℝ F
  let up i : C(X, ℝ) →L[ℝ] C(X, E) :=
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLeftContinuous ℝ X
  let down i : C(X, E) →L[ℝ] C(X, ℝ) := (innerSL ℝ (b i)).compLeftContinuous ℝ X
  choose μ ν hμ hν hΛ using fun ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ F) =>
    exists_eq_integral_sub_integral (innerSL ℝ (c ij.2) ∘L T ∘L up ij.1)
  let P (k : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ F)) × Bool) : E →L[ℝ] F :=
    (if k.2 then 1 else -1 : ℝ) • (innerSL ℝ (b k.1.1)).smulRight (c k.1.2)
  let m (k : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ F)) × Bool) : Measure X :=
    if k.2 then μ k.1 else ν k.1
  let e := Fintype.equivFin ((Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ F)) × Bool)
  refine ⟨_, fun k => P (e.symm k), fun k => m (e.symm k), fun k => ?_, fun φ => ?_⟩
  · dsimp only [m]
    split <;> infer_instance
  rw [e.symm.sum_comp (fun k => P k (∫ x, φ x ∂m k))]
  have hφ : φ = ∑ i, up i (down i φ) := by ext x; simp [up, down, b.sum_repr']
  have key j : ⟪c j, T φ⟫_ℝ =
      ∑ i, (⟪b i, ∫ x, φ x ∂μ (i, j)⟫_ℝ - ⟪b i, ∫ x, φ x ∂ν (i, j)⟫_ℝ) := by
    conv_lhs => rw [hφ]
    simp only [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hint {ρ : Measure X} [IsFiniteMeasure ρ] : Integrable φ ρ :=
      φ.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
    rw [← integral_inner hint, ← integral_inner hint]
    exact hΛ (i, j) (down i φ)
  conv_lhs => rw [← c.sum_repr' (T φ)]
  simp only [key, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [P, m]
  module

end Compact

/-! ### Bounded maps on continuous histories -/

section Delay

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {h : ℝ}

/-- The extension of a history is bounded by its norm. -/
theorem norm_IccExtend_le (h0 : -h ≤ 0) (φ : C(Icc (-h) 0, E)) (x : ℝ) :
    ‖IccExtend h0 φ x‖ ≤ ‖φ‖ := by
  rw [IccExtend_apply]
  exact φ.norm_coe_le_norm _

/-- The extended history, read backwards, is integrable against a finite measure. -/
theorem integrable_IccExtend_neg (h0 : -h ≤ 0) (φ : C(Icc (-h) 0, E)) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : Integrable (fun δ => IccExtend h0 φ (-δ)) μ :=
  .of_bound ((continuous_IccExtend_iff.2 φ.continuous).comp continuous_neg).aestronglyMeasurable
    ‖φ‖ (ae_of_all _ fun _ => norm_IccExtend_le h0 φ _)

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Riesz representation** of a bounded map on continuous histories:
`T φ = ∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ)` with finite measures `μₖ` on the delays `δ ∈ [0, h]`. -/
theorem exists_eq_sum_integral_delay (hh : 0 < h) (T : C(Icc (-h) 0, E) →L[ℝ] F) :
    ∃ (N : ℕ) (P : Fin N → E →L[ℝ] F) (μ : Fin N → Measure ℝ), (∀ k, IsFiniteMeasure (μ k)) ∧
      (∀ k, μ k (Icc 0 h)ᶜ = 0) ∧
      ∀ φ : C(Icc (-h) 0, E),
        T φ = ∑ k, P k (∫ δ, IccExtend (neg_nonpos.2 hh.le) φ (-δ) ∂μ k) := by
  obtain ⟨N, P, μ, hμ, hT⟩ := exists_eq_sum_integral T
  have hneg : Measurable fun s : Icc (-h) 0 => -(s : ℝ) := measurable_subtype_coe.neg
  refine ⟨N, P, fun k => (μ k).map fun s : Icc (-h) 0 => -(s : ℝ), fun k => inferInstance,
    fun k => ?_, fun φ => ?_⟩
  · rw [Measure.map_apply hneg measurableSet_Icc.compl]
    exact measure_mono_null
      (fun s hs => absurd ⟨by linarith [s.2.2], by linarith [s.2.1]⟩ hs) measure_empty
  · rw [hT]
    refine Finset.sum_congr rfl fun k _ => congrArg (P k) ?_
    dsimp only
    rw [integral_map (f := fun δ => IccExtend (neg_nonpos.2 hh.le) φ (-δ)) hneg.aemeasurable
      ((continuous_IccExtend_iff.2 φ.continuous).comp continuous_neg).aestronglyMeasurable]
    simp

/-- `T` has **no mass at delay `0`**: it is uniformly small on the histories that vanish before
`-η`, for small `η > 0`. -/
def NoMassAtZero (T : C(Icc (-h) 0, E) →L[ℝ] F) : Prop :=
  ∀ ε > 0, ∃ η > 0, ∀ φ : C(Icc (-h) 0, E), (∀ s : Icc (-h) 0, (s : ℝ) < -η → φ s = 0) →
    ‖T φ‖ ≤ ε * ‖φ‖

/-- **No mass at delay `0`.** A bounded map on continuous histories has no mass at delay `0` iff
it has a representation `T φ = ∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ)` whose measures have no atom at `0`. -/
theorem noMassAtZero_iff (hh : 0 < h) (T : C(Icc (-h) 0, E) →L[ℝ] F) :
    NoMassAtZero T ↔ ∃ (N : ℕ) (P : Fin N → E →L[ℝ] F) (μ : Fin N → Measure ℝ),
      (∀ k, IsFiniteMeasure (μ k)) ∧ (∀ k, μ k (Icc 0 h)ᶜ = 0) ∧ (∀ k, μ k {0} = 0) ∧
      ∀ φ : C(Icc (-h) 0, E),
        T φ = ∑ k, P k (∫ δ, IccExtend (neg_nonpos.2 hh.le) φ (-δ) ∂μ k) := by
  have h0 : -h ≤ 0 := neg_nonpos.2 hh.le
  constructor
  · intro hT
    obtain ⟨N, P, μ, hμ, hsupp, hrep⟩ := exists_eq_sum_integral_delay hh T
    -- The atoms at `0` cancel: test `T` on the tents `φₙ(s) = max 0 (1 + (n + 1) s) • v`.
    have hatom (v : E) : ∑ k, P k ((μ k).real {0} • v) = 0 := by
      let φ (n : ℕ) : C(Icc (-h) 0, E) :=
        ⟨fun s => max 0 (1 + (n + 1) * (s : ℝ)) • v, by fun_prop⟩
      have hφ (n : ℕ) (s : Icc (-h) 0) : ‖φ n s‖ ≤ ‖v‖ := by
        have : 1 + (n + 1) * (s : ℝ) ≤ 1 := by nlinarith [s.2.2]
        change ‖max 0 (1 + (n + 1) * (s : ℝ)) • v‖ ≤ ‖v‖
        rw [norm_smul, Real.norm_of_nonneg (le_max_left _ _)]
        exact mul_le_of_le_one_left (norm_nonneg v) (max_le zero_le_one this)
      refine tendsto_nhds_unique (f := fun n => T (φ n)) (l := atTop) ?_ ?_
      · simp only [hrep]
        refine tendsto_finsetSum _ fun k _ => ((P k).continuous.tendsto _).comp ?_
        rw [← integral_indicator_const v (measurableSet_singleton 0)]
        refine tendsto_integral_of_dominated_convergence (fun _ => ‖v‖)
          (fun n => (integrable_IccExtend_neg h0 (φ n) (μ k)).aestronglyMeasurable)
          (integrable_const _) (fun n => ae_of_all _ fun δ => norm_IccExtend_le h0 _ _ |>.trans
            ((ContinuousMap.norm_le _ (norm_nonneg _)).2 (hφ n))) ?_
        filter_upwards [ae_iff.2 (hsupp k)] with δ hδ
        rcases hδ.1.eq_or_lt with rfl | hpos
        · simp [φ]
        · rw [indicator_of_notMem (by simpa using hpos.ne')]
          obtain ⟨n₀, hn₀⟩ := exists_nat_gt δ⁻¹
          refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩)
          have : 1 + (n + 1) * -δ ≤ 0 := by
            have := (inv_lt_iff_one_lt_mul₀ hpos).1 (hn₀.trans_le (Nat.cast_le.2 hn))
            nlinarith
          dsimp only
          rw [IccExtend_of_mem _ _ ⟨by linarith [hδ.2], by linarith⟩]
          change 0 = max 0 (1 + (n + 1) * -δ) • v
          rw [max_eq_left this, zero_smul]
      · refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
        obtain ⟨η, hη, hTη⟩ := hT (ε / (‖v‖ + 1)) (by positivity)
        obtain ⟨n₀, hn₀⟩ := exists_nat_gt η⁻¹
        refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
        have hvan : ∀ s : Icc (-h) 0, (s : ℝ) < -η → φ n s = 0 := fun s hs => by
          have := (inv_lt_iff_one_lt_mul₀ hη).1 (hn₀.trans_le (Nat.cast_le.2 hn))
          have : 1 + (n + 1) * (s : ℝ) ≤ 0 := by nlinarith
          simp [φ, max_eq_left this]
        calc ‖T (φ n)‖ ≤ ε / (‖v‖ + 1) * ‖φ n‖ := hTη _ hvan
          _ ≤ ε / (‖v‖ + 1) * ‖v‖ := by
            gcongr
            exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 (hφ n)
          _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg v]
    refine ⟨N, P, fun k => (μ k).restrict {0}ᶜ, fun k => inferInstance, fun k => ?_, fun k => ?_,
      fun φ => ?_⟩
    · rw [Measure.restrict_apply measurableSet_Icc.compl]
      exact measure_mono_null inter_subset_left (hsupp k)
    · rw [Measure.restrict_apply (measurableSet_singleton 0)]
      simp
    · have hsplit k : ∫ δ, IccExtend h0 φ (-δ) ∂μ k =
          ∫ δ in {0}ᶜ, IccExtend h0 φ (-δ) ∂μ k + (μ k).real {0} • IccExtend h0 φ (-0) := by
        rw [← integral_add_compl (measurableSet_singleton 0) (integrable_IccExtend_neg h0 φ _),
          integral_singleton, add_comm]
      simp only [hrep, hsplit, map_add, Finset.sum_add_distrib, hatom, add_zero]
  · rintro ⟨N, P, μ, hμ, hsupp, hzero, hrep⟩ ε hε
    have hlim : Tendsto (fun η => ∑ k, ‖P k‖ * (μ k).real (Icc (0 - η) (0 + η))) (𝓝[>] 0)
        (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ fun k _ =>
        ((ENNReal.tendsto_toReal (by simp [hzero k])).comp
          (tendsto_measure_Icc_nhdsWithin_right' (μ k) 0)).const_mul ‖P k‖
      simpa [hzero, measureReal_def] using this
    obtain ⟨η, hηε, hη⟩ :=
      ((hlim.eventually (gt_mem_nhds hε)).and (Ioo_mem_nhdsGT hh)).exists
    refine ⟨η, hη.1, fun φ hφ => ?_⟩
    have hk k : ‖∫ δ, IccExtend h0 φ (-δ) ∂μ k‖ ≤ ‖φ‖ * (μ k).real (Icc (0 - η) (0 + η)) := by
      rw [← setIntegral_eq_integral_of_ae_compl_eq_zero ?_]
      · exact norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
          fun δ _ => norm_IccExtend_le h0 φ _
      filter_upwards [ae_iff.2 (hsupp k)] with δ hδ hδη
      have : η < δ := by
        by_contra hle
        exact hδη ⟨by linarith [hδ.1], by linarith⟩
      rw [IccExtend_of_mem _ _ ⟨by linarith [hδ.2], by linarith [hδ.1]⟩]
      exact hφ _ (by simpa using this)
    calc ‖T φ‖ ≤ ∑ k, ‖P k‖ * (‖φ‖ * (μ k).real (Icc (0 - η) (0 + η))) := by
          rw [hrep]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact (P k).le_opNorm_of_le (hk k)
      _ = ‖φ‖ * ∑ k, ‖P k‖ * (μ k).real (Icc (0 - η) (0 + η)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ε * ‖φ‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hηε.le (norm_nonneg _)

end Delay

end DataDrivenControl
