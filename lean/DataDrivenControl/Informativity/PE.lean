module

public import DataDrivenControl.Informativity.Window
public import DataDrivenControl.Signal.WeakDerivative

/-!
# Persistency of excitation

Paper: `def:PE`, the remark on regular inputs after it (Gramian of the derivatives),
`lem:window-pe-necessary` (`app:window-pe-necessity`).

## Main declarations

* `PersistentlyExciting T L ū` (`def:PE`): `ū` is persistently exciting of order `L` on
  `I = (0, T)`: if `ζ₀, …, ζ_{L-1} ∈ U` satisfy `∑ₖ ⟪ζₖ, Dᵏ ū⟫ = 0` in `𝒟'(I)`, then all
  `ζₖ = 0`.  The distribution `⟪ζₖ, Dᵏ ū⟫` is `φ ↦ ⟪ζₖ, derivMoment k ū φ⟫`
  (`Signal/TestFunction`); "`= 0` in `𝒟'(I)`" is "for every `φ` with
  `IsTestFunction T φ`".  The coefficients are a family `ζ : Fin L → U`.
* `PersistentlyExcitingInfinite T ū` (`def:PE`): persistently exciting of every finite order.
  Order `0` is vacuous (`persistentlyExciting_zero`), so "every `L ≥ 1`" and "every `L`" agree.
* `PersistentlyExciting.of_le`, `PersistentlyExciting.mono`, `PersistentlyExciting.congr_ae`:
  lower orders, longer windows, a.e. equal inputs.
* `persistentlyExciting_iff_injective_gramian` (the remark after `def:PE`): for
  `ū ∈ H^{L-1}(I; U)` with weak derivatives `v 1, …, v (L-1)` (`v 0 = ū`, `HasWeakDeriv`), `ū` is
  persistently exciting of order `L` iff the Gramian `𝒢(ū, ū', …, ū^{(L-1)})` on
  `U^L = PiLp 2 (fun _ : Fin L => U)` is injective.  (That `Dᵏ ū = ū⁽ᵏ⁾` is
  `derivMoment_eq_integral_of_hasWeakDeriv` in `Signal/WeakDerivative`; the finite-dimensional
  "coercivity" reading is `gramian_injective_iff_coercive` in `Signal/Gramian`.)
* `WindowInformative.persistentlyExcitingInfinite` (`lem:window-pe-necessary`): a window
  informative record `(ū, x̄)` on `(0, T + T')` has `ū` persistently exciting of infinite order
  on `(0, T + T')`.

## Upstream results used

`IsTestFunction.mono`, `IsTestFunction.comp_sub`, `exists_isTestFunction_ne_zero`,
`IsTestFunction.iteratedDeriv`, `derivMoment_comp_add`, `ae_eq_zero_of_integral_smul_eq_zero`
(`Signal/TestFunction`); `derivMoment_eq_integral_of_hasWeakDeriv`, `HasWeakDeriv.memLp_deriv`,
`IsTestFunction.eq_zero_of_sum_iteratedDeriv_smul_eq_zero` (`Signal/WeakDerivative`);
`gramian_injective_iff` (`Signal/Gramian`); `denseRange_shiftSynth_of_windowSynth`,
`denseRange_shiftSynth_iff` (`Signal/Shift`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- **Persistency of excitation of order `L`** (`def:PE`): `ū` is persistently exciting of order
`L` on `I = (0, T)` if whenever `ζ₀, …, ζ_{L-1} ∈ U` satisfy
`∑_{k < L} ⟪ζₖ, Dᵏ ū⟫_U = 0` in `𝒟'(I)`, that is,
`∑_{k < L} ⟪ζₖ, ⟨Dᵏ ū, φ⟩⟫ = 0` for every test function `φ ∈ 𝒟(I)`, then
`ζ₀ = ⋯ = ζ_{L-1} = 0`.  Here `⟨Dᵏ ū, φ⟩ = (-1)ᵏ ∫ ū φ⁽ᵏ⁾` is `derivMoment k ū φ`.  The paper
assumes `ū ∈ L²(I; U)`; lemmas carry the `MemLp` hypothesis. -/
def PersistentlyExciting (T : ℝ) (L : ℕ) (u : ℝ → U) : Prop :=
  ∀ ζ : Fin L → U,
    (∀ φ : ℝ → ℝ, IsTestFunction T φ →
      ∑ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) u φ⟫_ℝ = 0) →
    ζ = 0

/-- **Persistency of excitation of infinite order** (`def:PE`): `ū` is persistently exciting
of every finite order `L` (order `0` is vacuous, `persistentlyExciting_zero`). -/
def PersistentlyExcitingInfinite (T : ℝ) (u : ℝ → U) : Prop :=
  ∀ L : ℕ, PersistentlyExciting T L u

variable {T : ℝ} {L : ℕ} {u : ℝ → U}

/-- Persistency of excitation of order `0` holds trivially. -/
theorem persistentlyExciting_zero : PersistentlyExciting T 0 u :=
  fun ζ _ => Subsingleton.elim ζ 0

theorem PersistentlyExcitingInfinite.persistentlyExciting (h : PersistentlyExcitingInfinite T u)
    (L : ℕ) : PersistentlyExciting T L u :=
  h L

/-- Persistency of excitation of order `L` implies it for every lower order `L' ≤ L` (extend
the coefficients by zero). -/
theorem PersistentlyExciting.of_le {L' : ℕ} (h : PersistentlyExciting T L u) (hL : L' ≤ L) :
    PersistentlyExciting T L' u := by
  intro ζ hζ
  let ζ' : Fin L → U := fun k => if hk : (k : ℕ) < L' then ζ ⟨k, hk⟩ else 0
  have hζ' : ζ' = 0 := by
    refine h ζ' fun φ hφ => ?_
    let F : ℕ → ℝ := fun k => if hk : k < L' then ⟪ζ ⟨k, hk⟩, derivMoment k u φ⟫_ℝ else 0
    have h1 : ∑ k : Fin L, ⟪ζ' k, derivMoment (k : ℕ) u φ⟫_ℝ = ∑ k : Fin L, F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [ζ', F]
      split_ifs <;> simp
    have h2 : ∑ k : Fin L', ⟪ζ k, derivMoment (k : ℕ) u φ⟫_ℝ = ∑ k : Fin L', F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [F, k.2]
    rw [h1, Fin.sum_univ_eq_sum_range F, ← Finset.sum_subset (Finset.range_subset_range.2 hL),
      ← Fin.sum_univ_eq_sum_range F, ← h2, hζ φ hφ]
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [F, show ¬ k < L' by omega]
  funext k
  have := congrFun hζ' (Fin.castLE hL k)
  simpa [ζ', k.2] using this

/-- Persistency of excitation on `(0, T)` gives it on every longer window `(0, T')`: test
functions on `(0, T)` are test functions on `(0, T')`. -/
theorem PersistentlyExciting.mono {T' : ℝ} (h : PersistentlyExciting T L u) (hT : T ≤ T') :
    PersistentlyExciting T' L u :=
  fun ζ hζ => h ζ fun φ hφ => hζ φ (hφ.mono hT)

theorem PersistentlyExcitingInfinite.mono {T' : ℝ} (h : PersistentlyExcitingInfinite T u)
    (hT : T ≤ T') : PersistentlyExcitingInfinite T' u :=
  fun L => (h L).mono hT

/-- Persistency of excitation only depends on the input a.e. on the window. -/
theorem PersistentlyExciting.congr_ae {u' : ℝ → U} (h : PersistentlyExciting T L u)
    (hu : u =ᵐ[μI T] u') : PersistentlyExciting T L u' := by
  intro ζ hζ
  refine h ζ fun φ hφ => ?_
  have e : ∀ k : ℕ, derivMoment k u φ = derivMoment k u' φ := by
    intro k
    rw [hφ.derivMoment_eq_setIntegral, hφ.derivMoment_eq_setIntegral]
    congr 1
    exact integral_congr_ae (hu.mono fun t ht => by simp only [ht])
  simp only [e]
  exact hζ φ hφ

/-- **Regular inputs** (the remark after `def:PE`): let `ū = v 0 ∈ H^{L-1}(I; U)`, with
successive weak derivatives `v 1, …, v (L-1)` (`HasWeakDeriv T (v j) (v (j + 1))` for
`j + 1 < L`), so that `Dᵏ ū = ū⁽ᵏ⁾ = v k` for `k ≤ L - 1`.  Then `ū` is persistently exciting
of order `L` iff the Gramian `𝒢(ū, ū', …, ū^{(L-1)})` of the signal
`t ↦ (v 0 t, …, v (L-1) t)` is injective on `U^L` (with the `ℓ²` product inner product,
`PiLp 2`). -/
theorem persistentlyExciting_iff_injective_gramian [CompleteSpace U] {v : ℕ → ℝ → U}
    (hv0 : MemLp (v 0) 2 (μI T)) (hv : ∀ j, j + 1 < L → HasWeakDeriv T (v j) (v (j + 1))) :
    PersistentlyExciting T L (v 0) ↔
      Function.Injective
        (gramian ℝ (μI T) (fun t => WithLp.toLp 2 (fun k : Fin L => v k t) :
          ℝ → PiLp 2 (fun _ : Fin L => U))) := by
  set z : ℝ → PiLp 2 (fun _ : Fin L => U) := fun t => WithLp.toLp 2 (fun k : Fin L => v k t)
    with hzdef
  have hmem : ∀ k : Fin L, MemLp (v k) 2 (μI T) := by
    rintro ⟨k, hk⟩
    cases k with
    | zero => exact hv0
    | succ j => exact (hv j hk).memLp_deriv
  have hz : MemLp z 2 (μI T) := memLp_piLp_iff.2 fun k => by simpa [z] using hmem k
  -- `∑ₖ ⟪ζₖ, Dᵏ ū⟫` tested against `φ` is `∫ φ ⟪ζ, z⟫`
  have key : ∀ (ζ : Fin L → U) (φ : ℝ → ℝ), IsTestFunction T φ →
      ∑ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) (v 0) φ⟫_ℝ =
        ∫ t, φ t • ⟪(WithLp.toLp 2 ζ : PiLp 2 (fun _ : Fin L => U)), z t⟫_ℝ := by
    intro ζ φ hφ
    have hint : ∀ k : Fin L, Integrable (fun t => φ t • v k t) :=
      fun k => hφ.integrable_smul ((hmem k).integrable one_le_two)
    have hd : ∀ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) (v 0) φ⟫_ℝ =
        ∫ t, ⟪ζ k, φ t • v k t⟫_ℝ := by
      intro k
      rw [derivMoment_eq_integral_of_hasWeakDeriv hφ k fun j hj => hv j (by omega),
        integral_inner (hint k)]
    simp only [hd]
    rw [← integral_finsetSum _ fun k _ => (hint k).const_inner (ζ k)]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [z, PiLp.inner_apply, real_inner_smul_right, smul_eq_mul, Finset.mul_sum]
  have hint' : ∀ ζ : PiLp 2 (fun _ : Fin L => U), Integrable (fun t => ⟪ζ, z t⟫_ℝ) (μI T) :=
    fun ζ => (hz.integrable one_le_two).const_inner ζ
  rw [gramian_injective_iff hz, Submodule.eq_bot_iff]
  constructor
  · intro hPE ζ hζ
    rw [mem_annihilator] at hζ
    have h0 := hPE (WithLp.ofLp ζ) fun φ hφ => by
      rw [key _ φ hφ, hφ.integral_smul_eq_setIntegral]
      exact integral_eq_zero_of_ae (hζ.mono fun t ht => by simp [ht])
    have : ζ = WithLp.toLp 2 (WithLp.ofLp ζ) := rfl
    rw [this, h0]
    rfl
  · intro hann ζ hζ
    have hmemζ : (WithLp.toLp 2 ζ : PiLp 2 (fun _ : Fin L => U)) ∈ annihilator ℝ (μI T) z := by
      rw [mem_annihilator]
      exact ae_eq_zero_of_integral_smul_eq_zero (hint' _) fun φ hφ => by rw [← key ζ φ hφ, hζ φ hφ]
    have := hann _ hmemζ
    funext k
    exact congrArg (fun w : PiLp 2 (fun _ : Fin L => U) => w k) this

/-- **Window informativity forces excitation of infinite order** (`lem:window-pe-necessary`):
if the record `(ū, x̄)` is window informative on `(0, T + T')` (`WindowInformative T T' ū x̄`),
then `ū` is persistently exciting of infinite order on `(0, T + T')`.  Only the input windows
matter: `x̄` is arbitrary. -/
theorem WindowInformative.persistentlyExcitingInfinite [CompleteSpace U] {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {T' : ℝ} {x : ℝ → X}
    (hT : 0 < T) (hu : MemLp u 2 (μI (T + T'))) (h : WindowInformative T T' u x) :
    PersistentlyExcitingInfinite (T + T') u := by
  intro L ζ hζ
  by_contra hne
  have htot := (denseRange_shiftSynth_iff hu).1 (denseRange_shiftSynth_of_windowSynth h)
  obtain ⟨ψ, hψ, hψ0⟩ := exists_isTestFunction_ne_zero hT
  -- `g = ∑ₖ (-1)ᵏ ψ⁽ᵏ⁾ ζₖ` is a nonzero element of `L²(0, T; U)` orthogonal to every window
  set ζ' : Fin L → U := fun k => ((-1 : ℝ) ^ (k : ℕ)) • ζ k with hζ'def
  have hζ' : ζ' ≠ 0 := by
    intro h0
    apply hne
    funext k
    have := congrFun h0 k
    simpa [ζ'] using this
  set g : ℝ → U := fun t => ∑ k : Fin L, iteratedDeriv k ψ t • ζ' k with hgdef
  have hg_cont : Continuous g :=
    continuous_finsetSum _ fun k _ => (hψ.iteratedDeriv k).continuous.smul continuous_const
  have hg_mem : MemLp g 2 (μI T) := by
    refine memLp_finsetSum (f := fun (k : Fin L) t => iteratedDeriv k ψ t • ζ' k) _ fun k _ => ?_
    obtain ⟨C, hC⟩ := (hψ.iteratedDeriv k).continuous.bounded_above_of_compact_support
      (hψ.iteratedDeriv k).hasCompactSupport
    exact MemLp.of_bound ((hψ.iteratedDeriv k).continuous.smul
      continuous_const).aestronglyMeasurable (C * ‖ζ' k‖) (ae_of_all _ fun t => by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))
  have hG : hg_mem.toLp g = 0 := by
    refine htot _ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hw : Integrable (fun t => u (t + s)) (μI T) := by
      have := (memLp_comp_add hu hs.1.le (by linarith [hs.2] : s + T ≤ T + T')).integrable
        one_le_two
      simpa only [add_comm s] using this
    have hint : ∀ k : Fin L, Integrable (fun t => iteratedDeriv k ψ t • u (t + s)) (μI T) :=
      fun k => ((hψ.iteratedDeriv k).integrable_smul hw).restrict
    calc ∫ t in Ioc 0 T, ⟪(hg_mem.toLp g : ℝ → U) t, u (s + t)⟫_ℝ
        = ∫ t in Ioc 0 T, ∑ k : Fin L, ⟪ζ' k, iteratedDeriv k ψ t • u (t + s)⟫_ℝ := by
          refine integral_congr_ae (hg_mem.coeFn_toLp.mono fun t ht => ?_)
          simp only [ht, g, sum_inner, real_inner_smul_left, real_inner_smul_right, add_comm s]
      _ = ∑ k : Fin L, ⟪ζ' k, ∫ t in Ioc 0 T, iteratedDeriv k ψ t • u (t + s)⟫_ℝ := by
          rw [integral_finsetSum _ fun k _ => (hint k).const_inner (ζ' k)]
          exact Finset.sum_congr rfl fun k _ => integral_inner (hint k) (ζ' k)
      _ = ∑ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) u (fun t => ψ (t - s))⟫_ℝ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← derivMoment_comp_add, hψ.derivMoment_eq_setIntegral, hζ'def,
            real_inner_smul_left, real_inner_smul_right]
      _ = 0 := hζ _ (hψ.comp_sub hs.1.le (by linarith [hs.2]))
  -- hence `g = 0` on `(0, T)`, and everywhere
  have hg_ae : g =ᵐ[volume.restrict (Ioo 0 T)] 0 := by
    have : g =ᵐ[μI T] 0 := by
      filter_upwards [hg_mem.coeFn_toLp, Lp.coeFn_zero U 2 (μI T)] with t h1 h2
      rw [← h1, hG, h2]
    exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self this
  have hg0 : ∀ t, ∑ k : Fin L, iteratedDeriv k ψ t • ζ' k = 0 := by
    intro t
    by_cases ht : t ∈ Ioo 0 T
    · exact Measure.eqOn_open_of_ae_eq hg_ae isOpen_Ioo hg_cont.continuousOn
        continuousOn_const ht
    · refine Finset.sum_eq_zero fun k _ => ?_
      rw [(hψ.iteratedDeriv k).apply_eq_zero ht, zero_smul]
  exact hψ0 (hψ.eq_zero_of_sum_iteratedDeriv_smul_eq_zero ζ' hζ' hg0)

end DataDrivenControl
