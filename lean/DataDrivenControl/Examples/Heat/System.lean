module

public import DataDrivenControl.Examples.Heat.UnitSystem
public import DataDrivenControl.Examples.Heat.Input
public import DataDrivenControl.Informativity.AnalyticSufficiency
public import DataDrivenControl.System.TimeScale

/-!
# The boundary-controlled heat equation

Paper: `ex:intro-pde` (`introduction.tex`), `ex:boundary-heat-informative` (`informativity.tex`),
`app:boundary-heat-informative` (`appendix_proofs.tex`).

The heat equation `∂ₜx = ν ∂_ξξ x` on `(0, 1)` with diffusivity `ν > 0`, Neumann control
`∂_ξ x(t, 0) = u(t)`, `∂_ξ x(t, 1) = 0` and point observation `y(t) = x(t, ξ₀)`, `ξ₀ ∈ (0, 1)`.
The paper's `ex:boundary-heat-informative` takes `ν = 1`; everything here holds for every
`ν > 0`.

## Main declarations

* **`heatSystem hξ₀ χ hχ ν : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ`**: the time rescaling
  (`System.timeScale`) of `unitHeatSystem` (`Examples/Heat/UnitSystem`): `S_ν(t) = S(ν t)`,
  `A_ν = ν A`, `B_ν = ν B` (the Neumann boundary term carries the factor `ν`) and the same `C`,
  on the spaces `W ↪ L²(0, 1) ↪ V` of `ν = 1`.
* The ties to the PDE: `heatSystem_SX` (`S_X` is the diagonal semigroup with `λₙ = -ν (nπ)²`),
  `heatSystem_A_graph`, `heatSystem_A_domain`, `heatSystem_A_apply`, `heatSystem_A_adjoint`
  (`D(A) = H²_N(0, 1)`, `A φ = ν φ''`, `A⋆ = A`), `heatSystem_Bstar` (`B⋆η = -ν η(0)`),
  `exists_heatSystem_ιW_ae_eq` (`H²_N(0, 1) ⊆ W`) and `heatSystem_C` (`C w = φ(ξ₀)` there),
  `heatSystem_B_not_mem_range` and `heatSystem_C_unbounded` (`B` and `C` are unbounded on `X`).
* `heatSystem_H1`, `heatSystem_H2` (every horizon), `heatSystem_compat`.
* `heatSystem_approxControllable` (every `T > 0`), `heatSystem_TFAE`
  (`thm:analytic-universal-sufficiency` for `ū = heatInput`, `σ = 0`, `M = 1`),
  `heatSystem_informative`, `heatSystem_windowInformative`, and **`exists_boundaryHeat`**:
  `ex:boundary-heat-informative` for every `ν > 0`.

## The space `V` for a general `ν`

`V` carries the norm `eq:heat-localized-V` of the unit-diffusivity semigroup `S(t) = S_ν(t/ν)`.
In terms of `S_ν` (substitute `t = ν s`) it is
`‖z‖²_V = ‖z‖²_{X₋₁} + ν ∫₀^∞ e^{-2νs} ‖χ S_ν(s) z‖²_{H¹(0,1)} ds`, the form stated in
`exists_boundaryHeat`; for `ν = 1` it is the paper's formula.

## Indexing

The paper numbers the Neumann modes from `0` (`λ₀ = 0`, `e₀ = 1`), as Lean does.  The paper's
input index `k ≥ 1` is `k + 1` in `heatInput` (`heatInput_apply`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

open CosineBasis

/-- The eigenvalues `ν λₙ = -ν (nπ)²` are bounded above. -/
theorem bddAbove_mul_eig {ν : ℝ} (hν : 0 ≤ ν) : BddAbove (Set.range fun n => ν * eig n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; nlinarith [eig_nonpos n]⟩

variable {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (χ : Cutoff) (hχ : χ ξ₀ = 1) {ν : ℝ}

/-! ### The system -/

/-- **The boundary-controlled heat system with diffusivity `ν`** (`ex:intro-pde`): the time
rescaling `t ↦ ν t` of `unitHeatSystem`, on `W = D(A_V) ↪ L²(0, 1) ↪ V`. -/
def heatSystem (ν : ℝ) : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ :=
  (unitHeatSystem hξ₀ χ hχ).timeScale ν

/-- The embedding `W ↪ X`. -/
@[simp] theorem heatSystem_ιW : (heatSystem hξ₀ χ hχ ν).ιW = ιW χ := rfl
/-- The embedding `X ↪ V`. -/
@[simp] theorem heatSystem_ιV : (heatSystem hξ₀ χ hχ ν).ιV = ιV χ := rfl
/-- The control operator `ν B`. -/
@[simp] theorem heatSystem_B : (heatSystem hξ₀ χ hχ ν).B = ν • B χ := rfl

/-- **The state-space semigroup is the Neumann heat semigroup with diffusivity `ν`**
(`λₙ = -ν (nπ)²`, cosine basis). -/
theorem heatSystem_SX (hν : 0 < ν) : (heatSystem hξ₀ χ hχ ν).SX =
    diagSemigroup cosBasis (fun n => ν * eig n) (bddAbove_mul_eig hν.le) := by
  refine C0Semigroup.ext fun t => ContinuousLinearMap.ext fun x =>
    Diagonal.ext_inner cosBasis fun n => ?_
  show ⟪cosBasis n, SX (ν.toNNReal * t) x⟫_ℝ = _
  simp only [inner_diagSemigroup, NNReal.coe_mul, Real.coe_toNNReal _ hν.le, heatModal_lam]
  ring_nf

/-- `A_ν = ν A`, with the domain of `A`. -/
theorem heatSystem_A (hν : 0 < ν) : (heatSystem hξ₀ χ hχ ν).A = ν • SX.generator :=
  System.timeScale_A hν

/-- **The generator is `ν` times the Neumann Laplacian** (`ex:intro-pde`): the graph of `A` is
`{([φ], [ν φ'']) : φ ∈ H²_N(0, 1)}`. -/
theorem heatSystem_A_graph (hν : 0 < ν) (p : L2 ℝ 1 × L2 ℝ 1) :
    p ∈ (heatSystem hξ₀ χ hχ ν).A.graph ↔
      ∃ φ φ' φ'' : ℝ → ℝ, PDE.IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
        (p.2 : ℝ → ℝ) =ᵐ[μI 1] fun ξ => ν * φ'' ξ := by
  have key : p ∈ (heatSystem hξ₀ χ hχ ν).A.graph ↔ (p.1, ν⁻¹ • p.2) ∈ SX.generator.graph := by
    rw [heatSystem_A hξ₀ χ hχ hν, LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    exact exists_congr fun y => and_congr_right fun _ => (eq_inv_smul_iff₀ hν.ne').symm
  refine key.trans ((PDE.mem_graph_generator_iff _).trans (exists₃_congr fun φ φ' φ'' =>
    and_congr_right fun _ => and_congr_right fun _ => ?_))
  have hs := Lp.coeFn_smul ν⁻¹ p.2
  constructor <;> intro h <;> filter_upwards [hs, h] with ξ h1 h2
  · rw [← h2, h1, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hν.ne']
  · rw [h1, Pi.smul_apply, h2, smul_eq_mul, inv_mul_cancel_left₀ hν.ne']

/-- `D(A) = H²_N(0, 1)`. -/
theorem heatSystem_A_domain (hν : 0 < ν) (x : L2 ℝ 1) :
    x ∈ (heatSystem hξ₀ χ hχ ν).A.domain ↔
      ∃ φ φ' φ'' : ℝ → ℝ, PDE.IsNeumannH2 φ φ' φ'' ∧ (x : ℝ → ℝ) =ᵐ[μI 1] φ := by
  rw [heatSystem_A hξ₀ χ hχ hν]
  exact PDE.mem_generator_domain_iff x

/-- `A φ = ν φ''` on `H²_N(0, 1)`. -/
theorem heatSystem_A_apply (hν : 0 < ν) {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'')
    {x : L2 ℝ 1} (hx : x ∈ (heatSystem hξ₀ χ hχ ν).A.domain) (hxφ : (x : ℝ → ℝ) =ᵐ[μI 1] φ) :
    ((heatSystem hξ₀ χ hχ ν).A ⟨x, hx⟩ : ℝ → ℝ) =ᵐ[μI 1] fun ξ => ν * φ'' ξ := by
  have hx' : x ∈ SX.generator.domain := (SX.mem_generator_domain_timeScale hν).1 hx
  rw [show (heatSystem hξ₀ χ hχ ν).A ⟨x, hx⟩ = ν • SX.generator ⟨x, hx'⟩ from
    SX.generator_timeScale_apply hν ⟨x, hx⟩]
  filter_upwards [Lp.coeFn_smul ν (SX.generator ⟨x, hx'⟩), PDE.generator_ae_eq h hx' hxφ]
    with ξ h1 h2
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact congrArg (ν * ·) h2

/-- `A⋆ = A`: `ν` times the Neumann Laplacian is self-adjoint. -/
theorem heatSystem_A_adjoint (hν : 0 < ν) :
    (heatSystem hξ₀ χ hχ ν).A.adjoint = (heatSystem hξ₀ χ hχ ν).A := by
  rw [heatSystem_A hξ₀ χ hχ hν, LinearPMap.adjoint_smul hν.ne',
    generator_adjoint_diag cosBasis heatModal.lam heatModal.bddAbove_lam]

/-- **`B⋆` is `-ν` times the trace at `0`** (`app:boundary-heat-informative` for `ν = 1`): for
`η ∈ D(A⋆) = H²_N(0, 1)` the class of `φ`, `B⋆ η = -ν φ(0)` (`B⋆_ν = ν B⋆`,
`System.Bstar_timeScale`). -/
theorem heatSystem_Bstar (hν : 0 < ν) {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'')
    {η : L2 ℝ 1} (hη : η ∈ (heatSystem hξ₀ χ hχ ν).A.adjoint.domain)
    (hηφ : (η : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystem hξ₀ χ hχ ν).Bstar ⟨η, hη⟩ = -(ν * φ 0) := by
  refine (System.Bstar_timeScale (unitHeatSystem_H1 hξ₀ χ hχ 1) one_pos hν ⟨η, hη⟩).trans ?_
  have e : (unitHeatSystem hξ₀ χ hχ).Bstar (⟨η, (System.mem_adjoint_domain_timeScale hν).1 hη⟩ :
      (unitHeatSystem hξ₀ χ hχ).A.adjoint.domain) = -φ 0 :=
    unitHeatSystem_Bstar hξ₀ χ hχ h _ hηφ
  rw [e, smul_neg, smul_eq_mul]

/-- **`C` is point evaluation at `ξ₀`** (`ex:intro-pde`, `y(t) = x(t, ξ₀)`): if `ι_W w` is the
class of `φ ∈ H²_N(0, 1)`, then `C w = φ(ξ₀)`. -/
theorem heatSystem_C {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') (w : W χ)
    (hw : ((heatSystem hξ₀ χ hχ ν).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystem hξ₀ χ hχ ν).C w = φ ξ₀ :=
  (hasSum_C hξ₀ χ hχ w (PDE.mem_generator_domain_of_isNeumannH2 h hw)).unique
    (PDE.hasSum_obsCoeff_mul_inner h hw (Ioo_subset_Icc_self hξ₀))

/-- Every `φ ∈ H²_N(0, 1)` is the state `ι_W w` of some `w ∈ W` (`D(A) ⊆ W`). -/
theorem exists_heatSystem_ιW_ae_eq {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') :
    ∃ w : W χ, ((heatSystem hξ₀ χ hχ ν).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ := by
  obtain ⟨w, hw⟩ := exists_ιW_eq χ (PDE.mem_generator_domain_of_isNeumannH2 h h.memLp.coeFn_toLp)
  refine ⟨w, ?_⟩
  rw [heatSystem_ιW, hw]
  exact h.memLp.coeFn_toLp

/-- **`C` is unbounded on `X`**: point evaluation is not bounded by the `L²` norm on `D(A)`
(`∑ₙ cₙ² = ∞`; test on `x = ∑_{n < N} cₙ eₙ`, for which `C x = ‖x‖²`). -/
theorem heatSystem_C_unbounded (hν : 0 < ν) :
    ¬ ∃ K : ℝ, ∀ w : W χ, (heatSystem hξ₀ χ hχ ν).ιW w ∈ (heatSystem hξ₀ χ hχ ν).A.domain →
      ‖(heatSystem hξ₀ χ hχ ν).C w‖ ≤ K * ‖(heatSystem hξ₀ χ hχ ν).ιW w‖ := by
  rintro ⟨K, hK⟩
  apply not_summable_obsCoeff_sq ξ₀
  refine summable_of_sum_range_le (c := K ^ 2) (fun n => sq_nonneg _) fun N => ?_
  set a : ℕ → ℝ := fun n => if n < N then obsCoeff ξ₀ n else 0 with ha
  have ha0 : ∀ n ∉ Finset.range N, a n = 0 := fun n hn => by
    simp only [ha, Finset.mem_range] at hn ⊢; simp [hn]
  have has : Summable fun n => a n ^ 2 :=
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by rw [ha0 n hn]; ring
  set x : L2 ℝ 1 := ModalData.toX cosBasis (mkL2 a has) with hx
  have hxe : ∀ n, ⟪cosBasis n, x⟫_ℝ = a n := fun n => by
    rw [hx, ModalData.toX, Diagonal.inner_diagMap, inner_stdBasis, mkL2_apply, one_mul]
  have hxD : x ∈ SX.generator.domain := by
    rw [mem_generator_domain_diag_iff]
    exact summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      rw [hxe, ha0 n hn]; ring
  obtain ⟨w, hw⟩ := exists_ιW_eq χ hxD
  set S := ∑ n ∈ Finset.range N, obsCoeff ξ₀ n ^ 2 with hSdef
  have hsumS : ∀ f : ℕ → ℝ, (∀ n, f n = if n < N then obsCoeff ξ₀ n ^ 2 else 0) →
      HasSum f S := by
    intro f hf
    have h0 : HasSum f (∑ n ∈ Finset.range N, f n) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by
        rw [hf]; simp only [Finset.mem_range] at hn; simp [hn]
    have hs : ∑ n ∈ Finset.range N, f n = S := Finset.sum_congr rfl fun n hn => by
      rw [hf]; simp only [Finset.mem_range] at hn; simp [hn]
    rwa [hs] at h0
  have hCw : C hξ₀ χ hχ w = S := by
    refine (hasSum_C hξ₀ χ hχ w (hw ▸ hxD)).unique (hsumS _ fun n => ?_)
    rw [hw, hxe]; simp only [ha]; split_ifs <;> ring
  have hnx : ‖x‖ ^ 2 = S := (Diagonal.hasSum_inner_sq cosBasis x).unique (hsumS _ fun n => by
    rw [hxe]; simp only [ha]; split_ifs <;> ring)
  have hb : |C hξ₀ χ hχ w| ≤ K * ‖x‖ := by
    have := hK w (by rw [heatSystem_ιW, hw]; exact (SX.mem_generator_domain_timeScale hν).2 hxD)
    rwa [heatSystem_ιW, hw, Real.norm_eq_abs] at this
  rw [hCw] at hb
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => sq_nonneg _
  have h1 : S ≤ K * ‖x‖ := (le_abs_self S).trans hb
  have h2 : S ^ 2 ≤ K ^ 2 * S := by
    have := pow_le_pow_left₀ hS0 h1 2
    rwa [mul_pow, hnx] at this
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

/-- **`B` is unbounded on `X`**: `B 1 = ν b`, `b = -δ₀ ∉ X` (`B_not_mem_range`). -/
theorem heatSystem_B_not_mem_range (hν : 0 < ν) :
    (heatSystem hξ₀ χ hχ ν).B 1 ∉ Set.range (heatSystem hξ₀ χ hχ ν).ιV := by
  rintro ⟨x, hx⟩
  rw [heatSystem_ιV, heatSystem_B, smul_apply] at hx
  exact B_not_mem_range χ ⟨ν⁻¹ • x, by rw [map_smul, hx, inv_smul_smul₀ hν.ne']⟩

/-! ### The standing assumptions -/

/-- **`hyp:H1`** at every horizon (`System.H1.timeScale`). -/
theorem heatSystem_H1 (hν : 0 < ν) (T : ℝ) : (heatSystem hξ₀ χ hχ ν).H1 T :=
  (unitHeatSystem_H1 hξ₀ χ hχ (ν * T)).timeScale hν

/-- **`hyp:H2`** at every horizon (`System.H2.timeScale`). -/
theorem heatSystem_H2 (hν : 0 < ν) (T : ℝ) : (heatSystem hξ₀ χ hχ ν).H2 T :=
  (unitHeatSystem_H2 hξ₀ χ hχ (ν * T)).timeScale hν

/-- **`hyp:compat`** (`W = D(A_V)` by construction). -/
theorem heatSystem_compat (hν : 0 < ν) : (heatSystem hξ₀ χ hχ ν).Compat :=
  (unitHeatSystem_compat hξ₀ χ hχ).timeScale hν

/-! ### Approximate controllability and informativity -/

/-- **Approximate controllability** of `(A, B)` in every `T > 0` (`ex:boundary-heat-informative`):
that of `ν = 1` in time `ν T` (`System.approxControllable_timeScale`). -/
theorem heatSystem_approxControllable (hν : 0 < ν) {T : ℝ} (hT : 0 < T) :
    (heatSystem hξ₀ χ hχ ν).ApproxControllable T :=
  (System.approxControllable_timeScale hν T).2
    (unitHeatSystem_approxControllable hξ₀ χ hχ (mul_pos hν hT))

/-- The heat semigroup is analytic (`app:boundary-heat-informative`). -/
theorem heatSystem_isAnalytic (hν : 0 < ν) : (heatSystem hξ₀ χ hχ ν).SX.IsAnalytic :=
  (isAnalytic_diagSemigroup cosBasis heatModal.lam heatModal.bddAbove_lam).timeScale hν

/-- The growth bound `eq:analytic-growth-bound` with `M = 1`, `σ = 0`. -/
theorem norm_heatSystem_SX_le (hν : 0 < ν) (t : ℝ≥0) :
    ‖(heatSystem hξ₀ χ hχ ν).SX t‖ ≤ 1 * Real.exp (0 * t) := by
  have h : ∀ t : ℝ≥0, ‖SX t‖ ≤ 1 * Real.exp (0 * t) := fun t => by
    rw [one_mul]
    exact norm_diagSemigroup_le cosBasis heatModal.lam heatModal.bddAbove_lam
      heatModal.lam_nonpos t
  exact (SX.norm_timeScale_le h hν.le t).trans_eq (by simp)

/-- `iω ∈ ρ(A)` for `ω ≠ 0`: the spectrum `{-ν (nπ)²}` is real (`app:boundary-heat-informative`). -/
theorem mem_resolventSet_heatSystem (hν : 0 < ν) {ω : ℝ} (hω : ω ≠ 0) :
    ((0 : ℝ) : ℂ) + ω * Complex.I ∈ resolventSet (heatSystem hξ₀ χ hχ ν).A.complexify := by
  refine (System.mem_resolventSet_complexify_timeScale (sys := unitHeatSystem hξ₀ χ hχ) hν _).2
    (mem_resolventSet_complexify_diag_of_notMem_closure cosBasis heatModal.lam
      heatModal.bddAbove_lam fun h => ?_)
  have hcl : closure (Set.range fun n => (heatModal.lam n : ℂ)) ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal (by rintro _ ⟨n, rfl⟩; simp)
      (isClosed_eq Complex.continuous_im continuous_const)
  have := hcl h
  simp [hν.ne'] at this
  exact hω this

/-- **`thm:analytic-universal-sufficiency` for the heat equation** with the input `ū`
(`ex:boundary-heat-informative`): approximate controllability in time `T`, informativity in
`U × W` for every `x̄₀ ∈ W`, and window informativity for every `x̄₀ ∈ X` are equivalent. -/
theorem heatSystem_TFAE (hν : 0 < ν) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') :
    [(heatSystem hξ₀ χ hχ ν).ApproxControllable T,
      ∀ w₀ : W χ, Informative T heatInput ((heatSystem hξ₀ χ hχ ν).mildW w₀ heatInput),
      ∀ x₀ : L2 ℝ 1,
        WindowInformative T T' heatInput ((heatSystem hξ₀ χ hχ ν).mild x₀ heatInput)].TFAE := by
  have := Diagonal.separableSpace cosBasis
  have h := System.analytic_universal_sufficiency (sys := heatSystem hξ₀ χ hχ ν) (T := T)
    (T' := T') (σ := 0) (M := 1) hT hT' (heatSystem_isAnalytic hξ₀ χ hχ hν)
    (heatSystem_H1 hξ₀ χ hχ hν T) (heatSystem_compat hξ₀ χ hχ hν) isHarmonicPE_heatInput
    (fun ω hω => mem_resolventSet_heatSystem hξ₀ χ hχ hν (ne_zero_of_mem_closure_range_freq hω))
    (norm_heatSystem_SX_le hξ₀ χ hχ hν)
  have he : (fun t => Real.exp (0 * t) • heatInput t) = ⇑heatInput := by funext t; simp
  rw [he] at h
  exact h

/-- **`ex:boundary-heat-informative`, (ii)**: `(ū, x̄)` is informative in `U × W` for every
`x̄₀ ∈ W`. -/
theorem heatSystem_informative (hν : 0 < ν) {T : ℝ} (hT : 0 < T) (w₀ : W χ) :
    Informative T heatInput ((heatSystem hξ₀ χ hχ ν).mildW w₀ heatInput) := by
  have h := (heatSystem_TFAE hξ₀ χ hχ hν hT one_pos).out 1 2
  exact h.1 (heatSystem_approxControllable hξ₀ χ hχ hν hT) w₀

/-- **`ex:boundary-heat-informative`, (iii)**: `(ū, x̄)` is window informative for every
`x̄₀ ∈ X`. -/
theorem heatSystem_windowInformative (hν : 0 < ν) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (x₀ : L2 ℝ 1) :
    WindowInformative T T' heatInput ((heatSystem hξ₀ χ hχ ν).mild x₀ heatInput) := by
  have h := (heatSystem_TFAE hξ₀ χ hχ hν hT hT').out 1 3
  exact h.1 (heatSystem_approxControllable hξ₀ χ hχ hν hT) x₀

/-! ### The example -/

/-- **`ex:boundary-heat-informative`** for every diffusivity `ν > 0` (the paper's case is
`ν = 1`; `app:boundary-heat-informative`, `eq:heat-localized-V`, `eq:heat-W-domain`).  Let
`ξ₀ ∈ (0, 1)` and let `χ ∈ C¹` with `supp χ ⊆ (0, 1)` and `χ = 1` near `ξ₀` (every
`χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀` qualifies; one exists by `exists_smooth_cutoff`).  There
are Hilbert spaces `W ↪ L²(0, 1) ↪ V` and a system on them such that:
* `V` is the paper's space: `ζ : V → X₋₁` is injective and the identity on `X`, and
  `‖v‖²_V = ‖z‖²_{X₋₁} + ν ∫₀^∞ e^{-2νs} (∫₀¹ (χ S_ν(s) z)² + ∫₀¹ (∂_ξ (χ S_ν(s) z))²) ds` for
  `z = ζ v`, where `S_ν(s) z = S(ν s) z` is the profile `orbit z (ν s)` of the heat semigroup
  with diffusivity `ν` (for `ν = 1`, the paper's norm); `V = {z ∈ X₋₁ : this is finite}`, and
  `S_V` extends `S_ν` on `X₋₁`;
* `W = D(A_V) = {x ∈ X : A_{X,-1} x ∈ V}` (`eq:heat-W-domain`, as a set) with `hyp:compat`;
* `S_X` is the diagonal semigroup with `λₙ = -ν (nπ)²`; the generator is `ν` times the Neumann
  Laplacian (`D(A) = H²_N(0, 1)`, `A φ = ν φ''`, `A⋆ = A`), `B⋆η = -ν η(0)`, `H²_N(0, 1) ⊆ W`
  and `C` is the point evaluation at `ξ₀` there;
* `hyp:H1`, `hyp:H2` hold at every horizon, while `B` and `C` are unbounded on `L²(0, 1)`;
* `ū` is harmonically persistently exciting, `(A, B)` is approximately controllable in every
  positive time, and `(ū, x̄)` is informative in `U × W` for every `x̄₀ ∈ W` and window
  informative for every `x̄₀ ∈ L²(0, 1)`. -/
theorem exists_boundaryHeat {ν : ℝ} (hν : 0 < ν) {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχs : tsupport χ ⊆ Ioo 0 1) (hχ₀ : χ =ᶠ[𝓝 ξ₀] 1) :
    ∃ (W V : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W) (_ : CompleteSpace W)
      (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ W (L2 ℝ 1) V ℝ) (ζ : V →L[ℝ] Xm1),
      Function.Injective ζ ∧
      (∀ x : L2 ℝ 1, ζ (sys.ιV x) = heatModal.toXm1 cosBasis x) ∧
      (∀ v : V, ‖v‖ ^ 2 = ‖ζ v‖ ^ 2 + ν * ∫ s in Ioi 0,
        Real.exp (-2 * (ν * s)) * H1sq (fun ξ => χ ξ * orbit (ζ v) (ν * s) ξ)) ∧
      (∀ a : Xm1, a ∈ Set.range ζ ↔ IntegrableOn (fun s =>
        Real.exp (-2 * (ν * s)) * H1sq (fun ξ => χ ξ * orbit a (ν * s) ξ)) (Ioi 0)) ∧
      C0Semigroup.Consistent ζ sys.SV (heatModal.Sm.timeScale ν) ∧
      Set.range sys.ιW = {x | IntegrableOn (fun s => Real.exp (-2 * (ν * s)) *
        H1sq (fun ξ => χ ξ * orbit (heatModal.genXm1 cosBasis x) (ν * s) ξ)) (Ioi 0)} ∧
      sys.SX = diagSemigroup cosBasis (fun n => ν * eig n) (bddAbove_mul_eig hν.le) ∧
      (∀ p : L2 ℝ 1 × L2 ℝ 1, p ∈ sys.A.graph ↔
        ∃ φ φ' φ'' : ℝ → ℝ, PDE.IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
          (p.2 : ℝ → ℝ) =ᵐ[μI 1] fun ξ => ν * φ'' ξ) ∧
      sys.A.adjoint = sys.A ∧
      (∀ (η : L2 ℝ 1) (hη : η ∈ sys.A.adjoint.domain) (φ φ' φ'' : ℝ → ℝ),
        PDE.IsNeumannH2 φ φ' φ'' → (η : ℝ → ℝ) =ᵐ[μI 1] φ → sys.Bstar ⟨η, hη⟩ = -(ν * φ 0)) ∧
      (∀ φ φ' φ'' : ℝ → ℝ, PDE.IsNeumannH2 φ φ' φ'' →
        ∃ w : W, (sys.ιW w : ℝ → ℝ) =ᵐ[μI 1] φ) ∧
      (∀ (w : W) (φ φ' φ'' : ℝ → ℝ), PDE.IsNeumannH2 φ φ' φ'' →
        (sys.ιW w : ℝ → ℝ) =ᵐ[μI 1] φ → sys.C w = φ ξ₀) ∧
      (∀ T, sys.H1 T) ∧ (∀ T, sys.H2 T) ∧ sys.Compat ∧
      sys.B 1 ∉ Set.range sys.ιV ∧
      (¬ ∃ K : ℝ, ∀ w : W, sys.ιW w ∈ sys.A.domain → ‖sys.C w‖ ≤ K * ‖sys.ιW w‖) ∧
      heatInput.IsHarmonicPE ∧
      (∀ T > 0, sys.ApproxControllable T) ∧
      (∀ T > 0, ∀ w₀ : W, Informative T heatInput (sys.mildW w₀ heatInput)) ∧
      (∀ T > 0, ∀ T' > 0, ∀ x₀ : L2 ℝ 1,
        WindowInformative T T' heatInput (sys.mild x₀ heatInput)) := by
  let c : Cutoff := ⟨χ, hχ, hχs⟩
  have h1 : c ξ₀ = 1 := hχ₀.eq_of_nhds
  have hint : ∀ f : ℝ → ℝ, IntegrableOn (fun s => f (ν * s)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) :=
    fun f => by rw [integrableOn_Ioi_comp_mul_left_iff f 0 hν, mul_zero]
  refine ⟨W c, V c, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, heatSystem hξ₀ c h1 ν, fstV c, fstV_injective c, fun _ => rfl,
    fun v => ?_, fun a => ?_, (consistent_fstV c).timeScale ν, ?_,
    heatSystem_SX hξ₀ c h1 hν, heatSystem_A_graph hξ₀ c h1 hν, heatSystem_A_adjoint hξ₀ c h1 hν,
    fun _ hη _ _ _ h hηφ => heatSystem_Bstar hξ₀ c h1 hν h hη hηφ,
    fun _ _ _ h => exists_heatSystem_ιW_ae_eq hξ₀ c h1 h,
    fun w _ _ _ h hw => heatSystem_C hξ₀ c h1 h w hw,
    heatSystem_H1 hξ₀ c h1 hν, heatSystem_H2 hξ₀ c h1 hν, heatSystem_compat hξ₀ c h1 hν,
    heatSystem_B_not_mem_range hξ₀ c h1 hν, heatSystem_C_unbounded hξ₀ c h1 hν,
    isHarmonicPE_heatInput,
    fun _ hT => heatSystem_approxControllable hξ₀ c h1 hν hT,
    fun _ hT w₀ => heatSystem_informative hξ₀ c h1 hν hT w₀,
    fun _ hT _ hT' x₀ => heatSystem_windowInformative hξ₀ c h1 hν hT hT' x₀⟩
  · rw [norm_V_sq_eq c v, integral_comp_mul_left_Ioi (fun t => Real.exp (-2 * t) *
      H1sq (fun ξ => χ ξ * orbit (fstV c v) t ξ)) 0 hν, mul_zero, smul_eq_mul,
      mul_inv_cancel_left₀ hν.ne']
  · exact (exists_fstV_eq_iff c a).trans
      (hint fun t => Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit a t ξ)).symm
  · rw [heatSystem_ιW, range_ιW c]
    ext x
    exact (hint fun t => Real.exp (-2 * t) *
      H1sq (fun ξ => χ ξ * orbit (heatModal.genXm1 cosBasis x) t ξ)).symm

end BoundaryHeat

end DataDrivenControl
