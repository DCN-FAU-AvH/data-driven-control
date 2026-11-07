module

public import DataDrivenControl.Examples.Heat.System
public import DataDrivenControl.Examples.Heat.Kernel
public import DataDrivenControl.Examples.Heat.Input
public import DataDrivenControl.Informativity.AnalyticSufficiency

/-!
# The boundary-controlled heat equation

Paper: `ex:intro-pde` (`introduction.tex`), `ex:boundary-heat-informative`
(`informativity.tex`), `app:boundary-heat-informative` (`appendix_proofs.tex`).

The heat equation `∂ₜx = ∂_ξξ x` on `(0, 1)` with Neumann control `∂_ξ x(t, 0) = u(t)`,
`∂_ξ x(t, 1) = 0`, and point observation `y(t) = x(t, ξ₀)`, `ξ₀ ∈ (0, 1)` (`ν = 1`), in modal
form: `X` is any real Hilbert space with a Hilbert basis `e : HilbertBasis ℕ ℝ X`
(the cosine basis of `L²(0, 1)` in the paper), `A eₙ = λₙ eₙ` with `λₙ = -(nπ)²` (`eig`), the
control has the modal coefficients `bₙ = -eₙ(0)` (`ctrlCoeff`, `B⋆φ = -φ(0)`) and the observation
`cₙ = eₙ(ξ₀)` (`obsCoeff`).  The spaces `W ↪ X ↪ V` are those of `Examples/Heat/Spaces` (with the
scalar observation norm on `V`, see the deviation recorded there), and the system is
`ControlData.sys` of `Examples/Heat/System`, instantiated with the data of `Examples/Heat/Kernel`
(`heatData`).

## Main declarations

* `heatSystem e hξ₀ : System ℝ W X V ℝ` and its ties to the PDE:
  `heatSystem_SX` (`S_X = diagSemigroup e eig`), `hasSum_heatSystem_C` (`C w = ∑ cₙ ⟪eₙ, ι_W w⟫` on
  `D(A)`; `heatSystem_C_eq_tsum`), `hasSum_heatSystem_Bstar` (`B⋆η = ∑ bₙ ⟪eₙ, η⟫` on `D(A⋆)`;
  `heatSystem_Bstar_eq_tsum`),
  `heatSystem_B_not_mem_range` and `heatSystem_C_unbounded` (`B` and `C` are unbounded on `X`).
* `heatSystem_H1`, `heatSystem_H2`, `heatSystem_compat`: `hyp:H1`, `hyp:H2` at every horizon, and
  `hyp:compat`.
* `heatSystem_approxControllable`: `(A, B)` is approximately controllable in every `T > 0`
  (`System.approxControllable_of_modal`; the paper uses `prop:fattorini-hautus`).
* `heatSystem_TFAE`: `thm:analytic-universal-sufficiency` for the input `ū = heatInput`
  (`Examples/Heat/Input`, `ū(t) = ∑_{k≥1} 2^{-k} cos(ω_k t)`), with `σ = 0`, `M = 1`
  (`norm_heatSystem_SX_le`), `K = i · closure {± ω_k} ⊆ ρ(A)` (`mem_resolventSet_heatSystem`) and
  analyticity (`heatSystem_isAnalytic`).
* `heatSystem_informative` (informativity of `(ū, x̄)` in `U × W` for every `x̄₀ ∈ W`) and
  `heatSystem_windowInformative` (window informativity for every `x̄₀ ∈ X`).
* `exists_boundaryHeat`: **`ex:boundary-heat-informative`** in the paper's existential form:
  there are spaces `W ↪ X ↪ V` and a system with these properties.

## Indexing

The paper numbers the Neumann modes from `0` (`λ₀ = 0`, `e₀ = 1`), as Lean does: the paper's
`eₙ` is `e n`.  The paper's input index `k ≥ 1` is `k + 1` in `heatInput` (`heatInput_apply`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

/-- `∑ₙ 1/(1 + n²π²) < ∞` (the summability condition of `ModalData`). -/
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

/-- **The modal data of the boundary-controlled heat equation** (`app:boundary-heat-informative`):
`λₙ = -(nπ)²`, `cₙ = eₙ(ξ₀)`, `bₙ = -eₙ(0)`, with the kernel bounds of
`eq:heat-separated-kernel`. -/
def heatData {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) : ControlData where
  lam := eig
  c := obsCoeff ξ₀
  b := ctrlCoeff
  lam_nonpos := eig_nonpos
  summable_inv_wt := summable_inv_one_sub_eig
  exists_abs_c_le := ⟨Real.sqrt 2, abs_obsCoeff_le ξ₀⟩
  exists_abs_b_le := ⟨Real.sqrt 2, abs_ctrlCoeff_le⟩
  exists_abs_kernel_le := exists_abs_kernel_le hξ₀
  exists_abs_kernelDeriv_le := exists_abs_kernelDeriv_le hξ₀

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (e : HilbertBasis ℕ ℝ X) {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1)

/-- **The boundary-controlled heat system** (`ex:intro-pde`) on `W ↪ X ↪ V`. -/
abbrev heatSystem : System ℝ (heatData hξ₀).W X (heatData hξ₀).V ℝ := (heatData hξ₀).sys e

/-- The state-space semigroup is the diagonal semigroup with the Neumann eigenvalues
`λₙ = -(nπ)²` (`app:boundary-heat-informative`). -/
theorem heatSystem_SX : (heatSystem e hξ₀).SX = diagSemigroup e eig bddAbove_eig := rfl

/-- **`hyp:H1`** at every horizon (`app:boundary-heat-informative`). -/
theorem heatSystem_H1 (T : ℝ) : (heatSystem e hξ₀).H1 T :=
  System.H1.of_pos (heatSystem e hξ₀) ((heatData hξ₀).H1 e one_pos) one_pos T

/-- **`hyp:H2`** at every horizon (by construction of `V`). -/
theorem heatSystem_H2 (T : ℝ) : (heatSystem e hξ₀).H2 T := (heatData hξ₀).H2 e T

/-- **`hyp:compat`** (`W = D(A_V)`, as in `app:boundary-heat-informative`). -/
theorem heatSystem_compat : (heatSystem e hξ₀).Compat := (heatData hξ₀).compat e

/-- **`C` is point evaluation at `ξ₀`** on `D(A)`: `C w = ∑ₙ eₙ(ξ₀) ⟪eₙ, ι_W w⟫`
(`ex:intro-pde`, `y = x(ξ₀)`). -/
theorem hasSum_heatSystem_C (w : (heatData hξ₀).W)
    (hw : (heatSystem e hξ₀).ιW w ∈ (heatSystem e hξ₀).A.domain) :
    HasSum (fun n => obsCoeff ξ₀ n * ⟪e n, (heatSystem e hξ₀).ιW w⟫_ℝ)
      ((heatSystem e hξ₀).C w) :=
  (heatData hξ₀).hasSum_C e w hw

/-- **`B` is the Neumann control at `0`**: `B⋆η = ∑ₙ bₙ ⟪eₙ, η⟫ = -η(0)` on `D(A⋆)`
(`app:boundary-heat-informative`, `B⋆φ = -φ(0)`). -/
theorem hasSum_heatSystem_Bstar {η : X} (hη : η ∈ (heatSystem e hξ₀).A.adjoint.domain) :
    HasSum (fun n => ctrlCoeff n * ⟪e n, η⟫_ℝ) ((heatSystem e hξ₀).Bstar ⟨η, hη⟩) :=
  (heatData hξ₀).hasSum_Bstar e hη

/-- `C w = ∑ₙ eₙ(ξ₀) ⟪eₙ, ι_W w⟫` for `ι_W w ∈ D(A)` (`hasSum_heatSystem_C`). -/
theorem heatSystem_C_eq_tsum (w : (heatData hξ₀).W)
    (hw : (heatSystem e hξ₀).ιW w ∈ (heatSystem e hξ₀).A.domain) :
    (heatSystem e hξ₀).C w = ∑' n, obsCoeff ξ₀ n * ⟪e n, (heatSystem e hξ₀).ιW w⟫_ℝ :=
  (hasSum_heatSystem_C e hξ₀ w hw).tsum_eq.symm

/-- `B⋆η = ∑ₙ bₙ ⟪eₙ, η⟫` for `η ∈ D(A⋆)` (`hasSum_heatSystem_Bstar`). -/
theorem heatSystem_Bstar_eq_tsum {η : X} (hη : η ∈ (heatSystem e hξ₀).A.adjoint.domain) :
    (heatSystem e hξ₀).Bstar ⟨η, hη⟩ = ∑' n, ctrlCoeff n * ⟪e n, η⟫_ℝ :=
  (hasSum_heatSystem_Bstar e hξ₀ hη).tsum_eq.symm

/-- **`B` is unbounded on `X`**: `B 1 = b = -δ₀ ∉ X` (`app:boundary-heat-informative`). -/
theorem heatSystem_B_not_mem_range : (heatSystem e hξ₀).B 1 ∉ Set.range (heatSystem e hξ₀).ιV :=
  (heatData hξ₀).B_one_not_mem_range e not_summable_ctrlCoeff_sq

/-- **`C` is unbounded on `X`**: point evaluation is not bounded by the `L²` norm on `D(A)`
(`app:boundary-heat-informative`). -/
theorem heatSystem_C_unbounded :
    ¬ ∃ K : ℝ, ∀ w : (heatData hξ₀).W, (heatSystem e hξ₀).ιW w ∈ (heatSystem e hξ₀).A.domain →
      ‖(heatSystem e hξ₀).C w‖ ≤ K * ‖(heatSystem e hξ₀).ιW w‖ :=
  (heatData hξ₀).not_exists_bound_C e (not_summable_obsCoeff_sq ξ₀)

/-- **Approximate controllability** of `(A, B)` in every `T > 0`
(`ex:boundary-heat-informative`; proved from the modal coordinates, since the `λₙ` are simple and
`bₙ ≠ 0`, instead of through `prop:fattorini-hautus`). -/
theorem heatSystem_approxControllable {T : ℝ} (hT : 0 < T) :
    (heatSystem e hξ₀).ApproxControllable T :=
  (heatData hξ₀).approxControllable e eig_injective ctrlCoeff_ne_zero hT

/-- The heat semigroup is analytic. -/
theorem heatSystem_isAnalytic : (heatSystem e hξ₀).SX.IsAnalytic :=
  isAnalytic_diagSemigroup e eig bddAbove_eig

/-- The growth bound `eq:analytic-growth-bound` with `M = 1`, `σ = 0`. -/
theorem norm_heatSystem_SX_le (t : ℝ≥0) :
    ‖(heatSystem e hξ₀).SX t‖ ≤ 1 * Real.exp (0 * t) := by
  rw [one_mul]
  exact norm_diagSemigroup_le e eig bddAbove_eig (fun n => eig_nonpos n) t

/-- `iω ∈ ρ(A)` for `ω ≠ 0`: the spectrum is real (`app:boundary-heat-informative`). -/
theorem mem_resolventSet_heatSystem {ω : ℝ} (hω : ω ≠ 0) :
    ((0 : ℝ) : ℂ) + ω * Complex.I ∈ resolventSet (heatSystem e hξ₀).A.complexify := by
  refine mem_resolventSet_complexify_diag_of_notMem_closure e eig bddAbove_eig ?_
  have hcl : closure (Set.range fun n => (eig n : ℂ)) ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal (by rintro _ ⟨n, rfl⟩; simp)
      (isClosed_eq Complex.continuous_im continuous_const)
  intro h
  have := hcl h
  simp at this
  exact hω this

/-- With `σ = 0`, the input `e^{σ t} h(t)` of `thm:analytic-universal-sufficiency` is `ū`. -/
theorem heatInput_eq : (fun t => Real.exp (0 * t) • heatInput t) = ⇑heatInput := by
  funext t; simp

/-- **`thm:analytic-universal-sufficiency` for the heat equation** with the input `ū`
(`ex:boundary-heat-informative`): approximate controllability in time `T`, informativity in
`U × W` for every `x̄₀ ∈ W`, and window informativity for every `x̄₀ ∈ X` are equivalent. -/
theorem heatSystem_TFAE {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') :
    [(heatSystem e hξ₀).ApproxControllable T,
      ∀ w₀ : (heatData hξ₀).W, Informative T heatInput ((heatSystem e hξ₀).mildW w₀ heatInput),
      ∀ x₀ : X, WindowInformative T T' heatInput ((heatSystem e hξ₀).mild x₀ heatInput)].TFAE := by
  have := Diagonal.separableSpace e
  have h := System.analytic_universal_sufficiency (sys := heatSystem e hξ₀) (T := T) (T' := T')
    (σ := 0)
    (M := 1) hT hT' (heatSystem_isAnalytic e hξ₀) (heatSystem_H1 e hξ₀ T)
    (heatSystem_compat e hξ₀) isHarmonicPE_heatInput
    (fun ω hω => mem_resolventSet_heatSystem e hξ₀ (ne_zero_of_mem_closure_range_freq hω))
    (norm_heatSystem_SX_le e hξ₀)
  rw [heatInput_eq] at h
  exact h

/-- **`ex:boundary-heat-informative`, (ii)**: `(ū, x̄)` is informative in `U × W` on `(0, T)`
for every initial state `x̄₀ ∈ W`. -/
theorem heatSystem_informative {T : ℝ} (hT : 0 < T) (w₀ : (heatData hξ₀).W) :
    Informative T heatInput ((heatSystem e hξ₀).mildW w₀ heatInput) := by
  have h := (heatSystem_TFAE e hξ₀ hT one_pos).out 1 2
  exact h.1 (heatSystem_approxControllable e hξ₀ hT) w₀

/-- **`ex:boundary-heat-informative`, (iii)**: `(ū, x̄)` is window informative for every
initial state `x̄₀ ∈ X`. -/
theorem heatSystem_windowInformative {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (x₀ : X) :
    WindowInformative T T' heatInput ((heatSystem e hξ₀).mild x₀ heatInput) := by
  have h := (heatSystem_TFAE e hξ₀ hT hT').out 1 3
  exact h.1 (heatSystem_approxControllable e hξ₀ hT) x₀

include hξ₀ in
/-- **`ex:boundary-heat-informative`** (paper form): there are spaces `W ↪ X ↪ V` and a
system on them, with the Neumann heat semigroup, `B` the Neumann control at `0` and `C` the point
observation at `ξ₀`, for which `hyp:H1`, `hyp:H2` and `hyp:compat` hold while `B` and `C` are
unbounded on `X`; `ū` is harmonically persistently exciting, `(A, B)` is approximately
controllable in every positive time, and `(ū, x̄)` is informative in `U × W` for every `x̄₀ ∈ W`
and window informative for every `x̄₀ ∈ X`. -/
theorem exists_boundaryHeat :
    ∃ (W V : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W) (_ : CompleteSpace W)
      (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ W X V ℝ),
      sys.SX = diagSemigroup e eig bddAbove_eig ∧
      (∀ (η : X) (hη : η ∈ sys.A.adjoint.domain),
        HasSum (fun n => ctrlCoeff n * ⟪e n, η⟫_ℝ) (sys.Bstar ⟨η, hη⟩)) ∧
      (∀ w : W, sys.ιW w ∈ sys.A.domain →
        HasSum (fun n => obsCoeff ξ₀ n * ⟪e n, sys.ιW w⟫_ℝ) (sys.C w)) ∧
      (∀ T, sys.H1 T) ∧ (∀ T, sys.H2 T) ∧ sys.Compat ∧
      sys.B 1 ∉ Set.range sys.ιV ∧
      (¬ ∃ K : ℝ, ∀ w : W, sys.ιW w ∈ sys.A.domain → ‖sys.C w‖ ≤ K * ‖sys.ιW w‖) ∧
      heatInput.IsHarmonicPE ∧
      (∀ T > 0, sys.ApproxControllable T) ∧
      (∀ T > 0, ∀ w₀ : W, Informative T heatInput (sys.mildW w₀ heatInput)) ∧
      (∀ T > 0, ∀ T' > 0, ∀ x₀ : X,
        WindowInformative T T' heatInput (sys.mild x₀ heatInput)) :=
  ⟨(heatData hξ₀).W, (heatData hξ₀).V, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, heatSystem e hξ₀, heatSystem_SX e hξ₀,
    fun _ hη => hasSum_heatSystem_Bstar e hξ₀ hη, fun w hw => hasSum_heatSystem_C e hξ₀ w hw,
    heatSystem_H1 e hξ₀, heatSystem_H2 e hξ₀, heatSystem_compat e hξ₀,
    heatSystem_B_not_mem_range e hξ₀, heatSystem_C_unbounded e hξ₀, isHarmonicPE_heatInput,
    fun _ hT => heatSystem_approxControllable e hξ₀ hT,
    fun _ hT w₀ => heatSystem_informative e hξ₀ hT w₀,
    fun _ hT _ hT' x₀ => heatSystem_windowInformative e hξ₀ hT hT' x₀⟩

end BoundaryHeat

end DataDrivenControl
