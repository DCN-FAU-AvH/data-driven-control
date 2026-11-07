module

public import DataDrivenControl.Examples.Heat.LocalizedControl

/-!
# The boundary-controlled heat equation on the paper's localised spaces

Paper: `ex:boundary-heat-informative` (`informativity.tex`), `app:boundary-heat-informative`
(`appendix_proofs.tex`): the system on `W ↪ L²(0, 1) ↪ V` with the paper's `V`
(`eq:heat-localized-V`, the orbit measured in `H¹` near `ξ₀`) and `W = D(A_V)`
(`eq:heat-W-domain`), `hyp:H1`, `hyp:H2`, `hyp:compat`, and the informativity claims.

## Main declarations

* `J : V χ →L[ℝ] (heatData hξ₀).V`: **the localised norm dominates the scalar observation norm**
  of `Examples/Heat/Spaces`: `|C S(t) z| = |(S(t) z)(ξ₀)| ≤ eᵗ ‖F_z(t)‖` (`abs_orbit_le`), so
  `∫₀¹ |C S(t) z|² dt ≤ e² ‖z‖²_V` (`memLp_obs`); `JW : W χ →L[ℝ] (heatData hξ₀).W`.
* `C hξ₀ χ hχ = C_scalar ∘ JW`: the point observation, transported; on `D(A) = H²_N(0, 1)`
  it is `C w = φ(ξ₀)` (`heatSystemLoc_C`, `hasSum_heatSystemLoc_C`).
* **`heatSystemLoc hξ₀ χ hχ : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ`** with `S_X` the Neumann heat
  semigroup, `B` the Neumann control (`B⋆η = -η(0)`, `heatSystemLoc_Bstar`) and `C` the point
  observation.
* `heatSystemLoc_H1` (every horizon, from `exists_control_bound_loc`), `heatSystemLoc_H2` (every
  horizon, transported from the scalar system through `J`), `heatSystemLoc_compat`;
  `heatSystemLoc_B_not_mem_range`, `heatSystemLoc_C_unbounded`.
* `heatSystemLoc_approxControllable`, `heatSystemLoc_informative`,
  `heatSystemLoc_windowInformative`, and **`exists_boundaryHeat_loc`**:
  `ex:boundary-heat-informative` with the paper's spaces.

## Hypotheses on `χ`

The paper takes `χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀`.  The construction needs `χ ∈ C¹` with
`supp χ ⊆ (0, 1)` (`Cutoff`), and the observation only uses `χ(ξ₀) = 1`; `exists_boundaryHeat_loc`
takes the paper's hypothesis `χ =ᶠ[𝓝 ξ₀] 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

namespace Localized

open CosineBasis

variable {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) (χ : Cutoff) (hχ : χ ξ₀ = 1)

/-! ### The modal data of `Examples/Heat/System`

`heatData hξ₀` and `heatModal` have the same eigenvalues (they differ in the observation
coefficients), so they give the same `X₋₁`, `S_{X₋₁}`, `X ↪ X₋₁` and `S_X`.  These identities are
proved through `eig`, never by comparing the two structures. -/

/-- The eigenvalues of `heatData hξ₀`. -/
theorem heatData_lam : (heatData hξ₀).lam = eig := rfl

/-- The weights of `heatData hξ₀`. -/
theorem heatData_wt (n : ℕ) : (heatData hξ₀).wt n = 1 - eig n := rfl

/-- `heatData hξ₀` and `heatModal` have the same eigenvalues. -/
theorem heatData_lam_eq : (heatData hξ₀).lam = heatModal.lam :=
  (heatData_lam hξ₀).trans heatModal_lam.symm

/-- Diagonal semigroups with equal eigenvalues are equal. -/
theorem diagSemigroup_congr {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (e : HilbertBasis ℕ ℝ X) {l₁ l₂ : ℕ → ℝ} (h : l₁ = l₂)
    (p₁ : BddAbove (Set.range l₁)) (p₂ : BddAbove (Set.range l₂)) :
    diagSemigroup e l₁ p₁ = diagSemigroup e l₂ p₂ := by
  subst h; rfl

/-- The same semigroup on `X₋₁`. -/
theorem heatData_Sm : (heatData hξ₀).Sm = heatModal.Sm :=
  diagSemigroup_congr stdBasis (heatData_lam_eq hξ₀) _ _

/-- The same state-space semigroup. -/
theorem heatData_SX : (heatData hξ₀).SX cosBasis = SX :=
  diagSemigroup_congr cosBasis (heatData_lam_eq hξ₀) _ _

/-- The same embedding `X ↪ X₋₁`. -/
theorem heatData_toXm1 : (heatData hξ₀).toXm1 cosBasis = heatModal.toXm1 cosBasis :=
  ContinuousLinearMap.ext fun x => ext_Xm1 fun n => by
    rw [ModalData.toXm1_apply, ModalData.toXm1_apply, heatData_wt, heatModal_wt]

/-! ### The localised norm dominates the scalar observation norm -/

/-- The free output is the point value of the orbit: `C S(t) z = (S(t) z)(ξ₀)` for `t > 0`. -/
theorem obs_eq_orbit {t : ℝ} (ht : 0 < t) (a : Xm1) : (heatData hξ₀).obs a t = orbit a t ξ₀ := by
  have h := (heatData hξ₀).hasSum_obs ht a
  have e : (fun n => (heatData hξ₀).c n * (heatData hξ₀).wt n *
      Real.exp ((heatData hξ₀).lam n * t) * a n) = fun n => orbCoeff t n * a n * cosFun n ξ₀ := by
    funext n
    show obsCoeff ξ₀ n * (1 - eig n) * Real.exp (eig n * t) * a n =
      orbCoeff t n * a n * cosFun n ξ₀
    rw [obsCoeff_eq_cosFun_apply, orbCoeff]
    ring
  rw [e] at h
  exact h.unique (hasSum_orbit ht a ξ₀)

include hχ in
/-- **`V ⊆ V_scalar`**: for `z ∈ V`, `∫₀¹ |C S(t) z|² dt ≤ e² ∫₀¹ ‖F_z(t)‖² dt < ∞`. -/
theorem memLp_obs (v : V χ) : MemLp ((heatData hξ₀).obs (fstV χ v)) 2 (μI 1) := by
  have hmono : μI 1 ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  have hm : MemLp (fun t => orbitH χ t (fstV χ v)) 2 (μI 1) :=
    (memLp_orbitH χ v).mono_measure hmono
  refine hm.of_le_mul (c := Real.exp 1)
    ((heatData hξ₀).aestronglyMeasurable_obs _ measurableSet_Ioc fun t ht => ht.1)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [obs_eq_orbit hξ₀ ht.1, Real.norm_eq_abs]
  exact (abs_orbit_le χ hξ₀ hχ ht.1 _).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ht.2) (norm_nonneg _))

/-- `V ↪ V_scalar`, as a linear map. -/
def Jlin : V χ →ₗ[ℝ] (heatData hξ₀).V where
  toFun v := (heatData hξ₀).mkV (fstV χ v) (memLp_obs hξ₀ χ hχ v)
  map_add' v w := (heatData hξ₀).V_ext (by simp)
  map_smul' r v := (heatData hξ₀).V_ext (by simp)

/-- **`V ↪ V_scalar`**: the identity on `X₋₁`, bounded by the closed graph theorem. -/
def J : V χ →L[ℝ] (heatData hξ₀).V :=
  ⟨Jlin hξ₀ χ hχ, (heatData hξ₀).continuous_of_fstV (Jlin hξ₀ χ hχ) (fstV χ) fun _ => rfl⟩

/-- `J` is the identity on `X₋₁`. -/
@[simp] theorem fstV_J (v : V χ) : (heatData hξ₀).fstV (J hξ₀ χ hχ v) = fstV χ v := rfl

/-- `J ∘ ιV = ιV_scalar`. -/
theorem J_ιV (x : L2 ℝ 1) : J hξ₀ χ hχ (ιV χ x) = (heatData hξ₀).ιV cosBasis x :=
  (heatData hξ₀).V_ext (by rw [fstV_J, fstV_ιV, ModalData.fstV_ιV, heatData_toXm1])

/-- `J` is consistent with the semigroups. -/
theorem consistent_J : C0Semigroup.Consistent (J hξ₀ χ hχ) (SV χ) (heatData hξ₀).SV :=
  fun t v => (heatData hξ₀).V_ext (by
    rw [fstV_J, fstV_SV, (heatData hξ₀).fstV_SV, fstV_J, heatData_Sm])

/-- `J b = b`. -/
theorem J_ctrlV : J hξ₀ χ hχ (ctrlV χ) = (heatData hξ₀).ctrlV :=
  (heatData hξ₀).V_ext (ext_Xm1 fun _ => rfl)

/-- `J (D(A_V)) ⊆ D(A_{V_scalar})`. -/
theorem J_mem_domain (w : W χ) :
    J hξ₀ χ hχ ((SV χ).domIncl w) ∈ (heatData hξ₀).SV.generator.domain :=
  (consistent_J hξ₀ χ hχ).mem_generator_domain _ ((SV χ).domIncl_mem w)

/-- `A_{V_scalar} J = J A_V` on `D(A_V)`. -/
theorem generator_J (w : W χ) :
    (heatData hξ₀).SV.generator ⟨J hξ₀ χ hχ ((SV χ).domIncl w), J_mem_domain hξ₀ χ hχ w⟩ =
      J hξ₀ χ hχ ((SV χ).domGen w) := by
  rw [(consistent_J hξ₀ χ hχ).generator_apply _ ((SV χ).domIncl_mem w),
    (SV χ).generator_domIncl w]

/-- **`W ↪ W_scalar`**: `(v, A_V v) ↦ (J v, J A_V v)`. -/
def JW : W χ →L[ℝ] (heatData hξ₀).W :=
  (heatData hξ₀).SV.liftDom ((J hξ₀ χ hχ).comp (SV χ).domIncl)
    ((J hξ₀ χ hχ).comp (SV χ).domGen) fun w => ⟨J_mem_domain hξ₀ χ hχ w, generator_J hξ₀ χ hχ w⟩

/-- `JW` is consistent with the restricted semigroups. -/
theorem JW_SW (t : ℝ) (w : W χ) :
    JW hξ₀ χ hχ ((SW χ).real t w) = (heatData hξ₀).SW.real t (JW hξ₀ χ hχ w) :=
  (heatData hξ₀).SV.dom_ext ((consistent_J hξ₀ χ hχ).real t ((SV χ).domIncl w))

/-- `JW` is the identity on states: `ι_W (JW w) = ι_W w`. -/
theorem ιW_JW (w : W χ) : (heatData hξ₀).ιW cosBasis (JW hξ₀ χ hχ w) = ιW χ w :=
  (heatData hξ₀).ιV_injective cosBasis (by
    rw [(heatData hξ₀).ιV_ιW cosBasis, ← J_ιV hξ₀ χ hχ, ιV_ιW]
    rfl)

/-! ### The system -/

/-- **The point observation** `C ∈ L(W, ℝ)`: the observation of `Examples/Heat/System` through
`W ↪ W_scalar`; on `D(A) = H²_N(0, 1)` it is `w ↦ w(ξ₀)` (`heatSystemLoc_C`). -/
def C : W χ →L[ℝ] ℝ := (heatData hξ₀).C.comp (JW hξ₀ χ hχ)

/-- **The boundary-controlled heat system on the paper's localised spaces**
(`ex:boundary-heat-informative`): `W = D(A_V) ↪ L²(0, 1) ↪ V`, `V` as in `eq:heat-localized-V`. -/
def heatSystemLoc : System ℝ (W χ) (L2 ℝ 1) (V χ) ℝ where
  ιW := ιW χ
  ιV := ιV χ
  ιW_injective := ιW_injective χ
  ιV_injective := ιV_injective χ
  ιW_denseRange := denseRange_ιW χ
  ιV_denseRange := denseRange_ιV χ
  SW := SW χ
  SX := SX
  SV := SV χ
  consistentW := consistent_ιW χ
  consistentV := consistent_ιV χ
  B := B χ
  C := C hξ₀ χ hχ

/-- The embedding `W ↪ X`. -/
@[simp] theorem heatSystemLoc_ιW : (heatSystemLoc hξ₀ χ hχ).ιW = ιW χ := rfl
/-- The embedding `X ↪ V`. -/
@[simp] theorem heatSystemLoc_ιV : (heatSystemLoc hξ₀ χ hχ).ιV = ιV χ := rfl
/-- The semigroup on `V`. -/
@[simp] theorem heatSystemLoc_SV : (heatSystemLoc hξ₀ χ hχ).SV = SV χ := rfl
/-- The control operator. -/
@[simp] theorem heatSystemLoc_B : (heatSystemLoc hξ₀ χ hχ).B = B χ := rfl
/-- The observation operator. -/
@[simp] theorem heatSystemLoc_C_def : (heatSystemLoc hξ₀ χ hχ).C = C hξ₀ χ hχ := rfl

/-- The state-space semigroup is the Neumann heat semigroup (`λₙ = -(nπ)²`, cosine basis). -/
theorem heatSystemLoc_SX : (heatSystemLoc hξ₀ χ hχ).SX = diagSemigroup cosBasis eig bddAbove_eig :=
  rfl

/-- `W ↪ V` is the inclusion `D(A_V) ↪ V`. -/
theorem heatSystemLoc_ιWV (w : W χ) : (heatSystemLoc hξ₀ χ hχ).ιWV w = (SV χ).domIncl w :=
  ιV_ιW χ w

/-- **`hyp:compat`** (`W = D(A_V)` by construction). -/
theorem heatSystemLoc_compat : (heatSystemLoc hξ₀ χ hχ).Compat := by
  refine ⟨⟨1, fun v hv => ⟨(SV χ).toDom ⟨v, hv⟩, ?_, ?_⟩⟩, ?_⟩
  · rw [heatSystemLoc_ιWV]; rfl
  · rw [one_mul]; exact (SV χ).norm_toDom_le _
  · convert dense_univ (X := W χ)
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, heatSystemLoc_ιWV]
    exact (SV χ).domIncl_mem w

/-- `‖A_{X,-1}‖ ≤ 1`. -/
theorem norm_genXm1_le : ‖heatModal.genXm1 cosBasis‖ ≤ 1 :=
  (Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)

/-- **`hyp:H1`** at every positive horizon (`app:boundary-heat-informative`). -/
theorem heatSystemLoc_H1_pos {T : ℝ} (hT : 0 < T) : (heatSystemLoc hξ₀ χ hχ).H1 T := by
  obtain ⟨C₀, hC₀⟩ := exists_control_bound_loc χ hT
  refine ⟨(‖ιV χ‖ + 2) * C₀, fun u => ?_⟩
  obtain ⟨x, hx, hxn, h, hh⟩ := hC₀ u
  have hv := (mem_SV_generator_domain_iff χ x).2 h
  refine ⟨(SV χ).toDom ⟨ιV χ x, hv⟩, ?_, ?_⟩
  · rw [heatSystemLoc_ιWV]
    exact ιV_eq_conv χ u x hx
  · calc ‖(SV χ).toDom ⟨ιV χ x, hv⟩‖
        ≤ ‖ιV χ x‖ + ‖(SV χ).generator ⟨ιV χ x, hv⟩‖ := (SV χ).norm_toDom_le _
      _ ≤ ‖ιV χ‖ * (C₀ * ‖u‖) + (C₀ * ‖u‖ + C₀ * ‖u‖) := by
          refine add_le_add ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left hxn (norm_nonneg _))) ?_
          rw [SV_generator_ιV χ x h]
          refine (norm_V_le χ _).trans (add_le_add ?_ ?_)
          · rw [fstV_mkV]
            exact ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) norm_genXm1_le)).trans hxn
          · rw [sndV_mkV]; exact hh
      _ = (‖ιV χ‖ + 2) * C₀ * ‖u‖ := by ring

/-- **`hyp:H1`** at every horizon. -/
theorem heatSystemLoc_H1 (T : ℝ) : (heatSystemLoc hξ₀ χ hχ).H1 T :=
  System.H1.of_pos (heatSystemLoc hξ₀ χ hχ) (heatSystemLoc_H1_pos hξ₀ χ hχ one_pos) one_pos T

/-- **`hyp:H2`** at every horizon: `‖C S(·) w‖_{L²(0,T)} ≤ c ‖w‖_{V_scalar} ≤ c ‖J‖ ‖w‖_V`. -/
theorem heatSystemLoc_H2 (T : ℝ) : (heatSystemLoc hξ₀ χ hχ).H2 T := by
  obtain ⟨c, hc⟩ := (heatData hξ₀).H2 cosBasis T
  refine ⟨max c 0 * ‖J hξ₀ χ hχ‖, fun w => ?_⟩
  have h1 : (fun t => (heatSystemLoc hξ₀ χ hχ).C ((heatSystemLoc hξ₀ χ hχ).SW.real t w)) =
      fun t => ((heatData hξ₀).sys cosBasis).C
        (((heatData hξ₀).sys cosBasis).SW.real t (JW hξ₀ χ hχ w)) := by
    funext t
    show (heatData hξ₀).C (JW hξ₀ χ hχ ((SW χ).real t w)) =
      (heatData hξ₀).C ((heatData hξ₀).SW.real t (JW hξ₀ χ hχ w))
    rw [JW_SW]
  rw [h1]
  refine (hc (JW hξ₀ χ hχ w)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [ControlData.sys_ιWV]
  have e : (heatData hξ₀).SV.domIncl (JW hξ₀ χ hχ w) =
      J hξ₀ χ hχ ((heatSystemLoc hξ₀ χ hχ).ιWV w) := by
    rw [heatSystemLoc_ιWV]; rfl
  rw [e]
  calc c * ‖J hξ₀ χ hχ ((heatSystemLoc hξ₀ χ hχ).ιWV w)‖
      ≤ max c 0 * ‖J hξ₀ χ hχ ((heatSystemLoc hξ₀ χ hχ).ιWV w)‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max c 0 * (‖J hξ₀ χ hχ‖ * ‖(heatSystemLoc hξ₀ χ hχ).ιWV w‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (le_max_right _ _)
    _ = max c 0 * ‖J hξ₀ χ hχ‖ * ‖(heatSystemLoc hξ₀ χ hχ).ιWV w‖ := by ring

/-! ### The ties to the PDE -/

/-- **`C` is point evaluation at `ξ₀`** in modal form: `C w = ∑ₙ eₙ(ξ₀) ⟪eₙ, ι_W w⟫` on `D(A)`. -/
theorem hasSum_heatSystemLoc_C (w : W χ)
    (hw : (heatSystemLoc hξ₀ χ hχ).ιW w ∈ (heatSystemLoc hξ₀ χ hχ).A.domain) :
    HasSum (fun n => obsCoeff ξ₀ n * ⟪cosBasis n, (heatSystemLoc hξ₀ χ hχ).ιW w⟫_ℝ)
      ((heatSystemLoc hξ₀ χ hχ).C w) := by
  have h := hasSum_heatSystem_C cosBasis hξ₀ (JW hξ₀ χ hχ w)
    (by
      show (heatData hξ₀).ιW cosBasis (JW hξ₀ χ hχ w) ∈ ((heatData hξ₀).SX cosBasis).generator.domain
      rw [ιW_JW, heatData_SX]
      exact hw)
  have e : (heatSystem cosBasis hξ₀).ιW (JW hξ₀ χ hχ w) = ιW χ w := ιW_JW hξ₀ χ hχ w
  rw [e] at h
  exact h

/-- **`C` is point evaluation at `ξ₀`** (`ex:intro-pde`, `y(t) = x(t, ξ₀)`): if `ι_W w` is the class
of `φ ∈ H²_N(0, 1)`, then `C w = φ(ξ₀)`. -/
theorem heatSystemLoc_C {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') (w : W χ)
    (hw : ((heatSystemLoc hξ₀ χ hχ).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystemLoc hξ₀ χ hχ).C w = φ ξ₀ := by
  show (heatData hξ₀).C (JW hξ₀ χ hχ w) = φ ξ₀
  refine PDE.heatSystemL2_C hξ₀ h (JW hξ₀ χ hχ w) ?_
  have e : (PDE.heatSystemL2 hξ₀).ιW (JW hξ₀ χ hχ w) = ιW χ w := ιW_JW hξ₀ χ hχ w
  rw [e]
  exact hw

/-- Every `φ ∈ H²_N(0, 1)` is the state `ι_W w` of some `w ∈ W` (`D(A) ⊆ W`). -/
theorem exists_heatSystemLoc_ιW_ae_eq {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') :
    ∃ w : W χ, ((heatSystemLoc hξ₀ χ hχ).ιW w : ℝ → ℝ) =ᵐ[μI 1] φ := by
  obtain ⟨w, hw⟩ := exists_ιW_eq χ (PDE.mem_generator_domain_of_isNeumannH2 h h.memLp.coeFn_toLp)
  refine ⟨w, ?_⟩
  rw [heatSystemLoc_ιW, hw]
  exact h.memLp.coeFn_toLp

/-- **`C` is unbounded on `X`**: point evaluation is not bounded by the `L²` norm on `D(A)`. -/
theorem heatSystemLoc_C_unbounded :
    ¬ ∃ K : ℝ, ∀ w : W χ, (heatSystemLoc hξ₀ χ hχ).ιW w ∈ (heatSystemLoc hξ₀ χ hχ).A.domain →
      ‖(heatSystemLoc hξ₀ χ hχ).C w‖ ≤ K * ‖(heatSystemLoc hξ₀ χ hχ).ιW w‖ := by
  rintro ⟨K, hK⟩
  apply heatSystem_C_unbounded cosBasis hξ₀
  refine ⟨K, fun w' hw' => ?_⟩
  have hw'' : (heatData hξ₀).ιW cosBasis w' ∈ SX.generator.domain := by
    rw [← heatData_SX hξ₀]; exact hw'
  obtain ⟨w, hw⟩ := exists_ιW_eq χ hw''
  have hJ : JW hξ₀ χ hχ w = w' := (heatData hξ₀).ιW_injective cosBasis (by
    rw [ιW_JW, hw]; rfl)
  have h := hK w (by rw [heatSystemLoc_ιW, hw]; exact hw'')
  rw [← hJ]
  show ‖(heatData hξ₀).C (JW hξ₀ χ hχ w)‖ ≤ K * ‖(heatData hξ₀).ιW cosBasis (JW hξ₀ χ hχ w)‖
  rw [ιW_JW]
  exact h

/-- **`B` is unbounded on `X`**: `B 1 = b = -δ₀ ∉ X`. -/
theorem heatSystemLoc_B_not_mem_range :
    (heatSystemLoc hξ₀ χ hχ).B 1 ∉ Set.range (heatSystemLoc hξ₀ χ hχ).ιV := by
  rintro ⟨x, hx⟩
  apply heatSystem_B_not_mem_range cosBasis hξ₀
  refine ⟨x, ?_⟩
  show (heatData hξ₀).ιV cosBasis x = (heatData hξ₀).B 1
  have hx' : ιV χ x = B χ 1 := hx
  rw [← J_ιV hξ₀ χ hχ, hx', B_apply, map_smul, J_ctrlV, ControlData.B_apply]

/-- **`B⋆` in modal form**: `B⋆η = ∑ₙ bₙ ⟪eₙ, η⟫` on `D(A⋆)` (`System.inner_Bstar_of_dual`). -/
theorem hasSum_heatSystemLoc_Bstar {η : L2 ℝ 1}
    (hη : η ∈ (heatSystemLoc hξ₀ χ hχ).A.adjoint.domain) :
    HasSum (fun n => ctrlCoeff n * ⟪cosBasis n, η⟫_ℝ)
      ((heatSystemLoc hξ₀ χ hχ).Bstar ⟨η, hη⟩) := by
  have hA : (heatSystemLoc hξ₀ χ hχ).A.adjoint = SX.generator :=
    generator_adjoint_diag cosBasis heatModal.lam heatModal.bddAbove_lam
  have hηD : η ∈ SX.generator.domain := hA ▸ hη
  have hs := (mem_generator_domain_diag_iff cosBasis heatModal.lam heatModal.bddAbove_lam η).1 hηD
  have hsum : Summable fun n => ((1 - eig n) * ⟪cosBasis n, η⟫_ℝ) ^ 2 := by
    refine (((Diagonal.summable_inner_sq cosBasis η).mul_left 2).add
      (hs.mul_left 2)).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => ?_
    simp only [heatModal_lam]
    nlinarith [sq_nonneg (⟪cosBasis n, η⟫_ℝ + eig n * ⟪cosBasis n, η⟫_ℝ)]
  set ηm := mkL2 (fun n => (1 - eig n) * ⟪cosBasis n, η⟫_ℝ) hsum with hηm
  set ζ : V χ →L[ℝ] ℝ := (innerSL ℝ ηm).comp (fstV χ) with hζdef
  have hζ : ∀ x : L2 ℝ 1, ζ ((heatSystemLoc hξ₀ χ hχ).ιV x) =
      ⟪((⟨η, hη⟩ : (heatSystemLoc hξ₀ χ hχ).A.adjoint.domain) : L2 ℝ 1), x⟫_ℝ := by
    intro x
    simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, heatSystemLoc_ιV,
      fstV_ιV]
    refine (lp.hasSum_inner ηm (heatModal.toXm1 cosBasis x)).unique ?_
    convert cosBasis.hasSum_inner_mul_inner η x using 1
    funext n
    rw [hηm, mkL2_apply, heatModal.toXm1_apply, heatModal_wt, RCLike.inner_apply, conj_trivial,
      real_inner_comm η]
    field_simp [(one_sub_eig_pos n).ne']
  have h := System.inner_Bstar_of_dual (heatSystemLoc_H1_pos hξ₀ χ hχ one_pos) one_pos ⟨η, hη⟩
    ζ hζ 1
  have h1 : ⟪(heatSystemLoc hξ₀ χ hχ).Bstar ⟨η, hη⟩, (1 : ℝ)⟫_ℝ =
      (heatSystemLoc hξ₀ χ hχ).Bstar ⟨η, hη⟩ := by
    simp [RCLike.inner_apply]
  rw [show (heatSystemLoc hξ₀ χ hχ).Bstar ⟨η, hη⟩ = ζ ((heatSystemLoc hξ₀ χ hχ).B 1) from
    h1.symm.trans h]
  simp only [hζdef, ContinuousLinearMap.comp_apply, innerSL_apply_apply, heatSystemLoc_B,
    fstV_B, one_smul]
  convert lp.hasSum_inner ηm ctrlVec using 1
  funext n
  rw [hηm, mkL2_apply, ctrlVec_apply, RCLike.inner_apply, conj_trivial]
  field_simp [(one_sub_eig_pos n).ne']

/-- **`B⋆` is minus the trace at `0`** (`B⋆φ = -φ(0)`): for `η ∈ D(A⋆) = H²_N(0, 1)` the class of
`φ`, `B⋆ η = -φ(0)`. -/
theorem heatSystemLoc_Bstar {φ φ' φ'' : ℝ → ℝ} (h : PDE.IsNeumannH2 φ φ' φ'') {η : L2 ℝ 1}
    (hη : η ∈ (heatSystemLoc hξ₀ χ hχ).A.adjoint.domain) (hηφ : (η : ℝ → ℝ) =ᵐ[μI 1] φ) :
    (heatSystemLoc hξ₀ χ hχ).Bstar ⟨η, hη⟩ = -φ 0 :=
  (hasSum_heatSystemLoc_Bstar hξ₀ χ hχ hη).unique (PDE.hasSum_ctrlCoeff_mul_inner h hηφ)

/-! ### Approximate controllability and informativity -/

/-- The modal coordinates of the input-to-state map:
`⟪eₙ, L_T u⟫ = ∫₀ᵀ e^{λₙ (T - r)} ⟪bₙ, u(r)⟫ dr`. -/
theorem inner_ιW_Lop {T : ℝ} (hT : 0 < T) (u : L2 ℝ T) (n : ℕ) :
    ⟪cosBasis n, (heatSystemLoc hξ₀ χ hχ).ιW ((heatSystemLoc hξ₀ χ hχ).Lop T u)⟫_ℝ =
      ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * ⟪ctrlCoeff n, u r⟫_ℝ := by
  have hH1 := heatSystemLoc_H1_pos hξ₀ χ hχ hT
  have hL := (heatSystemLoc hξ₀ χ hχ).ιWV_L hH1 hT (Lp.memLp u)
  rw [(heatSystemLoc hξ₀ χ hχ).Lop_apply hH1 hT u]
  set w := (heatSystemLoc hξ₀ χ hχ).L T u
  have h1 : heatModal.toXm1 cosBasis (ιW χ w) =
      fstV χ (∫ r in Ioc 0 T, (SV χ).real (T - r) (B χ (u r))) := by
    rw [← fstV_ιV]
    exact congrArg (fstV χ) hL
  have h2 := congrArg (fun a : Xm1 => a n) h1
  simp only [heatModal.toXm1_apply, fstV_conv_apply, heatModal_wt] at h2
  have hw := (one_sub_eig_pos n).ne'
  have h3 : ⟪cosBasis n, ιW χ w⟫_ℝ =
      ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := by
    calc ⟪cosBasis n, ιW χ w⟫_ℝ = (1 - eig n) * ((1 - eig n)⁻¹ * ⟪cosBasis n, ιW χ w⟫_ℝ) := by
          rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
      _ = (1 - eig n) * (ctrlCoeff n / (1 - eig n) *
            ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r) := by rw [h2]
      _ = ctrlCoeff n * ∫ r in Ioc 0 T, Real.exp (eig n * (T - r)) * u r := by field_simp
  rw [heatSystemLoc_ιW, h3, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Approximate controllability** of `(A, B)` in every `T > 0` (`ex:boundary-heat-informative`). -/
theorem heatSystemLoc_approxControllable {T : ℝ} (hT : 0 < T) :
    (heatSystemLoc hξ₀ χ hχ).ApproxControllable T :=
  System.approxControllable_of_modal (heatSystemLoc hξ₀ χ hχ) cosBasis eig_injective
    (fun s hs => heatModal.summable_exp hs) (β := ctrlCoeff) (Cβ := Real.sqrt 2)
    (fun n => by rw [Real.norm_eq_abs]; exact abs_ctrlCoeff_le n) ctrlCoeff_ne_zero hT
    (heatSystemLoc_H1_pos hξ₀ χ hχ hT) (fun u n => inner_ιW_Lop hξ₀ χ hχ hT u n)

/-- `iω ∈ ρ(A)` for `ω ≠ 0`: the spectrum is real. -/
theorem mem_resolventSet_heatSystemLoc {ω : ℝ} (hω : ω ≠ 0) :
    ((0 : ℝ) : ℂ) + ω * Complex.I ∈ resolventSet (heatSystemLoc hξ₀ χ hχ).A.complexify := by
  refine mem_resolventSet_complexify_diag_of_notMem_closure cosBasis heatModal.lam
    heatModal.bddAbove_lam ?_
  have hcl : closure (Set.range fun n => (heatModal.lam n : ℂ)) ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal (by rintro _ ⟨n, rfl⟩; simp)
      (isClosed_eq Complex.continuous_im continuous_const)
  intro h
  have := hcl h
  simp at this
  exact hω this

/-- **`thm:analytic-universal-sufficiency`** for the localised heat system with the input `ū`. -/
theorem heatSystemLoc_TFAE {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') :
    [(heatSystemLoc hξ₀ χ hχ).ApproxControllable T,
      ∀ w₀ : W χ, Informative T heatInput ((heatSystemLoc hξ₀ χ hχ).mildW w₀ heatInput),
      ∀ x₀ : L2 ℝ 1,
        WindowInformative T T' heatInput ((heatSystemLoc hξ₀ χ hχ).mild x₀ heatInput)].TFAE := by
  have := Diagonal.separableSpace cosBasis
  have h := System.analytic_universal_sufficiency (sys := heatSystemLoc hξ₀ χ hχ) (T := T)
    (T' := T') (σ := 0) (M := 1) hT hT'
    (isAnalytic_diagSemigroup cosBasis heatModal.lam heatModal.bddAbove_lam)
    (heatSystemLoc_H1 hξ₀ χ hχ T) (heatSystemLoc_compat hξ₀ χ hχ) isHarmonicPE_heatInput
    (fun ω hω => mem_resolventSet_heatSystemLoc hξ₀ χ hχ (ne_zero_of_mem_closure_range_freq hω))
    (fun t => by
      rw [one_mul]
      exact norm_diagSemigroup_le cosBasis heatModal.lam heatModal.bddAbove_lam
        (fun n => heatModal.lam_nonpos n) t)
  rw [heatInput_eq] at h
  exact h

/-- **`ex:boundary-heat-informative`, (ii)**: `(ū, x̄)` is informative in `U × W` for every
`x̄₀ ∈ W`. -/
theorem heatSystemLoc_informative {T : ℝ} (hT : 0 < T) (w₀ : W χ) :
    Informative T heatInput ((heatSystemLoc hξ₀ χ hχ).mildW w₀ heatInput) :=
  ((heatSystemLoc_TFAE hξ₀ χ hχ hT one_pos).out 1 2).1
    (heatSystemLoc_approxControllable hξ₀ χ hχ hT) w₀

/-- **`ex:boundary-heat-informative`, (iii)**: `(ū, x̄)` is window informative for every
`x̄₀ ∈ X`. -/
theorem heatSystemLoc_windowInformative {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (x₀ : L2 ℝ 1) :
    WindowInformative T T' heatInput ((heatSystemLoc hξ₀ χ hχ).mild x₀ heatInput) :=
  ((heatSystemLoc_TFAE hξ₀ χ hχ hT hT').out 1 3).1
    (heatSystemLoc_approxControllable hξ₀ χ hχ hT) x₀

/-! ### The example with the paper's spaces -/

/-- **`ex:boundary-heat-informative` with the paper's localised spaces**
(`app:boundary-heat-informative`, `eq:heat-localized-V`, `eq:heat-W-domain`).  Let `ξ₀ ∈ (0, 1)`
and let `χ ∈ C¹` with `supp χ ⊆ (0, 1)` and `χ = 1` near `ξ₀` (every `χ ∈ C_c^∞(0, 1)` equal to one
near `ξ₀` qualifies; one exists by `exists_smooth_cutoff`).  There are Hilbert spaces
`W ↪ L²(0, 1) ↪ V` and a system on them such that:
* `V` is the paper's space: `ζ : V → X₋₁` is injective and the identity on `X`, and
  `‖v‖²_V = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} (∫₀¹ (χ S(t) z)² + ∫₀¹ (∂_ξ (χ S(t) z))²) dt` for `z = ζ v`,
  `V = {z ∈ X₋₁ : this is finite}`, and `S_V` extends `S_{X₋₁}`;
* `W = D(A_V) = {x ∈ X : A_{X,-1} x ∈ V}` (`eq:heat-W-domain`, as a set) with `hyp:compat`;
* the generator is the Neumann Laplacian (`D(A) = H²_N(0, 1)`, `A φ = φ''`, `A⋆ = A`),
  `B⋆η = -η(0)`, `H²_N(0, 1) ⊆ W` and `C` is the point evaluation at `ξ₀` there;
* `hyp:H1`, `hyp:H2` hold at every horizon, while `B` and `C` are unbounded on `L²(0, 1)`;
* `ū` is harmonically persistently exciting, `(A, B)` is approximately controllable in every
  positive time, and `(ū, x̄)` is informative in `U × W` for every `x̄₀ ∈ W` and window
  informative for every `x̄₀ ∈ L²(0, 1)`. -/
theorem exists_boundaryHeat_loc {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ Ioo 0 1) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχs : tsupport χ ⊆ Ioo 0 1) (hχ₀ : χ =ᶠ[𝓝 ξ₀] 1) :
    ∃ (W V : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W) (_ : CompleteSpace W)
      (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ W (L2 ℝ 1) V ℝ) (ζ : V →L[ℝ] Xm1),
      Function.Injective ζ ∧
      (∀ x : L2 ℝ 1, ζ (sys.ιV x) = heatModal.toXm1 cosBasis x) ∧
      (∀ v : V, ‖v‖ ^ 2 = ‖ζ v‖ ^ 2 +
        ∫ t in Ioi 0, Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit (ζ v) t ξ)) ∧
      (∀ a : Xm1, a ∈ Set.range ζ ↔
        IntegrableOn (fun t => Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit a t ξ)) (Ioi 0)) ∧
      C0Semigroup.Consistent ζ sys.SV heatModal.Sm ∧
      Set.range sys.ιW = {x | IntegrableOn (fun t => Real.exp (-2 * t) *
        H1sq (fun ξ => χ ξ * orbit (heatModal.genXm1 cosBasis x) t ξ)) (Ioi 0)} ∧
      sys.SX = diagSemigroup cosBasis eig bddAbove_eig ∧
      (∀ p : L2 ℝ 1 × L2 ℝ 1, p ∈ sys.A.graph ↔
        ∃ φ φ' φ'' : ℝ → ℝ, PDE.IsNeumannH2 φ φ' φ'' ∧ (p.1 : ℝ → ℝ) =ᵐ[μI 1] φ ∧
          (p.2 : ℝ → ℝ) =ᵐ[μI 1] φ'') ∧
      sys.A.adjoint = sys.A ∧
      (∀ (η : L2 ℝ 1) (hη : η ∈ sys.A.adjoint.domain) (φ φ' φ'' : ℝ → ℝ),
        PDE.IsNeumannH2 φ φ' φ'' → (η : ℝ → ℝ) =ᵐ[μI 1] φ → sys.Bstar ⟨η, hη⟩ = -φ 0) ∧
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
  exact ⟨W c, V c, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, heatSystemLoc hξ₀ c h1, fstV c, fstV_injective c, fun _ => rfl,
    norm_V_sq_eq c, exists_fstV_eq_iff c, consistent_fstV c, range_ιW c, rfl,
    PDE.mem_graph_generator_iff, generator_adjoint_diag cosBasis eig bddAbove_eig,
    fun _ hη _ _ _ h hηφ => heatSystemLoc_Bstar hξ₀ c h1 h hη hηφ,
    fun _ _ _ h => exists_heatSystemLoc_ιW_ae_eq hξ₀ c h1 h,
    fun w _ _ _ h hw => heatSystemLoc_C hξ₀ c h1 h w hw,
    heatSystemLoc_H1 hξ₀ c h1, heatSystemLoc_H2 hξ₀ c h1, heatSystemLoc_compat hξ₀ c h1,
    heatSystemLoc_B_not_mem_range hξ₀ c h1, heatSystemLoc_C_unbounded hξ₀ c h1,
    isHarmonicPE_heatInput,
    fun _ hT => heatSystemLoc_approxControllable hξ₀ c h1 hT,
    fun _ hT w₀ => heatSystemLoc_informative hξ₀ c h1 hT w₀,
    fun _ hT _ hT' x₀ => heatSystemLoc_windowInformative hξ₀ c h1 hT hT' x₀⟩

end Localized

end BoundaryHeat

end DataDrivenControl
