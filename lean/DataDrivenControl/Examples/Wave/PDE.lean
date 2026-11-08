module

public import Mathlib
public import DataDrivenControl.Analysis.Sobolev01
public import DataDrivenControl.Examples.Wave.System

/-!
# The wave equation with Dirichlet control on `L²(0, 1) × H⁻¹(0, 1)`: the dictionary

Paper: `ex:intro-wave` (`introduction.tex`): `∂ₜₜw = c² ∂_ξξ w` on `(0, 1)`, `w(t, 0) = u(t)`,
`w(t, 1) = 0`, `y(t) = ∫₀¹ q w(t, ·)`, as a first-order system for `x = (w, ∂ₜw)` on
`X = L²(0, 1) × H⁻¹(0, 1)`.

`Examples/Wave/System` proves the paper's claims for the modal model `waveSystem s f c q` on any
`X₁ × X₂` with Hilbert bases `s`, `f`.  This file instantiates it with the function spaces of
`Analysis/SineBasis` and `Analysis/Sobolev01` and states its ties to the PDE in function language.

## The instance and the scaling of the velocity

* `X₁ = L2 ℝ 1` with `s = sinBasis` (`sₙ(ξ) = √2 sin((n + 1)πξ)`).
* `X₂ = Hm1 = StrongDual ℝ H10`, `H⁻¹(0, 1)` with its dual norm, with `f = hm1Basis`,
  `hm1Basis n = (n + 1)π sₙ` (`hm1Basis_eq`).
* The paper takes `X₂ = H⁻¹` with the norm `c⁻¹‖·‖_{H⁻¹}` and the basis `fₙ = ωₙ sₙ`.  Here the
  scaling sits in the identification of the state: the velocity of the state `x = (w, x₂)` is
  `∂ₜw = c • x₂` (`waveSystemL2_Lop`).  The map `x₂ ↦ c • x₂` is an isometry from `Hm1` onto
  `H⁻¹` with the norm `c⁻¹‖·‖` (`norm_eq_inv_mul_norm_smul`) that sends `hm1Basis n` to
  `ωₙ sₙ` (`smul_hm1Basis`); in the scaled inner product `c⁻² ⟪·, ·⟫_{H⁻¹}` the `ωₙ sₙ` are
  orthonormal and complete (`scaledInner_freq_smul`, `hasSum_scaledInner_sq`).  So the energy
  norm of the state is `‖w‖²_{L²} + c⁻² ‖∂ₜw‖²_{H⁻¹}`, as in the paper.

## Main declarations

* **`waveSystemL2 c q = waveSystem sinBasis hm1Basis c q`**, `q ∈ L²(0, 1)`.
* `waveSystemL2_C`: **`C x = ∫₀¹ q w`**.
* `waveSystemL2_Lop`: the input-to-state map in function language: `∫₀¹ sₙ w(T)` and
  `∂ₜw(T)(sₙ)` (the velocity `c • x₂` applied to `sₙ ∈ H¹₀`) are the modal solutions.
* **The function form of `B⋆`**: for `η ∈ D(A⋆)`, let `ζ = (-∂_ξξ)⁻¹ η₂ ∈ H¹₀ ∩ H²` be the
  Dirichlet solution for the velocity component `η₂ = c • η.snd ∈ H⁻¹` (in weak form,
  `∫₀¹ ζ' ψ' = η₂(ψ)` for `ψ ∈ H¹₀`); then `B⋆ η = ζ'(0)` (`waveSystemL2_Bstar`), and such a `ζ`
  exists (`exists_isDirichletH2_of_mem_adjoint_domain`).  This is the normal derivative at the
  controlled end that defines Dirichlet boundary control.
* **The generator** (`waveSystemL2_A_domain`, `waveSystemL2_A_apply`): `D(A) = H¹₀ × L²`
  (`x₁ = ofH10 φ` with `φ ∈ H¹₀`, `x₂ = embed v` with `v ∈ L²`) and
  `A (φ, v) = (c v, c ∂_ξξ φ)`, where
  `∂_ξξ φ = lap φ ∈ H⁻¹` is the functional `ψ ↦ -∫₀¹ φ' ψ'`; with the velocity `c • x₂`, this is
  the paper's `A (w, v) = (v, c² ∂_ξξ w)`.
* `exists_wave`: **`ex:intro-wave`** on `L²(0, 1) × H⁻¹(0, 1)`, in existential form with these
  ties.

## Constants and signs of `B⋆`

`hasSum_waveSystem_Bstar` gives `B⋆ η = ∑ₙ c √2 ⟪hm1Basis n, η.snd⟫`, and
`⟪hm1Basis n, η.snd⟫ = η.snd (h10Basis n)`.  With `ζ' = riesz⁻¹ (c • η.snd)` (the derivative of
`ζ`), `c ⟪hm1Basis n, η.snd⟫ = ⟪e_{n+1}, ζ'⟫`, so the terms are `e_{n+1}(0) ⟪e_{n+1}, ζ'⟫`.  The
cosine series of `ζ'` converges absolutely at `0` because `ζ'' ∈ L²`, and its `e₀` term is
`∫₀¹ ζ' = ζ(1) - ζ(0) = 0`; so the sum is `ζ'(0)`, with constant `1` and sign `+`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace Wave

namespace PDE

open CosineBasis SineBasis Sobolev01

/-- The state space `L²(0, 1) × H⁻¹(0, 1)`. -/
abbrev State : Type := WithLp 2 (L2 ℝ 1 × Hm1)

/-- `ωₙ = c (n + 1)π`. -/
theorem freq_eq (c : ℝ) (n : ℕ) : freq c n = c * sinFreq n := by
  unfold freq sinFreq; ring

/-- `⟪r • ℓ, ℓ'⟫ = r ⟪ℓ, ℓ'⟫` in `Hm1`. -/
theorem inner_smul_left_Hm1 (ℓ ℓ' : Hm1) (r : ℝ) : ⟪r • ℓ, ℓ'⟫_ℝ = r * ⟪ℓ, ℓ'⟫_ℝ :=
  real_inner_smul_left (F := Hm1) _ _ _

/-! ### The velocity space `H⁻¹` with the norm `c⁻¹‖·‖` -/

/-- **`c • hm1Basis n = ωₙ sₙ`**: under the velocity map, the basis `f = hm1Basis` of the state
space becomes the paper's `fₙ = ωₙ sₙ`. -/
theorem smul_hm1Basis (c : ℝ) (n : ℕ) : c • hm1Basis n = freq c n • embed (sinBasis n) := by
  rw [hm1Basis_eq, smul_smul, freq_eq]

section Scaling

variable {c : ℝ} (hc : 0 < c)
include hc

/-- `x₂ ↦ c • x₂` is an isometry from `Hm1` onto `H⁻¹` with the norm `c⁻¹‖·‖`. -/
theorem norm_eq_inv_mul_norm_smul (x : Hm1) : ‖x‖ = c⁻¹ * ‖c • x‖ := by
  have h : ‖c • x‖ = ‖c‖ * ‖x‖ :=
    (NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := Hm1)).norm_smul c x
  rw [h, Real.norm_of_nonneg hc.le, inv_mul_cancel_left₀ hc.ne']

/-- **The `ωₙ sₙ` are orthonormal in `H⁻¹` with the norm `c⁻¹‖·‖`**, i.e. for the inner product
`c⁻² ⟪·, ·⟫_{H⁻¹}`. -/
theorem scaledInner_freq_smul (m n : ℕ) :
    (c ^ 2)⁻¹ * ⟪freq c m • embed (sinBasis m), freq c n • embed (sinBasis n)⟫_ℝ =
      if m = n then 1 else 0 := by
  rw [← smul_hm1Basis, ← smul_hm1Basis, inner_smul_left_Hm1, inner_smul_right_Hm1,
    orthonormal_iff_ite.1 hm1Basis.orthonormal]
  split_ifs <;> field_simp [hc.ne']

/-- **The `ωₙ sₙ` are complete in `H⁻¹` with the norm `c⁻¹‖·‖`**: Parseval's identity
`c⁻² ‖ℓ‖² = ∑ₙ (c⁻² ⟪ωₙ sₙ, ℓ⟫)²` for the inner product `c⁻² ⟪·, ·⟫_{H⁻¹}`. -/
theorem hasSum_scaledInner_sq (ℓ : Hm1) :
    HasSum (fun n => ((c ^ 2)⁻¹ * ⟪freq c n • embed (sinBasis n), ℓ⟫_ℝ) ^ 2)
      ((c ^ 2)⁻¹ * ‖ℓ‖ ^ 2) := by
  convert (hasSum_sq_inner hm1Basis ℓ).mul_left (c ^ 2)⁻¹ using 1
  funext n
  rw [← smul_hm1Basis, inner_smul_left_Hm1]
  field_simp [hc.ne']

end Scaling

/-! ### The system -/

variable (c : ℝ) (q : L2 ℝ 1)

/-- **The wave equation with Dirichlet control on `L²(0, 1) × H⁻¹(0, 1)`** (`ex:intro-wave`):
`waveSystem` with the sine basis of `L²(0, 1)` and the basis `(n + 1)π sₙ` of `H⁻¹(0, 1)`; the
state `(w, x₂)` has displacement `w` and velocity `c • x₂`. -/
abbrev waveSystemL2 : System ℝ State State Vsp ℝ := waveSystem sinBasis hm1Basis c q

/-- **`C` is the weighted integral observation** `C x = ∫₀¹ q w`. -/
theorem waveSystemL2_C (x : State) :
    (waveSystemL2 c q).C x = ∫ ξ in (0 : ℝ)..1, q ξ * x.fst ξ := by
  rw [waveSystem_C, Cop_apply, inner_eq_integral]

/-- **The input-to-state map in function language** (`c > 0`, `u ∈ L²(0, T)`): the state
`L_T u = (w, x₂)` reached from rest has `∫₀¹ sₙ w = c √2 ∫₀ᵀ sin(ωₙ (T - r)) u(r) dr` and
velocity `∂ₜw = c • x₂` with `∂ₜw(sₙ) = ωₙ c √2 ∫₀ᵀ cos(ωₙ (T - r)) u(r) dr`: the modal
solutions of `∂ₜₜw = c² ∂_ξξ w`, `w(·, 0) = u`, `w(·, 1) = 0`. -/
theorem waveSystemL2_Lop (hc : 0 < c) {T : ℝ} (u : L2 ℝ T) (n : ℕ) :
    ∫ ξ in (0 : ℝ)..1, sinFun n ξ * ((waveSystemL2 c q).Lop T u).fst ξ =
        c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.sin (freq c n * (T - r)) * u r ∧
      (c • ((waveSystemL2 c q).Lop T u).snd) (sinH10 n) =
        freq c n * (c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.cos (freq c n * (T - r)) * u r) := by
  obtain ⟨h1, h2⟩ := inner_waveSystem_Lop sinBasis hm1Basis c q hc u n
  refine ⟨by rw [← inner_sinBasis, h1], ?_⟩
  rw [smul_apply, apply_sinH10, h2, smul_eq_mul, freq_eq]
  ring

/-! ### `D(A⋆)` and `B⋆` -/

/-- `A⋆` is the generator of the rotation group with frequencies `-ωₙ`. -/
theorem waveSystemL2_A_adjoint :
    (waveSystemL2 c q).A.adjoint =
      (Rotation.rotGroup sinBasis hm1Basis fun n => -freq c n).generator := by
  show (Rotation.rotGroup sinBasis hm1Basis (freq c)).generator.adjoint = _
  rw [← C0Semigroup.generator_adjoint, Rotation.adjoint_rotGroup]

/-- On `D(A⋆)`: `∑ₙ (ωₙ ⟪hm1Basis n, η₂⟫)² < ∞`. -/
theorem summable_sq_snd_of_mem_adjoint_domain {η : State}
    (hη : η ∈ (waveSystemL2 c q).A.adjoint.domain) :
    Summable fun n => (freq c n * ⟪hm1Basis n, η.snd⟫_ℝ) ^ 2 := by
  have hηD : η ∈ (Rotation.rotGroup sinBasis hm1Basis fun n => -freq c n).generator.domain :=
    waveSystemL2_A_adjoint c q ▸ hη
  refine (Rotation.hasSum_sq_generator sinBasis hm1Basis _ ⟨η, hηD⟩).summable.of_nonneg_of_le
    (fun n => sq_nonneg _) fun n => ?_
  rw [neg_sq, mul_pow]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)

/-- **The function form of `B⋆`** (`ex:intro-wave`, Dirichlet control).  Let `η ∈ D(A⋆)` and let
`ζ ∈ H¹₀(0, 1) ∩ H²(0, 1)` solve `-ζ'' = η₂` weakly, where `η₂ = c • η.snd ∈ H⁻¹` is the velocity
component of `η`: `∫₀¹ ζ' ψ' = c η.snd(ψ)` for every `ψ ∈ H¹₀`.  Then `B⋆ η = ζ'(0)`. -/
theorem waveSystemL2_Bstar (hc : 0 < c) {η : State}
    (hη : η ∈ (waveSystemL2 c q).A.adjoint.domain) {ζ ζ' ζ'' : ℝ → ℝ}
    (hζ : IsDirichletH2 ζ ζ' ζ'')
    (hweak : ∀ ψ : H10, ∫ t in (0 : ℝ)..1, ζ' t * (ψ : L2 ℝ 1) t = c * η.snd ψ) :
    (waveSystemL2 c q).Bstar ⟨η, hη⟩ = ζ' 0 := by
  have hζ'L : MemLp ζ' 2 (μI 1) := hζ.hasWeakDeriv.memLp_deriv
  set G : L2 ℝ 1 := hζ'L.toLp ζ' with hG
  -- the modal terms of `B⋆ η` are the cosine terms of `ζ'` at `0`
  have hcoef : ∀ n, c * Real.sqrt 2 * ⟪hm1Basis n, η.snd⟫_ℝ =
      cosFun (n + 1) 0 * ⟪cosBasis (n + 1), G⟫_ℝ := by
    intro n
    rw [hG, inner_hm1Basis, cosFun_succ_zero, inner_cosBasis_toLp, mul_comm c, mul_assoc,
      ← hweak (h10Basis n), coe_h10Basis, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coeFn_cosBasis (n + 1)] with t ht
    rw [ht, mul_comm]
  -- `∫₀¹ ζ' = 0`
  have hG0 : ⟪cosBasis 0, G⟫_ℝ = 0 := by
    have h := hζ.hasWeakDeriv.eq_add_integral 1 ⟨zero_le_one, le_rfl⟩
    rw [hζ.zero, hζ.one, zero_add] at h
    rw [hG, inner_cosBasis_toLp]
    simp only [cosFun_zero, one_mul]
    exact h.symm
  -- `⟪e_{n+1}, ζ'⟫ = -⟪sₙ, ζ''⟫ / ((n + 1)π)`, absolutely summable
  have hζ''L : MemLp ζ'' 2 (μI 1) := hζ.hasWeakDeriv_deriv.memLp_deriv
  have hGn : ∀ n, ⟪cosBasis (n + 1), G⟫_ℝ =
      -⟪sinBasis n, hζ''L.toLp ζ''⟫_ℝ / sinFreq n := by
    intro n
    have h := integral_sinFun_mul_deriv hζ.hasWeakDeriv_deriv n
    rw [hG, inner_cosBasis_toLp, inner_sinBasis_of_ae_eq hζ''L.coeFn_toLp, h]
    field_simp [(sinFreq_pos n).ne']
  have hsum : Summable fun k => |⟪cosBasis k, G⟫_ℝ| := by
    rw [← summable_nat_add_iff 1]
    refine (summable_abs_div_sinFreq (a := fun n => -⟪sinBasis n, hζ''L.toLp ζ''⟫_ℝ)
      (by simpa only [neg_sq] using Diagonal.summable_inner_sq sinBasis (hζ''L.toLp ζ''))).congr
      fun n => ?_
    rw [hGn]
  -- point evaluation of the cosine series of `ζ'` at `0`
  have h1 := hasSum_cosFun_mul_inner hsum hζ.hasWeakDeriv_deriv.continuousOn hζ'L.coeFn_toLp
    ⟨le_rfl, zero_le_one⟩
  have h2 := (hasSum_nat_add_iff' 1).2 h1
  simp only [Finset.range_one, Finset.sum_singleton, hG0, mul_zero, sub_zero] at h2
  refine (hasSum_waveSystem_Bstar sinBasis hm1Basis c q hc hη).unique ?_
  convert h2 using 1
  funext n
  exact hcoef n

/-- **`(-∂_ξξ)⁻¹ η₂ ∈ H¹₀ ∩ H²` on `D(A⋆)`**: for `η ∈ D(A⋆)` the Dirichlet problem
`-ζ'' = c • η.snd` has a solution `ζ ∈ H¹₀(0, 1) ∩ H²(0, 1)`. -/
theorem exists_isDirichletH2_of_mem_adjoint_domain (hc : 0 < c) {η : State}
    (hη : η ∈ (waveSystemL2 c q).A.adjoint.domain) :
    ∃ ζ ζ' ζ'' : ℝ → ℝ, IsDirichletH2 ζ ζ' ζ'' ∧
      ∀ ψ : H10, ∫ t in (0 : ℝ)..1, ζ' t * (ψ : L2 ℝ 1) t = c * η.snd ψ := by
  have hs := summable_sq_snd_of_mem_adjoint_domain c q hη
  obtain ⟨v, hv⟩ := Diagonal.exists_inner_eq sinBasis
    (fun n => freq c n * ⟪hm1Basis n, η.snd⟫_ℝ) hs
  have hemb : embed v = c • η.snd := by
    refine basis_ext hm1Basis fun n => ?_
    rw [inner_hm1Basis_embed, hv, inner_smul_right_Hm1, freq_eq]
    field_simp [(sinFreq_pos n).ne']
  obtain ⟨ζ', hD, hae⟩ := exists_isDirichletH2_toH10 v
  refine ⟨_, ζ', _, hD, fun ψ => ?_⟩
  have h1 : (c • η.snd) ψ = c * η.snd ψ := by
    rw [smul_apply, smul_eq_mul]
  rw [← h1, ← hemb, embed_apply, ← inner_toH10, inner_H10,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  rw [ht]

/-! ### The generator -/

/-- `∂_ξξ φ ∈ H⁻¹(0, 1)` for `φ ∈ H¹₀(0, 1)`: the functional `ψ ↦ -∫₀¹ φ' ψ'`. -/
def lap (φ : H10) : Hm1 := -riesz φ

/-- The coordinates of the pair `(c v, c ∂_ξξ φ)`. -/
theorem inner_coord_gen (φ : H10) (v : L2 ℝ 1) (n : ℕ) :
    ⟪sinBasis n, c • v⟫_ℝ = freq c n * ⟪hm1Basis n, embed v⟫_ℝ ∧
      ⟪hm1Basis n, c • lap φ⟫_ℝ = -freq c n * ⟪sinBasis n, ofH10 φ⟫_ℝ := by
  constructor
  · rw [real_inner_smul_right, inner_hm1Basis_embed, freq_eq]
    field_simp [(sinFreq_pos n).ne']
  · rw [inner_smul_right_Hm1, inner_hm1Basis, lap, neg_apply, riesz_apply,
      inner_sinBasis_ofH10, real_inner_comm, freq_eq]
    field_simp [(sinFreq_pos n).ne']

/-- **`D(A) ⊆ H¹₀ × L²`**, with `A (φ, v) = (c v, c ∂_ξξ φ)`. -/
theorem exists_of_mem_A_domain (hc : 0 < c) {x : State}
    (hx : x ∈ (waveSystemL2 c q).A.domain) :
    ∃ (φ : H10) (v : L2 ℝ 1), ofH10 φ = x.fst ∧ embed v = x.snd := by
  have hs := (Rotation.hasSum_sq_generator sinBasis hm1Basis (freq c) ⟨x, hx⟩).summable
  have ha : Summable fun n => (sinFreq n * ⟪sinBasis n, x.fst⟫_ℝ) ^ 2 := by
    refine (hs.mul_left (c ^ 2)⁻¹).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
    rw [freq_eq]
    have h : (sinFreq n * ⟪sinBasis n, x.fst⟫_ℝ) ^ 2 =
        (c ^ 2)⁻¹ * ((c * sinFreq n) ^ 2 * ⟪sinBasis n, x.fst⟫_ℝ ^ 2) := by
      field_simp [hc.ne']
    rw [h]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)) (by positivity)
  have hb : Summable fun n => (sinFreq n * ⟪hm1Basis n, x.snd⟫_ℝ) ^ 2 := by
    refine (hs.mul_left (c ^ 2)⁻¹).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
    rw [freq_eq]
    have h : (sinFreq n * ⟪hm1Basis n, x.snd⟫_ℝ) ^ 2 =
        (c ^ 2)⁻¹ * ((c * sinFreq n) ^ 2 * ⟪hm1Basis n, x.snd⟫_ℝ ^ 2) := by
      field_simp [hc.ne']
    rw [h]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)) (by positivity)
  obtain ⟨φ, hφ⟩ := Diagonal.exists_inner_eq h10Basis _ ha
  obtain ⟨v, hv⟩ := Diagonal.exists_inner_eq sinBasis _ hb
  refine ⟨φ, v, basis_ext sinBasis fun n => ?_, basis_ext hm1Basis fun n => ?_⟩
  · rw [inner_sinBasis_ofH10, hφ]
    field_simp [(sinFreq_pos n).ne']
  · rw [inner_hm1Basis_embed, hv]
    field_simp [(sinFreq_pos n).ne']

/-- **`H¹₀ × L² ⊆ D(A)`**: `A = (A₋)†` for the generator `A₋` of the rotation group with
frequencies `-ωₙ`, and `(c v, c ∂_ξξ φ)` represents `y ↦ ⟪(φ, v), A₋ y⟫`. -/
theorem mem_A_domain (φ : H10) (v : L2 ℝ 1) :
    (WithLp.toLp 2 (ofH10 φ, embed v) : State) ∈ (waveSystemL2 c q).A.domain := by
  have hA : (waveSystemL2 c q).A =
      (Rotation.rotGroup sinBasis hm1Basis fun n => -freq c n).generator.adjoint := by
    show (Rotation.rotGroup sinBasis hm1Basis (freq c)).generator = _
    rw [← C0Semigroup.generator_adjoint, Rotation.adjoint_rotGroup]
    simp only [neg_neg]
  rw [hA]
  refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨WithLp.toLp 2 (c • v, c • lap φ), fun y => ?_⟩
  refine (Rotation.hasSum_inner_coord sinBasis hm1Basis _ _).unique ?_
  convert Rotation.hasSum_inner_coord sinBasis hm1Basis (WithLp.toLp 2 (ofH10 φ, embed v) : State)
    ((Rotation.rotGroup sinBasis hm1Basis fun n => -freq c n).generator y) using 1
  funext n
  obtain ⟨h1, h2⟩ := inner_coord_gen c φ v n
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [h1, h2, Rotation.inner_fst_generator, Rotation.inner_snd_generator]
  ring

/-- **`D(A) = H¹₀ × L²`** (`ex:intro-wave`): `x ∈ D(A)` iff the displacement is the class of some
`φ ∈ H¹₀(0, 1)` and the state velocity is (the functional of) some `v ∈ L²(0, 1)`. -/
theorem waveSystemL2_A_domain (hc : 0 < c) (x : State) :
    x ∈ (waveSystemL2 c q).A.domain ↔
      ∃ (φ : H10) (v : L2 ℝ 1), ofH10 φ = x.fst ∧ embed v = x.snd := by
  refine ⟨exists_of_mem_A_domain c q hc, fun ⟨φ, v, h1, h2⟩ => ?_⟩
  have : x = WithLp.toLp 2 (ofH10 φ, embed v) := by rw [h1, h2]; rfl
  rw [this]
  exact mem_A_domain c q φ v

/-- **The generator in function form** (`ex:intro-wave`): `A (φ, v) = (c v, c ∂_ξξ φ)` for
`φ ∈ H¹₀(0, 1)` and `v ∈ L²(0, 1)`.  With the velocity `c • x₂` this is the paper's
`A (w, v) = (v, c² ∂_ξξ w)`. -/
theorem waveSystemL2_A_apply {x : State} (hx : x ∈ (waveSystemL2 c q).A.domain) {φ : H10}
    {v : L2 ℝ 1} (hφ : ofH10 φ = x.fst) (hv : embed v = x.snd) :
    (waveSystemL2 c q).A ⟨x, hx⟩ = WithLp.toLp 2 (c • v, c • lap φ) := by
  refine Rotation.ext_coord sinBasis hm1Basis (fun n => ?_) fun n => ?_
  · show _ = ⟪sinBasis n, c • v⟫_ℝ
    rw [(inner_coord_gen c φ v n).1, hv]
    exact Rotation.inner_fst_generator sinBasis hm1Basis (freq c) ⟨x, hx⟩ n
  · show _ = ⟪hm1Basis n, c • lap φ⟫_ℝ
    rw [(inner_coord_gen c φ v n).2, hφ]
    exact Rotation.inner_snd_generator sinBasis hm1Basis (freq c) ⟨x, hx⟩ n

/-! ### The paper's statement -/

/-- **`ex:intro-wave` on `L²(0, 1) × H⁻¹(0, 1)`** (existential form, `c > 0`, `q ∈ L²(0, 1)`):
on `X = L²(0, 1) × H⁻¹(0, 1)` there are a Hilbert space `V` and a system on `W = X ↪ V` whose
semigroup is the block-rotation group of the sine basis with `ωₙ = c (n + 1) π`, whose generator
is `A (φ, v) = (c v, c ∂_ξξ φ)` on `D(A) = H¹₀ × L²`, whose `B⋆` is the derivative at `0` of
`(-∂_ξξ)⁻¹` of the velocity component on `D(A⋆)`, and whose `C` is `x ↦ ∫₀¹ q w`, such that
`hyp:H1`, `hyp:H2` (every horizon) and `hyp:compat` hold, `B` is unbounded on `X`, `C` is bounded
on `X`, and the semigroup is not analytic.  The state `(w, x₂)` has velocity `c • x₂`. -/
theorem exists_wave (hc : 0 < c) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (_ : CompleteSpace V)
      (sys : System ℝ State State V ℝ),
      sys.ιW = ContinuousLinearMap.id ℝ _ ∧
      sys.SX = Rotation.rotGroup sinBasis hm1Basis (freq c) ∧
      (∀ x : State, x ∈ sys.A.domain ↔
        ∃ (φ : H10) (v : L2 ℝ 1), ofH10 φ = x.fst ∧ embed v = x.snd) ∧
      (∀ (x : State) (hx : x ∈ sys.A.domain) (φ : H10) (v : L2 ℝ 1),
        ofH10 φ = x.fst → embed v = x.snd → sys.A ⟨x, hx⟩ = WithLp.toLp 2 (c • v, c • lap φ)) ∧
      (∀ (T : ℝ) (u : L2 ℝ T) (n : ℕ),
        ∫ ξ in (0 : ℝ)..1, sinFun n ξ * (sys.Lop T u).fst ξ =
            c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.sin (freq c n * (T - r)) * u r ∧
          (c • (sys.Lop T u).snd) (sinH10 n) =
            freq c n * (c * Real.sqrt 2 * ∫ r in Ioc 0 T, Real.cos (freq c n * (T - r)) * u r)) ∧
      (∀ η : State, η ∈ sys.A.adjoint.domain →
        ∃ ζ ζ' ζ'' : ℝ → ℝ, IsDirichletH2 ζ ζ' ζ'' ∧
          ∀ ψ : H10, ∫ t in (0 : ℝ)..1, ζ' t * (ψ : L2 ℝ 1) t = c * η.snd ψ) ∧
      (∀ (η : State) (hη : η ∈ sys.A.adjoint.domain) (ζ ζ' ζ'' : ℝ → ℝ),
        IsDirichletH2 ζ ζ' ζ'' →
        (∀ ψ : H10, ∫ t in (0 : ℝ)..1, ζ' t * (ψ : L2 ℝ 1) t = c * η.snd ψ) →
        sys.Bstar ⟨η, hη⟩ = ζ' 0) ∧
      (∀ x : State, sys.C x = ∫ ξ in (0 : ℝ)..1, q ξ * x.fst ξ) ∧
      (∀ T, sys.H1 T) ∧ (∀ T, sys.H2 T) ∧ sys.Compat ∧
      (∀ u : ℝ, u ≠ 0 → sys.B u ∉ Set.range sys.ιV) ∧
      (∀ x, ‖sys.C x‖ ≤ ‖q‖ * ‖sys.ιW x‖) ∧
      ¬ sys.SX.IsAnalytic :=
  ⟨Vsp, inferInstance, inferInstance, inferInstance, waveSystemL2 c q, rfl, rfl,
    waveSystemL2_A_domain c q hc, fun _ hx _ _ hφ hv => waveSystemL2_A_apply c q hx hφ hv,
    fun _ u n => waveSystemL2_Lop c q hc u n,
    fun _ hη => exists_isDirichletH2_of_mem_adjoint_domain c q hc hη,
    fun _ hη _ _ _ hζ hweak => waveSystemL2_Bstar c q hc hη hζ hweak,
    waveSystemL2_C c q,
    waveSystem_H1 sinBasis hm1Basis c q hc, waveSystem_H2 sinBasis hm1Basis c q hc,
    waveSystem_compat sinBasis hm1Basis c q,
    fun _ hu => waveSystem_B_apply_not_mem_range sinBasis hm1Basis c q hc.ne' hu,
    norm_waveSystem_C_le sinBasis hm1Basis c q,
    waveSystem_not_isAnalytic sinBasis hm1Basis c q hc.ne'⟩

end PDE

end Wave

end DataDrivenControl
