module

public import DataDrivenControl.Informativity.PE
public import DataDrivenControl.System.Controllability
public import DataDrivenControl.Semigroup.Diagonal

/-!
# Necessity of persistency of excitation

Paper: `prop:hilbert-pe-necessary` (`app:pe-necessity`, `eq:pe-necessary-transfer`).

## Main declarations

* `persistentlyExciting_of_forall_informative` (`prop:hilbert-pe-necessary`, `N < ∞`): if `X`
  has finite dimension `N` and `ū` produces an informative record for every admissible pair
  `(A, B)` and every initial state, then `ū` is persistently exciting of order `N + 1`.
* `persistentlyExcitingInfinite_of_forall_informative` (`prop:hilbert-pe-necessary`, `N = ∞`):
  if `X` is separable and infinite-dimensional, `ū` is persistently exciting of infinite order.

## Deviation (strengthening)

The paper's hypothesis quantifies over *every* approximately controllable pair `(A, B)` on `X`
satisfying `hyp:H1` (with any `W ↪ X ↪ V`) and every `x₀ ∈ X`.  The proof (`app:pe-necessity`,
Step 3) only uses diagonal self-adjoint `A` with **bounded** `B : U → X`, approximately
controllable in every time.  We quantify over the smaller class of bounded systems
`System.bounded S B 0` (`W = V = X`, so `hyp:H1` holds by `System.bounded_H1`) with
`(A, B)` approximately controllable in every time `τ > 0`.  The hypothesis is weaker, so the
theorem is stronger, and it implies the paper's statement (bounded systems belong to the
paper's class, and informativity in `U × X` does not involve `W`).  The paper's Step 3 takes
`W = D(A)`; with `W = X` assumption `hyp:H1` is automatic.  The hypothesis `0 < T` is not used:
for `T ≤ 0` no record is informative unless `U × X = 0`.

## Proof (`app:pe-necessity`), as formalised

Both theorems reduce to `Necessity.exists_not_informative`: from a terminating relation and
`r` distinct modes of a countable Hilbert basis, it builds the counterexample pair and initial
state.

* Step 1 (`Necessity.exists_terminating`): a failing relation `∑_{k < L} ⟪ζₖ, Dᵏ ū⟫ = 0`,
  `ζ ≠ 0`, is cut at its last nonzero coefficient `r < L`.
* Step 2 (`Necessity.exists_nodes`, `Necessity.coeff_eq_partialFraction`): distinct nodes
  `μₙ ∈ (0, 1)` avoiding the real zeros of `Ψ(s) = ∑ ζₖ sᵏ` (they are roots of the nonzero scalar
  polynomial `⟪ζ_r, Ψ⟫`); with `p = ∏ (X - μₙ)`, `qₙ = p / (X - μₙ)` and `bₙ = Ψ(μₙ)/qₙ(μₙ)`
  (`qₙ(μₙ) = p'(μₙ)`), `Ψ = ζ_r p + ∑ₙ bₙ qₙ` coefficientwise (`eq:pe-necessary-transfer`
  multiplied by `p`).  The `U`-valued identity is proved by pairing with every `v ∈ U`, which
  reduces it to scalar polynomial interpolation at the `r` nodes.
* Step 3 (`Necessity.exists_diag_data`): on a Hilbert basis `(eᵢ)` indexed by a countable type
  (`Fin N`, or any Hilbert basis of a separable space, `Necessity.countable_of_hilbertBasis`)
  the eigenvalues are `μₙ` on the `r` chosen modes and `-(enc i + 1)` elsewhere (`enc` an
  injection into `ℕ`); `B† eᵢ` is `bₙ` on the chosen modes and `2^{-enc i} ζ_r` elsewhere
  (`Necessity.exists_adjoint_apply_basis`, `B = ∑ᵢ ⟪B† eᵢ, ·⟫ eᵢ`).  Approximate
  controllability is `approxControllable_diag` (`Semigroup/Diagonal`), not
  `prop:fattorini-hautus`.
* Step 4 (`Necessity.exists_ae_eq_sum_exp`, `Necessity.ae_inner_mild_eq_zero`): the zero-state
  modes `yₙ = ∫₀ᵗ e^{μₙ (t - s)} ⟪bₙ, ū s⟫ ds` are `H¹` solutions of `ẏₙ = μₙ yₙ + ⟪bₙ, ū⟫`, so
  `p(D) yₙ = qₙ(D) ⟪bₙ, ū⟫` in `𝒟'(I)` (`HasWeakDeriv.polyDerivMoment_X_sub_C_mul`) and
  `w = ⟪ζ_r, ū⟫ + ∑ₙ yₙ` satisfies `p(D) w = ∑ₖ ⟪ζₖ, Dᵏ ū⟫ = 0`; hence `w = ∑ κₙ e^{μₙ t}` a.e.
  (`ae_eq_sum_exp_of_polyDerivMoment_eq_zero`).  The initial state `x₀ = -∑ κₙ e_{jₙ}` cancels
  the exponentials (coordinates of the mild solution: `inner_mild_diag`), so
  `(ζ_r, ∑ₙ e_{jₙ}) ≠ 0` annihilates the record.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

namespace Necessity

open Polynomial

section Algebra

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- `p = ∏ₙ (X - μₙ)`. -/
def nodePoly {r : ℕ} (μ : Fin r → ℝ) : ℝ[X] := ∏ n, (X - C (μ n))

/-- `qₙ = ∏_{m ≠ n} (X - μₘ) = p / (X - μₙ)`. -/
def cofPoly {r : ℕ} (μ : Fin r → ℝ) (n : Fin r) : ℝ[X] :=
  ∏ m ∈ Finset.univ.erase n, (X - C (μ m))

/-- The `U`-valued polynomial `Ψ(s) = ∑_{k ≤ r} sᵏ ζₖ`. -/
def psiEval (ζ : ℕ → U) (r : ℕ) (s : ℝ) : U := ∑ k ∈ Finset.range (r + 1), s ^ k • ζ k

/-- `p = (X - μₙ) qₙ`. -/
theorem nodePoly_eq_mul {r : ℕ} (μ : Fin r → ℝ) (n : Fin r) :
    nodePoly μ = (X - C (μ n)) * cofPoly μ n := by
  rw [nodePoly, cofPoly]
  exact (Finset.mul_prod_erase _ (fun m => X - C (μ m)) (Finset.mem_univ n)).symm

/-- `p` is monic. -/
theorem monic_nodePoly {r : ℕ} (μ : Fin r → ℝ) : (nodePoly μ).Monic :=
  monic_prod_of_monic _ _ fun n _ => monic_X_sub_C (μ n)

/-- `deg p = r`. -/
theorem natDegree_nodePoly {r : ℕ} (μ : Fin r → ℝ) : (nodePoly μ).natDegree = r := by
  rw [nodePoly, natDegree_prod_of_monic _ _ fun n _ => monic_X_sub_C (μ n)]
  simp

/-- `deg qₙ = r - 1`. -/
theorem natDegree_cofPoly {r : ℕ} (μ : Fin r → ℝ) (n : Fin r) :
    (cofPoly μ n).natDegree = r - 1 := by
  rw [cofPoly, natDegree_prod_of_monic _ _ fun n _ => monic_X_sub_C (μ n)]
  simp [Finset.card_erase_of_mem]

/-- `p(μₙ) = 0`. -/
theorem eval_nodePoly {r : ℕ} (μ : Fin r → ℝ) (n : Fin r) : (nodePoly μ).eval (μ n) = 0 := by
  rw [nodePoly_eq_mul μ n]; simp

/-- `qₙ(μₘ) = 0` for `m ≠ n`. -/
theorem eval_cofPoly_of_ne {r : ℕ} (μ : Fin r → ℝ) {n m : Fin r} (h : m ≠ n) :
    (cofPoly μ n).eval (μ m) = 0 := by
  rw [cofPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ m⟩) (by simp)

/-- `qₙ(μₙ) = ∏_{m ≠ n} (μₙ - μₘ) ≠ 0` for distinct nodes. -/
theorem eval_cofPoly_ne_zero {r : ℕ} {μ : Fin r → ℝ} (hμ : Function.Injective μ) (n : Fin r) :
    (cofPoly μ n).eval (μ n) ≠ 0 := by
  rw [cofPoly, eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun m hm => ?_
  have hmn : m ≠ n := (Finset.mem_erase.1 hm).1
  simpa [sub_eq_zero] using fun h => hmn (hμ h).symm

/-- The residues `bₙ = Ψ(μₙ) / qₙ(μₙ)` (`app:pe-necessity`, Step 2; `qₙ(μₙ) = p'(μₙ)`). -/
def residue (ζ : ℕ → U) {r : ℕ} (μ : Fin r → ℝ) (n : Fin r) : U :=
  ((cofPoly μ n).eval (μ n))⁻¹ • psiEval ζ r (μ n)

/-- Coefficients of the scalar polynomial `∑_{k ≤ r} ⟪v, ζₖ⟫ Xᵏ`. -/
theorem coeff_sum_C_mul_X_pow (c : ℕ → ℝ) (r m : ℕ) :
    (∑ k ∈ Finset.range (r + 1), C (c k) * X ^ k).coeff m = if m < r + 1 then c m else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- **Partial fractions** (`eq:pe-necessary-transfer`): with `p = ∏ (X - μₙ)`,
`qₙ = p / (X - μₙ)` and `bₙ = Ψ(μₙ)/qₙ(μₙ)`, `Ψ = ζ_r p + ∑ₙ bₙ qₙ` coefficientwise. -/
theorem coeff_eq_partialFraction (ζ : ℕ → U) {r : ℕ} {μ : Fin r → ℝ}
    (hμ : Function.Injective μ) {k : ℕ} (hk : k ≤ r) :
    ζ k = (nodePoly μ).coeff k • ζ r + ∑ n, (cofPoly μ n).coeff k • residue ζ μ n := by
  refine ext_inner_left ℝ fun v => ?_
  set f : ℝ[X] := ∑ k ∈ Finset.range (r + 1), C ⟪v, ζ k⟫_ℝ * X ^ k with hf
  set g : ℝ[X] := C ⟪v, ζ r⟫_ℝ * nodePoly μ + ∑ n, C ⟪v, residue ζ μ n⟫_ℝ * cofPoly μ n
    with hg
  have hfg : f = g := by
    refine eq_of_degree_sub_lt_of_eval_index_eq (s := Finset.univ) (v := μ) hμ.injOn ?_ ?_
    · rw [Finset.card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
      intro m hm
      rw [coeff_sub, hf, coeff_sum_C_mul_X_pow, hg, coeff_add, coeff_C_mul, finsetSum_coeff]
      have hq : ∀ n : Fin r, (C ⟪v, residue ζ μ n⟫_ℝ * cofPoly μ n).coeff m = 0 := by
        intro n
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
        rw [natDegree_cofPoly]
        have : 0 < r := Fin.pos n
        omega
      simp only [hq, Finset.sum_const_zero, add_zero]
      have hp1 : (nodePoly μ).coeff r = 1 := by
        simpa [natDegree_nodePoly] using (monic_nodePoly μ).coeff_natDegree
      rcases eq_or_lt_of_le hm with hrm | hm'
      · subst hrm
        rw [ite_eq_left (Nat.lt_succ_self _), hp1]
        ring
      · rw [ite_eq_right (by omega),
          coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodePoly]; exact hm')]
        ring
    · intro i _
      have hfe : f.eval (μ i) = ⟪v, psiEval ζ r (μ i)⟫_ℝ := by
        rw [hf, eval_finsetSum, psiEval, inner_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eval_mul, eval_C, eval_pow, eval_X, real_inner_smul_right, mul_comm]
      have hge : g.eval (μ i) = ⟪v, residue ζ μ i⟫_ℝ * (cofPoly μ i).eval (μ i) := by
        rw [hg, eval_add, eval_mul, eval_nodePoly, mul_zero, zero_add, eval_finsetSum,
          Finset.sum_eq_single i]
        · simp
        · intro m _ hm
          rw [eval_mul, eval_cofPoly_of_ne μ (Ne.symm hm), mul_zero]
        · simp
      rw [hfe, hge, residue, real_inner_smul_right, mul_comm, ← mul_assoc,
        mul_inv_cancel₀ (eval_cofPoly_ne_zero hμ i), one_mul]
  have hcoeff := congrArg (coeff · k) hfg
  rw [hf, coeff_sum_C_mul_X_pow, ite_eq_left (Nat.lt_succ_of_le hk), hg, coeff_add, coeff_C_mul,
    finsetSum_coeff] at hcoeff
  rw [hcoeff, inner_add_right, inner_sum, real_inner_smul_right]
  simp only [coeff_C_mul, real_inner_smul_right]
  ring_nf
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Step 1–2**: there are distinct nodes `μₙ ∈ (0, 1)` avoiding the real zeros of `Ψ`. -/
theorem exists_nodes (ζ : ℕ → U) {r : ℕ} (hζ : ζ r ≠ 0) :
    ∃ μ : Fin r → ℝ, Function.Injective μ ∧ (∀ n, μ n ∈ Ioo (0 : ℝ) 1) ∧
      ∀ n, psiEval ζ r (μ n) ≠ 0 := by
  set g : ℝ[X] := ∑ k ∈ Finset.range (r + 1), C ⟪ζ r, ζ k⟫_ℝ * X ^ k with hg
  have hg0 : g ≠ 0 := by
    intro h
    have := congrArg (coeff · r) h
    simp only [hg, coeff_sum_C_mul_X_pow, ite_eq_left (Nat.lt_succ_self r), coeff_zero] at this
    exact hζ (inner_self_eq_zero.1 this)
  have hgeval : ∀ x, g.eval x = ⟪ζ r, psiEval ζ r x⟫_ℝ := by
    intro x
    rw [hg, eval_finsetSum, psiEval, inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, real_inner_smul_right, mul_comm]
  have hZ : {s : ℝ | g.IsRoot s}.Finite := finite_setOfPred_isRoot hg0
  have hinf : (Ioo (0 : ℝ) 1 \ {s | g.IsRoot s}).Infinite :=
    (Ioo_infinite (by norm_num : (0 : ℝ) < 1)).sdiff hZ
  let f := hinf.natEmbedding
  refine ⟨fun n => (f n : ℝ), ?_, fun n => (f n).2.1, fun n h => ?_⟩
  · intro n m h
    exact Fin.val_injective (f.injective (Subtype.val_injective h))
  · apply (f n).2.2
    show g.IsRoot (f n : ℝ)
    rw [IsRoot.def, hgeval, h, inner_zero_right]

end Algebra

section Analytic

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {T : ℝ} {u : ℝ → U}

/-- `⟨p(D) f, φ⟩ = ∑_{k < N} pₖ ⟨Dᵏ f, φ⟩` for every `N > deg p`. -/
theorem polyDerivMoment_eq_sum_range_of_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℝ[X]) {N : ℕ} (hN : p.natDegree < N) (f : ℝ → E) (φ : ℝ → ℝ) :
    polyDerivMoment p f φ = ∑ k ∈ Finset.range N, p.coeff k • derivMoment k f φ := by
  rw [polyDerivMoment]
  exact sum_over_range' p (fun n => zero_smul ℝ (derivMoment n f φ)) N hN

/-- The zero-state response of the mode `ẏ = μ y + ⟪b, ū⟫`:
`y(t) = ∫₀ᵗ e^{μ (t - s)} ⟪b, ū s⟫ ds`. -/
def modeResp (μ : ℝ) (b : U) (u : ℝ → U) (t : ℝ) : ℝ :=
  ∫ s in 0..t, Real.exp (μ * (t - s)) • ⟪b, u s⟫_ℝ

omit [CompleteSpace U] in
/-- The mode `yₙ` is an `H¹` solution of `ẏ = μ y + ⟪b, ū⟫` (variation of constants). -/
theorem hasWeakDeriv_modeResp (hu : MemLp u 2 (μI T)) (μ : ℝ) (b : U) :
    HasWeakDeriv T (modeResp μ b u) (fun t => μ • modeResp μ b u t + ⟪b, u t⟫_ℝ) := by
  have := hasWeakDeriv_exp_smul_add_integral (T := T) (a := μ) (hu.const_inner b) (0 : ℝ)
  simp only [smul_zero, zero_add] at this
  exact this

/-- **Step 4** (`app:pe-necessity`): if `∑ₖ ⟪pₖ α + ∑ₙ qₙ,ₖ bₙ, Dᵏ ū⟫ = 0` in `𝒟'(I)`, then
`w = ⟪α, ū⟫ + ∑ₙ yₙ` solves `p(D) w = 0`, hence is an exponential sum `∑ₙ κₙ e^{μₙ t}`. -/
theorem exists_ae_eq_sum_exp {r : ℕ} {μ : Fin r → ℝ} (hμ : Function.Injective μ) (α : U)
    (b : Fin r → U) (hu : MemLp u 2 (μI T))
    (hrel : ∀ φ, IsTestFunction T φ → ∑ k ∈ Finset.range (r + 1),
      ⟪(nodePoly μ).coeff k • α + ∑ n, (cofPoly μ n).coeff k • b n, derivMoment k u φ⟫_ℝ = 0) :
    ∃ κ : Fin r → ℝ, ∀ᵐ t ∂(μI T),
      ⟪α, u t⟫_ℝ + ∑ n, modeResp (μ n) (b n) u t = ∑ n, κ n * Real.exp (μ n * t) := by
  have hui : Integrable u (μI T) := hu.integrable one_le_two
  have hy := fun n => hasWeakDeriv_modeResp hu (μ n) (b n)
  have hαi : Integrable (fun t => ⟪α, u t⟫_ℝ) (μI T) := hui.const_inner α
  have hyi : ∀ n, Integrable (modeResp (μ n) (b n) u) (μI T) := fun n => (hy n).integrable
  have hsi : Integrable (fun t => ∑ n, modeResp (μ n) (b n) u t) (μI T) :=
    integrable_finsetSum _ fun n _ => hyi n
  refine ae_eq_sum_exp_of_polyDerivMoment_eq_zero μ hμ (hαi.add hsi) fun φ hφ => ?_
  have hp : (∏ n, (X - C (μ n)) : ℝ[X]) = nodePoly μ := rfl
  have hdeg : (nodePoly μ).natDegree < r + 1 := by rw [natDegree_nodePoly]; omega
  rw [hp, polyDerivMoment_eq_sum_range_of_lt (nodePoly μ) hdeg]
  have hsplit : ∀ k, derivMoment k (fun t => ⟪α, u t⟫_ℝ + ∑ n, modeResp (μ n) (b n) u t) φ =
      ⟪α, derivMoment k u φ⟫_ℝ + ∑ n, derivMoment k (modeResp (μ n) (b n) u) φ := by
    intro k
    rw [derivMoment_add hφ hαi hsi, derivMoment_finset_sum _ hφ (fun n _ => hyi n),
      inner_derivMoment α hφ hui]
  have hmode : ∀ n, ∑ k ∈ Finset.range (r + 1),
      (nodePoly μ).coeff k * derivMoment k (modeResp (μ n) (b n) u) φ =
      ∑ k ∈ Finset.range (r + 1), (cofPoly μ n).coeff k * ⟪b n, derivMoment k u φ⟫_ℝ := by
    intro n
    have h1 := polyDerivMoment_eq_sum_range_of_lt (nodePoly μ) hdeg (modeResp (μ n) (b n) u) φ
    have h2 := polyDerivMoment_eq_sum_range_of_lt (cofPoly μ n) (N := r + 1)
      (by rw [natDegree_cofPoly]; omega) (fun t => ⟪b n, u t⟫_ℝ) φ
    rw [nodePoly_eq_mul μ n, (hy n).polyDerivMoment_X_sub_C_mul hφ, ← nodePoly_eq_mul μ n,
      h2] at h1
    simp only [smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_derivMoment (b n) hφ hui]
  have := hrel φ hφ
  simp only [inner_add_left, sum_inner, real_inner_smul_left, Finset.sum_add_distrib] at this
  rw [← this]
  simp only [hsplit, smul_eq_mul, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hmode n]

end Analytic

section System

variable {ι U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {T : ℝ} {u : ℝ → U}

/-- A bounded `B : U → X` with prescribed `B† eᵢ = bᵢ`, for absolutely summable `b`. -/
theorem exists_adjoint_apply_basis (e : HilbertBasis ι ℝ X) (b : ι → U)
    (hb : Summable fun i => ‖b i‖) :
    ∃ B : U →L[ℝ] X, ∀ i, ContinuousLinearMap.adjoint B (e i) = b i := by
  classical
  let F : ι → U →L[ℝ] X := fun i => (innerSL ℝ (b i)).smulRight (e i)
  have hFn : ∀ i, ‖F i‖ ≤ ‖b i‖ := by
    intro i
    have h1 : ‖F i‖ = ‖innerSL ℝ (b i)‖ * ‖e i‖ := ContinuousLinearMap.norm_smulRight_apply _ _
    rw [h1, innerSL_apply_norm, e.orthonormal.1 i, mul_one]
  have hF : Summable F := Summable.of_norm_bounded hb hFn
  refine ⟨∑' i, F i, fun i => ext_inner_right ℝ fun v => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hFv : HasSum (fun k => F k v) ((∑' k, F k) v) := by
    have := hF.hasSum
    exact this.mapL (ContinuousLinearMap.apply ℝ X v)
  have hFv' : HasSum (fun k => ⟪e i, F k v⟫_ℝ) ⟪e i, (∑' k, F k) v⟫_ℝ :=
    hFv.mapL (innerSL ℝ (e i))
  refine hFv'.unique ?_
  have hterm : ∀ k, ⟪e i, F k v⟫_ℝ = if k = i then ⟪b i, v⟫_ℝ else 0 := by
    intro k
    have : F k v = ⟪b k, v⟫_ℝ • e k := rfl
    rw [this, real_inner_smul_right]
    by_cases hk : k = i
    · subst hk
      rw [real_inner_self_eq_norm_sq, e.orthonormal.1 k, ite_eq_left rfl]
      ring
    · rw [orthonormal_iff_ite.1 e.orthonormal i k, ite_eq_right (Ne.symm hk), ite_eq_right hk,
        mul_zero]
  simp only [hterm]
  exact hasSum_ite_eq i _

omit [CompleteSpace X] in
/-- A Hilbert basis of a separable space is countable (the balls of radius `1/2` around the
basis vectors are disjoint). -/
theorem countable_of_hilbertBasis [TopologicalSpace.SeparableSpace X] (e : HilbertBasis ι ℝ X) :
    Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (e i) (1 / 2))
    (fun i k hik => Metric.ball_disjoint_ball ?_) (fun i => Metric.isOpen_ball)
    (fun i => ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  rw [dist_eq_norm]
  have h2 : ‖e i - e k‖ ^ 2 = 2 := by
    rw [@norm_sub_sq_real, e.orthonormal.1 i, e.orthonormal.1 k, e.orthonormal.2 hik]
    norm_num
  nlinarith [norm_nonneg (e i - e k)]

omit [CompleteSpace X] in
/-- A Hilbert basis of an infinite-dimensional space is infinite. -/
theorem infinite_of_hilbertBasis (hX : ¬ FiniteDimensional ℝ X) (e : HilbertBasis ι ℝ X) :
    Infinite ι := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite ι
  exact hX e.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

/-- **Step 3** (`app:pe-necessity`): the diagonal completion.  On a countable Hilbert basis,
eigenvalues `λ` extending `μ` (on the first `r` modes) by negative integers, and `B` with
`B† eᵢ` extending `b` by `2^{-enc i} c` (`enc : ι → ℕ` injective). -/
theorem exists_diag_data [Countable ι] (e : HilbertBasis ι ℝ X) {r : ℕ} (j : Fin r → ι)
    (hj : Function.Injective j) (μ : Fin r → ℝ) (hμ : Function.Injective μ)
    (hμpos : ∀ n, 0 < μ n) (b : Fin r → U) (hb : ∀ n, b n ≠ 0) (c : U) (hc : c ≠ 0) :
    ∃ (lam : ι → ℝ) (_ : BddAbove (range lam)) (B : U →L[ℝ] X), Function.Injective lam ∧
      (∀ i, ContinuousLinearMap.adjoint B (e i) ≠ 0) ∧ (∀ n, lam (j n) = μ n) ∧
      ∀ n, ContinuousLinearMap.adjoint B (e (j n)) = b n := by
  classical
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat ι
  let lam : ι → ℝ := Function.extend j μ (fun i => -((enc i : ℝ) + 1))
  let b' : ι → U := Function.extend j b (fun i => ((2 : ℝ)⁻¹) ^ (enc i) • c)
  have hlamj : ∀ n, lam (j n) = μ n := fun n => hj.extend_apply _ _ n
  have hb'j : ∀ n, b' (j n) = b n := fun n => hj.extend_apply _ _ n
  have hlamo : ∀ i, (¬ ∃ n, j n = i) → lam i = -((enc i : ℝ) + 1) :=
    fun i hi => Function.extend_apply' _ _ _ hi
  have hb'o : ∀ i, (¬ ∃ n, j n = i) → b' i = ((2 : ℝ)⁻¹) ^ (enc i) • c :=
    fun i hi => Function.extend_apply' _ _ _ hi
  obtain ⟨M, hM⟩ := (Set.finite_range μ).bddAbove
  have hlam : BddAbove (range lam) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    by_cases hi : ∃ n, j n = i
    · obtain ⟨n, rfl⟩ := hi
      rw [hlamj]
      exact (hM ⟨n, rfl⟩).trans (le_max_left _ _)
    · rw [hlamo i hi]
      have : (0 : ℝ) ≤ enc i := Nat.cast_nonneg _
      exact (by linarith : -((enc i : ℝ) + 1) ≤ 0).trans (le_max_right _ _)
  have hinj : Function.Injective lam := by
    intro i i' h
    by_cases hi : ∃ n, j n = i <;> by_cases hi' : ∃ n, j n = i'
    · obtain ⟨n, rfl⟩ := hi
      obtain ⟨n', rfl⟩ := hi'
      rw [hlamj, hlamj] at h
      rw [hμ h]
    · obtain ⟨n, rfl⟩ := hi
      rw [hlamj, hlamo i' hi'] at h
      have := hμpos n
      have : (0 : ℝ) ≤ enc i' := Nat.cast_nonneg _
      linarith
    · obtain ⟨n', rfl⟩ := hi'
      rw [hlamj, hlamo i hi] at h
      have := hμpos n'
      have : (0 : ℝ) ≤ enc i := Nat.cast_nonneg _
      linarith
    · rw [hlamo i hi, hlamo i' hi'] at h
      exact henc (by exact_mod_cast (by linarith : (enc i : ℝ) = enc i'))
  have hsum : Summable fun i => ‖b' i‖ := by
    have hg : Summable fun i => ((2 : ℝ)⁻¹) ^ (enc i) * ‖c‖ :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective henc).mul_right _
    refine Summable.of_norm_bounded_eventually hg ?_
    refine Filter.eventually_cofinite.2 ((Set.finite_range j).subset fun i hi => ?_)
    by_contra hi'
    apply hi
    rw [hb'o i (by simpa using hi'), norm_norm, norm_smul, norm_pow, norm_inv, Real.norm_two]
  obtain ⟨B, hB⟩ := exists_adjoint_apply_basis e b' hsum
  refine ⟨lam, hlam, B, hinj, fun i => ?_, hlamj, fun n => by rw [hB, hb'j]⟩
  rw [hB]
  by_cases hi : ∃ n, j n = i
  · obtain ⟨n, rfl⟩ := hi
    rw [hb'j]
    exact hb n
  · rw [hb'o i hi]
    exact smul_ne_zero (pow_ne_zero _ (by norm_num)) hc

/-- **Step 4** (`app:pe-necessity`), the non-informative trajectory: with
`x₀ = -∑ₙ κₙ e_{jₙ}`, the pair `(α, ∑ₙ e_{jₙ})` annihilates the record. -/
theorem ae_inner_mild_eq_zero (e : HilbertBasis ι ℝ X) (lam : ι → ℝ)
    (hlam : BddAbove (range lam)) (B : U →L[ℝ] X) {r : ℕ} (j : Fin r → ι)
    (hj : Function.Injective j) (μ : Fin r → ℝ) (hμj : ∀ n, lam (j n) = μ n) (b : Fin r → U)
    (hbj : ∀ n, ContinuousLinearMap.adjoint B (e (j n)) = b n) (α : U) (κ : Fin r → ℝ)
    (hu : MemLp u 2 (μI T))
    (hκ : ∀ᵐ t ∂(μI T),
      ⟪α, u t⟫_ℝ + ∑ n, modeResp (μ n) (b n) u t = ∑ n, κ n * Real.exp (μ n * t)) :
    ∀ᵐ t ∂(μI T), ⟪α, u t⟫_ℝ + ⟪∑ n, e (j n),
      (System.bounded (diagSemigroup e lam hlam) B (0 : X →L[ℝ] ℝ)).mild
        (-∑ n, κ n • e (j n)) u t⟫_ℝ = 0 := by
  have ho := e.orthonormal.comp j hj
  have hx0 : ∀ n, ⟪e (j n), -∑ m, κ m • e (j m)⟫_ℝ = -κ n := by
    intro n
    rw [inner_neg_right]
    exact congrArg Neg.neg (ho.inner_right_fintype κ n)
  filter_upwards [hκ, ae_restrict_mem measurableSet_Ioc] with t ht htI
  have hut : MemLp u 2 (μI t) :=
    hu.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right htI.2) le_rfl)
  have hy : ∀ n, ∫ s in Ioc 0 t, Real.exp (μ n * (t - s)) * ⟪b n, u s⟫_ℝ =
      modeResp (μ n) (b n) u t := by
    intro n
    rw [modeResp, intervalIntegral.integral_of_le htI.1.le]
    rfl
  rw [sum_inner]
  simp only [inner_mild_diag e lam hlam B 0 htI.1.le hut, hx0, hμj, hbj, hy]
  have hneg : ∑ n, (Real.exp (μ n * t) * -κ n + modeResp (μ n) (b n) u t) =
      ∑ n, modeResp (μ n) (b n) u t - ∑ n, κ n * Real.exp (μ n * t) := by
    rw [Finset.sum_add_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hneg]
  linarith

end System

section Core

variable {ι U X : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {T : ℝ} {u : ℝ → U}

omit [CompleteSpace U] in
/-- **Step 1**: a failing relation of order `L` terminates at some `r < L`: there are
`ζ : ℕ → U` with `ζ r ≠ 0` and `∑_{k ≤ r} ⟪ζₖ, Dᵏ ū⟫ = 0` in `𝒟'(I)`. -/
theorem exists_terminating {L : ℕ} (ζ : Fin L → U) (hne : ζ ≠ 0)
    (hrel : ∀ φ, IsTestFunction T φ → ∑ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) u φ⟫_ℝ = 0) :
    ∃ (ζ' : ℕ → U) (r : ℕ), r < L ∧ ζ' r ≠ 0 ∧ ∀ φ, IsTestFunction T φ →
      ∑ k ∈ Finset.range (r + 1), ⟪ζ' k, derivMoment k u φ⟫_ℝ = 0 := by
  classical
  let ζ' : ℕ → U := fun k => if h : k < L then ζ ⟨k, h⟩ else 0
  let s := (Finset.range L).filter fun k => ζ' k ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 i.2, by simpa [ζ'] using hi⟩⟩
  have hrs := s.max'_mem hs
  have hrL : s.max' hs < L := Finset.mem_range.1 (Finset.mem_filter.1 hrs).1
  have hzero : ∀ k, s.max' hs < k → ζ' k = 0 := by
    intro k hk
    by_contra hk'
    by_cases hkL : k < L
    · exact absurd (s.le_max' k (Finset.mem_filter.2 ⟨Finset.mem_range.2 hkL, hk'⟩))
        (not_le.2 hk)
    · exact hk' (dite_eq_right hkL)
  refine ⟨ζ', s.max' hs, hrL, (Finset.mem_filter.1 hrs).2, fun φ hφ => ?_⟩
  have h1 : ∑ k : Fin L, ⟪ζ k, derivMoment (k : ℕ) u φ⟫_ℝ =
      ∑ k ∈ Finset.range L, ⟪ζ' k, derivMoment k u φ⟫_ℝ := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ⟪ζ' k, derivMoment k u φ⟫_ℝ) L]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ζ', k.2]
  rw [← hrel φ hφ, h1]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k hkL hkr => ?_
  rw [hzero k (by simp only [Finset.mem_range, not_lt] at hkr; omega), inner_zero_left]

/-- **The construction of `app:pe-necessity`**: a terminating relation
`∑_{k ≤ r} ⟪ζₖ, Dᵏ ū⟫ = 0` (`ζ_r ≠ 0`) and `r` distinct modes `j` of a countable Hilbert basis of
`X` give a diagonal pair `(A, B)`, approximately controllable in every time, and an initial
state whose record is not informative. -/
theorem exists_not_informative [Countable ι] (e : HilbertBasis ι ℝ X) {r : ℕ} (j : Fin r → ι)
    (hj : Function.Injective j) (hu : MemLp u 2 (μI T)) (ζ : ℕ → U) (hζ : ζ r ≠ 0)
    (hrel : ∀ φ, IsTestFunction T φ →
      ∑ k ∈ Finset.range (r + 1), ⟪ζ k, derivMoment k u φ⟫_ℝ = 0) :
    ∃ (S : C0Semigroup ℝ X) (B : U →L[ℝ] X),
      (∀ τ, 0 < τ → (System.bounded S B (0 : X →L[ℝ] ℝ)).ApproxControllable τ) ∧
      ∃ x₀ : X, ¬ Informative T u ((System.bounded S B (0 : X →L[ℝ] ℝ)).mild x₀ u) := by
  obtain ⟨μ, hμ, hμ01, hΨ⟩ := exists_nodes ζ hζ
  have hb : ∀ n, residue ζ μ n ≠ 0 := fun n =>
    smul_ne_zero (inv_ne_zero (eval_cofPoly_ne_zero hμ n)) (hΨ n)
  obtain ⟨lam, hlam, B, hinj, hB, hlamj, hBj⟩ :=
    exists_diag_data e j hj μ hμ (fun n => (hμ01 n).1) (residue ζ μ) hb (ζ r) hζ
  have hrel' : ∀ φ, IsTestFunction T φ → ∑ k ∈ Finset.range (r + 1),
      ⟪(nodePoly μ).coeff k • ζ r + ∑ n, (cofPoly μ n).coeff k • residue ζ μ n,
        derivMoment k u φ⟫_ℝ = 0 := by
    intro φ hφ
    rw [← hrel φ hφ]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← coeff_eq_partialFraction ζ hμ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
  obtain ⟨κ, hκ⟩ := exists_ae_eq_sum_exp hμ (ζ r) (residue ζ μ) hu hrel'
  refine ⟨diagSemigroup e lam hlam, B,
    fun τ hτ => approxControllable_diag e lam hlam hinj B hB 0 hτ,
    -∑ n, κ n • e (j n), fun hinf => hζ ?_⟩
  exact ((informative_iff.1 hinf) (ζ r) (∑ n, e (j n))
    (ae_inner_mild_eq_zero e lam hlam B j hj μ hlamj (residue ζ μ) hBj (ζ r) κ hu hκ)).1

end Core

end Necessity

open Necessity

variable {U X : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {T : ℝ} {u : ℝ → U}

/-- **Necessity of persistency of excitation, `dim X = N < ∞`** (`prop:hilbert-pe-necessary`):
let `ū ∈ L²(I; U)`, `I = (0, T)`.  Suppose that for every pair `(A, B)` on `X` (here: `A`
generating `S`, `B ∈ L(U, X)` bounded, `W = V = X`) that is approximately controllable (here:
in every time `τ > 0`) and every initial state `x₀ ∈ X`, the record `(ū, x(·; x₀, ū))` is
informative.  Then `ū` is persistently exciting of order `N + 1`.  (Stronger than the paper:
see the module docstring.) -/
theorem persistentlyExciting_of_forall_informative [FiniteDimensional ℝ X] (hT : 0 < T)
    (hu : MemLp u 2 (μI T))
    (h : ∀ (S : C0Semigroup ℝ X) (B : U →L[ℝ] X),
      (∀ τ, 0 < τ → (System.bounded S B (0 : X →L[ℝ] ℝ)).ApproxControllable τ) →
      ∀ x₀ : X, Informative T u ((System.bounded S B (0 : X →L[ℝ] ℝ)).mild x₀ u)) :
    PersistentlyExciting T (Module.finrank ℝ X + 1) u := by
  have _hT := hT  -- not needed: the theorem holds for every `T`
  intro ζ hζ
  by_contra hne
  obtain ⟨ζ', r, hr, hζr, hrel⟩ := exists_terminating ζ hne hζ
  obtain ⟨S, B, hac, x₀, hni⟩ := exists_not_informative (stdOrthonormalBasis ℝ X).toHilbertBasis
    (Fin.castLE (Nat.lt_succ_iff.1 hr)) (Fin.castLE_injective _) hu ζ' hζr hrel
  exact hni (h S B hac x₀)

/-- **Necessity of persistency of excitation, `dim X = ∞`** (`prop:hilbert-pe-necessary`): let
`X` be a separable infinite-dimensional Hilbert space and `ū ∈ L²(I; U)`.  Suppose that for every
pair `(A, B)` on `X` (here: `A` generating `S`, `B ∈ L(U, X)` bounded, `W = V = X`) that is
approximately controllable (here: in every time `τ > 0`) and every initial state `x₀ ∈ X`, the
record `(ū, x(·; x₀, ū))` is informative.  Then `ū` is persistently exciting of infinite
order.  (Stronger than the paper: see the module docstring.) -/
theorem persistentlyExcitingInfinite_of_forall_informative [TopologicalSpace.SeparableSpace X]
    (hX : ¬ FiniteDimensional ℝ X) (hT : 0 < T) (hu : MemLp u 2 (μI T))
    (h : ∀ (S : C0Semigroup ℝ X) (B : U →L[ℝ] X),
      (∀ τ, 0 < τ → (System.bounded S B (0 : X →L[ℝ] ℝ)).ApproxControllable τ) →
      ∀ x₀ : X, Informative T u ((System.bounded S B (0 : X →L[ℝ] ℝ)).mild x₀ u)) :
    PersistentlyExcitingInfinite T u := by
  have _hT := hT  -- not needed: the theorem holds for every `T`
  intro L ζ hζ
  by_contra hne
  obtain ⟨ζ', r, -, hζr, hrel⟩ := exists_terminating ζ hne hζ
  obtain ⟨w, e, -⟩ := exists_hilbertBasis ℝ X
  have := countable_of_hilbertBasis e
  have := infinite_of_hilbertBasis hX e
  obtain ⟨S, B, hac, x₀, hni⟩ := exists_not_informative e
    (fun n : Fin r => Infinite.natEmbedding w n)
    ((Infinite.natEmbedding w).injective.comp Fin.val_injective) hu ζ' hζr hrel
  exact hni (h S B hac x₀)

end DataDrivenControl
