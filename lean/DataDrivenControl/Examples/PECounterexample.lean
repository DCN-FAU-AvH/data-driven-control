module

public import DataDrivenControl.Informativity.PE
public import DataDrivenControl.Informativity.Harmonic
public import DataDrivenControl.Semigroup.Diagonal
public import DataDrivenControl.Semigroup.Perturbation
public import DataDrivenControl.System.Controllability

/-!
# Infinite-order excitation is not sufficient

Paper: `prop:infinite-pe-insufficient`, `eq:pe-counterexample`, `eq:pe-counterexample-input`
(`app:infinite-pe-insufficient`).

## Setting (`eq:pe-counterexample`)

`X = ℓ²(ℕ)` (Mathlib's `lp (fun _ : ℕ => ℝ) 2`, `PECounterexample.ℓ2`) with its standard Hilbert
basis `e` (`e n = lp.single 2 n 1`), `U = ℝ`.  **Indexing starts at `0`:** the paper's `eₙ`,
`n ≥ 1`, is our `e (n - 1)`.  Hence

* `A₀ eₙ = -n eₙ` is the diagonal semigroup `S₀ = diagSemigroup e lam _` with
  `lam n = -(n + 1)` (`Semigroup/Diagonal`);
* `b = (2^{-n})_{n ≥ 1}` is `b = ∑ₙ 2^{-(n+1)} e n`; `B v = v b` (`B`), `K x = ⟪b, x⟫` (`K`), so
  that `b ⊗ b = B K`;
* `A = A₀ + b ⊗ b` with `D(A) = D(A₀)` is the generator of the perturbed semigroup
  `S = S₀.perturb (B ∘ K)` (`Semigroup/Perturbation`, `generator_perturb`; `sys_A`);
* the system is `System.bounded S B 0` (`W = V = X`, `hyp:H1` by boundedness of `B`; there is
  no output, `C = 0 : ℓ² → ℝ`).

## Main declarations

* `PECounterexample.input` (`eq:pe-counterexample-input`): `ū(t) = -∑_{n ≥ 1} 4^{-n} e^{-nt}`.
* `approxControllable`: `(A, B)` is approximately controllable (in every time `T > 0`).  This is
  proved directly (`Diagonal.approxControllable_diag` for `(A₀, B)` and feedback invariance
  `System.approxControllable_perturb_iff`), not through `prop:fattorini-hautus`.
* `persistentlyExcitingInfinite`: `ū` is persistently exciting of infinite order on every
  window `(0, T)`.
* `mild_b_input`, `input_eq_neg_inner`: the hidden feedback: from `x̄₀ = b`, the state is
  `x̄(t) = e^{t A₀} b` and `ū(t) = -⟪b, x̄(t)⟫`.
* `not_informative` (`prop:infinite-pe-insufficient`): the record `(ū, x̄)` generated from
  `x̄₀ = b` is not informative on any window `(0, T)`: `(1, b)` annihilates it.
* `not_isHarmonic`: `ū` is not a harmonic signal (the text after `def:harmonic-pe`: harmonic
  excitation is strictly stronger than excitation of infinite order).

Helpers: `injective_lam`, `adjoint_B_e_ne_zero` (controllability); `term`, `inputDeriv`
(`ū⁽ʲ⁾(t) = -∑ₙ 4^{-(n+1)} (-(n+1))ʲ e^{-(n+1)t}`), `hasDerivAt_inputDeriv` (termwise
differentiation on `(-1, ∞)`), `derivMoment_input` (`⟨Dᵏ ū, φ⟩ = ∫ φ ū⁽ᵏ⁾`),
`sum_inputDeriv_eq` (`p(D) ū` as a Dirichlet series); `continuousOn_input`, `memLp_input`;
`tendsto_input` (`ū(t) → 0`), `input_zero_ne`.

## Proof routes (deviations from `app:infinite-pe-insufficient`)

* Controllability: `approxControllable_diag` plus feedback invariance instead of
  `prop:fattorini-hautus`.
* Trajectory: instead of "`x̄` is smooth and `ẋ̄ = A₀ x̄ = A x̄ + B ū`", feedback invariance of
  mild solutions (`System.mild_perturb_iff`): `e^{t A₀} b` is the mild solution of `(A₀, B)` with
  input `ū + K x̄ = 0`, hence of `(A₀ + B K, B)` with input `ū`.
* Excitation: uniqueness of the Dirichlet series `∑ₙ cₙ e^{-(n+1) t}` on `(0, T)`
  (`coeff_eq_zero_of_tsum_rexp_ae_eq_zero`), instead of the power series in `q = e^{-t}`.
* `ū` is only meaningful for `t ≥ 0` (the series converges for `t > -log 4`; elsewhere `input`
  is the junk `0`); every statement reads `t ≥ 0` only, and `not_isHarmonic` uses Bohr means over
  `[0, S]`.

## Upstream results used

`diagSemigroup`, `inner_diagSemigroup_real`, `approxControllable_diag` (`Semigroup/Diagonal`);
`C0Semigroup.perturb`, `generator_perturb`, `System.mild_perturb_iff`,
`System.approxControllable_perturb_iff` (`Semigroup/Perturbation`); `Informative.eq_zero`
(`Informativity/Informative`); `derivMoment_eq_integral_of_hasDerivAt`,
`eqOn_zero_of_integral_smul_eq_zero` (`Signal/TestFunction`);
`coeff_eq_zero_of_tsum_rexp_ae_eq_zero` (`Analysis/ExpSums`);
`Polynomial.eq_zero_of_infinite_isRoot`, `hasDerivAt_tsum_of_isPreconnected` (Mathlib); for
`not_isHarmonic`, `HarmonicSignal.hasBohrMean` (`Informativity/Harmonic`, which rests on
`HarmonicSignal.ofReal_apply`) and `hasBohrMean_zero_of_tendsto_zero` (`Analysis/BohrMean`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace NNReal

noncomputable section

namespace DataDrivenControl

namespace PECounterexample

/-- `ℓ²(ℕ)`, the state space of `prop:infinite-pe-insufficient` (indexed from `0`). -/
abbrev ℓ2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- The standard Hilbert basis `e n = lp.single 2 n 1` of `ℓ²(ℕ)` (the paper's `e_{n+1}`). -/
def e : HilbertBasis ℕ ℝ ℓ2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ ℓ2)

/-- The eigenvalues of `A₀` (`eq:pe-counterexample`): the paper's `A₀ eₙ = -n eₙ`, `n ≥ 1`, is
`lam n = -(n + 1)` in our `0`-based indexing. -/
def lam (n : ℕ) : ℝ := -((n : ℝ) + 1)

theorem bddAbove_lam : BddAbove (Set.range lam) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; simp only [lam, Left.neg_nonpos_iff]; positivity⟩

/-- The diagonal semigroup `e^{t A₀}`, `A₀ eₙ = -n eₙ` (`eq:pe-counterexample`). -/
def S₀ : C0Semigroup ℝ ℓ2 := diagSemigroup e lam bddAbove_lam

/-- The vector `b = (2^{-n})_{n ≥ 1}` (`eq:pe-counterexample`), `∑ₙ 2^{-(n+1)} e n` in our
`0`-based indexing. -/
def b : ℓ2 := ∑' n : ℕ, ((2 : ℝ)⁻¹ ^ (n + 1)) • e n

/-- The control operator `B v = v b`, `B ∈ L(ℝ, ℓ²)` (`eq:pe-counterexample`). -/
def B : ℝ →L[ℝ] ℓ2 := ContinuousLinearMap.toSpanSingleton ℝ b

/-- The functional `K x = ⟪b, x⟫`, so that `b ⊗ b = B K` (`app:infinite-pe-insufficient`). -/
def K : ℓ2 →L[ℝ] ℝ := innerSL ℝ b

/-- The semigroup generated by `A = A₀ + b ⊗ b = A₀ + B K` (`eq:pe-counterexample`). -/
def S : C0Semigroup ℝ ℓ2 := S₀.perturb (B.comp K)

/-- The system `ẋ = A x + B u` of `prop:infinite-pe-insufficient`, with `W = V = X = ℓ²`,
`U = ℝ` and no output (`C = 0`). -/
def sys : System ℝ ℓ2 ℓ2 ℓ2 ℝ := System.bounded S B 0

/-- The coordinate sequence `(2^{-(n+1)})ₙ` of `b` is square summable. -/
private theorem memℓp_bCoord : Memℓp (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  have h : Summable fun n : ℕ => ((4 : ℝ)⁻¹) ^ (n + 1) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  refine h.congr fun n => ?_
  rw [Real.norm_of_nonneg (by positivity), ENNReal.toReal_ofNat, Real.rpow_two, ← pow_mul,
    pow_mul', show ((2 : ℝ)⁻¹) ^ 2 = 4⁻¹ by norm_num]

/-- The coordinates of `b`: `⟪eₙ, b⟫ = 2^{-n}` (`0`-based: `2^{-(n+1)}`). -/
theorem inner_e_b (n : ℕ) : ⟪e n, b⟫_ℝ = (2 : ℝ)⁻¹ ^ (n + 1) := by
  have hb : b = e.repr.symm ⟨_, memℓp_bCoord⟩ := (e.hasSum_repr_symm ⟨_, memℓp_bCoord⟩).tsum_eq
  rw [hb, ← e.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- `A₀ eₙ = -n eₙ` (`eq:pe-counterexample`, `0`-based). -/
theorem generator_S₀_e (n : ℕ) :
    S₀.generator ⟨e n, basis_mem_generator_domain e lam bddAbove_lam n⟩ = lam n • e n :=
  generator_basis e lam bddAbove_lam n

/-- `A = A₀ + b ⊗ b` with `D(A) = D(A₀)` (`eq:pe-counterexample`): `(b ⊗ b) x = ⟪b, x⟫ b`. -/
theorem sys_A : sys.A = ((B.comp K : ℓ2 →L[ℝ] ℓ2) : ℓ2 →ₗ[ℝ] ℓ2) +ᵥ S₀.generator :=
  S₀.generator_perturb (B.comp K)

theorem B_comp_K_apply (x : ℓ2) : B.comp K x = ⟪b, x⟫_ℝ • b := rfl

/-- The input `ū(t) = -∑_{n ≥ 1} 4^{-n} e^{-nt}` (`eq:pe-counterexample-input`), in our
`0`-based indexing `-∑ₙ 4^{-(n+1)} e^{-(n+1) t}`. -/
def input (t : ℝ) : ℝ := -∑' n : ℕ, (4 : ℝ)⁻¹ ^ (n + 1) * Real.exp (-(((n : ℝ) + 1) * t))

/-! ### Approximate controllability -/

/-- The eigenvalues `λₙ = -(n + 1)` of `A₀` are pairwise distinct (simple spectrum). -/
theorem injective_lam : Function.Injective lam := fun m n h => by
  simp only [lam, neg_inj, add_left_inj, Nat.cast_inj] at h
  exact h

/-- `B† eₙ = ⟪b, eₙ⟫ = 2^{-(n+1)} ≠ 0`: every mode is reached by the control. -/
theorem adjoint_B_e_ne_zero (n : ℕ) : ContinuousLinearMap.adjoint B (e n) ≠ 0 := by
  intro h
  have h1 := ContinuousLinearMap.adjoint_inner_left B (1 : ℝ) (e n)
  rw [h, inner_zero_left] at h1
  have h2 : B 1 = b := by simp [B]
  rw [h2, inner_e_b] at h1
  exact (pow_ne_zero _ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)) h1.symm

/-- **`(A, B)` is approximately controllable** (`prop:infinite-pe-insufficient`), in every time
`T > 0`.  `(A₀, B)` is approximately controllable by `approxControllable_diag` (distinct
eigenvalues, `B† eₙ ≠ 0`), and `A = A₀ + B K` by feedback invariance
(`System.approxControllable_perturb_iff`). -/
theorem approxControllable {T : ℝ} (hT : 0 < T) : sys.ApproxControllable T := by
  rw [sys, S, System.approxControllable_perturb_iff, S₀]
  exact approxControllable_diag e lam bddAbove_lam injective_lam B adjoint_B_e_ne_zero 0 hT

/-! ### Excitation of infinite order -/

/-- The terms `4^{-(n+1)} (-(n+1))^j e^{-(n+1) t}` of the `j`-th derivative of `ū`. -/
def term (j n : ℕ) (t : ℝ) : ℝ :=
  (4 : ℝ)⁻¹ ^ (n + 1) * (-((n : ℝ) + 1)) ^ j * Real.exp (-(((n : ℝ) + 1) * t))

/-- The `j`-th classical derivative of `ū` on `(-1, ∞)`. -/
def inputDeriv (j : ℕ) (t : ℝ) : ℝ := -∑' n, term j n t

/-- `ū⁽⁰⁾ = ū`. -/
theorem inputDeriv_zero : inputDeriv 0 = input := by
  funext t
  simp [inputDeriv, term, input]

/-- A summable majorant for the terms on `(-1, ∞)` (Weierstrass test). -/
private theorem summable_majorant (m : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ m * (Real.exp 1 / 4) ^ (n + 1) := by
  have hr : ‖Real.exp 1 / 4‖ < 1 := by
    rw [Real.norm_of_nonneg (by positivity), div_lt_one (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * (Real.exp 1 / 4) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one m hr
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ m * (Real.exp 1 / 4) ^ n) 1).2 h0
  refine h.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]

private theorem abs_term_le (j n : ℕ) {y : ℝ} (hy : -1 < y) :
    |term j n y| ≤ ((n : ℝ) + 1) ^ j * (Real.exp 1 / 4) ^ (n + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp (-(((n : ℝ) + 1) * y)) ≤ Real.exp 1 ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith
  rw [term, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹),
    abs_of_pos (Real.exp_pos _), div_eq_mul_inv, mul_pow]
  calc (4 : ℝ)⁻¹ ^ (n + 1) * ((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * y))
      ≤ (4 : ℝ)⁻¹ ^ (n + 1) * ((n : ℝ) + 1) ^ j * Real.exp 1 ^ (n + 1) := by gcongr
    _ = _ := by ring

/-- The series of `ū⁽ʲ⁾` converges absolutely on `(-1, ∞)`. -/
theorem summable_term (j : ℕ) {y : ℝ} (hy : -1 < y) : Summable fun n => term j n y :=
  (summable_majorant j).of_norm_bounded fun n => by
    rw [Real.norm_eq_abs]
    exact abs_term_le j n hy

/-- `d/dt` of the `j`-th term is the `(j+1)`-st term. -/
theorem hasDerivAt_term (j n : ℕ) (y : ℝ) : HasDerivAt (term j n) (term (j + 1) n y) y := by
  have h := (((hasDerivAt_id y).const_mul (-((n : ℝ) + 1))).exp).const_mul
    ((4 : ℝ)⁻¹ ^ (n + 1) * (-((n : ℝ) + 1)) ^ j)
  convert h using 1
  · funext t
    simp only [term, id, neg_mul]
  · simp only [term, id, pow_succ, neg_mul]
    ring

/-- **Termwise differentiation**: `d/dt ū⁽ʲ⁾ = ū⁽ʲ⁺¹⁾` on `(-1, ∞)`. -/
theorem hasDerivAt_inputDeriv (j : ℕ) {y : ℝ} (hy : -1 < y) :
    HasDerivAt (inputDeriv j) (inputDeriv (j + 1) y) y := by
  have h := hasDerivAt_tsum_of_isPreconnected (summable_majorant (j + 1)) isOpen_Ioi
    isPreconnected_Ioi (fun n y _ => hasDerivAt_term j n y)
    (fun n y hy => by rw [Real.norm_eq_abs]; exact abs_term_le (j + 1) n hy)
    (show (0 : ℝ) ∈ Ioi (-1) by norm_num) (summable_term j (by norm_num))
    (show y ∈ Ioi (-1) from hy)
  exact h.neg

/-- `ū⁽ʲ⁾` is continuous on `(-1, ∞)`. -/
theorem continuousOn_inputDeriv (j : ℕ) : ContinuousOn (inputDeriv j) (Ioi (-1)) :=
  fun _ hy => (hasDerivAt_inputDeriv j hy).continuousAt.continuousWithinAt

/-- The derivative moments of `ū` are the classical ones: `⟨Dᵏ ū, φ⟩ = ∫ φ ū⁽ᵏ⁾`. -/
theorem derivMoment_input {T : ℝ} {φ : ℝ → ℝ} (hφ : IsTestFunction T φ) (k : ℕ) :
    derivMoment k input φ = ∫ t, φ t • inputDeriv k t := by
  rw [← inputDeriv_zero]
  exact derivMoment_eq_integral_of_hasDerivAt hφ k
    (fun j _ t ht => hasDerivAt_inputDeriv j (by linarith [ht.1]))
    (fun j _ => (continuousOn_inputDeriv j).mono fun t ht => by
      simp only [mem_Ioi]; linarith [ht.1])

/-- The exponents `-(n+1)` have only finitely many terms above each level. -/
private theorem finite_exponents (M : ℝ) : {n : ℕ | M ≤ -((n : ℝ) + 1)}.Finite := by
  refine (Set.finite_Iic ⌊-M⌋₊).subset fun k hk => ?_
  have hk' : M ≤ -((k : ℝ) + 1) := hk
  exact Nat.le_floor (by linarith)

/-- `p(D) ū` as a Dirichlet series: `∑ₖ ζₖ ū⁽ᵏ⁾(t) = -∑ₙ e^{-(n+1)t} 4^{-(n+1)} p(-(n+1))`. -/
theorem sum_inputDeriv_eq {L : ℕ} (ζ : Fin L → ℝ) {t : ℝ} (ht : -1 < t) :
    ∑ k : Fin L, ζ k * inputDeriv k t =
      -∑' n : ℕ, Real.exp (-((n : ℝ) + 1) * t) •
        ((4 : ℝ)⁻¹ ^ (n + 1) * ∑ k : Fin L, ζ k * (-((n : ℝ) + 1)) ^ (k : ℕ)) := by
  simp only [inputDeriv, mul_neg, Finset.sum_neg_distrib, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun (k : Fin L) _ => (summable_term (k : ℕ) ht).mul_left (ζ k)]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [term, smul_eq_mul, Finset.mul_sum, neg_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **`ū` is persistently exciting of infinite order** (`prop:infinite-pe-insufficient`), on
every window `(0, T)`, `T > 0`.  If `∑ₖ ζₖ Dᵏ ū = 0` in `𝒟'(0, T)`, then termwise
differentiation gives `∑ₙ 4^{-(n+1)} p(-(n+1)) e^{-(n+1) t} = 0` on `(0, T)` with
`p(s) = ∑ₖ ζₖ sᵏ`; uniqueness of Dirichlet series gives `p(-(n+1)) = 0` for every `n`, so
`p = 0`. -/
theorem persistentlyExcitingInfinite {T : ℝ} (hT : 0 < T) :
    PersistentlyExcitingInfinite T input := by
  intro L ζ hζ
  set G : ℝ → ℝ := fun t => ∑ k : Fin L, ζ k * inputDeriv k t with hGdef
  have hsub : Icc 0 T ⊆ Ioi (-1) := fun t ht => by simp only [mem_Ioi]; linarith [ht.1]
  have hint : ∀ k : ℕ, Integrable (inputDeriv k) (μI T) := fun k =>
    (memLp_μI_of_continuousOn ((continuousOn_inputDeriv k).mono hsub)).integrable one_le_two
  -- Step 1: `p(D) ū = 0` in `𝒟'(0, T)` means `∫ φ G = 0` for every test function
  have hG : ∀ φ, IsTestFunction T φ → ∫ t, φ t • G t = 0 := by
    intro φ hφ
    have h := hζ φ hφ
    simp only [derivMoment_input hφ, RCLike.inner_apply, conj_trivial] at h
    rw [← h, hGdef]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext t
      ring
    · intro k _
      have := (hφ.integrable_smul (hint k)).const_mul (ζ k)
      refine this.congr (ae_of_all _ fun t => ?_)
      simp only [smul_eq_mul]
      ring
  have hGc : ContinuousOn G (Ioo 0 T) := by
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    exact (continuousOn_inputDeriv k).mono fun t ht => by simp only [mem_Ioi]; linarith [ht.1]
  have hG0 := eqOn_zero_of_integral_smul_eq_zero hGc hG
  -- Step 2: uniqueness of the Dirichlet series
  set c : ℕ → ℝ := fun n => (4 : ℝ)⁻¹ ^ (n + 1) * ∑ k : Fin L, ζ k * (-((n : ℝ) + 1)) ^ (k : ℕ)
    with hc
  have hμ : Function.Injective fun n : ℕ => -((n : ℝ) + 1) := fun m n h => by
    simpa using h
  have hsum : ∀ t, 0 < t → Summable fun n => ‖c n‖ * Real.exp (-((n : ℝ) + 1) * t) := by
    intro t ht
    have h1 : Summable fun n => ∑ k : Fin L, ζ k * term k n t :=
      summable_sum fun (k : Fin L) _ => (summable_term (k : ℕ) (by linarith)).mul_left (ζ k)
    refine h1.abs.congr fun n => ?_
    rw [Real.norm_eq_abs, ← abs_of_pos (Real.exp_pos (-((n : ℝ) + 1) * t)), ← abs_mul]
    congr 1
    simp only [term, hc, Finset.mul_sum, Finset.sum_mul, neg_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hzero : ∀ n, c n = 0 := by
    refine coeff_eq_zero_of_tsum_rexp_ae_eq_zero hμ finite_exponents hsum le_rfl hT ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
    have := sum_inputDeriv_eq ζ (t := t) (by linarith [ht.1])
    have hG0t := hG0 t ht
    simp only [hGdef] at hG0t
    rw [hG0t] at this
    show ∑' n : ℕ, Real.exp (-((n : ℝ) + 1) * t) •
      ((4 : ℝ)⁻¹ ^ (n + 1) * ∑ k : Fin L, ζ k * (-((n : ℝ) + 1)) ^ (k : ℕ)) = 0
    linarith
  -- Step 3: `p(-(n+1)) = 0` for all `n`, so `p = 0`
  set P : Polynomial ℝ := ∑ k : Fin L, Polynomial.monomial (k : ℕ) (ζ k) with hP
  have hroot : ∀ n : ℕ, P.IsRoot (-((n : ℝ) + 1)) := by
    intro n
    have h := hzero n
    simp only [hc, mul_eq_zero, pow_eq_zero_iff', inv_eq_zero, OfNat.ofNat_ne_zero, false_and,
      false_or] at h
    simp only [Polynomial.IsRoot, hP, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    exact h
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine (Set.infinite_range_of_injective hμ).mono ?_
    rintro x ⟨n, rfl⟩
    exact hroot n
  funext i
  have hcoeff : P.coeff i = ζ i := by
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]
    simp
  rw [← hcoeff, hP0, Polynomial.coeff_zero, Pi.zero_apply]

/-! ### The hidden feedback -/

/-- The hidden feedback (`app:infinite-pe-insufficient`): `ū(t) = -K e^{t A₀} b = -⟪b, x̄(t)⟫`. -/
theorem input_eq_neg_inner {t : ℝ} (ht : 0 ≤ t) : input t = -⟪b, S₀.real t b⟫_ℝ := by
  rw [input, ← e.tsum_inner_mul_inner]
  congr 1
  refine tsum_congr fun n => ?_
  rw [S₀, inner_diagSemigroup_real e lam bddAbove_lam ht, real_inner_comm, inner_e_b, lam]
  rw [show -((n : ℝ) + 1) * t = -(((n : ℝ) + 1) * t) by ring]
  rw [show (4 : ℝ)⁻¹ = 2⁻¹ * 2⁻¹ by norm_num, mul_pow]
  ring

/-- `ū` is continuous on `[0, τ]` (it is `-⟪b, e^{t A₀} b⟫` there). -/
theorem continuousOn_input (τ : ℝ) : ContinuousOn input (Icc 0 τ) := by
  have hc : Continuous fun t => -⟪b, S₀.real t b⟫_ℝ :=
    (continuous_const.inner (S₀.continuous_real_apply b)).neg
  exact hc.continuousOn.congr fun t ht => input_eq_neg_inner ht.1

/-- `ū ∈ L²(0, τ)`. -/
theorem memLp_input (τ : ℝ) : MemLp input 2 (μI τ) :=
  memLp_μI_of_continuousOn (continuousOn_input τ)

/-- The hidden feedback (`app:infinite-pe-insufficient`): from `x̄₀ = b` the state is
`x̄(t) = e^{t A₀} b`.  By feedback invariance (`System.mild_perturb_iff`), `t ↦ e^{t A₀} b` is the
mild solution of `(A₀ + B K, B)` with input `ū` iff it is the mild solution of `(A₀, B)` with
input `ū + K x̄ = 0`, which it is. -/
theorem mild_b_input {t : ℝ} (ht : 0 ≤ t) : sys.mild b input t = S₀.real t b := by
  have hx : ContinuousOn (fun s => S₀.real s b) (Icc 0 t) :=
    (S₀.continuous_real_apply b).continuousOn
  have key := (System.mild_perturb_iff S₀ B K (0 : ℓ2 →L[ℝ] ℝ) (memLp_input t) b hx).2
    (fun s hs => ?_) t ⟨ht, le_rfl⟩
  · exact key.symm
  · have hae : (fun r => input r + K (S₀.real r b)) =ᵐ[μI s] fun _ => (0 : ℝ) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
      simp only [input_eq_neg_inner hr.1.le, K, innerSL_apply_apply, neg_add_cancel]
    rw [System.mild_congr_ae hae, System.mild]
    simp only [System.bounded_SX, System.bounded_ιW, ContinuousLinearMap.id_apply]
    rw [System.L_eq_of_ιWV (w := 0) (by simp [System.convV]), add_zero]

/-! ### The input is not harmonic -/

/-- `ū(t) → 0` as `t → ∞`. -/
theorem tendsto_input : Tendsto input atTop (𝓝 0) := by
  have h : Tendsto (fun t => ∑' n : ℕ, (4 : ℝ)⁻¹ ^ (n + 1) * Real.exp (-(((n : ℝ) + 1) * t)))
      atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => (4 : ℝ)⁻¹ ^ (n + 1))
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
        (add_left_injective 1)) (fun n => ?_) ?_
    · have : Tendsto (fun t : ℝ => Real.exp (-(((n : ℝ) + 1) * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < (n : ℝ) + 1))
      simpa using this.const_mul ((4 : ℝ)⁻¹ ^ (n + 1))
    · filter_upwards [eventually_ge_atTop 0] with t ht n
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
      have : (0 : ℝ) ≤ ((n : ℝ) + 1) * t := by positivity
      linarith
  rw [tsum_zero] at h
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'

/-- `ū(0) = -∑ₙ 4^{-(n+1)} ≠ 0`. -/
theorem input_zero_ne : input 0 ≠ 0 := by
  have hs : Summable fun n : ℕ => (4 : ℝ)⁻¹ ^ (n + 1) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  have hpos : 0 < ∑' n : ℕ, (4 : ℝ)⁻¹ ^ (n + 1) :=
    hs.tsum_pos (fun n => by positivity) 0 (by norm_num)
  simp only [input, mul_zero, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- The input is **not harmonic** (`subsec:analytic-sufficient-input`, after `def:harmonic-pe`:
harmonic persistency of excitation is strictly stronger than excitation of infinite order).  A
harmonic signal has Bohr coefficients `ĥ(ωₗ) = vₗ ≠ 0`, while `ū(t) → 0` as `t → ∞`. -/
theorem not_isHarmonic : ¬ IsHarmonic input := by
  rintro ⟨h, hh⟩
  rcases isEmpty_or_nonempty h.ι with hι | ⟨⟨l⟩⟩
  · apply input_zero_ne
    rw [← hh, HarmonicSignal.coe_apply, bohrSeries_apply, tsum_empty]
    rfl
  · have h1 := h.hasBohrMean l
    have hc : Continuous fun t => ((h t : ℝ) : Complexification ℝ) :=
      Complexification.ofRealCLM.continuous.comp h.continuous
    have h2 : HasBohrMean (fun t => ((h t : ℝ) : Complexification ℝ)) (h.freq l) 0 := by
      refine hasBohrMean_zero_of_tendsto_zero ?_ (fun S => hc.intervalIntegrable 0 S) _
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [Complexification.norm_ofReal, hh]
      exact tendsto_input.norm.trans (by simp)
    exact h.coeff_ne_zero l (h1.unique h2)

set_option linter.unusedVariables false in
/-- **Infinite-order excitation is not sufficient** (`prop:infinite-pe-insufficient`): the
record `(ū, x̄)` generated by `ū` from `x̄₀ = b` is not informative on any window `(0, T)`: the
nonzero pair `(1, b)` annihilates it (`hT` is not needed). -/
theorem not_informative {T : ℝ} (hT : 0 < T) : ¬ Informative T input (sys.mild b input) := by
  intro h
  have := h.eq_zero (a := (1 : ℝ)) (b := b) (ae_restrict_of_forall_mem measurableSet_Ioc
    fun t ht => by
      rw [mild_b_input ht.1.le, input_eq_neg_inner ht.1.le]
      simp)
  exact one_ne_zero this.1

end PECounterexample

end DataDrivenControl
