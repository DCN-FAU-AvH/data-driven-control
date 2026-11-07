module

public import DataDrivenControl.Informativity.PE
public import DataDrivenControl.Analysis.BohrMean
public import DataDrivenControl.Analysis.Complexification
public import DataDrivenControl.Analysis.ExpSums

/-!
# Harmonic persistency of excitation

Paper: `def:harmonic-signal`, the facts stated after it, `def:harmonic-pe`, `lem:harmonic-pe`,
`lem:harmonic-pe-implies-pe` (`app:harmonic-pe`).

## Main declarations

* `HarmonicSignal U` (`def:harmonic-signal`): a representation
  `h(t) = ∑ₗ vₗ e^{i ωₗ t}` with `vₗ ∈ U_ℂ \ {0}` (`U_ℂ = Complexification U`), pairwise distinct
  frequencies `ωₗ ∈ ℝ` bounded by `Ω = sup |ωₗ|`, `∑ ‖vₗ‖ < ∞`, the set of pairs `(ωₗ, vₗ)`
  invariant under `(ω, v) ↦ (-ω, v̄)`, and `vₗ ∈ U` when `ωₗ = 0`.  The index set `ι` is any
  countable type (the paper's `ℓ ≥ 1`; see the deviation note below).  The signal is the
  function `h : ℝ → U`, `h t = re (∑ₗ e^{i ωₗ t} vₗ)` (`HarmonicSignal.toFun`, a `CoeFun`); by
  the symmetry the series is real (`HarmonicSignal.ofReal_apply`), so `h` *is* the series.
  `IsHarmonic f` says that a function `f : ℝ → U` admits such a representation.
* The facts after `def:harmonic-signal` (`app:harmonic-pe`): `h` is real valued
  (`ofReal_apply`), bounded (`norm_apply_le`), continuous (`continuous`), square integrable on
  every window (`memLp`), its coefficients are its Bohr means, `ĥ(ωₗ) = vₗ` and `ĥ(ω) = 0` at
  other frequencies (`hasBohrMean`, `hasBohrMean_of_ne`, `bohrMean_freq`), and it is entire of
  exponential type at most `Ω` (`exists_entire`).
* `HarmonicSignal.IsHarmonicPE` (`def:harmonic-pe`): there is a countable total family
  `(φⱼ)_{j ∈ J}` in `U_ℂ` (its complex closed span is `U_ℂ`) such that for every `j` there are
  pairwise distinct frequencies `ω_{j,k} = ω_{ℓ(j,k)}` of `h` (an injective `k ↦ ℓ(j,k)`),
  nonzero scalars `a_{j,k}` and `νⱼ ∈ ℝ` with `ĥ(ω_{j,k}) = v_{ℓ(j,k)} = a_{j,k} φⱼ` and
  `ω_{j,k} → νⱼ`.
* `hpeFreq`, `hpeSignal` and `isHarmonicPE_hpeSignal` (`lem:harmonic-pe`, the explicit signal):
  for a real orthonormal basis `(φⱼ)` of `U` (a `HilbertBasis J ℝ U`) numbered injectively by
  `n : J → ℕ` (the paper's `j` is `n j + 1`, its `k ≥ 1` is `k + 1`),
  `h(t) = ∑ⱼ ∑ₖ 2^{-j-k} cos(ω_{j,k} t) φⱼ`, `ω_{j,k} = 2 - 2^{-j} - 2^{-j-k}`, is harmonically
  persistently exciting; `exists_isHarmonicPE`: every nonzero separable `U` admits one.
* `HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite` (`lem:harmonic-pe-implies-pe`):
  `ū(t) = e^{σ t} h(t)` is persistently exciting of infinite order on every window `(0, T)`.

## Deviation (generalisation, harmless)

The paper indexes the representation by `ℓ ≥ 1`.  We allow any countable index type, so a finite
trigonometric polynomial is also "harmonic".  Harmonically persistently exciting signals have
infinitely many frequencies, so `IsHarmonicPE` and every theorem about it are unaffected.

## Proof of `lem:harmonic-pe-implies-pe`

With `sₗ = σ + i ωₗ`, `⟪ζₖ, ū t⟫ = ∑ₗ e^{sₗ t} ⟪ζₖ, vₗ⟫` (Hermitian product of `U_ℂ`, real on
`U`).  Derivative moments of an exponential series are computed termwise
(`⟨Dᵏ e^{s ·}, φ⟩ = sᵏ ∫ φ e^{s ·}`, and `∫`, `∑ₗ` commute by domination), so the relation
`∑ₖ ⟪ζₖ, Dᵏ ū⟫ = 0` in `𝒟'(I)` reads `∫ φ G = 0` with
`G t = e^{σ t} ∑ₗ pₗ e^{i ωₗ t}`, `pₗ = ∑ₖ sₗᵏ ⟪ζₖ, vₗ⟫`.  `G` is continuous, so it vanishes on `I`;
the identity theorem extends this to `ℝ`, and uniqueness of the Bohr coefficients gives
`pₗ = 0`.  Along the frequencies `ω_{j,k}` of `φⱼ` the polynomial `∑ₖ ⟪ζₖ, φⱼ⟫ Xᵏ` then has the
infinitely many distinct roots `σ + i ω_{j,k}` (the limit `νⱼ` is not needed), so it vanishes,
and totality of `(φⱼ)` gives `ζ = 0`.  The signal `ū` is never differentiated.

## Upstream results used

`bohrSeries`, `norm_bohrSeries_le`, `continuous_bohrSeries`, `hasBohrMean_bohrSeries`,
`hasBohrMean_bohrSeries_of_ne`, `eq_zero_of_bohrSeries_ae_eq_zero` (`Analysis/BohrMean`);
`differentiable_tsum_cexp_smul`, `harmonic_eq_zero_of_ae` (`Analysis/ExpSums`);
`Complexification.star_eq_self_iff`, `norm_re_le`, `Submodule.topologicalClosure_complexify`
(`Analysis/Complexification`);
`inner_derivMoment`, `derivMoment_eq_integral_of_hasDerivAt`, `eqOn_zero_of_integral_smul_eq_zero`
(`Signal/TestFunction`); for the polynomial step, `Polynomial.eq_zero_of_infinite_isRoot`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

open Complexification

/-- A **harmonic signal** (`def:harmonic-signal`), given by its representation
`h(t) = ∑ₗ vₗ e^{i ωₗ t}`: coefficients `vₗ ∈ U_ℂ \ {0}`, pairwise distinct frequencies
`ωₗ ∈ ℝ` with `Ω = sup |ωₗ| < ∞`, `∑ ‖vₗ‖ < ∞`, the set of pairs `(ωₗ, vₗ)` invariant under
`(ω, v) ↦ (-ω, v̄)`, and `vₗ ∈ U` when `ωₗ = 0`.  The index type `ι` is any countable type
(the paper's `ℓ ≥ 1`).  The signal itself is `HarmonicSignal.toFun`. -/
structure HarmonicSignal (U : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U] where
  /-- The index set of the representation. -/
  ι : Type
  [countable : Countable ι]
  /-- The frequencies `ωₗ`. -/
  freq : ι → ℝ
  /-- The coefficients `vₗ ∈ U_ℂ`. -/
  coeff : ι → Complexification U
  coeff_ne_zero : ∀ l, coeff l ≠ 0
  /-- The frequencies are pairwise distinct. -/
  freq_injective : Function.Injective freq
  /-- The frequencies are bounded. -/
  exists_abs_freq_le : ∃ Ω : ℝ, ∀ l, |freq l| ≤ Ω
  /-- The coefficients are absolutely summable. -/
  summable_norm_coeff : Summable fun l => ‖coeff l‖
  /-- The set of pairs `(ωₗ, vₗ)` is invariant under `(ω, v) ↦ (-ω, v̄)`. -/
  exists_conj : ∀ l, ∃ l', freq l' = -freq l ∧ coeff l' = star (coeff l)
  /-- `vₗ ∈ U` (it is real) when `ωₗ = 0`. -/
  coeff_im_eq_zero : ∀ l, freq l = 0 → (coeff l).im = 0

namespace HarmonicSignal

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

attribute [instance] HarmonicSignal.countable

/-- The harmonic signal `h(t) = ∑ₗ vₗ e^{i ωₗ t}` as a function `ℝ → U`: the real part of the
series, which is the series itself (`ofReal_apply`). -/
def toFun (h : HarmonicSignal U) (t : ℝ) : U :=
  (bohrSeries h.freq h.coeff t).re

instance : CoeFun (HarmonicSignal U) (fun _ => ℝ → U) := ⟨toFun⟩

theorem coe_apply (h : HarmonicSignal U) (t : ℝ) : h t = (bohrSeries h.freq h.coeff t).re :=
  rfl

/-- The frequency bound `Ω = sup_ℓ |ωₗ|` (`def:harmonic-signal`). -/
def Ω (h : HarmonicSignal U) : ℝ := ⨆ l, |h.freq l|

theorem abs_freq_le_Ω (h : HarmonicSignal U) (l : h.ι) : |h.freq l| ≤ h.Ω := by
  obtain ⟨Ω, hΩ⟩ := h.exists_abs_freq_le
  exact le_ciSup ⟨Ω, by rintro _ ⟨l', rfl⟩; exact hΩ l'⟩ l

/-- **Harmonic signals are bounded**: `‖h t‖ ≤ ∑ₗ ‖vₗ‖`. -/
theorem norm_apply_le (h : HarmonicSignal U) (t : ℝ) : ‖h t‖ ≤ ∑' l, ‖h.coeff l‖ :=
  (norm_re_le _).trans (norm_bohrSeries_le h.summable_norm_coeff t)

variable [CompleteSpace U] (h : HarmonicSignal U)

set_option linter.unusedSectionVars false in
/-- **Harmonic signals are real valued** (`app:harmonic-pe`): by the symmetry of the pairs
`(ωₗ, vₗ)`, the series `∑ₗ vₗ e^{i ωₗ t}` lies in `U ⊂ U_ℂ`, so it equals `h t`. -/
theorem ofReal_apply (t : ℝ) : ((h t : U) : Complexification U) = bohrSeries h.freq h.coeff t := by
  choose σ hσf hσc using h.exists_conj
  have hinv : Function.Involutive σ := fun l =>
    h.freq_injective (by rw [hσf, hσf, neg_neg])
  have hstar : star (bohrSeries h.freq h.coeff t) = bohrSeries h.freq h.coeff t := by
    rw [bohrSeries_apply, tsum_star,
      ← (hinv.toPerm σ).tsum_eq (fun l => Complex.exp (h.freq l * t * Complex.I) • h.coeff l)]
    congr 1
    funext l
    simp only [Function.Involutive.coe_toPerm, hσf, hσc, star_smul]
    congr 1
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  rw [coe_apply]
  exact (eq_ofReal_re_iff.2 (star_eq_self_iff.1 hstar)).symm

/-- **Harmonic signals are continuous.** -/
theorem continuous : Continuous h :=
  (reCLM (X := U)).continuous.comp (continuous_bohrSeries h.summable_norm_coeff)

/-- A harmonic signal restricted to a window is square integrable, `h|_I ∈ L²(I; U)`. -/
theorem memLp (T : ℝ) : MemLp h 2 (μI T) :=
  MemLp.of_bound h.continuous.aestronglyMeasurable _ (ae_of_all _ h.norm_apply_le)

/-- **Bohr coefficients** (`app:harmonic-pe`): `ĥ(ωₗ) = vₗ`, where
`ĥ(ω) = lim_{S→∞} S⁻¹ ∫₀^S e^{-iωt} h(t) dt` is computed in `U_ℂ`. -/
theorem hasBohrMean (l : h.ι) :
    HasBohrMean (fun t => (h t : Complexification U)) (h.freq l) (h.coeff l) := by
  simp_rw [h.ofReal_apply]
  exact hasBohrMean_bohrSeries h.summable_norm_coeff h.freq_injective l

/-- The Bohr mean of a harmonic signal vanishes at every frequency that is not one of its
`ωₗ`. -/
theorem hasBohrMean_of_ne {ω : ℝ} (hω : ∀ l, h.freq l ≠ ω) :
    HasBohrMean (fun t => (h t : Complexification U)) ω 0 := by
  simp_rw [h.ofReal_apply]
  exact hasBohrMean_bohrSeries_of_ne h.summable_norm_coeff hω

/-- `ĥ(ωₗ) = vₗ`, with the Bohr mean `bohrMean`. -/
theorem bohrMean_freq (l : h.ι) :
    bohrMean (fun t => (h t : Complexification U)) (h.freq l) = h.coeff l :=
  (h.hasBohrMean l).bohrMean_eq

/-- **Harmonic signals are entire of exponential type at most `Ω`** (`app:harmonic-pe`): the
series `z ↦ ∑ₗ vₗ e^{i ωₗ z}` is an entire extension of `h`, bounded by
`(∑ ‖vₗ‖) e^{Ω |Im z|}`. -/
theorem exists_entire :
    ∃ F : ℂ → Complexification U, Differentiable ℂ F ∧
      (∀ t : ℝ, F t = (h t : Complexification U)) ∧
      ∀ z : ℂ, ‖F z‖ ≤ (∑' l, ‖h.coeff l‖) * Real.exp (h.Ω * |z.im|) := by
  refine ⟨fun z => ∑' l, Complex.exp ((h.freq l * Complex.I) * z) • h.coeff l, ?_, ?_, ?_⟩
  · exact differentiable_tsum_cexp_smul (M := h.Ω)
      (fun l => by simpa [Complex.norm_real] using h.abs_freq_le_Ω l) h.summable_norm_coeff
  · intro t
    rw [h.ofReal_apply, bohrSeries_apply]
    refine tsum_congr fun l => ?_
    ring_nf
  · intro z
    have hb : ∀ l, ‖Complex.exp ((h.freq l * Complex.I) * z) • h.coeff l‖ ≤
        ‖h.coeff l‖ * Real.exp (h.Ω * |z.im|) := by
      intro l
      rw [norm_smul, Complex.norm_exp, mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      have e : ((h.freq l : ℂ) * Complex.I * z).re = -(h.freq l * z.im) := by
        simp [Complex.mul_re]
      rw [e]
      calc -(h.freq l * z.im) ≤ |h.freq l * z.im| := neg_le_abs _
        _ = |h.freq l| * |z.im| := abs_mul _ _
        _ ≤ h.Ω * |z.im| := mul_le_mul_of_nonneg_right (h.abs_freq_le_Ω l) (abs_nonneg _)
    have hs : Summable fun l => ‖h.coeff l‖ * Real.exp (h.Ω * |z.im|) :=
      h.summable_norm_coeff.mul_right _
    have hs' : Summable fun l => ‖Complex.exp ((h.freq l * Complex.I) * z) • h.coeff l‖ :=
      hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    calc ‖∑' l, Complex.exp ((h.freq l * Complex.I) * z) • h.coeff l‖
        ≤ ∑' l, ‖Complex.exp ((h.freq l * Complex.I) * z) • h.coeff l‖ :=
          norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' l, ‖h.coeff l‖ * Real.exp (h.Ω * |z.im|) := hs'.tsum_le_tsum hb hs
      _ = (∑' l, ‖h.coeff l‖) * Real.exp (h.Ω * |z.im|) := tsum_mul_right

end HarmonicSignal

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- A signal `f : ℝ → U` is **harmonic** (`def:harmonic-signal`) if it admits a representation
`f(t) = ∑ₗ vₗ e^{i ωₗ t}` as in `HarmonicSignal`. -/
def IsHarmonic (f : ℝ → U) : Prop := ∃ h : HarmonicSignal U, ⇑h = f

namespace HarmonicSignal

/-- A harmonic signal is **harmonically persistently exciting** (`def:harmonic-pe`) if there is
a finite or countable total family `(φⱼ)_{j ∈ J}` in `U_ℂ` (its complex closed span is `U_ℂ`)
such that, for each `j ∈ J`, there are pairwise distinct frequencies `ω_{j,k}` of `h`
(`k ≥ 1`; here `ω_{j,k} = h.freq (ℓ k)` for an injective `ℓ : ℕ → h.ι`), nonzero scalars
`a_{j,k}` and a limit `νⱼ ∈ ℝ` with `ĥ(ω_{j,k}) = a_{j,k} φⱼ` and `ω_{j,k} → νⱼ`.  The Bohr
coefficient `ĥ(ω_{j,k})` is the coefficient `h.coeff (ℓ k)` (`bohrMean_freq`). -/
def IsHarmonicPE (h : HarmonicSignal U) : Prop :=
  ∃ (J : Type) (_ : Countable J) (φ : J → Complexification U),
    (Submodule.span ℂ (Set.range φ)).topologicalClosure = ⊤ ∧
    ∀ j, ∃ (ℓ : ℕ → h.ι) (a : ℕ → ℂ) (ν : ℝ), Function.Injective ℓ ∧ (∀ k, a k ≠ 0) ∧
      (∀ k, h.coeff (ℓ k) = a k • φ j) ∧ Tendsto (fun k => h.freq (ℓ k)) atTop (𝓝 ν)

end HarmonicSignal

/-- The frequencies of `lem:harmonic-pe`, `ω_{j,k} = 2 - 2^{-j} - 2^{-j-k}`, in the paper's
numbering `j, k ≥ 1`: `hpeFreq j k` is `ω_{j+1, k+1}`. -/
def hpeFreq (j k : ℕ) : ℝ := 2 - (2 : ℝ)⁻¹ ^ (j + 1) - (2 : ℝ)⁻¹ ^ (j + 1 + (k + 1))

/-- The signal of `lem:harmonic-pe`, `h(t) = ∑ⱼ ∑_{k ≥ 1} 2^{-j-k} cos(ω_{j,k} t) φⱼ`, for a real
orthonormal basis `φ` of `U` indexed by `J` and an injective numbering `n : J → ℕ` (the basis
vector `φ i` plays the role of the paper's `φ_{n i + 1}`; the inner index `k : ℕ` is the
paper's `k + 1`). -/
def hpeSignal {J : Type*} (φ : HilbertBasis J ℝ U) (n : J → ℕ) (t : ℝ) : U :=
  ∑' i, ∑' k : ℕ, ((2 : ℝ)⁻¹ ^ (n i + 1 + (k + 1)) * Real.cos (hpeFreq (n i) k * t)) • φ i

/-! ### The explicit harmonically persistently exciting signal -/

private theorem hpeFreq_pos (m k : ℕ) : 0 < hpeFreq m k := by
  unfold hpeFreq
  have h1 : (2 : ℝ)⁻¹ ^ (m + 1) ≤ 2⁻¹ := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (2 : ℝ)⁻¹ ^ (m + 1 + (k + 1)) ≤ 2⁻¹ :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

private theorem hpeFreq_le_two (m k : ℕ) : hpeFreq m k ≤ 2 := by
  unfold hpeFreq
  have h1 : (0 : ℝ) ≤ 2⁻¹ ^ (m + 1) := by positivity
  have h2 : (0 : ℝ) ≤ 2⁻¹ ^ (m + 1 + (k + 1)) := by positivity
  linarith

/-- The blocks of frequencies are ordered: block `m` lies below block `m'` for `m < m'`. -/
private theorem hpeFreq_lt {m m' : ℕ} (hm : m < m') (k k' : ℕ) : hpeFreq m k < hpeFreq m' k' := by
  unfold hpeFreq
  have h1 : (2 : ℝ)⁻¹ ^ (m' + 1) ≤ 2⁻¹ ^ (m + 1 + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (2 : ℝ)⁻¹ ^ (m' + 1 + (k' + 1)) < 2⁻¹ ^ (m' + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have h3 : (0 : ℝ) < 2⁻¹ ^ (m + 1 + (k + 1)) := by positivity
  have h4 : (2 : ℝ)⁻¹ ^ (m + 1 + 1) = 2⁻¹ ^ (m + 1) * 2⁻¹ := pow_succ _ _
  linarith

/-- The frequencies `ω_{j,k}` are pairwise distinct. -/
private theorem hpeFreq_inj {m k m' k' : ℕ} (h : hpeFreq m k = hpeFreq m' k') :
    m = m' ∧ k = k' := by
  rcases lt_trichotomy m m' with hm | rfl | hm
  · exact absurd h (hpeFreq_lt hm k k').ne
  · refine ⟨rfl, ?_⟩
    unfold hpeFreq at h
    have h' : (2 : ℝ)⁻¹ ^ (m + 1 + (k + 1)) = 2⁻¹ ^ (m + 1 + (k' + 1)) := by linarith
    have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num) h'
    omega
  · exact absurd h (hpeFreq_lt hm k' k).ne'

private theorem summable_hpe_aux (n : ℕ → Prop) :
    Summable fun l : {m : ℕ // n m} × ℕ × Bool =>
      (2 : ℝ)⁻¹ ^ ((l.1 : ℕ) + 1 + (l.2.1 + 1)) / 2 := by
  have hg : Summable fun m : ℕ => (2 : ℝ)⁻¹ ^ (m + 1) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right 2⁻¹).congr
      fun m => (pow_succ _ _).symm
  have hf : Summable fun m : {m : ℕ // n m} => (2 : ℝ)⁻¹ ^ ((m : ℕ) + 1) :=
    hg.comp_injective Subtype.val_injective
  have hb : Summable fun _ : Bool => (2 : ℝ)⁻¹ := Summable.of_finite
  have hkb : Summable fun x : ℕ × Bool => (2 : ℝ)⁻¹ ^ (x.1 + 1) * (2 : ℝ)⁻¹ :=
    Summable.mul_of_nonneg (f := fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1))
      (g := fun _ : Bool => (2 : ℝ)⁻¹) hg hb (fun _ => by positivity) (fun _ => by positivity)
  have hall : Summable fun x : {m : ℕ // n m} × (ℕ × Bool) =>
      (2 : ℝ)⁻¹ ^ ((x.1 : ℕ) + 1) * ((2 : ℝ)⁻¹ ^ (x.2.1 + 1) * (2 : ℝ)⁻¹) :=
    Summable.mul_of_nonneg (f := fun m : {m : ℕ // n m} => (2 : ℝ)⁻¹ ^ ((m : ℕ) + 1))
      (g := fun x : ℕ × Bool => (2 : ℝ)⁻¹ ^ (x.1 + 1) * (2 : ℝ)⁻¹) hf hkb
      (fun _ => by positivity) (fun _ => by positivity)
  refine hall.congr fun l => ?_
  rw [pow_add (2 : ℝ)⁻¹ ((l.1 : ℕ) + 1)]
  ring

/-- The harmonic signal of `lem:harmonic-pe`, in complex exponential form: index set
`range n × ℕ × Bool`, frequencies `± ω_{j,k}`, coefficients `2^{-j-k-1} φⱼ`. -/
private def hpeHarmonic {J : Type*} (φ : HilbertBasis J ℝ U) {n : J → ℕ}
    (hn : Function.Injective n) : HarmonicSignal U where
  ι := Set.range n × ℕ × Bool
  freq l := if l.2.2 then hpeFreq l.1 l.2.1 else -hpeFreq l.1 l.2.1
  coeff l := (((2 : ℝ)⁻¹ ^ ((l.1 : ℕ) + 1 + (l.2.1 + 1)) / 2) •
    φ ((Equiv.ofInjective n hn).symm l.1) : U)
  coeff_ne_zero l := by
    rw [Ne, ofReal_eq_zero]
    exact smul_ne_zero (by positivity) (φ.orthonormal.ne_zero _)
  freq_injective := by
    rintro ⟨⟨m, hm⟩, k, b⟩ ⟨⟨m', hm'⟩, k', b'⟩ h
    have hp := hpeFreq_pos m k
    have hp' := hpeFreq_pos m' k'
    cases b <;> cases b' <;>
      simp only [Bool.false_eq_true, ↓reduceIte, neg_inj] at h
    · obtain ⟨rfl, rfl⟩ := hpeFreq_inj h
      rfl
    · linarith
    · linarith
    · obtain ⟨rfl, rfl⟩ := hpeFreq_inj h
      rfl
  exists_abs_freq_le := ⟨2, fun l => by
    have := hpeFreq_pos l.1 l.2.1
    have := hpeFreq_le_two l.1 l.2.1
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith⟩
  summable_norm_coeff := (summable_hpe_aux (· ∈ Set.range n)).congr fun l => by
    rw [norm_ofReal, norm_smul, φ.orthonormal.1, mul_one, Real.norm_of_nonneg (by positivity)]
  exists_conj l := ⟨(l.1, l.2.1, !l.2.2), by cases l.2.2 <;> simp, by simp⟩
  coeff_im_eq_zero l _ := ofReal_im _

private theorem hpeHarmonic_apply [CompleteSpace U] {J : Type*} (φ : HilbertBasis J ℝ U) {n : J → ℕ}
    (hn : Function.Injective n) : ⇑(hpeHarmonic φ hn) = hpeSignal φ n := by
  funext t
  set e := Equiv.ofInjective n hn
  -- the real part of the exponential series
  set F : Set.range n × ℕ × Bool → U := fun l =>
    Real.cos ((if l.2.2 then hpeFreq l.1 l.2.1 else -hpeFreq l.1 l.2.1) * t) •
      (((2 : ℝ)⁻¹ ^ ((l.1 : ℕ) + 1 + (l.2.1 + 1)) / 2) • φ (e.symm l.1)) with hF
  have hsumm : Summable fun l => Complex.exp ((hpeHarmonic φ hn).freq l * t * Complex.I) •
      (hpeHarmonic φ hn).coeff l :=
    Summable.of_norm ((hpeHarmonic φ hn).summable_norm_coeff.congr fun l => by
      rw [norm_smul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul])
  have h1 : (hpeHarmonic φ hn) t = ∑' l : Set.range n × ℕ × Bool, F l := by
    rw [HarmonicSignal.coe_apply, bohrSeries_apply, ← reCLM_apply, reCLM.map_tsum hsumm]
    refine tsum_congr fun l => ?_
    change (Complex.exp (((if l.2.2 then hpeFreq l.1 l.2.1 else -hpeFreq l.1 l.2.1 : ℝ) : ℂ) *
      t * Complex.I) • ((((2 : ℝ)⁻¹ ^ ((l.1 : ℕ) + 1 + (l.2.1 + 1)) / 2) •
        φ (e.symm l.1) : U) : Complexification U)).re = F l
    rw [smul_re, ofReal_re, ofReal_im, smul_zero, sub_zero, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  have hFs : Summable F := by
    refine Summable.of_norm ((summable_hpe_aux (· ∈ Set.range n)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun l => ?_)
    have hc : (0 : ℝ) ≤ 2⁻¹ ^ ((l.1 : ℕ) + 1 + (l.2.1 + 1)) / 2 := by positivity
    simp only [hF, norm_smul, φ.orthonormal.1, mul_one, Real.norm_of_nonneg hc, Real.norm_eq_abs]
    exact mul_le_of_le_one_left hc (Real.abs_cos_le_one _)
  rw [h1, hFs.tsum_prod, ← e.tsum_eq]
  refine tsum_congr fun i => ?_
  rw [(hFs.prod_factor _).tsum_prod]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [hF, e, Equiv.ofInjective_apply, Equiv.ofInjective_symm_apply, ↓reduceIte,
    Bool.false_eq_true, neg_mul, Real.cos_neg, ← add_smul, smul_smul]
  congr 1
  ring

/-- A Hilbert basis of a separable space is countable (the balls of radius `1/2` around the
basis vectors are disjoint; as `Necessity.countable_of_hilbertBasis`). -/
private theorem countable_hilbertBasis' [TopologicalSpace.SeparableSpace U] {ι : Type*}
    (e : HilbertBasis ι ℝ U) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (e i) (1 / 2))
    (fun i k hik => Metric.ball_disjoint_ball ?_) (fun i => Metric.isOpen_ball)
    (fun i => ⟨e i, Metric.mem_ball_self (by norm_num)⟩)
  rw [dist_eq_norm]
  have h2 : ‖e i - e k‖ ^ 2 = 2 := by
    rw [@norm_sub_sq_real, e.orthonormal.1 i, e.orthonormal.1 k, e.orthonormal.2 hik]
    norm_num
  nlinarith [norm_nonneg (e i - e k)]

/-- **Existence of harmonically persistently exciting signals, explicit form**
(`lem:harmonic-pe`): for a real orthonormal basis `(φⱼ)_{j ∈ J}` of `U` and an injective
numbering `n : J → ℕ` (`J = {1, …, dim U}` or `ℕ` in the paper), the signal
`h(t) = ∑ⱼ ∑ₖ 2^{-j-k} cos(ω_{j,k} t) φⱼ`, `ω_{j,k} = 2 - 2^{-j} - 2^{-j-k}` (`hpeSignal`), is
harmonic and harmonically persistently exciting. -/
theorem isHarmonicPE_hpeSignal [CompleteSpace U] {J : Type*} (φ : HilbertBasis J ℝ U)
    {n : J → ℕ} (hn : Function.Injective n) :
    ∃ h : HarmonicSignal U, ⇑h = hpeSignal φ n ∧ h.IsHarmonicPE := by
  refine ⟨hpeHarmonic φ hn, hpeHarmonic_apply φ hn, ?_⟩
  set e := Equiv.ofInjective n hn
  refine ⟨Set.range n, inferInstance, fun m => ((φ (e.symm m) : U) : Complexification U), ?_,
    fun m => ?_⟩
  · -- totality: the complex span of the real basis is dense in `U_ℂ`
    have hof : ∀ x ∈ Submodule.span ℝ (Set.range ⇑φ), (x : Complexification U) ∈
        Submodule.span ℂ (Set.range fun m => ((φ (e.symm m) : U) : Complexification U)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨e i, by simp [e]⟩
      | zero => simp
      | add x y _ _ hx hy => rw [ofReal_add]; exact add_mem hx hy
      | smul r x _ hx => rw [ofReal_smul, ← Complex.coe_smul]; exact Submodule.smul_mem _ _ hx
    have hle : (Submodule.span ℝ (Set.range ⇑φ)).complexify ≤
        Submodule.span ℂ (Set.range fun m => ((φ (e.symm m) : U) : Complexification U)) := by
      intro z hz
      rw [Submodule.mem_complexify] at hz
      rw [← re_add_I_smul_im z]
      exact add_mem (hof _ hz.1) (Submodule.smul_mem _ _ (hof _ hz.2))
    rw [eq_top_iff]
    calc ⊤ = (Submodule.span ℝ (Set.range ⇑φ)).complexify.topologicalClosure := by
          rw [Submodule.topologicalClosure_complexify, φ.dense_span, Submodule.complexify_top]
      _ ≤ _ := Submodule.topologicalClosure_mono hle
  · -- the frequencies `ω_{j,k}`, `k ≥ 1`, of the direction `φⱼ`
    have h0 : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ ((m : ℕ) + 1 + (k + 1))) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
    refine ⟨fun k => (m, k, true), fun k => (((2 : ℝ)⁻¹ ^ ((m : ℕ) + 1 + (k + 1)) / 2 : ℝ) : ℂ),
      2 - (2 : ℝ)⁻¹ ^ ((m : ℕ) + 1), fun k k' hk => congrArg (fun l : Set.range n × ℕ × Bool => l.2.1) hk,
      fun k => Complex.ofReal_ne_zero.2 (by positivity), fun k => ?_, ?_⟩
    · change ((((2 : ℝ)⁻¹ ^ ((m : ℕ) + 1 + (k + 1)) / 2) • φ (e.symm m) : U) :
        Complexification U) = _
      rw [ofReal_smul, Complex.coe_smul]
    · change Tendsto (fun k : ℕ => hpeFreq m k) atTop _
      unfold hpeFreq
      simpa using (tendsto_const_nhds (x := 2 - (2 : ℝ)⁻¹ ^ ((m : ℕ) + 1))).sub h0

/-- **Existence of harmonically persistently exciting signals** (`lem:harmonic-pe`): every
nonzero separable Hilbert space `U` admits a harmonically persistently exciting signal. -/
theorem exists_isHarmonicPE [CompleteSpace U] [TopologicalSpace.SeparableSpace U]
    [Nontrivial U] : ∃ h : HarmonicSignal U, h.IsHarmonicPE := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ U
  have := countable_hilbertBasis' b
  obtain ⟨n, hn⟩ := Countable.exists_injective_nat w
  obtain ⟨h, -, hh⟩ := isHarmonicPE_hpeSignal b hn
  exact ⟨h, hh⟩

/-! ### Harmonic excitation implies excitation of infinite order -/

/-- `⟨Dᵏ e^{s ·}, φ⟩ = sᵏ ∫ φ e^{s ·}`. -/
private theorem derivMoment_cexp {T : ℝ} {φ : ℝ → ℝ} (hφ : IsTestFunction T φ) (s : ℂ) (k : ℕ) :
    derivMoment k (fun t : ℝ => Complex.exp (s * t)) φ =
      s ^ k * ∫ t, φ t • Complex.exp (s * t) := by
  have hd : ∀ j : ℕ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => s ^ j * Complex.exp (s * t))
      (s ^ (j + 1) * Complex.exp (s * t)) t := by
    intro j t
    have h1 : HasDerivAt (fun t : ℝ => s * (t : ℂ)) s t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul s
    have := h1.cexp.const_mul (s ^ j)
    convert this using 1
    ring
  have := derivMoment_eq_integral_of_hasDerivAt hφ
    (v := fun j t => s ^ j * Complex.exp (s * t)) k (fun j _ t _ => hd j t)
    (fun j _ => (by fun_prop : Continuous fun t : ℝ => s ^ j * Complex.exp (s * t)).continuousOn)
  simp only [pow_zero, one_mul] at this
  rw [this]
  simp_rw [← mul_smul_comm]
  exact integral_const_mul _ _

private theorem norm_integral_smul_cexp_le (ψ : ℝ → ℝ) (s : ℂ) :
    ‖∫ t, ψ t • Complex.exp (s * t)‖ ≤ ∫ t, |ψ t| * Real.exp (s.re * t) := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [norm_smul, Complex.norm_exp, Real.norm_eq_abs, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Derivative moments of an exponential series `∑ₗ aₗ e^{sₗ t}` with `Re sₗ = σ` and
`∑ |aₗ| < ∞` are computed termwise. -/
private theorem derivMoment_tsum_cexp {ι : Type*} [Countable ι] {T σ : ℝ} {φ : ℝ → ℝ}
    (hφ : IsTestFunction T φ) {a s : ι → ℂ} (ha : Summable fun l => ‖a l‖)
    (hs : ∀ l, (s l).re = σ) (k : ℕ) :
    derivMoment k (fun t : ℝ => ∑' l, a l * Complex.exp (s l * t)) φ =
      ∑' l, a l * derivMoment k (fun t : ℝ => Complex.exp (s l * t)) φ := by
  have hψ : IsTestFunction T (iteratedDeriv k φ) := hφ.iteratedDeriv k
  have hint : ∀ l, Integrable (fun t => iteratedDeriv k φ t • (a l * Complex.exp (s l * t))) :=
    fun l => hψ.integrable_smul ((by fun_prop : Continuous fun t : ℝ =>
      a l * Complex.exp (s l * t)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hnorm : ∀ l, ∫ t, ‖iteratedDeriv k φ t • (a l * Complex.exp (s l * t))‖ =
      ‖a l‖ * ∫ t, |iteratedDeriv k φ t| * Real.exp (σ * t) := by
    intro l
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [norm_smul, norm_mul, Complex.norm_exp, Real.norm_eq_abs, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hs l]
    ring
  have hsum := integral_tsum_of_summable_integral_norm hint
    (by simp_rw [hnorm]; exact ha.mul_right _)
  simp only [derivMoment]
  simp_rw [← tsum_const_smul'' (iteratedDeriv k φ _ : ℝ)]
  rw [← hsum, ← tsum_const_smul'']
  refine tsum_congr fun l => ?_
  have e : ∀ t : ℝ, iteratedDeriv k φ t • (a l * Complex.exp (s l * t)) =
      a l * (iteratedDeriv k φ t • Complex.exp (s l * t)) := fun t => (mul_smul_comm _ _ _).symm
  simp_rw [e]
  rw [integral_const_mul, mul_smul_comm]

/-- **Harmonic persistency of excitation implies excitation of infinite order**
(`lem:harmonic-pe-implies-pe`): if `h` is harmonically persistently exciting and `σ ∈ ℝ`, then
`ū(t) = e^{σ t} h(t)`, restricted to `I = (0, T)`, is persistently exciting of infinite order. -/
theorem HarmonicSignal.IsHarmonicPE.persistentlyExcitingInfinite [CompleteSpace U]
    {h : HarmonicSignal U} (hh : h.IsHarmonicPE) (σ : ℝ) {T : ℝ} (hT : 0 < T) :
    PersistentlyExcitingInfinite T (fun t => Real.exp (σ * t) • h t) := by
  intro L ζ hζ
  obtain ⟨J, _, φ, hφtot, hφ⟩ := hh
  set ub : ℝ → U := fun t => Real.exp (σ * t) • h t with hub
  set s : h.ι → ℂ := fun l => σ + h.freq l * Complex.I with hs_def
  have hs_re : ∀ l, (s l).re = σ := fun l => by simp [s]
  set c : Fin L → h.ι → ℂ := fun k l => ⟪((ζ k : U) : Complexification U), h.coeff l⟫_ℂ
    with hc_def
  set p : h.ι → ℂ := fun l => ∑ k : Fin L, s l ^ (k : ℕ) * c k l with hp_def
  -- summability
  have hcsum : ∀ k, Summable fun l => ‖c k l‖ := fun k =>
    (h.summable_norm_coeff.mul_left ‖((ζ k : U) : Complexification U)‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun l => norm_inner_le_norm _ _
  set M : ℝ := |σ| + h.Ω with hM
  have hsM : ∀ l, ‖s l‖ ≤ M := fun l => by
    calc ‖s l‖ ≤ ‖(σ : ℂ)‖ + ‖(h.freq l : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |σ| + |h.freq l| := by simp [Complex.norm_real]
      _ ≤ M := by linarith [h.abs_freq_le_Ω l]
  have hpsum : Summable fun l => ‖p l‖ := by
    have : Summable fun l => ∑ k : Fin L, M ^ (k : ℕ) * ‖c k l‖ :=
      summable_sum fun k _ => (hcsum k).mul_left _
    refine this.of_nonneg_of_le (fun _ => norm_nonneg _) fun l => ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hsM l) _)
      (norm_nonneg _)
  -- the pairing `⟪ζₖ, ū t⟫` as an exponential series
  have hexp : ∀ (k : Fin L) (t : ℝ),
      ((⟪ζ k, ub t⟫_ℝ : ℝ) : ℂ) = ∑' l, c k l * Complex.exp (s l * t) := by
    intro k t
    have hsumm : Summable fun l => Complex.exp (h.freq l * t * Complex.I) • h.coeff l :=
      Summable.of_norm (h.summable_norm_coeff.congr fun l => by
        rw [norm_smul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul])
    rw [← inner_ofReal_ofReal, hub, ofReal_smul, h.ofReal_apply, bohrSeries_apply,
      ← Complex.coe_smul, inner_smul_right, ← innerSL_apply_apply, (innerSL ℂ _).map_tsum hsumm,
      ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [innerSL_apply_apply, inner_smul_right, Complex.ofReal_exp]
    simp only [c, s]
    rw [mul_left_comm, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  have hub_cont : Continuous ub :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul h.continuous
  have hub_int : Integrable ub (μI T) :=
    (hub_cont.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self
  -- Step 1: tested against `ψ`, the relation reads `∫ ψ G = 0`, `G t = ∑ₗ pₗ e^{sₗ t}`
  have hG0 : ∀ ψ : ℝ → ℝ, IsTestFunction T ψ →
      ∫ t, ψ t • ∑' l, p l * Complex.exp (s l * t) = 0 := by
    intro ψ hψ
    set B : ℕ → ℝ := fun k => ∫ t, |iteratedDeriv k ψ t| * Real.exp (σ * t) with hB
    have hD : ∀ (k : ℕ) l, ‖derivMoment k (fun t : ℝ => Complex.exp (s l * t)) ψ‖ ≤ B k := by
      intro k l
      rw [derivMoment, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      simpa [hs_re l] using norm_integral_smul_cexp_le (iteratedDeriv k ψ) (s l)
    have hk : ∀ k : Fin L, ((⟪ζ k, derivMoment (k : ℕ) ub ψ⟫_ℝ : ℝ) : ℂ) =
        ∑' l, c k l * derivMoment (k : ℕ) (fun t : ℝ => Complex.exp (s l * t)) ψ := by
      intro k
      have h1 := Complex.ofRealCLM.map_derivMoment hψ (hub_int.const_inner (ζ k)) (k : ℕ)
      simp only [Complex.ofRealCLM_apply] at h1
      rw [inner_derivMoment (ζ k) hψ hub_int, h1]
      simp_rw [hexp k]
      exact derivMoment_tsum_cexp hψ (hcsum k) hs_re _
    have hsk : ∀ k : Fin L, Summable fun l =>
        c k l * derivMoment (k : ℕ) (fun t : ℝ => Complex.exp (s l * t)) ψ := fun k =>
      Summable.of_norm (((hcsum k).mul_right (B k)).of_nonneg_of_le (fun _ => norm_nonneg _)
        fun l => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hD k l) (norm_nonneg _))
    have h0 := congrArg (fun r : ℝ => (r : ℂ)) (hζ ψ hψ)
    simp only [Complex.ofReal_sum, Complex.ofReal_zero, hk] at h0
    rw [← Summable.tsum_finsetSum fun k _ => hsk k] at h0
    have e : ∀ l, ∑ k : Fin L, c k l * derivMoment (k : ℕ) (fun t : ℝ => Complex.exp (s l * t)) ψ
        = p l * derivMoment 0 (fun t : ℝ => Complex.exp (s l * t)) ψ := by
      intro l
      simp only [derivMoment_cexp hψ, p, Finset.sum_mul, pow_zero, one_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e] at h0
    rw [← derivMoment_tsum_cexp hψ hpsum hs_re, derivMoment_zero] at h0
    exact h0
  -- Step 2: `G = e^{σ t} ∑ₗ pₗ e^{i ωₗ t}` vanishes on `I`, hence on `ℝ`, hence `p = 0`
  have hG : ∀ t : ℝ, ∑' l, p l * Complex.exp (s l * t) =
      Complex.exp (σ * t) * bohrSeries h.freq p t := by
    intro t
    rw [bohrSeries_apply, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    simp only [s]
    ring
  have hGc : Continuous fun t : ℝ => Complex.exp (σ * t) * bohrSeries h.freq p t :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (σ * t)).mul (continuous_bohrSeries hpsum)
  have hzero := eqOn_zero_of_integral_smul_eq_zero (T := T) hGc.continuousOn fun ψ hψ => by
    simpa only [hG] using hG0 ψ hψ
  have hB : ∀ t ∈ Ioo 0 T, bohrSeries h.freq p t = 0 := fun t ht =>
    (mul_eq_zero.1 (hzero t ht)).resolve_left (Complex.exp_ne_zero _)
  have hB' := harmonic_eq_zero_of_ae h.abs_freq_le_Ω hpsum hT
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => by
      rw [← bohrSeries_apply]; exact hB t ht))
  have hp0 : p = 0 := eq_zero_of_bohrSeries_ae_eq_zero hpsum h.freq_injective
    (ae_of_all _ fun t => by rw [bohrSeries_apply]; exact hB' t)
  -- Step 3: along the frequencies of `φ j`, `∑ₖ sᵏ ⟪ζₖ, φ j⟫` has infinitely many zeros
  have hd : ∀ (j : J) (k : Fin L), ⟪((ζ k : U) : Complexification U), φ j⟫_ℂ = 0 := by
    intro j
    obtain ⟨ℓ, a, ν, hℓ, ha, hca, -⟩ := hφ j
    set d : Fin L → ℂ := fun k => ⟪((ζ k : U) : Complexification U), φ j⟫_ℂ with hd_def
    set P : Polynomial ℂ := ∑ k : Fin L, Polynomial.C (d k) * Polynomial.X ^ (k : ℕ) with hP_def
    have hroot : ∀ m, P.IsRoot (s (ℓ m)) := by
      intro m
      have h1 := congrFun hp0 (ℓ m)
      simp only [p, c, hca m, inner_smul_right, Pi.zero_apply] at h1
      have h2 : a m * ∑ k : Fin L, d k * s (ℓ m) ^ (k : ℕ) = 0 := by
        rw [Finset.mul_sum, ← h1]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp [P, Polynomial.IsRoot, Polynomial.eval_finsetSum,
        (mul_eq_zero.1 h2).resolve_left (ha m)]
    have hinj : Function.Injective fun m => s (ℓ m) := by
      intro m m' hm
      have := congrArg Complex.im hm
      simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at this
      exact hℓ (h.freq_injective this)
    have hP : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P
      ((Set.infinite_range_of_injective hinj).mono (by rintro _ ⟨m, rfl⟩; exact hroot m))
    intro k
    have := congrArg (fun q : Polynomial ℂ => q.coeff k) hP
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single k (fun i _ hi => ite_eq_right fun h' => hi (Fin.ext h').symm)
      (by simp)] at this
    simpa using this
  -- Step 4: totality of `(φ j)`
  funext k
  have hle : Submodule.span ℂ (range φ) ≤
      (innerSL ℂ ((ζ k : U) : Complexification U)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp [hd j k]
  have hmem := Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker _)
  rw [hφtot] at hmem
  have := hmem (Submodule.mem_top (x := ((ζ k : U) : Complexification U)))
  simpa using this

end DataDrivenControl
