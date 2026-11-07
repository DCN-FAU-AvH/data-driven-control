module

public import DataDrivenControl.Informativity.Harmonic

/-!
# The exciting input of the boundary-heat example

Paper: `ex:boundary-heat-informative` (`informativity.tex`) and the paragraph "Excitation and
informativity" of `app:boundary-heat-informative` (`appendix_proofs.tex`).

The paper's input is `ū(t) = ∑_{k ≥ 1} 2^{-k} cos(ω_k t)` with `ω_k = 1 + 1/(k + 1)`.

**Index shift.**  Lean counts from `0`: Lean's `k : ℕ` is the paper's `k + 1`.  So
`heatFreq k = 1 + 1/(k + 2)` is the paper's `ω_{k+1}`, and the weight of `cos (heatFreq k t)` is
`2^{-(k+1)}`.  In complex exponential form, `2^{-(k+1)} cos(ω t) = 2^{-(k+2)} e^{iωt} +
2^{-(k+2)} e^{-iωt}`, so `heatInput` is indexed by `ℕ × Bool` (`true ↦ +ω`, `false ↦ -ω`) with
the coefficients `2^{-(k+2)}` (the paper's `2^{-k-1}`) in `U_ℂ = Complexification ℝ`.

## Main declarations

* `heatFreq`, `heatInput : HarmonicSignal ℝ`; `heatInput_apply`
  (`ū(t) = ∑ₖ 2^{-(k+1)} cos(heatFreq k · t)`), `memLp_heatInput`;
* `isHarmonicPE_heatInput`: `ū` is harmonically persistently exciting, with the total family
  `{1}` in `U_ℂ`, the frequencies `ω_k → 1` and the coefficients `2^{-(k+2)}`;
* `abs_mem_closure_range_freq_heatInput`: every `ω` in the closure of the frequency set
  satisfies `1 ≤ |ω| ≤ 3/2`; in particular `ω ≠ 0` (`ne_zero_of_mem_closure_range_freq`), which
  puts `iω` in the resolvent set of the heat generator (spectrum `{-n²π²} ⊂ (-∞, 0]`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace DataDrivenControl

namespace BoundaryHeat

open Complexification

/-- The frequencies `ω_k = 1 + 1/(k + 1)` of `ex:boundary-heat-informative`, shifted to start at
`k = 0`: `heatFreq k = 1 + 1/(k + 2)` is the paper's `ω_{k+1}`. -/
def heatFreq (k : ℕ) : ℝ := 1 + 1 / ((k : ℝ) + 2)

/-- `1 < heatFreq k`. -/
theorem one_lt_heatFreq (k : ℕ) : 1 < heatFreq k := by
  unfold heatFreq
  have : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  linarith

/-- `heatFreq k ≤ 3/2`. -/
theorem heatFreq_le (k : ℕ) : heatFreq k ≤ 3 / 2 := by
  unfold heatFreq
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- The frequencies `ω_k` are pairwise distinct. -/
theorem heatFreq_injective : Function.Injective heatFreq := by
  intro k k' h
  unfold heatFreq at h
  have h' : 1 / ((k : ℝ) + 2) = 1 / ((k' : ℝ) + 2) := by linarith
  rw [one_div, one_div, inv_inj] at h'
  exact_mod_cast add_right_cancel h'

/-- `ω_k → 1`. -/
theorem tendsto_heatFreq : Tendsto heatFreq atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have := (tendsto_const_nhds (x := (1 : ℝ))).add h
  rw [add_zero] at this
  exact this

/-- The coefficients of `heatInput` are summable: `∑_{(k, b) ∈ ℕ × Bool} 2^{-(k+2)} < ∞`. -/
theorem summable_heatCoeff : Summable fun l : ℕ × Bool => (2 : ℝ)⁻¹ ^ (l.1 + 2) := by
  have hg : Summable fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 2) :=
    (summable_nat_add_iff 2).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hb : Summable fun l : ℕ × Bool => (2 : ℝ)⁻¹ ^ (l.1 + 2) * 1 :=
    Summable.mul_of_nonneg (f := fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 2)) (g := fun _ : Bool => (1 : ℝ))
      hg Summable.of_finite (fun _ => by positivity) (fun _ => by positivity)
  exact hb.congr fun l => mul_one _

/-- The input `ū(t) = ∑_{k ≥ 1} 2^{-k} cos(ω_k t)` of `ex:boundary-heat-informative` as a
harmonic signal (`def:harmonic-signal`): index set `ℕ × Bool`, frequencies `± heatFreq k`,
coefficients `2^{-(k+2)} ∈ U_ℂ` (Lean's `k` is the paper's `k + 1`). -/
def heatInput : HarmonicSignal ℝ where
  ι := ℕ × Bool
  freq l := if l.2 then heatFreq l.1 else -heatFreq l.1
  coeff l := (((2 : ℝ)⁻¹ ^ (l.1 + 2) : ℝ) : Complexification ℝ)
  coeff_ne_zero l := by
    rw [Ne, ofReal_eq_zero]
    positivity
  freq_injective := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h
    have hp := one_lt_heatFreq k
    have hp' := one_lt_heatFreq k'
    cases b <;> cases b' <;>
      simp only [Bool.false_eq_true, ↓reduceIte, neg_inj] at h
    · rw [heatFreq_injective h]
    · linarith
    · linarith
    · rw [heatFreq_injective h]
  exists_abs_freq_le := ⟨3 / 2, fun l => by
    have := one_lt_heatFreq l.1
    have := heatFreq_le l.1
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith⟩
  summable_norm_coeff := summable_heatCoeff.congr fun l => by
    rw [norm_ofReal, Real.norm_of_nonneg (by positivity)]
  exists_conj l := ⟨(l.1, !l.2), by cases l.2 <;> simp, by simp⟩
  coeff_im_eq_zero l _ := ofReal_im _

/-- The frequencies of `heatInput`. -/
theorem heatInput_freq (l : ℕ × Bool) :
    heatInput.freq l = if l.2 then heatFreq l.1 else -heatFreq l.1 := rfl

/-- The coefficients of `heatInput`. -/
theorem heatInput_coeff (l : ℕ × Bool) :
    heatInput.coeff l = (((2 : ℝ)⁻¹ ^ (l.1 + 2) : ℝ) : Complexification ℝ) := rfl

/-- **The input of `ex:boundary-heat-informative`**:
`ū(t) = ∑ₖ 2^{-(k+1)} cos(heatFreq k · t)`, i.e. the paper's `∑_{k ≥ 1} 2^{-k} cos(ω_k t)`. -/
theorem heatInput_apply (t : ℝ) :
    heatInput t = ∑' k : ℕ, (2 : ℝ)⁻¹ ^ (k + 1) * Real.cos (heatFreq k * t) := by
  set F : ℕ × Bool → ℝ := fun l =>
    Real.cos ((if l.2 then heatFreq l.1 else -heatFreq l.1) * t) * (2 : ℝ)⁻¹ ^ (l.1 + 2)
    with hF
  have hsumm : Summable fun l => Complex.exp (heatInput.freq l * t * Complex.I) •
      heatInput.coeff l :=
    Summable.of_norm (heatInput.summable_norm_coeff.congr fun l => by
      rw [norm_smul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul])
  have h1 : heatInput t = ∑' l, F l := by
    rw [HarmonicSignal.coe_apply, bohrSeries_apply, ← reCLM_apply, reCLM.map_tsum hsumm]
    refine tsum_congr fun l => ?_
    change (Complex.exp (((if l.2 then heatFreq l.1 else -heatFreq l.1 : ℝ) : ℂ) * t *
      Complex.I) • ((((2 : ℝ)⁻¹ ^ (l.1 + 2) : ℝ) : Complexification ℝ))).re = F l
    rw [smul_re, ofReal_re, ofReal_im, smul_zero, sub_zero, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re, smul_eq_mul]
  have hFs : Summable F := by
    refine Summable.of_norm (summable_heatCoeff.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun l => ?_)
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ (l.1 + 2))]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
  rw [h1, hFs.tsum_prod]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [hF, ↓reduceIte, Bool.false_eq_true, neg_mul, Real.cos_neg]
  ring

/-- The input is square integrable on every window (`HarmonicSignal.memLp`). -/
theorem memLp_heatInput (T : ℝ) : MemLp heatInput 2 (μI T) :=
  heatInput.memLp T

/-- **`ū` is harmonically persistently exciting** (`def:harmonic-pe`;
`app:boundary-heat-informative`): the total family is `{1}` in `U_ℂ`, and along `ℓ k = (k, +)`
the coefficients are `2^{-(k+2)} · 1 ≠ 0` and the frequencies `ω_k → 1`. -/
theorem isHarmonicPE_heatInput : heatInput.IsHarmonicPE := by
  have hreal : ∀ r : ℝ,
      ((r : ℝ) : Complexification ℝ) = (r : ℂ) • ((1 : ℝ) : Complexification ℝ) := by
    intro r
    rw [Complex.coe_smul, ← ofReal_smul, smul_eq_mul, mul_one]
  refine ⟨Unit, inferInstance, fun _ => ((1 : ℝ) : Complexification ℝ), ?_, fun _ => ?_⟩
  · -- totality of `{1}` in `U_ℂ`
    rw [eq_top_iff]
    intro z _
    apply Submodule.le_topologicalClosure
    have hmem : ∀ r : ℝ, ((r : ℝ) : Complexification ℝ) ∈
        Submodule.span ℂ (Set.range fun _ : Unit => ((1 : ℝ) : Complexification ℝ)) := by
      intro r
      rw [hreal r]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
    rw [show z = (⟨z.re, z.im⟩ : Complexification ℝ) from rfl, mk_eq_add_I_smul]
    exact add_mem (hmem _) (Submodule.smul_mem _ _ (hmem _))
  · refine ⟨fun k => (k, true), fun k => (((2 : ℝ)⁻¹ ^ (k + 2) : ℝ) : ℂ), 1,
      fun k k' h => congrArg Prod.fst h, fun k => Complex.ofReal_ne_zero.2 (by positivity),
      fun k => ?_, ?_⟩
    · rw [heatInput_coeff]
      exact hreal _
    · simpa [heatInput_freq] using tendsto_heatFreq

/-- The closure of the frequency set `{± ω_k}` lies in `{ω : 1 ≤ |ω| ≤ 3/2}`
(`app:boundary-heat-informative`: `K = i({± ω_k} ∪ {± 1})`). -/
theorem abs_mem_closure_range_freq_heatInput {ω : ℝ}
    (hω : ω ∈ closure (Set.range heatInput.freq)) : 1 ≤ |ω| ∧ |ω| ≤ 3 / 2 := by
  have hS : IsClosed {ω : ℝ | 1 ≤ |ω| ∧ |ω| ≤ 3 / 2} :=
    (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hsub : Set.range heatInput.freq ⊆ {ω : ℝ | 1 ≤ |ω| ∧ |ω| ≤ 3 / 2} := by
    rintro _ ⟨⟨k, b⟩, rfl⟩
    have h1 := one_lt_heatFreq k
    have h2 := heatFreq_le k
    rw [heatInput_freq]
    cases b <;>
      simp only [Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_of_pos (by linarith : (0 : ℝ) < heatFreq k)] <;>
      constructor <;> linarith
  exact closure_minimal hsub hS hω

/-- No frequency in the closure of `{± ω_k}` vanishes, so `K = i · closure {± ω_k}` consists of
nonzero purely imaginary numbers (`app:boundary-heat-informative`). -/
theorem ne_zero_of_mem_closure_range_freq {ω : ℝ}
    (hω : ω ∈ closure (Set.range heatInput.freq)) : ω ≠ 0 := by
  rintro rfl
  have := (abs_mem_closure_range_freq_heatInput hω).1
  norm_num at this

end BoundaryHeat

end DataDrivenControl
