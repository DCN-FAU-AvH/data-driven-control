module

public import Mathlib

/-!
# Hilbert–Schmidt and trace-class operators

Paper: `eq:hilbert-gramian` asserts that the Gramian `𝒢(z) = ∫ z(t) ⊗ z(t) dt` is trace class.
Mathlib v4.35 has neither Hilbert–Schmidt nor trace-class operators, and `CFC.abs` needs a complex
C⋆-algebra, so there is no `|T|` on real Hilbert spaces.  We therefore use **nuclear
representations**; everything is generic over `𝕜` with `[RCLike 𝕜]`.

## Definitions (namespace `DataDrivenControl.TraceClass`)

* `stdHilbertBasis 𝕜 E` (index type `stdHilbertBasisIndex 𝕜 E`): a Hilbert basis of the Hilbert
  space `E`, chosen from `exists_hilbertBasis`;
* `IsHilbertSchmidt T`: `∑ᵢ ‖T eᵢ‖² < ∞` in `stdHilbertBasis`;
* `IsTraceClass T`: `T = ∑ₙ aₙ ⊗ bₙ` (convergence in operator norm) with `∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`,
  where `a ⊗ b = ⟪b, ·⟫ • a = InnerProductSpace.rankOne 𝕜 a b`;
* `trace T = ∑ᵢ ⟪eᵢ, T eᵢ⟫` in `stdHilbertBasis`.

## Main results

* Parseval: `hasSum_norm_inner_sq`, `enorm_sq_eq_tsum` (in `ℝ≥0∞`);
* Hilbert–Schmidt: `tsum_enorm_apply_sq_eq_adjoint` (`∑ᵢ ‖T bᵢ‖² = ∑ⱼ ‖T† cⱼ‖²` in `ℝ≥0∞` for any
  Hilbert bases `b`, `c`), basis independence `isHilbertSchmidt_iff`,
  `IsHilbertSchmidt.adjoint`, `add`, `smul`, `comp_left`;
* trace in every basis and for every representation: `IsTraceClass.hasSum_trace`
  (`∑ᵢ ⟪bᵢ, T bᵢ⟫ = trace T` for **every** Hilbert basis `b`), `trace_eq_tsum_of_hasSum`
  (`trace T = ∑ₙ ⟪bₙ, aₙ⟫` for every nuclear representation, over any index type);
  `isTraceClass_of_hasSum` accepts representations over any index type;
* `IsTraceClass.add`, `.smul`, `.neg`, `.sub`, `.comp_left`, `.adjoint`;
* `isTraceClass_adjoint_comp`: `A† B` is trace class for Hilbert–Schmidt `A, B : E →L[𝕜] F`, and
  `hasSum_inner_trace_adjoint_comp`: `trace (A† B) = ∑ᵢ ⟪A bᵢ, B bᵢ⟫` in every Hilbert basis;
* validation: `trace_rankOne` (`trace (a ⊗ b) = ⟪b, a⟫`), `isTraceClass_of_finiteDimensional` and
  `trace_eq_linearMap_trace` (in finite dimension every operator is trace class and the trace is
  `LinearMap.trace`).

## The textbook definition

The equivalence with the textbook definition through `|T|` (`tr |T| < ∞`), and `tr |T|` as the
nuclear norm, are proved in `Analysis/TraceClassAbs`, with the polar decomposition of
`Analysis/PolarDecomposition`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct ENNReal NNReal ComplexConjugate

noncomputable section

namespace DataDrivenControl

namespace TraceClass

open InnerProductSpace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section Basis

variable (𝕜 E) [CompleteSpace E]

/-- The index set of the chosen Hilbert basis `stdHilbertBasis 𝕜 E`. -/
def stdHilbertBasisIndex : Set E :=
  (exists_hilbertBasis 𝕜 E).choose

/-- A Hilbert basis of `E`, chosen once and for all from `exists_hilbertBasis`. -/
def stdHilbertBasis : HilbertBasis (stdHilbertBasisIndex 𝕜 E) 𝕜 E :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose

end Basis

section Parseval

variable {ι : Type*}

/-- Parseval's identity: `∑ᵢ ‖⟪bᵢ, x⟫‖² = ‖x‖²` for a Hilbert basis `b`. -/
theorem hasSum_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simp only [b.repr_apply_apply, LinearIsometryEquiv.norm_map] at h
  convert h using 2 <;> norm_num

/-- Parseval's identity in `ℝ≥0∞`. -/
theorem enorm_sq_eq_tsum (b : HilbertBasis ι 𝕜 E) (x : E) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by
  have h := hasSum_norm_inner_sq b x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h.summable]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Square summability in `ℝ` and finiteness in `ℝ≥0∞`. -/
theorem summable_norm_sq_iff {X : Type*} [SeminormedAddCommGroup X] (f : ι → X) :
    Summable (fun i => ‖f i‖ ^ 2) ↔ ∑' i, ‖f i‖ₑ ^ 2 ≠ ∞ := by
  have h1 : (fun i => ‖f i‖ₑ ^ 2) = fun i => ((‖f i‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    funext i; simp [enorm_eq_nnnorm]
  rw [h1, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp

/-- The real sum of squares is the `toReal` of the `ℝ≥0∞` sum. -/
theorem tsum_norm_sq_eq_toReal {X : Type*} [SeminormedAddCommGroup X] (f : ι → X) :
    ∑' i, ‖f i‖ ^ 2 = (∑' i, ‖f i‖ₑ ^ 2).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun i => by simp)]
  simp [ENNReal.toReal_pow]

end Parseval

section HilbertSchmidt

variable [CompleteSpace E]

/-- **Hilbert–Schmidt operators**: `∑ᵢ ‖T eᵢ‖² < ∞` in the chosen Hilbert basis `stdHilbertBasis`
(any Hilbert basis gives the same sum, `isHilbertSchmidt_iff`). -/
def IsHilbertSchmidt (T : E →L[𝕜] F) : Prop :=
  Summable fun i => ‖T (stdHilbertBasis 𝕜 E i)‖ ^ 2

/-- Sums of Hilbert–Schmidt operators are Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.add {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) := by
  refine ((Summable.add hS hT).mul_left 2).of_nonneg_of_le (fun _ => by positivity) fun i => ?_
  have h := norm_add_le (S (stdHilbertBasis 𝕜 E i)) (T (stdHilbertBasis 𝕜 E i))
  have h0 := norm_nonneg (S (stdHilbertBasis 𝕜 E i) + T (stdHilbertBasis 𝕜 E i))
  simp only [add_apply]
  nlinarith [sq_nonneg (‖S (stdHilbertBasis 𝕜 E i)‖ - ‖T (stdHilbertBasis 𝕜 E i)‖)]

/-- Scalar multiples of Hilbert–Schmidt operators are Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.smul {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) := by
  have h := hT.mul_left (‖c‖ ^ 2)
  simp only [IsHilbertSchmidt, smul_apply, norm_smul, mul_pow] at h ⊢
  exact h

/-- `S T` is Hilbert–Schmidt if `T` is (left ideal property). -/
theorem IsHilbertSchmidt.comp_left {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) (S : F →L[𝕜] G) :
    IsHilbertSchmidt (S ∘L T) :=
  (hT.mul_left (‖S‖ ^ 2)).of_nonneg_of_le (fun _ => by positivity) fun i => by
    rw [comp_apply, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.le_opNorm _) 2

variable [CompleteSpace F]

variable {ι κ : Type*}

/-- `∑ᵢ ‖T bᵢ‖² = ∑ⱼ ‖T† cⱼ‖²` in `ℝ≥0∞`, for Hilbert bases `b` of `E` and `c` of `F`. -/
theorem tsum_enorm_apply_sq_eq_adjoint (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (T : E →L[𝕜] F) :
    ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' j, ‖adjoint T (c j)‖ₑ ^ 2 := by
  calc ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
        simp_rw [enorm_sq_eq_tsum c]
    _ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ‖⟪b i, adjoint T (c j)⟫_𝕜‖ₑ ^ 2 := by
        congr 1 with j
        congr 1 with i
        rw [adjoint_inner_right, ← inner_conj_symm, enorm_eq_nnnorm, enorm_eq_nnnorm,
          RCLike.nnnorm_conj]
    _ = ∑' j, ‖adjoint T (c j)‖ₑ ^ 2 := by
        simp_rw [← enorm_sq_eq_tsum b]

/-- The Hilbert–Schmidt sum does not depend on the Hilbert basis (in `ℝ≥0∞`). -/
theorem tsum_enorm_apply_sq_eq (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis κ 𝕜 E)
    (T : E →L[𝕜] F) :
    ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' i, ‖T (b' i)‖ₑ ^ 2 := by
  rw [tsum_enorm_apply_sq_eq_adjoint b (stdHilbertBasis 𝕜 F),
    tsum_enorm_apply_sq_eq_adjoint b' (stdHilbertBasis 𝕜 F)]

/-- Hilbert–Schmidt in terms of an arbitrary Hilbert basis. -/
theorem isHilbertSchmidt_iff (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] F} :
    IsHilbertSchmidt T ↔ Summable fun i => ‖T (b i)‖ ^ 2 := by
  rw [IsHilbertSchmidt, summable_norm_sq_iff, summable_norm_sq_iff,
    tsum_enorm_apply_sq_eq (stdHilbertBasis 𝕜 E) b]

/-- Hilbert–Schmidt in terms of the `ℝ≥0∞` sum in an arbitrary Hilbert basis. -/
theorem isHilbertSchmidt_iff_tsum_ne_top (b : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] F} :
    IsHilbertSchmidt T ↔ ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by
  rw [isHilbertSchmidt_iff b, summable_norm_sq_iff]

/-- `T` is Hilbert–Schmidt iff `T†` is. -/
theorem isHilbertSchmidt_adjoint_iff {T : E →L[𝕜] F} :
    IsHilbertSchmidt (adjoint T) ↔ IsHilbertSchmidt T := by
  rw [isHilbertSchmidt_iff_tsum_ne_top (stdHilbertBasis 𝕜 F),
    isHilbertSchmidt_iff_tsum_ne_top (stdHilbertBasis 𝕜 E),
    tsum_enorm_apply_sq_eq_adjoint (stdHilbertBasis 𝕜 E) (stdHilbertBasis 𝕜 F)]

/-- The adjoint of a Hilbert–Schmidt operator is Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.adjoint {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (ContinuousLinearMap.adjoint T) :=
  isHilbertSchmidt_adjoint_iff.2 hT

end HilbertSchmidt

/-- Cauchy–Schwarz in a Hilbert basis: `∑ᵢ ‖⟪eᵢ, x⟫‖ ‖⟪eᵢ, y⟫‖ ≤ ‖x‖ ‖y‖` (and the series
converges). -/
theorem summable_and_tsum_norm_inner_mul_le {ι : Type*} (e : HilbertBasis ι 𝕜 E) (x y : E) :
    Summable (fun i => ‖⟪e i, x⟫_𝕜‖ * ‖⟪e i, y⟫_𝕜‖) ∧
      ∑' i, ‖⟪e i, x⟫_𝕜‖ * ‖⟪e i, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ := by
  set u := lp.toNorm (e.repr x)
  set v := lp.toNorm (e.repr y)
  have h := lp.hasSum_inner (𝕜 := ℝ) u v
  have huv : ∀ i, inner ℝ (u i) (v i) = ‖⟪e i, x⟫_𝕜‖ * ‖⟪e i, y⟫_𝕜‖ := by
    intro i
    simp [u, v, lp.toNorm, e.repr_apply_apply, mul_comm]
  simp_rw [huv] at h
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq]
  calc inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
    _ = ‖x‖ * ‖y‖ := by simp [u, v, lp.norm_toNorm]

section TraceClassDef

/-- **Trace class** (`eq:hilbert-gramian`): `T = ∑ₙ aₙ ⊗ bₙ` with
`∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`, where `a ⊗ b = ⟪b, ·⟫ • a = rankOne 𝕜 a b` (a *nuclear representation*). -/
def IsTraceClass (T : E →L[𝕜] E) : Prop :=
  ∃ a b : ℕ → E, Summable (fun n => ‖a n‖ * ‖b n‖) ∧
    HasSum (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) T

variable [CompleteSpace E]

/-- The **trace** `∑ᵢ ⟪eᵢ, T eᵢ⟫` in the chosen Hilbert basis `stdHilbertBasis`.  For trace-class
`T` the series converges in every Hilbert basis to the same value (`IsTraceClass.hasSum_trace`). -/
def trace (T : E →L[𝕜] E) : 𝕜 :=
  ∑' i, ⟪stdHilbertBasis 𝕜 E i, T (stdHilbertBasis 𝕜 E i)⟫_𝕜

end TraceClassDef

variable {ι κ : Type*}

/-- The diagonal sum of a nuclear representation in a Hilbert basis: if `T = ∑ₙ aₙ ⊗ bₙ` with
`∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`, then `∑ᵢ ⟪eᵢ, T eᵢ⟫ = ∑ₙ ⟪bₙ, aₙ⟫` in every Hilbert basis `e`. -/
theorem hasSum_inner_apply_of_hasSum (e : HilbertBasis ι 𝕜 E) {T : E →L[𝕜] E} {a b : κ → E}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (hT : HasSum (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) T) :
    HasSum (fun i => ⟪e i, T (e i)⟫_𝕜) (∑' n, ⟪b n, a n⟫_𝕜) := by
  set G : κ × ι → 𝕜 := fun p => ⟪b p.1, e p.2⟫_𝕜 * ⟪e p.2, a p.1⟫_𝕜 with hG
  have hnorm : ∀ p, ‖G p‖ = ‖⟪e p.2, b p.1⟫_𝕜‖ * ‖⟪e p.2, a p.1⟫_𝕜‖ := by
    intro p
    rw [hG, norm_mul, norm_inner_symm]
  have hrow : ∀ n, Summable (fun i => ‖G (n, i)‖) ∧ ∑' i, ‖G (n, i)‖ ≤ ‖a n‖ * ‖b n‖ := by
    intro n
    simp_rw [hnorm]
    obtain ⟨h1, h2⟩ := summable_and_tsum_norm_inner_mul_le e (b n) (a n)
    exact ⟨h1, h2.trans_eq (mul_comm _ _)⟩
  have hGn : Summable fun p => ‖G p‖ := by
    refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).2 ⟨fun n => (hrow n).1, ?_⟩
    exact hs.of_nonneg_of_le (fun n => tsum_nonneg fun i => norm_nonneg _) (fun n => (hrow n).2)
  have hGs : Summable G := hGn.of_norm
  have hrowsum : ∀ n, HasSum (fun i => G (n, i)) ⟪b n, a n⟫_𝕜 := fun n =>
    e.hasSum_inner_mul_inner (b n) (a n)
  have htot : ∑' p, G p = ∑' n, ⟪b n, a n⟫_𝕜 := by
    rw [hGs.tsum_prod]
    exact tsum_congr fun n => (hrowsum n).tsum_eq
  have hswap : HasSum (G ∘ Prod.swap) (∑' n, ⟪b n, a n⟫_𝕜) := by
    rw [← htot]
    exact (Equiv.prodComm ι κ).hasSum_iff.2 hGs.hasSum
  refine hswap.prod_fiberwise fun i => ?_
  have h := hT.mapL ((innerSL 𝕜 (e i)).comp (ContinuousLinearMap.apply 𝕜 E (e i)))
  simpa [G, inner_smul_right] using h

section Complete

variable [CompleteSpace E]

/-- The trace of an operator with a nuclear representation is `∑ₙ ⟪bₙ, aₙ⟫`. -/
theorem trace_eq_tsum_of_hasSum {T : E →L[𝕜] E} {a b : κ → E}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (hT : HasSum (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) T) :
    trace T = ∑' n, ⟪b n, a n⟫_𝕜 :=
  (hasSum_inner_apply_of_hasSum (stdHilbertBasis 𝕜 E) hs hT).tsum_eq

/-- The trace of a trace-class operator is `∑ᵢ ⟪eᵢ, T eᵢ⟫` in **every** Hilbert basis `e`. -/
theorem IsTraceClass.hasSum_trace {T : E →L[𝕜] E} (hT : IsTraceClass T)
    (e : HilbertBasis ι 𝕜 E) : HasSum (fun i => ⟪e i, T (e i)⟫_𝕜) (trace T) := by
  obtain ⟨a, b, hs, h⟩ := hT
  rw [trace_eq_tsum_of_hasSum hs h]
  exact hasSum_inner_apply_of_hasSum e hs h

end Complete

/-- A summable nuclear representation over any index type gives a trace-class operator. -/
theorem isTraceClass_of_hasSum {T : E →L[𝕜] E} {a b : κ → E}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (hT : HasSum (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) T) : IsTraceClass T := by
  set s := Function.support fun n => ‖a n‖ * ‖b n‖
  have hsc : s.Countable := hs.countable_support
  have : Countable s := hsc.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat s
  set a' : ℕ → E := Function.extend f (fun x : s => a x) 0
  set b' : ℕ → E := Function.extend f (fun x : s => b x) 0
  have ha' : ∀ x : s, a' (f x) = a x := fun x => hf.extend_apply _ _ x
  have hb' : ∀ x : s, b' (f x) = b x := fun x => hf.extend_apply _ _ x
  have ha0 : ∀ n ∉ range f, a' n = 0 := fun n hn => by
    simp only [a']
    rw [Function.extend_apply' _ _ _ (by simpa using hn)]
    rfl
  have hsupp : Function.support (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) ⊆ s := by
    intro n hn
    simp only [Function.mem_support, ne_eq, InnerProductSpace.rankOne_eq_zero, not_or] at hn
    simp [s, hn.1, hn.2]
  refine ⟨a', b', ?_, ?_⟩
  · refine (hf.summable_iff fun n hn => by simp [ha0 n hn]).1 ?_
    have : (fun n => ‖a' n‖ * ‖b' n‖) ∘ f = (fun n => ‖a n‖ * ‖b n‖) ∘ Subtype.val := by
      funext x; simp [ha', hb']
    rw [this]
    exact hs.subtype _
  · refine (hf.hasSum_iff fun n hn => by simp [ha0 n hn]).1 ?_
    have : (fun n => InnerProductSpace.rankOne 𝕜 (a' n) (b' n)) ∘ f =
        (fun n => InnerProductSpace.rankOne 𝕜 (a n) (b n)) ∘ Subtype.val := by
      funext x; simp [ha', hb']
    rw [this]
    exact (hasSum_subtype_iff_of_support_subset hsupp).2 hT

section Operations

/-- Sums of trace-class operators are trace class. -/
theorem IsTraceClass.add {S T : E →L[𝕜] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  obtain ⟨a, b, hs, h⟩ := hS
  obtain ⟨a', b', hs', h'⟩ := hT
  exact isTraceClass_of_hasSum (a := Sum.elim a a') (b := Sum.elim b b')
    (Summable.sum _ hs hs') (HasSum.sum h h')

/-- Scalar multiples of trace-class operators are trace class. -/
theorem IsTraceClass.smul {T : E →L[𝕜] E} (hT : IsTraceClass T) (c : 𝕜) :
    IsTraceClass (c • T) := by
  obtain ⟨a, b, hs, h⟩ := hT
  refine ⟨fun n => c • a n, b, ?_, ?_⟩
  · simpa [norm_smul, mul_assoc] using hs.mul_left ‖c‖
  · have : ∀ n, rankOne 𝕜 (c • a n) (b n) = c • rankOne 𝕜 (a n) (b n) := fun n => by
      ext x
      simp only [rankOne_apply, smul_apply]
      rw [smul_comm]
    simpa only [this] using h.const_smul c

/-- Negatives of trace-class operators are trace class. -/
theorem IsTraceClass.neg {T : E →L[𝕜] E} (hT : IsTraceClass T) : IsTraceClass (-T) := by
  simpa using hT.smul (-1)

/-- Differences of trace-class operators are trace class. -/
theorem IsTraceClass.sub {S T : E →L[𝕜] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S - T) := by
  simpa [sub_eq_add_neg] using hS.add hT.neg

private theorem hasSum_comp_left {T : E →L[𝕜] E} {a b : ℕ → E}
    (h : HasSum (fun n => rankOne 𝕜 (a n) (b n)) T) (S : E →L[𝕜] E) :
    HasSum (fun n => rankOne 𝕜 (S (a n)) (b n)) (S ∘L T) := by
  simpa [comp_rankOne] using h.mapL (compL 𝕜 E E E S)

private theorem summable_comp_left {a b : ℕ → E} (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (S : E →L[𝕜] E) : Summable fun n => ‖S (a n)‖ * ‖b n‖ := by
  refine (hs.mul_left ‖S‖).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (S.le_opNorm _) (norm_nonneg _)

/-- `S T` is trace class if `T` is (left ideal property). -/
theorem IsTraceClass.comp_left {T : E →L[𝕜] E} (hT : IsTraceClass T) (S : E →L[𝕜] E) :
    IsTraceClass (S ∘L T) := by
  obtain ⟨a, b, hs, h⟩ := hT
  exact isTraceClass_of_hasSum (summable_comp_left hs S) (hasSum_comp_left h S)

variable [CompleteSpace E]

/-- The adjoint of a trace-class operator is trace class: `(∑ aₙ ⊗ bₙ)† = ∑ bₙ ⊗ aₙ`. -/
theorem IsTraceClass.adjoint {T : E →L[𝕜] E} (hT : IsTraceClass T) :
    IsTraceClass (ContinuousLinearMap.adjoint T) := by
  obtain ⟨a, b, hs, h⟩ := hT
  refine ⟨b, a, by simpa [mul_comm] using hs, ?_⟩
  simpa [Function.comp_def] using
    h.map (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := E) (F := E))
      (LinearIsometryEquiv.continuous _)

/-- `trace 0 = 0`. -/
@[simp] theorem trace_zero : trace (0 : E →L[𝕜] E) = 0 := by
  simp [trace]

/-- Validation: `trace (a ⊗ b) = ⟪b, a⟫`. -/
theorem trace_rankOne (x y : E) : trace (rankOne 𝕜 x y) = ⟪y, x⟫_𝕜 := by
  simp only [trace, rankOne_apply, inner_smul_right]
  exact (stdHilbertBasis 𝕜 E).tsum_inner_mul_inner y x

end Operations

section Compact

end Compact

section FiniteDimensional

/-- Validation: in finite dimension every operator is trace class. -/
theorem isTraceClass_of_finiteDimensional [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    IsTraceClass T := by
  set e := stdOrthonormalBasis 𝕜 E
  have hT : ∑ i, rankOne 𝕜 (T (e i)) (e i) = T := by
    ext x
    simp only [sum_apply, rankOne_apply]
    conv_rhs => rw [← e.sum_repr' x]
    simp [map_sum, map_smul]
  have h := hasSum_fintype fun i => rankOne 𝕜 (T (e i)) (e i)
  rw [hT] at h
  exact isTraceClass_of_hasSum (a := fun i => T (e i)) (b := fun i => e i) Summable.of_finite h

/-- Validation: in finite dimension the trace is `LinearMap.trace`.  (`[CompleteSpace E]` holds
by `FiniteDimensional.complete`; it is needed to state `trace`.) -/
theorem trace_eq_linearMap_trace [FiniteDimensional 𝕜 E] [CompleteSpace E] (T : E →L[𝕜] E) :
    trace T = LinearMap.trace 𝕜 E T := by
  set e := stdOrthonormalBasis 𝕜 E
  have h := (isTraceClass_of_finiteDimensional T).hasSum_trace e.toHilbertBasis
  simp only [OrthonormalBasis.coe_toHilbertBasis] at h
  rw [LinearMap.trace_eq_sum_inner _ e, h.unique (hasSum_fintype _)]
  rfl

end FiniteDimensional

section HilbertSchmidtProduct

variable [CompleteSpace E] [CompleteSpace F] {ι : Type*}

/-- `A† B` is trace class for Hilbert–Schmidt `A, B : E → F`: `A† B = ∑ⱼ A† fⱼ ⊗ B† fⱼ` in a
Hilbert basis `f` of `F`, and `∑ⱼ ‖A† fⱼ‖ ‖B† fⱼ‖ ≤ ∑ⱼ ‖A† fⱼ‖² + ‖B† fⱼ‖² < ∞`. -/
theorem isTraceClass_adjoint_comp {A B : E →L[𝕜] F} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : IsTraceClass (adjoint A ∘L B) := by
  set c := stdHilbertBasis 𝕜 F
  have hA' : Summable fun j => ‖adjoint A (c j)‖ ^ 2 := hA.adjoint
  have hB' : Summable fun j => ‖adjoint B (c j)‖ ^ 2 := hB.adjoint
  have hs : Summable fun j => ‖adjoint A (c j)‖ * ‖adjoint B (c j)‖ :=
    (Summable.add hA' hB').of_nonneg_of_le (fun j => by positivity) fun j => by
      nlinarith [sq_nonneg (‖adjoint A (c j)‖ - ‖adjoint B (c j)‖),
        norm_nonneg (adjoint A (c j)), norm_nonneg (adjoint B (c j))]
  have hsum : Summable fun j => rankOne 𝕜 (adjoint A (c j)) (adjoint B (c j)) :=
    Summable.of_norm (by simpa using hs)
  refine isTraceClass_of_hasSum hs ?_
  convert hsum.hasSum using 1
  ext x
  have h1 := hsum.hasSum.mapL (ContinuousLinearMap.apply 𝕜 E x)
  have h2 : HasSum (fun j => rankOne 𝕜 (adjoint A (c j)) (adjoint B (c j)) x)
      (adjoint A (B x)) := by
    have := (c.hasSum_repr (B x)).mapL (adjoint A)
    convert this using 1
    funext j
    simp [c.repr_apply_apply, adjoint_inner_left]
  simpa using h2.unique h1

/-- The trace of `A† B` for Hilbert–Schmidt `A, B`: `∑ᵢ ⟪A eᵢ, B eᵢ⟫` in every Hilbert basis. -/
theorem hasSum_inner_trace_adjoint_comp {A B : E →L[𝕜] F} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) (b : HilbertBasis ι 𝕜 E) :
    HasSum (fun i => ⟪A (b i), B (b i)⟫_𝕜) (trace (adjoint A ∘L B)) := by
  simpa [adjoint_inner_right] using (isTraceClass_adjoint_comp hA hB).hasSum_trace b

end HilbertSchmidtProduct

end TraceClass

end DataDrivenControl
