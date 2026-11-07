module

public import Mathlib
public import DataDrivenControl.Analysis.TraceClass
public import DataDrivenControl.Analysis.PolarDecomposition
public import DataDrivenControl.Signal.GramianTrace

/-!
# The trace class through `|T|`

Paper: `eq:hilbert-gramian` asserts that the Gramian is trace class.  `Analysis/TraceClass`
defines `TraceClass.IsTraceClass` by nuclear representations `T = ∑ₙ aₙ ⊗ bₙ`,
`∑ₙ ‖aₙ‖ ‖bₙ‖ < ∞`.  This file proves that it is the textbook definition `tr |T| < ∞`, on complex
Hilbert spaces with `|T| = CFC.abs T` and on real Hilbert spaces (the paper's setting) with
`|T| = TraceClass.realAbs T`, both from `Analysis/PolarDecomposition`.

## Main results (namespace `DataDrivenControl.TraceClass`)

* The generic core, for `T = U P`, `U† T = P` (a polar decomposition) and `Q† Q = P`:
  `isTraceClass_iff_of_polar` (`T` is trace class iff `P` is), `isTraceClass_of_summable_re_inner`
  (a summable diagonal of `P = Q† Q` makes `Q` Hilbert–Schmidt and `P` trace class),
  `IsTraceClass.hasSum_re_inner`, `norm_trace_le_of_polar` (`‖tr P‖ ≤ ∑ₙ ‖aₙ‖ ‖bₙ‖` for every
  nuclear representation of `T`, if `‖U‖ ≤ 1`), and `isLeast_nuclearSums_of_polar` (if moreover
  `P = Q²` with `Q` self-adjoint, `re (tr P)` is the least `∑ₙ ‖aₙ‖ ‖bₙ‖`, attained by
  `T = ∑ⱼ U Q fⱼ ⊗ Q fⱼ`, `hasSum_rankOne_of_polar`).  `nuclearSums T` is the set of the values
  `∑ₙ ‖aₙ‖ ‖bₙ‖` of the nuclear representations of `T`; `tsum_mem_nuclearSums` reindexes a
  representation over any index type to `ℕ`.
* Complex Hilbert spaces, `|T| = CFC.abs T`: `isTraceClass_iff_summable_cfcAbs`
  (`IsTraceClass T ↔ ∑ᵢ re ⟪bᵢ, |T| bᵢ⟫ < ∞`, in **every** Hilbert basis `b`; the terms are
  nonnegative, `re_inner_cfcAbs_nonneg`), `isTraceClass_iff_isTraceClass_cfcAbs`,
  `IsTraceClass.hasSum_re_inner_cfcAbs`, `norm_trace_cfcAbs_le` (`‖tr |T|‖ ≤ ∑ₙ ‖aₙ‖ ‖bₙ‖`),
  `isLeast_nuclearSums_cfcAbs` (the nuclear norm of `T` is `tr |T|`).
* Real Hilbert spaces (the paper's setting), `|T| = realAbs T`:
  `isTraceClass_iff_summable_realAbs`, `isTraceClass_iff_isTraceClass_realAbs`,
  `IsTraceClass.hasSum_inner_realAbs`, `inner_realAbs_nonneg`, `trace_realAbs_le`,
  `isLeast_nuclearSums_realAbs`.
* Complexification: `complexifyHilbertBasis` (a real Hilbert basis is a Hilbert basis of `X_ℂ`),
  `isTraceClass_complexify_iff` (`T_ℂ` is trace class iff `T` is), `trace_complexify`
  (`tr T_ℂ = tr T`).
* The Gramian (`eq:hilbert-gramian`): `cfcAbs_gramian`, `realAbs_gramian` (`|𝒢(z)| = 𝒢(z)`), so
  the equivalence specialises to `hasSum_re_inner_gramian`: `hasSum_inner_realAbs_gramian`,
  `hasSum_re_inner_cfcAbs_gramian`.

## Deviations

* `nuclearSums T` uses representations indexed by `ℕ`, as `IsTraceClass` does; the nuclear norm
  is stated as `IsLeast (nuclearSums T) (tr |T|)`, without a separate definition.
* The complex statements are about `CFC.abs`, which Lean cannot elaborate on
  `Complexification X` (see `Analysis/PolarDecomposition`); there `|T_ℂ|` is
  `sqrtOp (T_ℂ† T_ℂ)` (`cfcAbs_eq_sqrtOp`), and the proof of `isTraceClass_complexify_iff`
  instantiates the complex statements at `E = Complexification X`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace DataDrivenControl

namespace TraceClass

open InnerProductSpace ContinuousLinearMap

/-! ### The generic core -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {ι κ : Type*}

/-- `‖Q x‖² = re ⟪x, P x⟫` if `Q† Q = P`. -/
theorem norm_sq_eq_re_inner_of_adjoint_comp {P Q : E →L[𝕜] E} (hQ : adjoint Q ∘L Q = P)
    (x : E) : ‖Q x‖ ^ 2 = RCLike.re ⟪x, P x⟫_𝕜 := by
  rw [← hQ, comp_apply, adjoint_inner_right, inner_self_eq_norm_sq]

/-- If `P = Q† Q` and the diagonal `∑ᵢ re ⟪bᵢ, P bᵢ⟫` converges in one Hilbert basis `b`, then
`Q` is Hilbert–Schmidt and `P` is trace class. -/
theorem isTraceClass_of_summable_re_inner {P Q : E →L[𝕜] E} (hQ : adjoint Q ∘L Q = P)
    (b : HilbertBasis ι 𝕜 E) (h : Summable fun i => RCLike.re ⟪b i, P (b i)⟫_𝕜) :
    IsTraceClass P := by
  have hHS : IsHilbertSchmidt Q := by
    rw [isHilbertSchmidt_iff b]
    simpa only [norm_sq_eq_re_inner_of_adjoint_comp hQ] using h
  rw [← hQ]
  exact isTraceClass_adjoint_comp hHS hHS

/-- The real part of the trace in every Hilbert basis. -/
theorem IsTraceClass.hasSum_re_inner {P : E →L[𝕜] E} (hP : IsTraceClass P)
    (b : HilbertBasis ι 𝕜 E) :
    HasSum (fun i => RCLike.re ⟪b i, P (b i)⟫_𝕜) (RCLike.re (trace P)) := by
  simpa using (hP.hasSum_trace b).mapL RCLike.reCLM

/-- The trace of a positive trace-class operator has a nonnegative real part. -/
theorem IsTraceClass.re_trace_nonneg {P : E →L[𝕜] E} (hP : IsTraceClass P)
    (hpos : P.IsPositive) : 0 ≤ RCLike.re (trace P) :=
  (hP.hasSum_re_inner (stdHilbertBasis 𝕜 E)).nonneg fun _ => hpos.re_inner_nonneg_right _

/-- If `T = U P` and `U† T = P` (a polar decomposition), then `T` is trace class iff `P` is. -/
theorem isTraceClass_iff_of_polar {T P U : E →L[𝕜] E} (h1 : U ∘L P = T)
    (h2 : adjoint U ∘L T = P) : IsTraceClass T ↔ IsTraceClass P :=
  ⟨fun hT => h2 ▸ hT.comp_left _, fun hP => h1 ▸ hP.comp_left _⟩

/-- If `U† T = P` with `‖U‖ ≤ 1`, then `‖tr P‖ ≤ ∑ₙ ‖aₙ‖ ‖bₙ‖` for every nuclear
representation `T = ∑ₙ aₙ ⊗ bₙ`: `tr P = tr (U† T) = ∑ₙ ⟪bₙ, U† aₙ⟫`. -/
theorem norm_trace_le_of_polar {T P U : E →L[𝕜] E} (hU : ‖U‖ ≤ 1) (h2 : adjoint U ∘L T = P)
    {a b : κ → E} (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (hT : HasSum (fun n => rankOne 𝕜 (a n) (b n)) T) :
    ‖trace P‖ ≤ ∑' n, ‖a n‖ * ‖b n‖ := by
  have hUa : ∀ x, ‖adjoint U x‖ ≤ ‖x‖ := fun x => by
    refine ((adjoint U).le_opNorm x).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    exact (mul_le_of_le_one_left (norm_nonneg _) hU)
  have hs' : Summable fun n => ‖adjoint U (a n)‖ * ‖b n‖ :=
    hs.of_nonneg_of_le (fun n => by positivity) fun n =>
      mul_le_mul_of_nonneg_right (hUa _) (norm_nonneg _)
  have hT' : HasSum (fun n => rankOne 𝕜 (adjoint U (a n)) (b n)) (adjoint U ∘L T) := by
    simpa [comp_rankOne] using hT.mapL (compL 𝕜 E E E (adjoint U))
  have hle : ∀ n, ‖⟪b n, adjoint U (a n)⟫_𝕜‖ ≤ ‖a n‖ * ‖b n‖ := fun n =>
    calc ‖⟪b n, adjoint U (a n)⟫_𝕜‖ ≤ ‖b n‖ * ‖adjoint U (a n)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b n‖ * ‖a n‖ := mul_le_mul_of_nonneg_left (hUa _) (norm_nonneg _)
      _ = ‖a n‖ * ‖b n‖ := mul_comm _ _
  have hsn : Summable fun n => ‖⟪b n, adjoint U (a n)⟫_𝕜‖ :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  rw [← h2, trace_eq_tsum_of_hasSum hs' hT']
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hle hs)

/-- The values `∑ₙ ‖aₙ‖ ‖bₙ‖` of the nuclear representations `T = ∑ₙ aₙ ⊗ bₙ` (indexed by `ℕ`,
as in `IsTraceClass`).  `IsTraceClass T` says that this set is nonempty; its infimum is the
nuclear norm of `T`. -/
def nuclearSums (T : E →L[𝕜] E) : Set ℝ :=
  {s | ∃ a b : ℕ → E, Summable (fun n => ‖a n‖ * ‖b n‖) ∧
    HasSum (fun n => rankOne 𝕜 (a n) (b n)) T ∧ s = ∑' n, ‖a n‖ * ‖b n‖}

omit [CompleteSpace E] in
/-- A summable nuclear representation over any index type can be reindexed over `ℕ` with the same
sum `∑ ‖aₙ‖ ‖bₙ‖` (the refinement of `isTraceClass_of_hasSum` that keeps track of the sum). -/
theorem tsum_mem_nuclearSums {T : E →L[𝕜] E} {a b : κ → E}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖)
    (hT : HasSum (fun n => rankOne 𝕜 (a n) (b n)) T) :
    ∑' n, ‖a n‖ * ‖b n‖ ∈ nuclearSums T := by
  set s := Function.support fun n => ‖a n‖ * ‖b n‖
  have : Countable s := hs.countable_support.to_subtype
  obtain ⟨f, hf⟩ := exists_injective_nat s
  set a' : ℕ → E := Function.extend f (fun x : s => a x) 0
  set b' : ℕ → E := Function.extend f (fun x : s => b x) 0
  have ha' : ∀ x : s, a' (f x) = a x := fun x => hf.extend_apply _ _ x
  have hb' : ∀ x : s, b' (f x) = b x := fun x => hf.extend_apply _ _ x
  have ha0 : ∀ n ∉ Set.range f, a' n = 0 := fun n hn => by
    simp only [a']
    rw [Function.extend_apply' _ _ _ (by simpa using hn)]
    rfl
  have hzero : ∀ n ∉ Set.range f, ‖a' n‖ * ‖b' n‖ = 0 := fun n hn => by simp [ha0 n hn]
  have hcomp : (fun n => ‖a' n‖ * ‖b' n‖) ∘ f = (fun n => ‖a n‖ * ‖b n‖) ∘ Subtype.val := by
    funext x
    simp [ha', hb']
  have hsupp : Function.support (fun n => rankOne 𝕜 (a n) (b n)) ⊆ s := by
    intro n hn
    simp only [Function.mem_support, ne_eq, rankOne_eq_zero, not_or] at hn
    simp [s, hn.1, hn.2]
  refine ⟨a', b', ?_, ?_, ?_⟩
  · refine (hf.summable_iff hzero).1 ?_
    rw [hcomp]
    exact hs.subtype _
  · refine (hf.hasSum_iff fun n hn => by simp [ha0 n hn]).1 ?_
    have : (fun n => rankOne 𝕜 (a' n) (b' n)) ∘ f =
        (fun n => rankOne 𝕜 (a n) (b n)) ∘ Subtype.val := by
      funext x
      simp [ha', hb']
    rw [this]
    exact (hasSum_subtype_iff_of_support_subset hsupp).2 hT
  · have h1 : ∑' x : s, ‖a' (f x)‖ * ‖b' (f x)‖ = ∑' n, ‖a' n‖ * ‖b' n‖ :=
      hf.tsum_eq (f := fun n => ‖a' n‖ * ‖b' n‖) fun n hn => by
        by_contra h
        exact hn (hzero n h)
    have h2 : ∑' x : s, ‖a x‖ * ‖b x‖ = ∑' n, ‖a n‖ * ‖b n‖ :=
      tsum_subtype_eq_of_support_subset subset_rfl
    rw [← h1, ← h2]
    simp [ha', hb']

/-- If `T = U Q²` with `Q` self-adjoint and Hilbert–Schmidt and `‖U‖ ≤ 1`, then in every Hilbert
basis `f`, `T = ∑ⱼ U Q fⱼ ⊗ Q fⱼ`, with `∑ⱼ ‖U Q fⱼ‖ ‖Q fⱼ‖ ≤ ∑ⱼ ‖Q fⱼ‖²`. -/
theorem hasSum_rankOne_of_polar {T U Q : E →L[𝕜] E} (hU : ‖U‖ ≤ 1) (hQ : adjoint Q = Q)
    (hT : U ∘L (Q ∘L Q) = T) (f : HilbertBasis ι 𝕜 E) (hs : Summable fun j => ‖Q (f j)‖ ^ 2) :
    Summable (fun j => ‖U (Q (f j))‖ * ‖Q (f j)‖) ∧
      HasSum (fun j => rankOne 𝕜 (U (Q (f j))) (Q (f j))) T ∧
      ∑' j, ‖U (Q (f j))‖ * ‖Q (f j)‖ ≤ ∑' j, ‖Q (f j)‖ ^ 2 := by
  have hUx : ∀ y, ‖U y‖ ≤ ‖y‖ := fun y =>
    (U.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) hU)
  have hle : ∀ j, ‖U (Q (f j))‖ * ‖Q (f j)‖ ≤ ‖Q (f j)‖ ^ 2 := fun j => by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hUx _) (norm_nonneg _)
  have hs' : Summable fun j => ‖U (Q (f j))‖ * ‖Q (f j)‖ :=
    hs.of_nonneg_of_le (fun j => by positivity) hle
  have hsum : Summable fun j => rankOne 𝕜 (U (Q (f j))) (Q (f j)) :=
    Summable.of_norm (by simpa using hs')
  refine ⟨hs', ?_, hs'.tsum_le_tsum hle hs⟩
  convert hsum.hasSum using 1
  ext x
  have h1 := hsum.hasSum.mapL (ContinuousLinearMap.apply 𝕜 E x)
  have h2 : HasSum (fun j => rankOne 𝕜 (U (Q (f j))) (Q (f j)) x) (T x) := by
    have h3 := (f.hasSum_repr (Q x)).mapL (U ∘L Q)
    rw [← hT]
    convert h3 using 1
    · funext j
      have hinner : ⟪Q (f j), x⟫_𝕜 = ⟪f j, Q x⟫_𝕜 := by
        rw [← adjoint_inner_left, hQ]
      simp [f.repr_apply_apply, rankOne_apply, hinner]
    · rfl
  simpa using h2.unique h1

/-- **The nuclear norm is `tr P`**: if `T = U P`, `U† T = P`, `‖U‖ ≤ 1` (a polar decomposition)
and `P = Q²` with `Q` self-adjoint, then for trace-class `T` the least value of `∑ₙ ‖aₙ‖ ‖bₙ‖`
over all nuclear representations `T = ∑ₙ aₙ ⊗ bₙ` is `re (tr P)`, and it is attained. -/
theorem isLeast_nuclearSums_of_polar {T P U Q : E →L[𝕜] E} (hU : ‖U‖ ≤ 1) (h1 : U ∘L P = T)
    (h2 : adjoint U ∘L T = P) (hQ : adjoint Q = Q) (hQP : Q ∘L Q = P) (hT : IsTraceClass T) :
    IsLeast (nuclearSums T) (RCLike.re (trace P)) := by
  have hP : IsTraceClass P := (isTraceClass_iff_of_polar h1 h2).1 hT
  set f := stdHilbertBasis 𝕜 E
  have hdiag : HasSum (fun j => ‖Q (f j)‖ ^ 2) (RCLike.re (trace P)) := by
    have hQP' : adjoint Q ∘L Q = P := by rw [hQ, hQP]
    simpa only [norm_sq_eq_re_inner_of_adjoint_comp hQP'] using hP.hasSum_re_inner f
  obtain ⟨hs, hsum, hle⟩ := hasSum_rankOne_of_polar hU hQ (by rw [hQP, h1]) f hdiag.summable
  have hlow : ∀ s ∈ nuclearSums T, RCLike.re (trace P) ≤ s := by
    rintro s ⟨a, b, hab, hTab, rfl⟩
    exact (RCLike.re_le_norm _).trans (norm_trace_le_of_polar hU h2 hab hTab)
  have hmem := tsum_mem_nuclearSums hs hsum
  have heq : ∑' j, ‖U (Q (f j))‖ * ‖Q (f j)‖ = RCLike.re (trace P) :=
    le_antisymm (hle.trans_eq hdiag.tsum_eq) (hlow _ hmem)
  rw [heq] at hmem
  exact ⟨hmem, hlow⟩

end Generic

/-! ### Complex Hilbert spaces -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι κ : Type*}

/-- The diagonal entries `re ⟪x, |T| x⟫` are nonnegative. -/
theorem re_inner_cfcAbs_nonneg (T : E →L[ℂ] E) (x : E) :
    0 ≤ RCLike.re ⟪x, CFC.abs T x⟫_ℂ :=
  (isPositive_cfcAbs T).re_inner_nonneg_right x

/-- `T` is trace class iff `|T|` is. -/
theorem isTraceClass_iff_isTraceClass_cfcAbs (T : E →L[ℂ] E) :
    IsTraceClass T ↔ IsTraceClass (CFC.abs T) :=
  isTraceClass_iff_of_polar (polar_decomposition_cfcAbs T).1 (polar_decomposition_cfcAbs T).2.1

/-- **The trace class is `tr |T| < ∞`** (complex Hilbert spaces): `T` is trace class iff
`∑ᵢ re ⟪bᵢ, |T| bᵢ⟫ < ∞`, in **every** Hilbert basis `b` (the terms are nonnegative,
`re_inner_cfcAbs_nonneg`). -/
theorem isTraceClass_iff_summable_cfcAbs (T : E →L[ℂ] E) (b : HilbertBasis ι ℂ E) :
    IsTraceClass T ↔ Summable fun i => RCLike.re ⟪b i, CFC.abs T (b i)⟫_ℂ := by
  rw [isTraceClass_iff_isTraceClass_cfcAbs]
  refine ⟨fun h => (h.hasSum_re_inner b).summable, fun h => ?_⟩
  refine isTraceClass_of_summable_re_inner (Q := sqrtOp (CFC.abs T)) ?_ b h
  rw [(isPositive_sqrtOp _).isSelfAdjoint.adjoint_eq, sqrtOp_comp_sqrtOp (isPositive_cfcAbs T)]

/-- For trace-class `T`, `∑ᵢ re ⟪bᵢ, |T| bᵢ⟫ = re (tr |T|)` in every Hilbert basis. -/
theorem IsTraceClass.hasSum_re_inner_cfcAbs {T : E →L[ℂ] E} (hT : IsTraceClass T)
    (b : HilbertBasis ι ℂ E) :
    HasSum (fun i => RCLike.re ⟪b i, CFC.abs T (b i)⟫_ℂ) (RCLike.re (trace (CFC.abs T))) :=
  ((isTraceClass_iff_isTraceClass_cfcAbs T).1 hT).hasSum_re_inner b

/-- `‖tr |T|‖ ≤ ∑ₙ ‖aₙ‖ ‖bₙ‖` for every nuclear representation `T = ∑ₙ aₙ ⊗ bₙ`. -/
theorem norm_trace_cfcAbs_le (T : E →L[ℂ] E) {a b : κ → E}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖) (hT : HasSum (fun n => rankOne ℂ (a n) (b n)) T) :
    ‖trace (CFC.abs T)‖ ≤ ∑' n, ‖a n‖ * ‖b n‖ :=
  norm_trace_le_of_polar (polar_decomposition_cfcAbs T).2.2.1 (polar_decomposition_cfcAbs T).2.1
    hs hT

/-- **The nuclear norm of `T` is `tr |T|`** (complex Hilbert spaces): for trace-class `T`, the
least value of `∑ₙ ‖aₙ‖ ‖bₙ‖` over all nuclear representations `T = ∑ₙ aₙ ⊗ bₙ` is
`re (tr |T|)`, and it is attained (by `T = ∑ⱼ U |T|^{1/2} fⱼ ⊗ |T|^{1/2} fⱼ` in a Hilbert basis). -/
theorem isLeast_nuclearSums_cfcAbs {T : E →L[ℂ] E} (hT : IsTraceClass T) :
    IsLeast (nuclearSums T) (RCLike.re (trace (CFC.abs T))) :=
  isLeast_nuclearSums_of_polar (polar_decomposition_cfcAbs T).2.2.1
    (polar_decomposition_cfcAbs T).1 (polar_decomposition_cfcAbs T).2.1
    (isPositive_sqrtOp _).isSelfAdjoint.adjoint_eq (sqrtOp_comp_sqrtOp (isPositive_cfcAbs T)) hT

end Complex

/-! ### Real Hilbert spaces -/

section Real

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  {ι κ : Type*}

/-- The diagonal entries `⟪x, |T| x⟫` are nonnegative. -/
theorem inner_realAbs_nonneg (T : X →L[ℝ] X) (x : X) : 0 ≤ ⟪x, realAbs T x⟫_ℝ := by
  simpa using (isPositive_realAbs T).re_inner_nonneg_right x

/-- `T` is trace class iff `|T|` is. -/
theorem isTraceClass_iff_isTraceClass_realAbs (T : X →L[ℝ] X) :
    IsTraceClass T ↔ IsTraceClass (realAbs T) :=
  isTraceClass_iff_of_polar (polar_decomposition_realAbs T).1 (polar_decomposition_realAbs T).2.1

/-- **The trace class is `tr |T| < ∞`** (real Hilbert spaces, the paper's setting): `T` is trace
class iff `∑ᵢ ⟪bᵢ, |T| bᵢ⟫ < ∞`, in **every** Hilbert basis `b` (the terms are nonnegative,
`inner_realAbs_nonneg`). -/
theorem isTraceClass_iff_summable_realAbs (T : X →L[ℝ] X) (b : HilbertBasis ι ℝ X) :
    IsTraceClass T ↔ Summable fun i => ⟪b i, realAbs T (b i)⟫_ℝ := by
  rw [isTraceClass_iff_isTraceClass_realAbs]
  refine ⟨fun h => by simpa using (h.hasSum_re_inner b).summable, fun h => ?_⟩
  refine isTraceClass_of_summable_re_inner (Q := realSqrt (realAbs T)) ?_ b (by simpa using h)
  rw [(isPositive_realSqrt (isPositive_realAbs T)).isSelfAdjoint.adjoint_eq,
    realSqrt_comp_realSqrt (isPositive_realAbs T)]

/-- For trace-class `T`, `∑ᵢ ⟪bᵢ, |T| bᵢ⟫ = tr |T|` in every Hilbert basis. -/
theorem IsTraceClass.hasSum_inner_realAbs {T : X →L[ℝ] X} (hT : IsTraceClass T)
    (b : HilbertBasis ι ℝ X) :
    HasSum (fun i => ⟪b i, realAbs T (b i)⟫_ℝ) (trace (realAbs T)) :=
  ((isTraceClass_iff_isTraceClass_realAbs T).1 hT).hasSum_trace b

/-- `tr |T| ≤ ∑ₙ ‖aₙ‖ ‖bₙ‖` for every nuclear representation `T = ∑ₙ aₙ ⊗ bₙ`. -/
theorem trace_realAbs_le (T : X →L[ℝ] X) {a b : κ → X}
    (hs : Summable fun n => ‖a n‖ * ‖b n‖) (hT : HasSum (fun n => rankOne ℝ (a n) (b n)) T) :
    trace (realAbs T) ≤ ∑' n, ‖a n‖ * ‖b n‖ :=
  (le_abs_self _).trans (norm_trace_le_of_polar (polar_decomposition_realAbs T).2.2.1
    (polar_decomposition_realAbs T).2.1 hs hT)

/-- **The nuclear norm of `T` is `tr |T|`** (real Hilbert spaces): for trace-class `T`, the least
value of `∑ₙ ‖aₙ‖ ‖bₙ‖` over all nuclear representations `T = ∑ₙ aₙ ⊗ bₙ` is `tr |T|`, and it is
attained. -/
theorem isLeast_nuclearSums_realAbs {T : X →L[ℝ] X} (hT : IsTraceClass T) :
    IsLeast (nuclearSums T) (trace (realAbs T)) := by
  simpa using isLeast_nuclearSums_of_polar (polar_decomposition_realAbs T).2.2.1
    (polar_decomposition_realAbs T).1 (polar_decomposition_realAbs T).2.1
    (isPositive_realSqrt (isPositive_realAbs T)).isSelfAdjoint.adjoint_eq
    (realSqrt_comp_realSqrt (isPositive_realAbs T)) hT

/-! ### Complexification -/

open Complexification

/-- The complexification `(bᵢ + i 0)ᵢ` of a Hilbert basis of `X` is a Hilbert basis of `X_ℂ`. -/
def complexifyHilbertBasis (b : HilbertBasis ι ℝ X) : HilbertBasis ι ℂ (Complexification X) :=
  HilbertBasis.mk (v := fun i => (b i : Complexification X))
    (by
      classical
      rw [orthonormal_iff_ite]
      intro i j
      rw [inner_ofReal_ofReal, orthonormal_iff_ite.1 b.orthonormal i j]
      split_ifs <;> simp)
    (by
      set S := Submodule.span ℂ (Set.range fun i => (b i : Complexification X))
      have key : ∀ x ∈ Submodule.span ℝ (Set.range b), (x : Complexification X) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [ofReal_add]
          exact S.add_mem hy hz
        | smul r y _ hy =>
          rw [ofReal_smul, ← Complex.coe_smul]
          exact S.smul_mem _ hy
      have hle : (Submodule.span ℝ (Set.range b)).complexify ≤ S := fun z hz => by
        rw [← re_add_I_smul_im z]
        exact S.add_mem (key _ hz.1) (S.smul_mem _ (key _ hz.2))
      calc (⊤ : Submodule ℂ (Complexification X))
          = (Submodule.span ℝ (Set.range b)).complexify.topologicalClosure := by
            rw [Submodule.topologicalClosure_complexify, b.dense_span, Submodule.complexify_top]
        _ ≤ S.topologicalClosure := Submodule.topologicalClosure_mono hle)

@[simp] theorem complexifyHilbertBasis_apply (b : HilbertBasis ι ℝ X) (i : ι) :
    complexifyHilbertBasis b i = (b i : Complexification X) := by
  simp [complexifyHilbertBasis]

/-- `T_ℂ` is trace class iff `T` is. -/
theorem isTraceClass_complexify_iff (T : X →L[ℝ] X) :
    IsTraceClass T.complexify ↔ IsTraceClass T := by
  set b := stdHilbertBasis ℝ X
  rw [isTraceClass_iff_summable_cfcAbs _ (complexifyHilbertBasis b),
    isTraceClass_iff_summable_realAbs T b, cfcAbs_eq_sqrtOp, ← complexify_realAbs]
  simp

/-- `tr T_ℂ = tr T` for trace-class `T`. -/
theorem trace_complexify {T : X →L[ℝ] X} (hT : IsTraceClass T) :
    trace T.complexify = ((trace T : ℝ) : ℂ) := by
  set b := stdHilbertBasis ℝ X
  have h1 := ((isTraceClass_complexify_iff T).2 hT).hasSum_trace (complexifyHilbertBasis b)
  have h2 := (hT.hasSum_trace b).mapL Complex.ofRealCLM
  simp only [complexifyHilbertBasis_apply, complexify_ofReal, inner_ofReal_ofReal] at h1
  exact h1.unique (by simpa using h2)

end Real

/-! ### The Gramian -/

section Gramian

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {ι : Type*}

/-- `|𝒢(z)| = 𝒢(z)` on a complex Hilbert space: the Gramian is positive. -/
theorem cfcAbs_gramian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (z : α → E) : CFC.abs (gramian ℂ μ z) = gramian ℂ μ z :=
  cfcAbs_of_isPositive isPositive_gramian

/-- `|𝒢(z)| = 𝒢(z)` on a real Hilbert space: the Gramian is positive. -/
theorem realAbs_gramian {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (z : α → X) : realAbs (gramian ℝ μ z) = gramian ℝ μ z :=
  realAbs_of_isPositive isPositive_gramian

/-- `eq:hilbert-gramian` in the textbook form `tr |𝒢(z)| < ∞` (real Hilbert spaces): in every
Hilbert basis, `∑ᵢ ⟪eᵢ, |𝒢(z)| eᵢ⟫ = ∫ ‖z‖²`; this is `hasSum_re_inner_gramian` through
`realAbs_gramian`, and `isTraceClass_iff_summable_realAbs` turns it into `isTraceClass_gramian`. -/
theorem hasSum_inner_realAbs_gramian {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {z : α → X} (hz : MemLp z 2 μ) (e : HilbertBasis ι ℝ X) :
    HasSum (fun i => ⟪e i, realAbs (gramian ℝ μ z) (e i)⟫_ℝ) (∫ t, ‖z t‖ ^ 2 ∂μ) := by
  rw [realAbs_gramian]
  simpa using (hasSum_re_inner_gramian hz e).2

/-- The complex form of `hasSum_inner_realAbs_gramian`. -/
theorem hasSum_re_inner_cfcAbs_gramian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {z : α → E} (hz : MemLp z 2 μ) (e : HilbertBasis ι ℂ E) :
    HasSum (fun i => RCLike.re ⟪e i, CFC.abs (gramian ℂ μ z) (e i)⟫_ℂ) (∫ t, ‖z t‖ ^ 2 ∂μ) := by
  rw [cfcAbs_gramian]
  exact (hasSum_re_inner_gramian hz e).2

end Gramian

end TraceClass

end DataDrivenControl
