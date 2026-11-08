module

public import DataDrivenControl.LQR.ModelBased

/-!
# Tail operators of the finite-horizon regulator

Step R1 of the proof of `thm:lqr-riccati` (Pritchard–Salamon Thm 2.7) through the value
operator.

The control space is the **fixed** Hilbert space `H = L²(0, T; U)` for every starting time
`s ∈ [0, T]`: controls before `s` are cut off (`cut T s`, multiplication by `1_(s,T]`) and only
receive the input penalty.  For `x ∈ V` (the state at time `s`) and `u ∈ H`, the tail problem
has terminal state `a s x + b s u ∈ V` and output `c s x + d s u ∈ L²(0, T; Y)` (zero on
`(0, s]`), where

* `a s = S_V(T - s)` (`System.tailA`), `b s = ιWV ∘ L_T ∘ cut s` (`System.tailB`),
* `c s = shR s ∘ 𝓞_V` (`System.tailC`), `d s = 𝓕_T ∘ cut s` (`System.tailD`);

`shR T s` is the right shift by `s` on `L²(0, T)` and `𝓞_V : V → L²(0, T; Y)` is the extension
of `x ↦ C S(·) x` from `W` to `V`, which exists by the `V`-norm bound of `hyp:H2`
(`System.𝓞V`).  The tail cost is the bounded quadratic expression `Riccati.LQ.cost` of
`System.lqTail wts T s`; at `s = 0` it is the cost `eq:lqr-cost` (`System.lqrCost_eq_cost`).

## Main declarations

* `Riccati.shR`, `Riccati.cut` with `coeFn_shR`, `coeFn_cut`, `adjoint_shR`, `adjoint_cut`,
  `cut_cut`, `cut_shR`, `cut_zero`, `cut_self`, `shR_self`, continuity in `s`, and the
  short-interval bound `norm_cut_sub_cut_le`;
* `Riccati.LQ` (data `g, r, a, b, c, d` of a quadratic control problem) and `Riccati.LQ.cost`;
* `System.𝓞V`, `System.𝓞V_ae_eq`; `System.tailA/B/C/D`, `System.lqTail`;
* the cocycle identities `System.L_cut` (`L_τ u = S(τ - t) L_t u + L_τ (cut t u)`),
  `System.tailState`, `System.tailOutput`, causality `System.cut_𝓕_cut`;
* `System.lqrCost_eq_cost`: `J(u; x₀) = J_0(ιWV x₀, u)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Riccati

/-! ### Strong continuity of bounded families -/

section Families

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A family of operators that is strongly continuous and uniformly bounded on `S` is jointly
continuous along continuous paths: `s ↦ A s (g s)` is continuous on `S`. -/
theorem continuousOn_apply_of_bounded {S : Set ℝ} {A : ℝ → E →L[ℝ] F} {g : ℝ → E}
    (hA : ∀ e, ContinuousOn (fun s => A s e) S) {C : ℝ} (hC : ∀ s ∈ S, ‖A s‖ ≤ C)
    (hg : ContinuousOn g S) : ContinuousOn (fun s => A s (g s)) S := by
  intro s₀ hs₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have key : ∀ s ∈ S, ‖A s (g s) - A s₀ (g s₀)‖ ≤
      C * ‖g s - g s₀‖ + ‖A s (g s₀) - A s₀ (g s₀)‖ := by
    intro s hs
    calc ‖A s (g s) - A s₀ (g s₀)‖ = ‖A s (g s - g s₀) + (A s (g s₀) - A s₀ (g s₀))‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖A s (g s - g s₀)‖ + ‖A s (g s₀) - A s₀ (g s₀)‖ := norm_add_le _ _
      _ ≤ C * ‖g s - g s₀‖ + ‖A s (g s₀) - A s₀ (g s₀)‖ := by
          gcongr
          exact ((A s).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hC s hs) (norm_nonneg _))
  have h1 : Tendsto (fun s => C * ‖g s - g s₀‖ + ‖A s (g s₀) - A s₀ (g s₀)‖) (𝓝[S] s₀)
      (𝓝 0) := by
    have ha := (tendsto_iff_norm_sub_tendsto_zero.1 (hg s₀ hs₀)).const_mul C
    have hb := tendsto_iff_norm_sub_tendsto_zero.1 (hA (g s₀) s₀ hs₀)
    simpa using ha.add hb
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact key s hs

end Families

/-! ### Right shift and cut-off on `L²(0, T)` -/

section L2ops

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The **right shift** by `s` on `L²(0, T; E)`: `(shR T s f)(t) = f (t - s)` on `(s, s + T]`,
zero elsewhere (`windowL T T (-s)`). -/
def shR (T s : ℝ) : L2 E T →L[ℝ] L2 E T := windowL T T (-s)

/-- The **cut-off** `cut T s` on `L²(0, T; E)`: multiplication by the indicator of `(s, T]`
(for `s ≥ 0`, `coeFn_cut`).  It is `shR T s ∘ (shR T s)†`, an orthogonal projection. -/
def cut (T s : ℝ) : L2 E T →L[ℝ] L2 E T := shR T s ∘L windowL T T s

variable {T s : ℝ}

/-- The adjoint of the right shift is the left shift `windowL T T s`. -/
theorem adjoint_shR (T s : ℝ) : (shR (E := E) T s)† = windowL T T s := by
  rw [shR, adjoint_windowL, extendL, neg_neg]

/-- A representative of the right shift. -/
theorem coeFn_shR (f : L2 E T) :
    ⇑(shR T s f) =ᵐ[μI T] fun t => (Ioc 0 T).indicator (⇑f) (t - s) := by
  filter_upwards [coeFn_windowL (T := T) (r := -s) f] with t ht
  rw [shR, ht, neg_add_eq_sub]

/-- An a.e. statement on `(0, T]`, translated by `t ↦ r - t`. -/
theorem ae_sub_of_ae {τ t : ℝ} {p : ℝ → Prop} (h : ∀ᵐ σ ∂(μI τ), p σ) :
    ∀ᵐ r, r - t ∈ Ioc 0 τ → p (r - t) := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  exact (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae h

/-- A representative of the cut-off: `cut T s f = 1_(s,T] f` for `s ≥ 0`. -/
theorem coeFn_cut (hs : 0 ≤ s) (f : L2 E T) :
    ⇑(cut T s f) =ᵐ[μI T] (Ioc s T).indicator ⇑f := by
  set g := windowL T T s f
  have hg := ae_sub_of_ae (t := s) (coeFn_windowL (T := T) (r := s) f)
  filter_upwards [coeFn_shR (T := T) (s := s) g, ae_restrict_of_ae hg,
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
  rw [cut, ContinuousLinearMap.comp_apply, h1]
  by_cases hts : s < t
  · have hm : t - s ∈ Ioc 0 T := ⟨by linarith, by linarith [ht.2]⟩
    rw [indicator_of_mem hm, indicator_of_mem (show t ∈ Ioc s T from ⟨hts, ht.2⟩)]
    rw [h2 hm, show s + (t - s) = t by ring, indicator_of_mem ht]
  · rw [indicator_of_notMem (show t - s ∉ Ioc 0 T from fun h => hts (by linarith [h.1])),
      indicator_of_notMem (show t ∉ Ioc s T from fun h => hts h.1)]

/-- The cut-off is self-adjoint. -/
theorem adjoint_cut (T s : ℝ) : (cut (E := E) T s)† = cut T s := by
  rw [cut, ContinuousLinearMap.adjoint_comp, ← adjoint_shR, ContinuousLinearMap.adjoint_adjoint]

/-- `cut T s` is symmetric: `⟪cut s f, g⟫ = ⟪f, cut s g⟫`. -/
theorem inner_cut_left (f g : L2 E T) : ⟪cut T s f, g⟫_ℝ = ⟪f, cut T s g⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_cut]

/-- The right shift is a contraction. -/
theorem norm_shR_le (T s : ℝ) : ‖shR (E := E) T s‖ ≤ 1 := norm_windowL_le _ _ _

/-- The cut-off is a contraction. -/
theorem norm_cut_le (T s : ℝ) : ‖cut (E := E) T s‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa using mul_le_mul (norm_shR_le (E := E) T s) (norm_windowL_le (E := E) T T s)
      (norm_nonneg (windowL (E := E) T T s)) zero_le_one)

/-- `s ↦ shR T s f` is continuous (continuity of translation in `L²`). -/
theorem continuous_shR_apply (T : ℝ) (f : L2 E T) : Continuous fun s => shR T s f :=
  (continuous_windowL T T f).comp continuous_neg

/-- `s ↦ cut T s f` is continuous. -/
theorem continuous_cut_apply (T : ℝ) (f : L2 E T) : Continuous fun s => cut T s f := by
  have h := continuousOn_apply_of_bounded (S := univ) (A := fun s => shR (E := E) T s)
    (g := fun s => windowL T T s f) (fun g => (continuous_shR_apply T g).continuousOn)
    (fun s _ => norm_shR_le T s) (continuous_windowL T T f).continuousOn
  exact continuousOn_univ.1 h

/-- `cut T 0` is the identity. -/
@[simp] theorem cut_zero (T : ℝ) : cut (E := E) T 0 = ContinuousLinearMap.id ℝ _ := by
  ext f : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_cut le_rfl f, ae_restrict_mem measurableSet_Ioc] with t h1 h2
  rw [h1, indicator_of_mem h2, ContinuousLinearMap.id_apply]

/-- `cut T s = 0` for `0 ≤ T ≤ s`. -/
theorem cut_of_le (hT : 0 ≤ T) (hs : T ≤ s) : cut (E := E) T s = 0 := by
  ext f : 1
  rw [zero_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_cut (hT.trans hs) f, Lp.coeFn_zero E 2 (μI T)] with t h1 h2
  rw [h1, h2, indicator_of_notMem (fun h => by linarith [h.1, h.2])]
  rfl

/-- `shR T s = 0` for `s ≥ T`. -/
theorem shR_of_le (hs : T ≤ s) : shR (E := E) T s = 0 := by
  ext f : 1
  exact windowL_eq_zero (fun t ht h => by linarith [h.2, ht.1, h.1, ht.2]) f

/-- Composition of cut-offs: `cut s ∘ cut t = cut (max s t)`. -/
theorem cut_cut {t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (f : L2 E T) :
    cut T s (cut T t f) = cut T (max s t) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_cut hs (cut T t f), coeFn_cut ht f,
    coeFn_cut (le_max_of_le_left hs) f] with r h1 h2 h3
  rw [h1, h3]
  by_cases hr : r ∈ Ioc s T
  · rw [indicator_of_mem hr, h2]
    by_cases hr' : r ∈ Ioc t T
    · rw [indicator_of_mem hr', indicator_of_mem (show r ∈ Ioc (max s t) T from
        ⟨max_lt hr.1 hr'.1, hr.2⟩)]
    · rw [indicator_of_notMem hr', indicator_of_notMem (show r ∉ Ioc (max s t) T from
        fun h => hr' ⟨(le_max_right _ _).trans_lt h.1, h.2⟩)]
  · rw [indicator_of_notMem hr, indicator_of_notMem (show r ∉ Ioc (max s t) T from
      fun h => hr ⟨(le_max_left _ _).trans_lt h.1, h.2⟩)]

/-- The cut-off is idempotent. -/
theorem cut_idem (hs : 0 ≤ s) (f : L2 E T) : cut T s (cut T s f) = cut T s f := by
  rw [cut_cut hs hs, max_self]

/-- The right shift by `s` is supported on `(s, T]`. -/
theorem cut_shR (hs : 0 ≤ s) (f : L2 E T) : cut T s (shR T s f) = shR T s f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_cut hs (shR T s f), coeFn_shR (T := T) (s := s) f,
    ae_restrict_mem measurableSet_Ioc] with r h1 h2 hr
  rw [h1]
  by_cases hrs : s < r
  · rw [indicator_of_mem (show r ∈ Ioc s T from ⟨hrs, hr.2⟩)]
  · rw [indicator_of_notMem (show r ∉ Ioc s T from fun h => hrs h.1), h2,
      indicator_of_notMem (show r - s ∉ Ioc 0 T from fun h => hrs (by linarith [h.1]))]

/-- The difference of two cut-offs is a projection: `⟪y, P f⟫ = ⟪P y, P f⟫` for
`P = cut β - cut γ`, `0 ≤ β ≤ γ`. -/
theorem inner_cut_sub_cut {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (y f : L2 E T) :
    ⟪y, cut T β f - cut T γ f⟫_ℝ = ⟪cut T β y - cut T γ y, cut T β f - cut T γ f⟫_ℝ := by
  have hγ : 0 ≤ γ := hβ.trans hβγ
  have hP : cut T β (cut T β f - cut T γ f) - cut T γ (cut T β f - cut T γ f) =
      cut T β f - cut T γ f := by
    simp only [map_sub, cut_cut hβ hβ, cut_cut hβ hγ, cut_cut hγ hβ, cut_cut hγ hγ, max_self,
      max_eq_right hβγ, max_eq_left hβγ]
    abel
  conv_lhs => rw [← hP]
  rw [inner_sub_right, ← inner_cut_left, ← inner_cut_left, ← inner_sub_left]

/-- Short-interval bound: if `‖f r‖ ≤ K` a.e., then `‖(cut β - cut γ) f‖ ≤ √(γ - β) K`. -/
theorem norm_cut_sub_cut_le {β γ K : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ) (hK : 0 ≤ K) {f : L2 E T}
    (hf : ∀ᵐ r ∂(μI T), ‖f r‖ ≤ K) :
    ‖cut T β f - cut T γ f‖ ≤ √(γ - β) * K := by
  have hγ : 0 ≤ γ := hβ.trans hβγ
  have hae : ⇑(cut T β f - cut T γ f) =ᵐ[μI T] (Ioc β γ).indicator ⇑f := by
    filter_upwards [Lp.coeFn_sub (cut T β f) (cut T γ f), coeFn_cut hβ f, coeFn_cut hγ f,
      ae_restrict_mem measurableSet_Ioc] with r h1 h2 h3 hr
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hr1 : r ≤ β
    · rw [indicator_of_notMem (show r ∉ Ioc β T from fun h => by linarith [h.1]),
        indicator_of_notMem (show r ∉ Ioc γ T from fun h => by linarith [h.1]),
        indicator_of_notMem (show r ∉ Ioc β γ from fun h => by linarith [h.1]), sub_zero]
    by_cases hr2 : r ≤ γ
    · rw [indicator_of_mem (show r ∈ Ioc β T from ⟨not_le.1 hr1, hr.2⟩),
        indicator_of_notMem (show r ∉ Ioc γ T from fun h => by linarith [h.1]),
        indicator_of_mem (show r ∈ Ioc β γ from ⟨not_le.1 hr1, hr2⟩), sub_zero]
    · rw [indicator_of_mem (show r ∈ Ioc β T from ⟨not_le.1 hr1, hr.2⟩),
        indicator_of_mem (show r ∈ Ioc γ T from ⟨not_le.1 hr2, hr.2⟩),
        indicator_of_notMem (show r ∉ Ioc β γ from fun h => hr2 h.2), sub_self]
  have hsq : ‖cut T β f - cut T γ f‖ ^ 2 ≤ (γ - β) * K ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc ∫ r, ⟪(cut T β f - cut T γ f) r, (cut T β f - cut T γ f) r⟫_ℝ ∂(μI T)
        ≤ ∫ r, (Ioc β γ).indicator (fun _ => K ^ 2) r ∂(μI T) := by
          refine integral_mono_ae (L2.integrable_inner _ _)
            ((integrable_const (K ^ 2)).indicator measurableSet_Ioc) ?_
          filter_upwards [hae, hf] with r h1 h2
          rw [h1, real_inner_self_eq_norm_sq]
          by_cases hr : r ∈ Ioc β γ
          · rw [indicator_of_mem hr, indicator_of_mem hr]
            exact pow_le_pow_left₀ (norm_nonneg _) h2 2
          · rw [indicator_of_notMem hr, indicator_of_notMem hr, norm_zero]
            norm_num
      _ = (μI T).real (Ioc β γ) * K ^ 2 := by
          rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul]
      _ ≤ (γ - β) * K ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg K)
          calc (μI T).real (Ioc β γ) ≤ volume.real (Ioc β γ) :=
                ENNReal.toReal_mono (by simp) (Measure.restrict_apply_le _ _)
            _ = γ - β := by rw [Real.volume_real_Ioc_of_le hβγ]
  rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (by linarith)]
  exact Real.le_sqrt_of_sq_le hsq

end L2ops

/-! ### Quadratic control problems -/

section LQ

variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

variable (V H Z) in
/-- The data of a **quadratic control problem** on real Hilbert spaces (states `V`, controls
`H`, outputs `Z`): terminal weight `g`, input weight `r`, free and controlled terminal state
`a`, `b`, free and controlled output `c`, `d`.  Its cost is `LQ.cost`. -/
structure LQ where
  /-- The terminal weight `𝔾 ∈ L(V)`. -/
  g : V →L[ℝ] V
  /-- The input weight `R̃ ∈ L(H)`. -/
  r : H →L[ℝ] H
  /-- The free terminal state `x ↦ a x`. -/
  a : V →L[ℝ] V
  /-- The controlled terminal state `u ↦ b u`. -/
  b : H →L[ℝ] V
  /-- The free output `x ↦ c x`. -/
  c : V →L[ℝ] Z
  /-- The controlled output `u ↦ d u`. -/
  d : H →L[ℝ] Z

/-- The cost `J(x, u) = ⟪𝔾 (a x + b u), a x + b u⟫ + ‖c x + d u‖² + ⟪R̃ u, u⟫` of a quadratic
control problem (the tail cost of `eq:lqr-cost`). -/
def LQ.cost (p : LQ V H Z) (x : V) (u : H) : ℝ :=
  ⟪p.g (p.a x + p.b u), p.a x + p.b u⟫_ℝ + ‖p.c x + p.d u‖ ^ 2 + ⟪p.r u, u⟫_ℝ

end LQ

/-! ### The weights as operators -/

section Weights

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The terminal weight as an operator `𝔾 ∈ L(V)`: `⟪𝔾 v, w⟫ = G v w` (Riesz). -/
def gOp (wts : LQRWeights U V) : V →L[ℝ] V :=
  InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) wts.G

/-- The defining property of `𝔾`: `⟪𝔾 v, w⟫ = G v w`. -/
theorem inner_gOp (wts : LQRWeights U V) (v w : V) : ⟪gOp wts v, w⟫_ℝ = wts.G v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ v w

/-- `𝔾` is symmetric. -/
theorem inner_gOp_comm (wts : LQRWeights U V) (v w : V) :
    ⟪gOp wts v, w⟫_ℝ = ⟪v, gOp wts w⟫_ℝ := by
  rw [inner_gOp, real_inner_comm, inner_gOp, wts.G_symm]

/-- `𝔾` is nonnegative. -/
theorem inner_gOp_nonneg (wts : LQRWeights U V) (v : V) : 0 ≤ ⟪gOp wts v, v⟫_ℝ := by
  rw [inner_gOp]; exact wts.G_nonneg v

/-- `𝔾` is self-adjoint. -/
theorem adjoint_gOp (wts : LQRWeights U V) : (gOp wts)† = gOp wts := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact inner_gOp_comm wts

/-- The input weight acting pointwise on `L²(0, T; U)`: `(R̃ u)(t) = R (u t)`. -/
def rOp (wts : LQRWeights U V) (T : ℝ) : L2 U T →L[ℝ] L2 U T := wts.R.compLpL 2 (μI T)

/-- A representative of `R̃ u`: `(R̃ u)(t) = R (u t)`. -/
theorem coeFn_rOp (wts : LQRWeights U V) {T : ℝ} (u : L2 U T) :
    ⇑(rOp wts T u) =ᵐ[μI T] fun t => wts.R (u t) :=
  wts.R.coeFn_compLpL u

/-- `⟪R̃ u, v⟫ = ∫₀ᵀ ⟪R u(t), v(t)⟫ dt`. -/
theorem inner_rOp (wts : LQRWeights U V) {T : ℝ} (u v : L2 U T) :
    ⟪rOp wts T u, v⟫_ℝ = ∫ t in Ioc 0 T, ⟪wts.R (u t), v t⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_rOp wts u] with t ht
  rw [ht]

/-- `R̃` is self-adjoint. -/
theorem inner_rOp_comm (wts : LQRWeights U V) {T : ℝ} (u v : L2 U T) :
    ⟪rOp wts T u, v⟫_ℝ = ⟪u, rOp wts T v⟫_ℝ := by
  rw [real_inner_comm (rOp wts T v) u, inner_rOp, inner_rOp]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have h := wts.R_isSymmetric (u t) (v t)
  simp only [ContinuousLinearMap.coe_coe] at h
  simp only
  rw [h, real_inner_comm]

/-- `R̃` is self-adjoint. -/
theorem adjoint_rOp (wts : LQRWeights U V) (T : ℝ) : (rOp wts T)† = rOp wts T := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact inner_rOp_comm wts

/-- `R̃` is coercive, with the constant of `R`. -/
theorem rOp_coercive (wts : LQRWeights U V) (T : ℝ) :
    ∃ ε > 0, ∀ u : L2 U T, ε * ‖u‖ ^ 2 ≤ ⟪rOp wts T u, u⟫_ℝ := by
  obtain ⟨ε, hε, hR⟩ := wts.R_coercive
  refine ⟨ε, hε, fun u => ?_⟩
  rw [inner_rOp, ← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  refine integral_mono_ae ((L2.integrable_inner u u).const_mul ε) ?_
    (Eventually.of_forall fun t => ?_)
  · refine (L2.integrable_inner (rOp wts T u) u).congr ?_
    filter_upwards [coeFn_rOp wts u] with t ht
    rw [ht]
  · simp only
    rw [real_inner_self_eq_norm_sq, real_inner_comm]
    exact hR (u t)

/-- `R̃` commutes with the cut-offs. -/
theorem cut_rOp (wts : LQRWeights U V) {T s : ℝ} (hs : 0 ≤ s) (u : L2 U T) :
    cut T s (rOp wts T u) = rOp wts T (cut T s u) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_cut hs (rOp wts T u), coeFn_rOp wts u, coeFn_rOp wts (cut T s u),
    coeFn_cut hs u] with t h1 h2 h3 h4
  rw [h1, h3, h4]
  by_cases ht : t ∈ Ioc s T
  · rw [indicator_of_mem ht, indicator_of_mem ht, h2]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, map_zero]

end Weights

end Riccati

namespace System

open Riccati

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable {sys : System U W X V Y}

/-! ### The free output on `V` -/

/-- `W` is dense in `V`. -/
theorem denseRange_ιWV : DenseRange sys.ιWV :=
  sys.ιV_denseRange.comp sys.ιW_denseRange sys.ιV.continuous

variable (sys) in
/-- Existence of `𝓞_V`: `x ↦ C S(·) x` extends from `W` to a bounded operator on `V`, by the
`V`-norm bound of `hyp:H2` (`lem:finite-horizon-output`). -/
theorem exists_𝓞V {τ : ℝ} (h : sys.H2 τ) :
    ∃ O : V →L[ℝ] L2 Y τ, ∀ w : W,
      ⇑(O (sys.ιWV w)) =ᵐ[μI τ] fun t => sys.C (sys.SW.real t w) := by
  obtain ⟨c, hc⟩ := h
  have hmem : ∀ w : W, MemLp (fun t => sys.C (sys.SW.real t w)) 2 (μI τ) := fun w =>
    memLp_iff.2 (lt_of_le_of_lt (hc w) ENNReal.ofReal_lt_top)
  let O₀ : W →ₗ[ℝ] L2 Y τ :=
    { toFun := fun w => (hmem w).toLp _
      map_add' := fun w w' => by
        rw [← MemLp.toLp_add]
        congr 1
        funext t
        simp only [Pi.add_apply, map_add]
      map_smul' := fun a w => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        funext t
        simp only [Pi.smul_apply, map_smul] }
  have hbound : ∀ w : W, ‖O₀ w‖ ≤ max c 0 * ‖(sys.ιWV : W →ₗ[ℝ] V) w‖ := by
    intro w
    change ‖(hmem w).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((hc w).trans (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  refine ⟨O₀.extendOfNorm (sys.ιWV : W →ₗ[ℝ] V), fun w => ?_⟩
  have hd : DenseRange (sys.ιWV : W →ₗ[ℝ] V) := denseRange_ιWV
  have := LinearMap.extendOfNorm_eq hd ⟨_, hbound⟩ w
  rw [ContinuousLinearMap.coe_coe] at this
  rw [this]
  exact (hmem w).coeFn_toLp

variable (sys) in
open scoped Classical in
/-- The **observability operator on `V`**, `𝓞_V : V → L²(0, τ; Y)`, `x ↦ C S(·) x` (junk `0` if
`hyp:H2` fails at `τ`). -/
def 𝓞V (τ : ℝ) : V →L[ℝ] L2 Y τ := if h : sys.H2 τ then (sys.exists_𝓞V h).choose else 0

/-- `𝓞_V x = C S(·) x` for `x ∈ W`. -/
theorem 𝓞V_ae_eq {T : ℝ} (hH2 : sys.H2 T) (hT : 0 < T) {τ : ℝ} (w : W) :
    ⇑(sys.𝓞V τ (sys.ιWV w)) =ᵐ[μI τ] fun t => sys.C (sys.SW.real t w) := by
  have h := hH2.of_pos sys hT τ
  rw [𝓞V, dite_eq_left h]
  exact (sys.exists_𝓞V h).choose_spec w

/-! ### The tail operators -/

variable (sys)

/-- Free terminal state of the tail problem started at time `s`: `a s = S_V(T - s)`. -/
def tailA (T s : ℝ) : V →L[ℝ] V := sys.SV.real (T - s)

/-- Controlled terminal state of the tail problem: `b s u = ιWV (L_T (cut s u))`. -/
def tailB (T s : ℝ) : L2 U T →L[ℝ] V := sys.ιWV ∘L sys.Lop T ∘L cut T s

/-- Free output of the tail problem: `c s x = shR s (𝓞_V x)`. -/
def tailC (T s : ℝ) : V →L[ℝ] L2 Y T := shR T s ∘L sys.𝓞V T

/-- Controlled output of the tail problem: `d s u = 𝓕_T (cut s u)`. -/
def tailD (T s : ℝ) : L2 U T →L[ℝ] L2 Y T := sys.𝓕 T ∘L cut T s

/-- The **tail problem** started at time `s`, as a quadratic control problem on
`V × L²(0, T; U)`. -/
def lqTail (wts : LQRWeights U V) (T s : ℝ) : LQ V (L2 U T) (L2 Y T) where
  g := gOp wts
  r := rOp wts T
  a := sys.tailA T s
  b := sys.tailB T s
  c := sys.tailC T s
  d := sys.tailD T s

variable {sys}

/-- At `s = 0` the free terminal state is `S_V(T)`. -/
@[simp] theorem tailA_zero (T : ℝ) : sys.tailA T 0 = sys.SV.real T := by simp [tailA]

/-- Unfolding `tailA`. -/
theorem tailA_apply (T s : ℝ) (x : V) : sys.tailA T s x = sys.SV.real (T - s) x := rfl

/-- Unfolding `tailB`. -/
theorem tailB_apply (T s : ℝ) (u : L2 U T) :
    sys.tailB T s u = sys.ιWV (sys.Lop T (cut T s u)) := rfl

/-- Unfolding `tailC`. -/
theorem tailC_apply (T s : ℝ) (x : V) : sys.tailC T s x = shR T s (sys.𝓞V T x) := rfl

/-- Unfolding `tailD`. -/
theorem tailD_apply (T s : ℝ) (u : L2 U T) : sys.tailD T s u = sys.𝓕 T (cut T s u) := rfl

/-- At `s = 0` the controlled terminal state is `ιWV ∘ L_T`. -/
@[simp] theorem tailB_zero (T : ℝ) : sys.tailB T 0 = sys.ιWV ∘L sys.Lop T := by
  simp [tailB]

/-- At `s = 0` the controlled terminal state is `ιWV (L_T u)`. -/
theorem tailB_zero_apply (T : ℝ) (u : L2 U T) : sys.tailB T 0 u = sys.ιWV (sys.Lop T u) := by
  rw [tailB_apply, cut_zero, ContinuousLinearMap.id_apply]

/-- At `s = 0` the free output is `𝓞_V`. -/
@[simp] theorem tailC_zero (T : ℝ) : sys.tailC T 0 = sys.𝓞V T := by
  simp [tailC, shR]

/-- At `s = 0` the controlled output is `𝓕_T`. -/
@[simp] theorem tailD_zero (T : ℝ) : sys.tailD T 0 = sys.𝓕 T := by
  simp [tailD]

/-- At `s = T` the free terminal state is the identity. -/
@[simp] theorem tailA_self (T : ℝ) : sys.tailA T T = 1 := by simp [tailA]

/-- At `s = T` there is no control left. -/
theorem tailB_self {T : ℝ} (hT : 0 ≤ T) : sys.tailB T T = 0 := by
  simp [tailB, cut_of_le hT le_rfl]

/-- At `s = T` the free output vanishes. -/
theorem tailC_self (T : ℝ) : sys.tailC T T = 0 := by
  simp [tailC, shR_of_le le_rfl]

/-- At `s = T` the controlled output vanishes. -/
theorem tailD_self {T : ℝ} (hT : 0 ≤ T) : sys.tailD T T = 0 := by
  simp [tailD, cut_of_le hT le_rfl]

/-! ### The cocycle identities -/

/-- `L_t 0 = 0`. -/
theorem L_zero_input (t : ℝ) : sys.L t (0 : ℝ → U) = 0 :=
  L_eq_of_ιWV (by simp [convV])

/-- A cut-off input does not act before the cut: `L_r (cut s u) = 0` for `r ≤ s`, `r ≤ T`. -/
theorem L_cut_of_le {T s r : ℝ} (hs : 0 ≤ s) (hr : r ≤ s) (hrT : r ≤ T) (u : L2 U T) :
    sys.L r (cut T s u) = 0 := by
  rw [← L_zero_input (sys := sys) r]
  refine L_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hrT)
    (coeFn_cut hs u), ae_restrict_mem measurableSet_Ioc] with t h1 h2
  rw [h1, indicator_of_notMem (fun h => by linarith [h.1, h2.2])]
  rfl

/-- **Cocycle identity** for the control convolution: for `0 ≤ t ≤ τ ≤ T`,
`L_τ u = S_W(τ - t) L_t u + L_τ (cut t u)`. -/
theorem L_cut {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t τ : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ)
    (hτT : τ ≤ T) (u : L2 U T) :
    sys.L τ u = sys.SW.real (τ - t) (sys.L t u) + sys.L τ (cut T t u) := by
  have he : t + (τ - t) = τ := by ring
  have hu : MemLp (⇑u) 2 (μI (t + (τ - t))) := by
    rw [he]; exact memLp_μI_of_le (Lp.memLp u) hτT
  have hcu : MemLp (⇑(cut T t u)) 2 (μI (t + (τ - t))) := by
    rw [he]; exact memLp_μI_of_le (Lp.memLp _) hτT
  have h1 := L_add_time hH1 hT ht (sub_nonneg.2 htτ) hu
  have h2 := L_add_time hH1 hT ht (sub_nonneg.2 htτ) hcu
  rw [he] at h1 h2
  rw [h1, h2, L_cut_of_le ht le_rfl (htτ.trans hτT) u, map_zero, zero_add]
  congr 1
  refine L_congr_ae ?_
  have := ae_comp_add (coeFn_cut ht u) ht (by linarith : t + (τ - t) ≤ T)
  filter_upwards [this, ae_restrict_mem measurableSet_Ioc] with r hr hr'
  rw [hr, indicator_of_mem (show t + r ∈ Ioc t T from
    ⟨by linarith [hr'.1], by linarith [hr'.2]⟩)]

/-- **Terminal state of the tail** (`R1`): for `t ∈ [0, T]`, the tail problem started at
`x(t) = x(t; x₀, u)` with the input `u` reaches `x(T)`:
`S_V(T - t) x(t) + ιWV L_T (cut t u) = x(T)`. -/
theorem tailState {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (x₀ : W) (u : L2 U T) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    sys.tailA T t (sys.ιWV (sys.mildW x₀ u t)) + sys.tailB T t u =
      sys.ιWV (sys.mildW x₀ u T) := by
  have key : sys.SW.real (T - t) (sys.mildW x₀ u t) + sys.L T (cut T t u) =
      sys.mildW x₀ u T := by
    rw [mildW, mildW, map_add, L_cut hH1 hT ht.1 ht.2 le_rfl u,
      ← sys.SW.real_add_apply (sub_nonneg.2 ht.2) ht.1, sub_add_cancel]
    abel
  rw [tailA_apply, tailB_apply, Lop_apply hH1 hT, ← ιWV_SW, ← map_add, key]

/-- **Output of the tail** (`R1`): for `t ∈ [0, T]`, the tail problem started at `x(t)` with
the input `u` produces the output `y = 𝓞_V x₀ + 𝓕_T u` cut off at `t`. -/
theorem tailOutput {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T) (x₀ : W)
    (u : L2 U T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    sys.tailC T t (sys.ιWV (sys.mildW x₀ u t)) + sys.tailD T t u =
      cut T t (sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u) := by
  rw [tailC_apply, tailD_apply]
  refine Lp.ext ?_
  set xt := sys.mildW x₀ u t with hxt
  have hA := ae_sub_of_ae (t := t) (𝓞V_ae_eq hH2 hT (τ := T) xt)
  filter_upwards [Lp.coeFn_add (shR T t (sys.𝓞V T (sys.ιWV xt))) (sys.𝓕 T (cut T t u)),
    coeFn_shR (T := T) (s := t) (sys.𝓞V T (sys.ιWV xt)), ae_restrict_of_ae hA,
    𝓕_ae_eq hH1 hT (cut T t u), coeFn_cut ht.1 (sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u),
    Lp.coeFn_add (sys.𝓞V T (sys.ιWV x₀)) (sys.𝓕 T u), 𝓞V_ae_eq hH2 hT (τ := T) x₀,
    𝓕_ae_eq hH1 hT u, ae_restrict_mem measurableSet_Ioc] with r h1 h2 h3 h4 h5 h6 h7 h8 hr
  rw [h1, Pi.add_apply, h2, h4, h5]
  by_cases hrt : t < r
  · have hm : r - t ∈ Ioc 0 T := ⟨by linarith, by linarith [hr.2, ht.1]⟩
    rw [indicator_of_mem hm, h3 hm, indicator_of_mem (show r ∈ Ioc t T from ⟨hrt, hr.2⟩), h6,
      Pi.add_apply, h7, h8, ← map_add, ← map_add]
    congr 1
    rw [hxt, mildW, map_add, L_cut hH1 hT ht.1 hrt.le hr.2 u,
      ← sys.SW.real_add_apply (sub_nonneg.2 hrt.le) ht.1, sub_add_cancel]
    abel
  · rw [indicator_of_notMem (show r - t ∉ Ioc 0 T from fun h => hrt (by linarith [h.1])),
      indicator_of_notMem (show r ∉ Ioc t T from fun h => hrt h.1),
      L_cut_of_le ht.1 (not_lt.1 hrt) hr.2 u, map_zero, zero_add]

/-- **Causality** of `𝓕_T`: the output of an input cut off at `t` vanishes before `t`. -/
theorem cut_𝓕_cut {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T)
    (u : L2 U T) : cut T t (sys.𝓕 T (cut T t u)) = sys.𝓕 T (cut T t u) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_cut ht.1 (sys.𝓕 T (cut T t u)), 𝓕_ae_eq hH1 hT (cut T t u),
    ae_restrict_mem measurableSet_Ioc] with r h1 h2 hr
  rw [h1]
  by_cases hrt : t < r
  · rw [indicator_of_mem (show r ∈ Ioc t T from ⟨hrt, hr.2⟩)]
  · rw [indicator_of_notMem (show r ∉ Ioc t T from fun h => hrt h.1), h2,
      L_cut_of_le ht.1 (not_lt.1 hrt) hr.2 u, map_zero]

/-- **The cost as a tail cost** (`R1`, `eq:lqr-cost`): `J(u; x₀) = J_0(ιWV x₀, u)`. -/
theorem lqrCost_eq_cost {T : ℝ} (hH1 : sys.H1 T) (hH2 : sys.H2 T) (hT : 0 < T)
    (wts : LQRWeights U V) (x₀ : W) (u : L2 U T) :
    sys.lqrCost wts T x₀ u = (sys.lqTail wts T 0).cost (sys.ιWV x₀) u := by
  have hxT : sys.SV.real T (sys.ιWV x₀) + sys.ιWV (sys.Lop T u) = sys.ιWV (sys.mildW x₀ u T) := by
    rw [mildW, map_add, ιWV_SW, Lop_apply hH1 hT]
  have hyae : (fun t => ⟪(sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u) t,
      (sys.𝓞V T (sys.ιWV x₀) + sys.𝓕 T u) t⟫_ℝ) =ᵐ[μI T]
        fun t => ‖sys.C (sys.mildW x₀ u t)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add (sys.𝓞V T (sys.ιWV x₀)) (sys.𝓕 T u),
      𝓞V_ae_eq hH2 hT (τ := T) x₀, 𝓕_ae_eq hH1 hT u] with t h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, real_inner_self_eq_norm_sq, mildW, map_add]
  have hRae : (fun t => ⟪rOp wts T u t, u t⟫_ℝ) =ᵐ[μI T] fun t => ⟪u t, wts.R (u t)⟫_ℝ := by
    filter_upwards [coeFn_rOp wts u] with t ht
    rw [ht, real_inner_comm]
  have hint1 : Integrable (fun t => ‖sys.C (sys.mildW x₀ u t)‖ ^ 2) (μI T) :=
    (L2.integrable_inner _ _).congr hyae
  have hint2 : Integrable (fun t => ⟪u t, wts.R (u t)⟫_ℝ) (μI T) :=
    (L2.integrable_inner _ _).congr hRae
  simp only [LQ.cost, lqTail, tailA_zero, tailB_zero_apply, tailC_zero, tailD_zero]
  rw [hxT, inner_gOp, lqrCost, integral_add hint1 hint2, ← real_inner_self_eq_norm_sq,
    L2.inner_def, L2.inner_def, integral_congr_ae hyae, integral_congr_ae hRae, add_assoc]

end System

end DataDrivenControl
