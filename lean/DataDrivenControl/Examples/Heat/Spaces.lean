module

public import DataDrivenControl.Semigroup.Modal
public import DataDrivenControl.Semigroup.DomainSpace
public import DataDrivenControl.Signal.Shift

/-!
# The spaces `X₋₁`, `V` and `W` of the boundary-controlled heat equation

Paper: `ex:boundary-heat-informative` (`informativity.tex`), `app:boundary-heat-informative`
(`appendix_proofs.tex`): `eq:heat-localized-V` (the space `V`, see the deviation below) and
`eq:heat-W-domain` (`W = D(A_V) = {w ∈ X : A_{X,-1} w ∈ V}`).

## Setting: modal data

The construction only uses the modal data of a diagonal model with a scalar observation, bundled
in `ModalData`: eigenvalues `λₙ ≤ 0` with `∑ₙ 1/(1 - λₙ) < ∞` and bounded observation
coefficients `cₙ`.  The heat equation (`Examples/Heat/Kernel`) has `λₙ = -(nπ)²` and
`cₙ = eₙ(ξ₀)`.  The state space is any real Hilbert space `X` with a Hilbert basis
`e : HilbertBasis ℕ ℝ X`, and `A` generates `S_X = diagSemigroup e λ` (`ModalData.SX`).
Indexing starts at `0`: the paper's constant mode `e₀` is `e 0`, and its `eₙ` (`n ≥ 1`) is `e n`.

## Main declarations

* `Xm1 = ℓ²(ℕ, ℝ)`, the extrapolation space `X₋₁` in the coordinates `aₙ = xₙ / wₙ`,
  `wₙ = 1 - λₙ` (`‖z‖_{X₋₁} = ‖(1 - A)⁻¹ z‖_X`); `d.toXm1 e : X →L[ℝ] Xm1` (diagonal) and the
  diagonal semigroup `d.Sm` on `Xm1`.
* `d.obs a t = ∑ₙ cₙ wₙ e^{λₙ t} aₙ` (`t > 0`), the free output `C S(t) z` of `z ∈ X₋₁`
  (`hasSum_obs`, `hasSum_obs_toXm1`, `continuousOn_obs`, `obs_Sm`).
* **`V`** (`d.V`): the graph `{(a, g) : g = obs a a.e. on (0, 1]}` in `WithLp 2 (Xm1 × L2 ℝ 1)`,
  so `‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀¹ |C S(t) z|² dt`; closed (`isClosed_Vsub`), hence a Hilbert space.
  Elements are determined by their first component (`V_ext`); `mkV`, `fstV`, `sndV`.
* `d.SV : C0Semigroup ℝ d.V` (translation of the output, `fstV_SV`, `consistent_fstV`).
* **`X ↪ V`**: `d.ιV e` (`memLp_obs_toXm1`, the Schur test with `∑ₘ 1/(1 - λₙ - λₘ) ≤ ∑ₘ 1/wₘ`;
  continuity by the closed graph theorem, `continuous_of_fstV`), injective, dense
  (`denseRange_ιV`, via `S_V(s) z ∈ X` for `s > 0`), consistent (`consistent_ιV`).
* **`W = D(A_V)`** with the graph norm (`d.W = d.SV.Dom`, `Semigroup/DomainSpace`), the
  restricted semigroup `d.SW`, and **`W ↪ X`**: `d.ιW e` (`ιV_ιW : ιV (ιW w) = w` in `V`),
  injective, dense (`D(A) ⊆ W`, `exists_ιW_eq`), consistent (`consistent_ιW`).
* **`eq:heat-W-domain`**: `mem_SV_generator_domain_iff` (`x ∈ W ↔ A_{X,-1} x ∈ V`, with
  `A_{X,-1} = d.genXm1 e`), `SV_generator_ιV` (`A_V x = A_{X,-1} x`), `range_ιW`,
  `fstV_domGen`.

## Deviation from the paper (`eq:heat-localized-V`)

The paper measures the orbit `χ S(t) z` in `H¹(0, 1)` with a cut-off `χ` near `ξ₀`.  Here `V`
uses the scalar observation norm `‖z‖²_{X₋₁} + ∫₀¹ |C S(t) z|² dt`:
it needs no `H¹(0, 1)`, `hyp:H2` holds by construction, and the claims of
`ex:boundary-heat-informative` are unchanged.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace lp

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

/-- The extrapolation space `X₋₁`, modelled as `ℓ²(ℕ, ℝ)` in the coordinates `aₙ = zₙ / wₙ`
(`‖z‖_{X₋₁} = ‖(1 - A)⁻¹ z‖_X`, `app:boundary-heat-informative`). -/
abbrev Xm1 : Type := ℓ²(ℕ, ℝ)

/-- The standard Hilbert basis of `ℓ²`. -/
def stdBasis : HilbertBasis ℕ ℝ Xm1 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ Xm1)

/-- Coordinates in the standard basis: `⟪δₙ, a⟫ = aₙ`. -/
theorem inner_stdBasis (a : Xm1) (n : ℕ) : ⟪stdBasis n, a⟫_ℝ = a n := by
  rw [← HilbertBasis.repr_apply_apply]; rfl

/-- The element of `ℓ²` with the given square-summable coordinates. -/
def mkL2 (f : ℕ → ℝ) (hf : Summable fun n => f n ^ 2) : Xm1 :=
  ⟨f, show Memℓp f 2 from (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
    (by simpa [Real.norm_eq_abs, sq_abs] using hf)⟩

/-- Coordinates of `mkL2`. -/
@[simp] theorem mkL2_apply (f : ℕ → ℝ) (hf : Summable fun n => f n ^ 2) (n : ℕ) :
    mkL2 f hf n = f n := rfl

/-- Parseval in `ℓ²`: `∑ₙ aₙ² = ‖a‖²`. -/
theorem hasSum_sq (a : Xm1) : HasSum (fun n => a n ^ 2) (‖a‖ ^ 2) := by
  simpa [inner_stdBasis] using Diagonal.hasSum_inner_sq stdBasis a

/-- The coordinates of `a ∈ ℓ²` are square summable. -/
theorem summable_sq (a : Xm1) : Summable fun n => a n ^ 2 := (hasSum_sq a).summable

/-- Elements of `ℓ²` are determined by their coordinates. -/
theorem ext_Xm1 {a b : Xm1} (h : ∀ n, a n = b n) : a = b := lp.ext (funext h)

/-- **Modal data** of a diagonal model with a scalar observation: eigenvalues `λₙ ≤ 0` with
`∑ₙ 1/(1 - λₙ) < ∞` and bounded observation coefficients `cₙ` (`y = ∑ₙ cₙ xₙ` on `D(A)`).  The heat
equation of `ex:intro-pde` has `λₙ = -(nπ)²` and `cₙ = eₙ(ξ₀)` (`Examples/Heat/Kernel`). -/
structure ModalData where
  /-- The eigenvalues `λₙ`. -/
  lam : ℕ → ℝ
  /-- The observation coefficients `cₙ`. -/
  c : ℕ → ℝ
  lam_nonpos : ∀ n, lam n ≤ 0
  summable_inv_wt : Summable fun n => (1 - lam n)⁻¹
  exists_abs_c_le : ∃ K, ∀ n, |c n| ≤ K

namespace ModalData

variable (d : ModalData)

/-- The weights `wₙ = 1 - λₙ ≥ 1` of `X₋₁`. -/
def wt (n : ℕ) : ℝ := 1 - d.lam n

/-- `wₙ = 1 - λₙ ≥ 1`. -/
theorem one_le_wt (n : ℕ) : 1 ≤ d.wt n := by unfold wt; linarith [d.lam_nonpos n]

/-- `wₙ > 0`. -/
theorem wt_pos (n : ℕ) : 0 < d.wt n := lt_of_lt_of_le one_pos (d.one_le_wt n)

/-- `|λₙ| ≤ wₙ`. -/
theorem abs_lam_le_wt (n : ℕ) : |d.lam n| ≤ d.wt n := by
  unfold wt; rw [abs_of_nonpos (d.lam_nonpos n)]; linarith

/-- The eigenvalues are bounded above (by `0`). -/
theorem bddAbove_lam : BddAbove (Set.range d.lam) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact d.lam_nonpos n⟩

/-- Smoothing estimate: `wₙᵏ e^{λₙ t} ≤ k! eᵗ / tᵏ` for `t > 0` (from `yᵏ/k! ≤ eʸ`). -/
theorem wt_pow_mul_exp_le (k : ℕ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    d.wt n ^ k * Real.exp (d.lam n * t) ≤ k.factorial * Real.exp t / t ^ k := by
  have hw := d.wt_pos n
  have h1 := Real.pow_div_factorial_le_exp _ (mul_nonneg ht.le hw.le) k
  have hE : 0 < Real.exp (t * d.wt n) := Real.exp_pos _
  have h2 : Real.exp (d.lam n * t) = Real.exp t / Real.exp (t * d.wt n) := by
    rw [← Real.exp_sub]; congr 1; unfold wt; ring
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : t ^ k * d.wt n ^ k ≤ k.factorial * Real.exp (t * d.wt n) := by
    rw [← mul_pow]
    rw [div_le_iff₀ hf] at h1
    linarith
  have htk : 0 < t ^ k := pow_pos ht k
  rw [h2, mul_div_assoc', div_le_div_iff₀ hE htk]
  calc d.wt n ^ k * Real.exp t * t ^ k = (t ^ k * d.wt n ^ k) * Real.exp t := by ring
    _ ≤ (k.factorial * Real.exp (t * d.wt n)) * Real.exp t := by gcongr
    _ = _ := by ring

/-- The extended (diagonal) semigroup `S(t) a = (e^{λₙ t} aₙ)ₙ` on `X₋₁`. -/
abbrev Sm : C0Semigroup ℝ Xm1 := diagSemigroup stdBasis d.lam d.bddAbove_lam

/-- Coordinates of the diagonal semigroup on `X₋₁`: `(S(t) a)ₙ = e^{λₙ t} aₙ`. -/
theorem Sm_apply {t : ℝ} (ht : 0 ≤ t) (a : Xm1) (n : ℕ) :
    d.Sm.real t a n = Real.exp (d.lam n * t) * a n := by
  rw [← inner_stdBasis, inner_diagSemigroup_real _ _ _ ht, inner_stdBasis]

/-- The semigroup on `X₋₁` is a contraction semigroup. -/
theorem norm_Sm_le (t : ℝ) : ‖d.Sm.real t‖ ≤ 1 := by
  have h := norm_diagSemigroup_le stdBasis d.lam d.bddAbove_lam (ω := 0)
    (fun n => d.lam_nonpos n) t.toNNReal
  simp only [zero_mul, Real.exp_zero] at h
  exact h

/-- The observation vector at `t > 0` is square summable. -/
theorem summable_obsVec_sq {t : ℝ} (ht : 0 < t) :
    Summable fun n => (d.c n * d.wt n * Real.exp (d.lam n * t)) ^ 2 := by
  obtain ⟨K, hK⟩ := d.exists_abs_c_le
  refine (d.summable_inv_wt.mul_left
    (K ^ 2 * ((Nat.factorial 3) * Real.exp (2 * t) / (2 * t) ^ 3))).of_nonneg_of_le
    (fun n => sq_nonneg _) (fun n => ?_)
  have hw := d.wt_pos n
  have hb := d.wt_pow_mul_exp_le 3 (by linarith : 0 < 2 * t) n
  have hc : d.c n ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK n) 2
  have hinv : (1 - d.lam n)⁻¹ = (d.wt n)⁻¹ := rfl
  rw [hinv]
  have heq : (d.c n * d.wt n * Real.exp (d.lam n * t)) ^ 2 =
      d.c n ^ 2 * (d.wt n ^ 3 * Real.exp (d.lam n * (2 * t))) * (d.wt n)⁻¹ := by
    rw [show d.lam n * (2 * t) = d.lam n * t + d.lam n * t by ring, Real.exp_add]
    field_simp
  rw [heq]
  have : 0 ≤ d.wt n ^ 3 * Real.exp (d.lam n * (2 * t)) := by positivity
  calc d.c n ^ 2 * (d.wt n ^ 3 * Real.exp (d.lam n * (2 * t))) * (d.wt n)⁻¹
      ≤ K ^ 2 * ((Nat.factorial 3) * Real.exp (2 * t) / (2 * t) ^ 3) * (d.wt n)⁻¹ := by
        gcongr
    _ = _ := rfl

/-- The observation vector `(cₙ wₙ e^{λₙ t})ₙ ∈ X₋₁` (`t > 0`; `0` for `t ≤ 0`): the Riesz
representative of `z ↦ C S(t) z` on `X₋₁`. -/
def obsVec (t : ℝ) : Xm1 :=
  if h : 0 < t then mkL2 (fun n => d.c n * d.wt n * Real.exp (d.lam n * t))
    (d.summable_obsVec_sq h) else 0

/-- Coordinates of the observation vector. -/
theorem obsVec_apply {t : ℝ} (ht : 0 < t) (n : ℕ) :
    d.obsVec t n = d.c n * d.wt n * Real.exp (d.lam n * t) := by
  simp only [obsVec, ht, ↓reduceDIte, mkL2_apply]

/-- The observation vector vanishes (by convention) for `t ≤ 0`. -/
theorem obsVec_of_nonpos {t : ℝ} (ht : t ≤ 0) : d.obsVec t = 0 :=
  dite_eq_right_iff.2 fun h => absurd h (not_lt.2 ht)

/-- `S(s) obsVec t = obsVec (t + s)` (`t > 0`, `s ≥ 0`). -/
theorem Sm_obsVec {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    d.Sm.real s (d.obsVec t) = d.obsVec (t + s) := by
  refine ext_Xm1 fun n => ?_
  rw [Sm_apply _ hs, obsVec_apply _ ht, obsVec_apply _ (by linarith), mul_add, Real.exp_add]
  ring

/-! ### The free output -/

/-- The free output `t ↦ C S(t) z = ⟪obsVec t, a⟫` of `z ∈ X₋₁` (coordinates `a`). -/
def obs (a : Xm1) (t : ℝ) : ℝ := ⟪d.obsVec t, a⟫_ℝ

/-- The free output as a modal series: `obs a t = ∑ₙ cₙ wₙ e^{λₙ t} aₙ` for `t > 0`. -/
theorem hasSum_obs {t : ℝ} (ht : 0 < t) (a : Xm1) :
    HasSum (fun n => d.c n * d.wt n * Real.exp (d.lam n * t) * a n) (d.obs a t) := by
  convert lp.hasSum_inner (d.obsVec t) a using 1
  · funext n
    rw [RCLike.inner_apply, conj_trivial, obsVec_apply _ ht]
    ring
  · rfl

/-- `obs a t = 0` for `t ≤ 0` (convention). -/
theorem obs_of_nonpos {t : ℝ} (ht : t ≤ 0) (a : Xm1) : d.obs a t = 0 := by
  rw [obs, obsVec_of_nonpos _ ht, inner_zero_left]

/-- `obs` is additive in `a`. -/
theorem obs_add (a b : Xm1) (t : ℝ) : d.obs (a + b) t = d.obs a t + d.obs b t :=
  inner_add_right _ _ _

/-- `obs` is homogeneous in `a`. -/
theorem obs_smul (r : ℝ) (a : Xm1) (t : ℝ) : d.obs (r • a) t = r * d.obs a t :=
  real_inner_smul_right _ _ _

/-- `obs 0 = 0`. -/
theorem obs_zero (t : ℝ) : d.obs 0 t = 0 := inner_zero_right _

/-- Cauchy–Schwarz: `|obs a t| ≤ ‖obsVec t‖ ‖a‖`. -/
theorem abs_obs_le (a : Xm1) (t : ℝ) : |d.obs a t| ≤ ‖d.obsVec t‖ * ‖a‖ :=
  abs_real_inner_le_norm _ _

/-- Time shift: `obs (S(t) a) s = obs a (s + t)`. -/
theorem obs_Sm {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (a : Xm1) :
    d.obs (d.Sm.real t a) s = d.obs a (s + t) := by
  rw [obs, obs, ← d.Sm_obsVec hs ht, ← adjoint_diagSemigroup_real,
    ContinuousLinearMap.adjoint_inner_left, adjoint_diagSemigroup_real]

/-- `‖obsVec t‖` is nonincreasing on `(0, ∞)`. -/
theorem norm_obsVec_le {t₀ t : ℝ} (h₀ : 0 < t₀) (h : t₀ ≤ t) :
    ‖d.obsVec t‖ ≤ ‖d.obsVec t₀‖ := by
  have h1 := d.Sm_obsVec h₀ (sub_nonneg.2 h)
  rw [add_sub_cancel] at h1
  rw [← h1]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (d.norm_Sm_le (t - t₀)) (norm_nonneg _))

/-- `t ↦ obsVec t` is continuous on `(0, ∞)`. -/
theorem continuousOn_obsVec : ContinuousOn d.obsVec (Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  have hev : (fun τ => d.Sm.real (τ - t / 2) (d.obsVec (t / 2))) =ᶠ[𝓝 t] d.obsVec := by
    filter_upwards [Ioi_mem_nhds (half_lt_self ht')] with τ hτ
    have hτ' : t / 2 < τ := hτ
    rw [d.Sm_obsVec (half_pos ht') (by linarith), add_sub_cancel]
  exact ((d.Sm.continuous_real_apply _).comp
    (continuous_id.sub continuous_const)).continuousAt.congr hev

/-- The free output is continuous on `(0, ∞)`. -/
theorem continuousOn_obs (a : Xm1) : ContinuousOn (d.obs a) (Ioi 0) :=
  d.continuousOn_obsVec.inner continuousOn_const

/-- The free output is measurable on subsets of `(0, ∞)`. -/
theorem aestronglyMeasurable_obs (a : Xm1) {s : Set ℝ} (hs : MeasurableSet s)
    (hsub : s ⊆ Ioi 0) : AEStronglyMeasurable (d.obs a) (volume.restrict s) :=
  ((d.continuousOn_obs a).mono hsub).aestronglyMeasurable hs

/-! ### The space `V` -/

/-- The space `V` (deviation from `eq:heat-localized-V`: scalar observation norm) as a
submodule of `X₋₁ × L²(0, 1)`: the graph of the free output, `{(a, g) : g = obs a a.e.}`. -/
def Vsub : Submodule ℝ (WithLp 2 (Xm1 × L2 ℝ 1)) where
  carrier := {p | (p.snd : ℝ → ℝ) =ᵐ[μI 1] d.obs p.fst}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq, WithLp.add_fst, WithLp.add_snd] at *
    filter_upwards [Lp.coeFn_add p.snd q.snd, hp, hq] with t h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, obs_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, WithLp.zero_fst, WithLp.zero_snd]
    filter_upwards [Lp.coeFn_zero ℝ 2 (μI 1)] with t h
    rw [h, obs_zero]; rfl
  smul_mem' := by
    intro r p hp
    simp only [Set.mem_ofPred_eq, WithLp.smul_fst, WithLp.smul_snd] at *
    filter_upwards [Lp.coeFn_smul r p.snd, hp] with t h1 h2
    rw [h1, Pi.smul_apply, h2, obs_smul]; rfl

/-- `V` is closed in `X₋₁ × L²(0, 1)`: along an `L²`-convergent sequence a subsequence converges
a.e., and `obs` is continuous in `a` for each `t`. -/
theorem isClosed_Vsub : IsClosed (d.Vsub : Set (WithLp 2 (Xm1 × L2 ℝ 1))) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hqV, hq⟩ := mem_closure_iff_seq_limit.1 hp
  have h1 : Tendsto (fun k => (q k).fst) atTop (𝓝 p.fst) :=
    ((WithLp.continuous_fst 2 Xm1 (L2 ℝ 1)).tendsto p).comp hq
  have h2 : Tendsto (fun k => (q k).snd) atTop (𝓝 p.snd) :=
    ((WithLp.continuous_snd 2 Xm1 (L2 ℝ 1)).tendsto p).comp hq
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hall : ∀ᵐ t ∂(μI 1), ∀ k, ((q k).snd : ℝ → ℝ) t = d.obs (q k).fst t :=
    ae_all_iff.2 fun k => hqV k
  show (p.snd : ℝ → ℝ) =ᵐ[μI 1] d.obs p.fst
  filter_upwards [hae, hall] with t ht1 ht2
  have h3 : Tendsto (fun k => d.obs (q (ns k)).fst t) atTop (𝓝 (d.obs p.fst t)) :=
    ((continuous_const.inner continuous_id).tendsto _).comp (h1.comp hns.tendsto_atTop)
  refine tendsto_nhds_unique ht1 ?_
  simpa only [ht2] using h3

/-- **The space `V`**: `‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀¹ |C S(t) z|² dt` (a Hilbert space). -/
abbrev V : Type := ↥d.Vsub

instance : CompleteSpace d.V := d.isClosed_Vsub.isComplete.completeSpace_coe

instance : NormedAddCommGroup d.V := inferInstance
instance : InnerProductSpace ℝ d.V := inferInstance
instance : NormedSpace ℝ d.V := inferInstance
instance : Module ℝ d.V := inferInstance

/-- The embedding `V ↪ X₋₁`. -/
def fstV : d.V →L[ℝ] Xm1 := (WithLp.fstL 2 ℝ Xm1 (L2 ℝ 1)).comp d.Vsub.subtypeL

/-- The free output `V → L²(0, 1)`. -/
def sndV : d.V →L[ℝ] L2 ℝ 1 := (WithLp.sndL 2 ℝ Xm1 (L2 ℝ 1)).comp d.Vsub.subtypeL

/-- The first projection of `V`. -/
theorem fstV_apply (v : d.V) : d.fstV v = (v : WithLp 2 (Xm1 × L2 ℝ 1)).fst := rfl

/-- The second projection of `V`. -/
theorem sndV_apply (v : d.V) : d.sndV v = (v : WithLp 2 (Xm1 × L2 ℝ 1)).snd := rfl

/-- The second component of `v ∈ V` is the free output of its first component. -/
theorem sndV_ae (v : d.V) : (d.sndV v : ℝ → ℝ) =ᵐ[μI 1] d.obs (d.fstV v) := v.2

/-- The free output of `v ∈ V` is square integrable on `(0, 1]`. -/
theorem memLp_obs (v : d.V) : MemLp (d.obs (d.fstV v)) 2 (μI 1) :=
  (Lp.memLp _).ae_eq (d.sndV_ae v)

/-- Elements of `V` are determined by their `X₋₁` component. -/
theorem V_ext {v w : d.V} (h : d.fstV v = d.fstV w) : v = w := by
  have h2 : d.sndV v = d.sndV w := Lp.ext ((d.sndV_ae v).trans (h ▸ (d.sndV_ae w).symm))
  apply Subtype.ext
  exact (WithLp.ext_iff 2).2 (Prod.ext h h2)

/-- `‖v‖²_V = ‖a‖²_{X₋₁} + ∫₀¹ |obs a|²`. -/
theorem norm_V_sq (v : d.V) : ‖v‖ ^ 2 = ‖d.fstV v‖ ^ 2 + ‖d.sndV v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- `‖v‖_V ≤ ‖a‖_{X₋₁} + ‖obs a‖_{L²(0,1)}`. -/
theorem norm_V_le (v : d.V) : ‖v‖ ≤ ‖d.fstV v‖ + ‖d.sndV v‖ := by
  nlinarith [d.norm_V_sq v, norm_nonneg v, norm_nonneg (d.fstV v), norm_nonneg (d.sndV v)]

/-- The element `(a, obs a)` of `V`, for `a ∈ X₋₁` with square-integrable free output. -/
def mkV (a : Xm1) (ha : MemLp (d.obs a) 2 (μI 1)) : d.V :=
  ⟨WithLp.toLp 2 (a, ha.toLp _), ha.coeFn_toLp⟩

/-- First component of `mkV`. -/
@[simp] theorem fstV_mkV (a : Xm1) (ha : MemLp (d.obs a) 2 (μI 1)) : d.fstV (d.mkV a ha) = a :=
  rfl

/-- Second component of `mkV`. -/
theorem sndV_mkV (a : Xm1) (ha : MemLp (d.obs a) 2 (μI 1)) :
    d.sndV (d.mkV a ha) = ha.toLp _ := rfl

/-- Every `v ∈ V` is `mkV` of its first component. -/
theorem mkV_fstV (v : d.V) : d.mkV (d.fstV v) (d.memLp_obs v) = v := d.V_ext rfl

/-- The free output of an element of `V` is square integrable on every `(0, R]`. -/
theorem memLp_obs_Ioc (v : d.V) (R : ℝ) : MemLp (d.obs (d.fstV v)) 2 (μI R) := by
  by_cases hR : R ≤ 1
  · exact (d.memLp_obs v).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hR) le_rfl)
  · push Not at hR
    have hU : μI R = μI 1 + volume.restrict (Ioc 1 R) := by
      show volume.restrict (Ioc 0 R) = volume.restrict (Ioc 0 1) + volume.restrict (Ioc 1 R)
      rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hR.le, Measure.restrict_union _ measurableSet_Ioc]
      exact Set.disjoint_left.2 fun x h1 h2 => absurd h1.2 (not_le.2 h2.1)
    rw [hU]
    refine (d.memLp_obs v).add_measure ?_
    have : IsFiniteMeasure (volume.restrict (Ioc (1 : ℝ) R)) :=
      isFiniteMeasure_restrict.2 (by simp)
    refine MemLp.of_bound (d.aestronglyMeasurable_obs _ measurableSet_Ioc
      (fun t ht => lt_trans one_pos ht.1)) (‖d.obsVec 1‖ * ‖d.fstV v‖) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact (d.abs_obs_le _ _).trans
      (mul_le_mul_of_nonneg_right (d.norm_obsVec_le one_pos ht.1.le) (norm_nonneg _))

/-- `S(t)` maps `V` into `V`: the free output of `S(t) a` is `obs a (t + ·)`. -/
theorem memLp_obs_Sm (v : d.V) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (d.obs (d.Sm.real t (d.fstV v))) 2 (μI 1) := by
  have h := memLp_comp_add (d.memLp_obs_Ioc v (t + 1)) ht le_rfl
  refine MemLp.ae_eq ?_ h
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  rw [d.obs_Sm hs.1 ht, add_comm]

/-- Closed graph: a linear map into `V` whose first component is continuous is continuous. -/
theorem continuous_of_fstV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (L : E →ₗ[ℝ] d.V) (M : E →L[ℝ] Xm1) (h : ∀ x, d.fstV (L x) = M x) :
    Continuous L := by
  refine L.continuous_of_seq_closed_graph fun u x y hu hy => d.V_ext ?_
  rw [h]
  have h1 : Tendsto (fun n => d.fstV (L (u n))) atTop (𝓝 (d.fstV y)) :=
    (d.fstV.continuous.tendsto _).comp hy
  have h2 : Tendsto (fun n => M (u n)) atTop (𝓝 (M x)) := (M.continuous.tendsto _).comp hu
  simp only [h] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### The semigroup on `V` -/

/-- The semigroup on `V`, as a linear map: `(a, g) ↦ (S(t) a, obs a (t + ·))`. -/
def SVlin (t : ℝ≥0) : d.V →ₗ[ℝ] d.V where
  toFun v := d.mkV (d.Sm.real t (d.fstV v)) (d.memLp_obs_Sm v t.coe_nonneg)
  map_add' v w := d.V_ext (by simp)
  map_smul' r v := d.V_ext (by simp)

/-- The semigroup on `V`, as a bounded operator (`continuous_of_fstV`). -/
def SVop (t : ℝ≥0) : d.V →L[ℝ] d.V :=
  ⟨d.SVlin t, d.continuous_of_fstV (d.SVlin t) ((d.Sm.real t).comp d.fstV) fun _ => rfl⟩

/-- First component of `S_V(t)`. -/
theorem fstV_SVop (t : ℝ≥0) (v : d.V) : d.fstV (d.SVop t v) = d.Sm.real t (d.fstV v) := rfl

/-- Second component of `S_V(t) v`: the window `obs a (t + ·)`. -/
theorem sndV_SVop (t : ℝ≥0) (v : d.V) :
    d.sndV (d.SVop t v) = window 1 (d.obs (d.fstV v)) t := by
  refine Lp.ext ((d.sndV_ae _).trans ?_)
  refine EventuallyEq.trans ?_
    (coeFn_window_of_memLp (T := 1) (d.memLp_obs_Ioc v (t + 1)) t.coe_nonneg le_rfl).symm
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
  rw [fstV_SVop, d.obs_Sm hs.1 t.coe_nonneg, add_comm]

/-- The second component of `v` is the window `obs a (0 + ·)`. -/
theorem sndV_eq_window (v : d.V) : d.sndV v = window 1 (d.obs (d.fstV v)) 0 := by
  refine Lp.ext ((d.sndV_ae v).trans ?_)
  refine EventuallyEq.trans ?_
    (coeFn_window_of_memLp (T := 1) (d.memLp_obs v) le_rfl (by norm_num)).symm
  exact Eventually.of_forall fun s => by simp

/-- Strong continuity of `S_V` at `0` (continuity of translation in `L²`). -/
theorem tendsto_SVop (v : d.V) : Tendsto (fun t => d.SVop t v) (𝓝 0) (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝 0) (𝓝[Icc 0 1] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using NNReal.continuous_coe.tendsto 0, ?_⟩
    filter_upwards [eventually_le_nhds (zero_lt_one' ℝ≥0)] with t ht
    exact ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have h1 : Tendsto (fun t : ℝ≥0 => d.fstV (d.SVop t v) - d.fstV v) (𝓝 0) (𝓝 0) := by
    have := ((d.Sm.continuous_real_apply (d.fstV v)).tendsto 0).comp
      (NNReal.continuous_coe.tendsto 0)
    simp only [C0Semigroup.real_zero, one_apply_eq_self] at this
    simpa [fstV_SVop] using this.sub_const (d.fstV v)
  have h2 : Tendsto (fun t : ℝ≥0 => d.sndV (d.SVop t v) - d.sndV v) (𝓝 0) (𝓝 0) := by
    have hw := ((continuousOn_window (T := 1) (T' := 1) (d.memLp_obs_Ioc v (1 + 1)))
      0 ⟨le_rfl, zero_le_one⟩).tendsto.comp hc
    simp only [sndV_SVop, d.sndV_eq_window v]
    simpa using hw.sub_const (window 1 (d.obs (d.fstV v)) 0)
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_)
    (by simpa using (h1.norm.add h2.norm))
  refine (d.norm_V_le _).trans (le_of_eq ?_)
  rw [map_sub, map_sub]

/-- **The semigroup `S_V` on `V`** (`app:boundary-heat-informative`). -/
def SV : C0Semigroup ℝ d.V :=
  C0Semigroup.ofTendsto d.SVop
    (ContinuousLinearMap.ext fun v => d.V_ext (by simp [fstV_SVop]))
    (fun s t => ContinuousLinearMap.ext fun v => d.V_ext (by
      simp only [fstV_SVop, ContinuousLinearMap.comp_apply, NNReal.coe_add]
      exact d.Sm.real_add_apply s.coe_nonneg t.coe_nonneg _))
    d.tendsto_SVop

/-- `S_V(t)` is `SVop t`. -/
theorem SV_apply (t : ℝ≥0) : d.SV t = d.SVop t := C0Semigroup.ofTendsto_apply _ _ _ _ _

/-- `S_V` acts as `S_{X₋₁}` on the first component. -/
theorem fstV_SV (t : ℝ≥0) (v : d.V) : d.fstV (d.SV t v) = d.Sm.real t (d.fstV v) := by
  rw [SV_apply]; rfl

/-- `S_V` acts as `S_{X₋₁}` on the first component (real times). -/
theorem fstV_SV_real {t : ℝ} (ht : 0 ≤ t) (v : d.V) :
    d.fstV (d.SV.real t v) = d.Sm.real t (d.fstV v) := by
  show d.fstV (d.SV t.toNNReal v) = _
  rw [fstV_SV, Real.coe_toNNReal t ht]

/-- `V ↪ X₋₁` is consistent with the semigroups. -/
theorem consistent_fstV : C0Semigroup.Consistent d.fstV d.SV d.Sm := fun t v => by
  rw [fstV_SV, C0Semigroup.real_coe]

end ModalData


/-- `∫₀ᵀ e^{-y s} ds ≤ (T + 1)/(1 + y)` for `y, T ≥ 0`. -/
theorem setIntegral_exp_neg_mul_le {y T : ℝ} (hy : 0 ≤ y) (hT : 0 ≤ T) :
    ∫ s in Ioc 0 T, Real.exp (-(y * s)) ≤ (T + 1) / (1 + y) := by
  set I := ∫ s in Ioc 0 T, Real.exp (-(y * s)) with hI
  have hc : Continuous fun s : ℝ => Real.exp (-(y * s)) := by fun_prop
  have h1 : I ≤ T := by
    calc I ≤ ∫ _ in Ioc 0 T, (1 : ℝ) :=
          setIntegral_mono_on hc.integrableOn_Ioc (integrableOn_const (by simp))
            measurableSet_Ioc fun s hs => by
              rw [Real.exp_le_one_iff]; nlinarith [hs.1]
      _ = T := by simp [hT]
  have h2 : y * I = 1 - Real.exp (-(y * T)) := by
    rw [hI, ← integral_const_mul, ← intervalIntegral.integral_of_le hT,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s => -Real.exp (-(y * s))) (f' := fun s => y * Real.exp (-(y * s)))
        (fun s _ => ?_)
        ((by fun_prop : Continuous fun s => y * Real.exp (-(y * s))).intervalIntegrable _ _)]
    · simp; ring
    · have h1 : HasDerivAt (fun s => -(y * s)) (-y) s := by
        simpa using (hasDerivAt_id' s).const_mul (-y)
      have := h1.exp.neg
      convert this using 1
      ring
  have h3 : y * I ≤ 1 := by rw [h2]; linarith [Real.exp_pos (-(y * T))]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

namespace ModalData

variable (d : ModalData)

/-- `|1/wₙ| ≤ 1`. -/
theorem abs_inv_wt_le (n : ℕ) : |(d.wt n)⁻¹| ≤ 1 := by
  rw [abs_inv, abs_of_pos (d.wt_pos n)]
  exact inv_le_one_of_one_le₀ (d.one_le_wt n)

/-- `∑ₙ e^{λₙ t} < ∞` for `t > 0`. -/
theorem summable_exp {t : ℝ} (ht : 0 < t) : Summable fun n => Real.exp (d.lam n * t) := by
  refine (d.summable_inv_wt.mul_left (Real.exp t / t)).of_nonneg_of_le
    (fun n => (Real.exp_pos _).le) (fun n => ?_)
  have h := d.wt_pow_mul_exp_le 1 ht n
  have hw := d.wt_pos n
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
  show Real.exp (d.lam n * t) ≤ Real.exp t / t * (d.wt n)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_comm]
  exact h

/-- `∫₀¹ e^{λₙ t} e^{λₘ t} dt ≤ 2 / wₘ`. -/
theorem lintegral_exp_mul_exp_le (n m : ℕ) :
    ∫⁻ t in Ioc 0 1, ENNReal.ofReal (Real.exp (d.lam n * t) * Real.exp (d.lam m * t)) ≤
      ENNReal.ofReal (2 / d.wt m) := by
  set y := -(d.lam n + d.lam m) with hy
  have hy0 : 0 ≤ y := by linarith [d.lam_nonpos n, d.lam_nonpos m]
  have he : ∀ t, Real.exp (d.lam n * t) * Real.exp (d.lam m * t) = Real.exp (-(y * t)) := by
    intro t; rw [← Real.exp_add]; congr 1; rw [hy]; ring
  simp only [he]
  have hc : Continuous fun s : ℝ => Real.exp (-(y * s)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Ioc
    (Eventually.of_forall fun t => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ((setIntegral_exp_neg_mul_le hy0 zero_le_one).trans ?_)
  have hw := d.wt_pos m
  rw [show (1 : ℝ) + 1 = 2 by norm_num]
  refine div_le_div_of_nonneg_left (by norm_num) hw ?_
  unfold wt; rw [hy]; linarith [d.lam_nonpos n]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (e : HilbertBasis ℕ ℝ X)

/-- The embedding `X ↪ X₋₁`, `x ↦ (⟪eₙ, x⟫ / wₙ)ₙ`. -/
def toXm1 : X →L[ℝ] Xm1 := Diagonal.diagMap e stdBasis (fun n => (d.wt n)⁻¹) 1 d.abs_inv_wt_le

/-- Coordinates of `X ↪ X₋₁`: `(toXm1 x)ₙ = ⟪eₙ, x⟫ / wₙ`. -/
theorem toXm1_apply (x : X) (n : ℕ) : d.toXm1 e x n = (d.wt n)⁻¹ * ⟪e n, x⟫_ℝ := by
  rw [← inner_stdBasis, toXm1, Diagonal.inner_diagMap]

/-- The free output of `x ∈ X`: `C S(t) x = ∑ₙ cₙ e^{λₙ t} ⟪eₙ, x⟫` for `t > 0`. -/
theorem hasSum_obs_toXm1 {t : ℝ} (ht : 0 < t) (x : X) :
    HasSum (fun n => d.c n * Real.exp (d.lam n * t) * ⟪e n, x⟫_ℝ) (d.obs (d.toXm1 e x) t) := by
  convert d.hasSum_obs ht (d.toXm1 e x) using 1
  funext n
  rw [toXm1_apply]
  field_simp [(d.wt_pos n).ne']

/-- **`X ↪ V`**: the free output of `x ∈ X` is square integrable on `(0, 1]` (Schur test with
`∑ₘ 1/wₘ < ∞`). -/
theorem memLp_obs_toXm1 (x : X) : MemLp (d.obs (d.toXm1 e x)) 2 (μI 1) := by
  obtain ⟨K, hK⟩ := d.exists_abs_c_le
  set xs : ℕ → ℝ := fun n => ⟪e n, x⟫_ℝ with hxs
  have hxs2 : Summable fun n => xs n ^ 2 := Diagonal.summable_inner_sq e x
  have haS : ∀ {t : ℝ}, 0 < t → Summable fun n => |xs n| * Real.exp (d.lam n * t) := by
    intro t ht
    refine (hxs2.add (d.summable_exp (by linarith : 0 < 2 * t))).of_nonneg_of_le
      (fun n => by positivity) (fun n => ?_)
    have h2 : Real.exp (d.lam n * (2 * t)) = Real.exp (d.lam n * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2, ← sq_abs (xs n)]
    nlinarith [two_mul_le_add_sq |xs n| (Real.exp (d.lam n * t)), abs_nonneg (xs n),
      Real.exp_pos (d.lam n * t)]
  have hmeas : AEStronglyMeasurable (d.obs (d.toXm1 e x)) (μI 1) :=
    d.aestronglyMeasurable_obs _ measurableSet_Ioc (fun t ht => ht.1)
  rw [memLp_two_iff_integrable_sq hmeas]
  refine ⟨hmeas.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun t => sq_nonneg _)]
  set F : ℕ → ℕ → ℝ → ℝ≥0∞ := fun n m t =>
    ENNReal.ofReal (xs n ^ 2 * (Real.exp (d.lam n * t) * Real.exp (d.lam m * t))) +
      ENNReal.ofReal (xs m ^ 2 * (Real.exp (d.lam n * t) * Real.exp (d.lam m * t))) with hF
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (d.obs (d.toXm1 e x) t ^ 2) ≤
      ENNReal.ofReal (K ^ 2) * ∑' n, ∑' m, F n m t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    set G := ∑' n, |xs n| * Real.exp (d.lam n * t) with hG
    have hG0 : 0 ≤ G := tsum_nonneg fun n => by positivity
    have hS := ((haS ht0).hasSum).mul_left K
    have hf := d.hasSum_obs_toXm1 e ht0 x
    have hle : ∀ n, |d.c n * Real.exp (d.lam n * t) * xs n| ≤
        K * (|xs n| * Real.exp (d.lam n * t)) := by
      intro n
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |d.c n| * Real.exp (d.lam n * t) * |xs n|
          = |d.c n| * (|xs n| * Real.exp (d.lam n * t)) := by ring
        _ ≤ K * (|xs n| * Real.exp (d.lam n * t)) :=
          mul_le_mul_of_nonneg_right (hK n) (by positivity)
    have habs : |d.obs (d.toXm1 e x) t| ≤ K * G := by
      refine abs_le.2 ⟨?_, ?_⟩
      · have := hasSum_le (fun n => (neg_abs_le _).trans' (neg_le_neg (hle n))) hS.neg hf
        linarith
      · exact hasSum_le (fun n => (le_abs_self _).trans (hle n)) hf hS
    have hsq : d.obs (d.toXm1 e x) t ^ 2 ≤ K ^ 2 * G ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine (ENNReal.ofReal_le_ofReal hsq).trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hG0, hG,
      ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (haS ht0)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sq, ← ENNReal.tsum_mul_right]
    gcongr with n
    rw [← ENNReal.tsum_mul_left]
    gcongr with m
    rw [← ENNReal.ofReal_mul (by positivity), hF]
    dsimp only
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := two_mul_le_add_sq |xs n| |xs m|
    have h2 : 0 ≤ Real.exp (d.lam n * t) * Real.exp (d.lam m * t) := by positivity
    rw [sq_abs, sq_abs] at h1
    nlinarith [abs_nonneg (xs n), abs_nonneg (xs m)]
  have hFm : ∀ n m, Measurable (F n m) := fun n m => by
    simp only [hF]
    exact ((by fun_prop : Continuous fun t : ℝ => xs n ^ 2 *
      (Real.exp (d.lam n * t) * Real.exp (d.lam m * t))).measurable.ennreal_ofReal).add
      ((by fun_prop : Continuous fun t : ℝ => xs m ^ 2 *
      (Real.exp (d.lam n * t) * Real.exp (d.lam m * t))).measurable.ennreal_ofReal)
  have hint : ∀ n m, ∫⁻ t in Ioc 0 1, F n m t ≤
      ENNReal.ofReal (xs n ^ 2) * ENNReal.ofReal (2 / d.wt m) +
        ENNReal.ofReal (xs m ^ 2) * ENNReal.ofReal (2 / d.wt n) := by
    intro n m
    simp only [hF]
    rw [lintegral_add_left ((by fun_prop : Continuous fun t : ℝ => xs n ^ 2 *
      (Real.exp (d.lam n * t) * Real.exp (d.lam m * t))).measurable.ennreal_ofReal)]
    simp only [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    · exact d.lintegral_exp_mul_exp_le n m
    · have := d.lintegral_exp_mul_exp_le m n
      simp only [mul_comm (Real.exp (d.lam m * _))] at this
      exact this
  have hA : ∑' n, ENNReal.ofReal (xs n ^ 2) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hxs2]; exact ENNReal.ofReal_ne_top
  have hB : ∑' n, ENNReal.ofReal (2 / d.wt n) ≠ ⊤ := by
    have hs2 : Summable fun n => 2 / d.wt n :=
      (d.summable_inv_wt.mul_left 2).congr fun n => by simp only [wt, div_eq_mul_inv]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := d.wt_pos n; positivity) hs2]
    exact ENNReal.ofReal_ne_top
  calc ∫⁻ t in Ioc 0 1, ENNReal.ofReal (d.obs (d.toXm1 e x) t ^ 2)
      ≤ ∫⁻ t in Ioc 0 1, ENNReal.ofReal (K ^ 2) * ∑' n, ∑' m, F n m t :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (K ^ 2) * ∑' n, ∑' m, ∫⁻ t in Ioc 0 1, F n m t := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_tsum fun n => (Measurable.tsum fun m => hFm n m).aemeasurable]
        congr 1
        refine tsum_congr fun n => ?_
        exact lintegral_tsum fun m => (hFm n m).aemeasurable
    _ ≤ ENNReal.ofReal (K ^ 2) * ∑' n, ∑' m, (ENNReal.ofReal (xs n ^ 2) *
          ENNReal.ofReal (2 / d.wt m) +
            ENNReal.ofReal (xs m ^ 2) * ENNReal.ofReal (2 / d.wt n)) := by
        gcongr with n m
        exact hint n m
    _ = ENNReal.ofReal (K ^ 2) * (2 * ((∑' n, ENNReal.ofReal (xs n ^ 2)) *
          ∑' n, ENNReal.ofReal (2 / d.wt n))) := by
        congr 1
        simp only [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
        rw [two_mul]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (by simp) ?_)
        exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hA) (lt_top_iff_ne_top.2 hB)


/-- The embedding `X ↪ V`, as a linear map. -/
def ιVlin : X →ₗ[ℝ] d.V where
  toFun x := d.mkV (d.toXm1 e x) (d.memLp_obs_toXm1 e x)
  map_add' x y := d.V_ext (by simp)
  map_smul' r x := d.V_ext (by simp)

/-- **The embedding `X ↪ V`**, `x ↦ (x, C S(·) x)` (bounded by the closed graph theorem). -/
def ιV : X →L[ℝ] d.V :=
  ⟨d.ιVlin e, d.continuous_of_fstV (d.ιVlin e) (d.toXm1 e) fun _ => rfl⟩

/-- The `X₋₁` component of `ιV x`. -/
@[simp] theorem fstV_ιV (x : X) : d.fstV (d.ιV e x) = d.toXm1 e x := rfl

omit [CompleteSpace X] in
/-- `X ↪ X₋₁` is injective. -/
theorem toXm1_injective : Function.Injective (d.toXm1 e) :=
  Diagonal.injective_diagMap e stdBasis d.abs_inv_wt_le fun n => inv_ne_zero (d.wt_pos n).ne'

/-- `V ↪ X₋₁` is injective. -/
theorem fstV_injective : Function.Injective d.fstV := fun _ _ h => d.V_ext h

/-- `X ↪ V` is injective. -/
theorem ιV_injective : Function.Injective (d.ιV e) := fun x y h =>
  d.toXm1_injective e (by simpa using congrArg d.fstV h)

/-- The state-space semigroup `S_X`, diagonal in `e`. -/
abbrev SX : C0Semigroup ℝ X := diagSemigroup e d.lam d.bddAbove_lam

/-- `X ↪ X₋₁` is consistent with the semigroups. -/
theorem consistent_toXm1 : C0Semigroup.Consistent (d.toXm1 e) (d.SX e) d.Sm :=
  Diagonal.consistent_diagMap e stdBasis d.abs_inv_wt_le d.lam d.bddAbove_lam

/-- `X ↪ V` is consistent with the semigroups. -/
theorem consistent_ιV : C0Semigroup.Consistent (d.ιV e) (d.SX e) d.SV := fun t x =>
  d.V_ext (by rw [fstV_ιV, fstV_SV, fstV_ιV, C0Semigroup.real_coe, d.consistent_toXm1 e t x])

/-- The smoothing `S(s) : X₋₁ → X`, `a ↦ ∑ₙ wₙ e^{λₙ s} aₙ eₙ` (`s > 0`). -/
def smoothing {s : ℝ} (hs : 0 < s) : Xm1 →L[ℝ] X :=
  Diagonal.diagMap stdBasis e (fun n => d.wt n * Real.exp (d.lam n * s)) (Real.exp s / s)
    fun n => by
      have h := d.wt_pow_mul_exp_le 1 hs n
      simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at h
      rw [abs_of_pos (mul_pos (d.wt_pos n) (Real.exp_pos _))]
      exact h

/-- `smoothing s a` is `S(s) a`, read in `X`. -/
theorem toXm1_smoothing {s : ℝ} (hs : 0 < s) (a : Xm1) :
    d.toXm1 e (d.smoothing e hs a) = d.Sm.real s a := by
  refine ext_Xm1 fun n => ?_
  rw [toXm1_apply, smoothing, Diagonal.inner_diagMap, inner_stdBasis, Sm_apply _ hs.le]
  field_simp [(d.wt_pos n).ne']

/-- `S_V(s) v ∈ X` for `s > 0`. -/
theorem ιV_smoothing {s : ℝ} (hs : 0 < s) (v : d.V) :
    d.ιV e (d.smoothing e hs (d.fstV v)) = d.SV.real s v :=
  d.V_ext (by rw [fstV_ιV, toXm1_smoothing, fstV_SV_real _ hs.le])

/-- `X` is dense in `V`. -/
theorem denseRange_ιV : DenseRange (d.ιV e) := by
  intro v
  have hT : Tendsto (fun s : ℝ => d.SV.real s v) (𝓝[>] 0) (𝓝 v) := by
    have := (d.SV.continuous_real_apply v).tendsto 0
    simp only [C0Semigroup.real_zero, one_apply_eq_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ⟨_, d.ιV_smoothing e hs v⟩

/-! ### The space `W = D(A_V)` -/

/-- The generator of `S_V` acts diagonally on the first component. -/
theorem fstV_generator (v : d.SV.generator.domain) (n : ℕ) :
    d.fstV (d.SV.generator v) n = d.lam n * d.fstV v n := by
  have h := d.consistent_fstV.generator_apply d.Sm v.2
  rw [← inner_stdBasis, ← h, inner_generator_diag, inner_stdBasis]

/-- **The space `W = D(A_V)`** with the graph norm (`app:boundary-heat-informative`). -/
abbrev W : Type := d.SV.Dom

instance : NormedAddCommGroup d.W := inferInstance
instance : InnerProductSpace ℝ d.W := inferInstance
instance : NormedSpace ℝ d.W := inferInstance
instance : Module ℝ d.W := inferInstance
instance : CompleteSpace d.W := inferInstance

/-- The isometry `ℓ² → X`, `a ↦ ∑ₙ aₙ eₙ`. -/
def toX : Xm1 →L[ℝ] X := Diagonal.diagMap stdBasis e (fun _ => 1) 1 fun _ => by simp

/-- **`W ↪ X`**: `w ↦ ∑ wₙ aₙ eₙ`, where `a` is the `X₋₁` component of `w`
(`(1 - A_{-1}) a`). -/
def ιW : d.W →L[ℝ] X :=
  (toX e).comp (d.fstV.comp d.SV.domIncl - d.fstV.comp d.SV.domGen)

/-- Coordinates of `ι_W w`: `wₙ aₙ`, where `a` is the `X₋₁` component of `w`. -/
theorem inner_ιW (w : d.W) (n : ℕ) :
    ⟪e n, d.ιW e w⟫_ℝ = d.wt n * d.fstV (d.SV.domIncl w) n := by
  rw [ιW, ContinuousLinearMap.comp_apply, toX, Diagonal.inner_diagMap, inner_stdBasis,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← d.SV.generator_domIncl w, lp.coeFn_sub, Pi.sub_apply,
    fstV_generator]
  unfold wt; ring

/-- `ι_W w` read in `X₋₁` is the first component of `w`. -/
theorem toXm1_ιW (w : d.W) : d.toXm1 e (d.ιW e w) = d.fstV (d.SV.domIncl w) := by
  refine ext_Xm1 fun n => ?_
  rw [toXm1_apply, inner_ιW]
  field_simp [(d.wt_pos n).ne']

/-- `ιV ∘ ιW` is the inclusion `W = D(A_V) ↪ V`. -/
theorem ιV_ιW (w : d.W) : d.ιV e (d.ιW e w) = d.SV.domIncl w :=
  d.V_ext (by rw [fstV_ιV, d.toXm1_ιW e w])

/-- `W ↪ X` is injective. -/
theorem ιW_injective : Function.Injective (d.ιW e) := fun w w' h =>
  d.SV.domIncl_injective (by rw [← d.ιV_ιW e w, h, d.ιV_ιW e w'])

/-- The semigroup restricted to `W`. -/
abbrev SW : C0Semigroup ℝ d.W := d.SV.domSemigroup

/-- `W ↪ X` is consistent with the semigroups. -/
theorem consistent_ιW : C0Semigroup.Consistent (d.ιW e) d.SW (d.SX e) := fun t w =>
  d.ιV_injective e (by
    rw [ιV_ιW, d.consistent_ιV e, ιV_ιW, C0Semigroup.domIncl_domSemigroup])

/-- `W ↪ V` is consistent with the semigroups. -/
theorem consistent_ιWV : C0Semigroup.Consistent ((d.ιV e).comp (d.ιW e)) d.SW d.SV :=
  (d.consistent_ιV e).comp (d.consistent_ιW e)

/-- `D(A) ⊆ W`: the image of `x ∈ D(A)`. -/
theorem exists_ιW_eq {x : X} (hx : x ∈ (d.SX e).generator.domain) : ∃ w : d.W, d.ιW e w = x := by
  obtain ⟨w, hw⟩ := d.SV.exists_domIncl_eq ((d.consistent_ιV e).mem_generator_domain d.SV hx)
  exact ⟨w, d.ιV_injective e (by rw [ιV_ιW, hw])⟩

/-- `W` is dense in `X` (it contains `D(A)`). -/
theorem denseRange_ιW : DenseRange (d.ιW e) :=
  (d.SX e).dense_generator_domain.mono fun _ hx => d.exists_ιW_eq e hx

/-- The extension `A_{X,-1} : X → X₋₁` of `A`, `x ↦ (λₙ ⟪eₙ, x⟫ / wₙ)ₙ`. -/
def genXm1 : X →L[ℝ] Xm1 :=
  Diagonal.diagMap e stdBasis (fun n => d.lam n / d.wt n) 1 fun n => by
    rw [abs_div, abs_of_pos (d.wt_pos n), div_le_one (d.wt_pos n)]
    exact d.abs_lam_le_wt n

/-- Coordinates of `A_{X,-1} x`: `λₙ ⟪eₙ, x⟫ / wₙ`. -/
theorem genXm1_apply (x : X) (n : ℕ) : d.genXm1 e x n = d.lam n / d.wt n * ⟪e n, x⟫_ℝ := by
  rw [← inner_stdBasis, genXm1, Diagonal.inner_diagMap]

/-- `X ⊆ D(A_{X₋₁})`. -/
theorem toXm1_mem_generator_domain (x : X) : d.toXm1 e x ∈ d.Sm.generator.domain := by
  rw [mem_generator_domain_diag_iff]
  refine (Diagonal.summable_inner_sq e x).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  rw [inner_stdBasis, toXm1_apply, ← sq_abs, ← sq_abs ⟪e n, x⟫_ℝ]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  rw [abs_mul, abs_mul, ← mul_assoc]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [abs_inv, abs_of_pos (d.wt_pos n), ← div_eq_mul_inv, div_le_one (d.wt_pos n)]
  exact d.abs_lam_le_wt n

/-- `A_{X₋₁} x = A_{X,-1} x` for `x ∈ X`. -/
theorem Sm_generator_toXm1 (x : X) :
    d.Sm.generator ⟨d.toXm1 e x, d.toXm1_mem_generator_domain e x⟩ = d.genXm1 e x := by
  refine ext_Xm1 fun n => ?_
  rw [← inner_stdBasis, inner_generator_diag, inner_stdBasis, toXm1_apply, genXm1_apply]
  ring

/-- **`eq:heat-W-domain`**: `x ∈ X` lies in `W = D(A_V)` iff `A_{X,-1} x ∈ V`, i.e. iff the free
output of `A_{X,-1} x` is square integrable on `(0, 1]`. -/
theorem mem_SV_generator_domain_iff (x : X) :
    d.ιV e x ∈ d.SV.generator.domain ↔ MemLp (d.obs (d.genXm1 e x)) 2 (μI 1) := by
  constructor
  · intro h
    have h1 := d.consistent_fstV.generator_apply d.Sm h
    have h2 : d.fstV (d.SV.generator ⟨d.ιV e x, h⟩) = d.genXm1 e x := by
      rw [← h1]; exact d.Sm_generator_toXm1 e x
    rw [← h2]
    exact d.memLp_obs _
  · intro h
    obtain ⟨hv, -⟩ := d.consistent_fstV.exists_mem_generator_domain d.fstV_injective
      (v := d.ιV e x) (g := d.mkV (d.genXm1 e x) h) (d.toXm1_mem_generator_domain e x)
      (d.Sm_generator_toXm1 e x)
    exact hv

/-- **`eq:heat-W-domain`**, the generator: `A_V x = A_{X,-1} x` for `x ∈ W`. -/
theorem SV_generator_ιV (x : X) (h : MemLp (d.obs (d.genXm1 e x)) 2 (μI 1)) :
    d.SV.generator ⟨d.ιV e x, (d.mem_SV_generator_domain_iff e x).2 h⟩ =
      d.mkV (d.genXm1 e x) h := by
  obtain ⟨hv, h2⟩ := d.consistent_fstV.exists_mem_generator_domain d.fstV_injective
    (v := d.ιV e x) (g := d.mkV (d.genXm1 e x) h) (d.toXm1_mem_generator_domain e x)
    (d.Sm_generator_toXm1 e x)
  exact h2

/-- The components of `w ∈ W` in terms of `x = ι_W w`: `w = (x, A_{X,-1} x)`. -/
theorem fstV_domGen (w : d.W) : d.fstV (d.SV.domGen w) = d.genXm1 e (d.ιW e w) := by
  refine ext_Xm1 fun n => ?_
  rw [← d.SV.generator_domIncl w, fstV_generator, genXm1_apply, inner_ιW]
  field_simp [(d.wt_pos n).ne']

/-- **`eq:heat-W-domain`** as a set: `W = {x ∈ X : A_{X,-1} x ∈ V}`. -/
theorem range_ιW : Set.range (d.ιW e) = {x | MemLp (d.obs (d.genXm1 e x)) 2 (μI 1)} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_ofPred_eq, ← d.mem_SV_generator_domain_iff, ιV_ιW]
    exact d.SV.domIncl_mem w
  · intro h
    obtain ⟨w, hw⟩ := d.SV.exists_domIncl_eq ((d.mem_SV_generator_domain_iff e x).2 h)
    exact ⟨w, d.ιV_injective e (by rw [ιV_ιW, hw])⟩

/-- The free output of `A_{X,-1} x`: `∑ₙ cₙ λₙ e^{λₙ t} ⟪eₙ, x⟫` for `t > 0`. -/
theorem hasSum_obs_genXm1 {t : ℝ} (ht : 0 < t) (x : X) :
    HasSum (fun n => d.c n * d.lam n * Real.exp (d.lam n * t) * ⟪e n, x⟫_ℝ)
      (d.obs (d.genXm1 e x) t) := by
  convert d.hasSum_obs ht (d.genXm1 e x) using 1
  funext n
  rw [genXm1_apply]
  field_simp [(d.wt_pos n).ne']

/-- The first graph component of `w ∈ W` is `ι_W w` read in `V`. -/
theorem domIncl_eq_ιV (w : d.W) : d.SV.domIncl w = d.ιV e (d.ιW e w) := (d.ιV_ιW e w).symm

/-- The free output of `ι_W w` is the second component of `w ∈ V`. -/
theorem sndV_domIncl_ae (w : d.W) :
    (d.sndV (d.SV.domIncl w) : ℝ → ℝ) =ᵐ[μI 1] d.obs (d.toXm1 e (d.ιW e w)) := by
  rw [toXm1_ιW]; exact d.sndV_ae _

/-- The free output of `A_{X,-1} ι_W w` is the second component of `A_V w ∈ V`. -/
theorem sndV_domGen_ae (w : d.W) :
    (d.sndV (d.SV.domGen w) : ℝ → ℝ) =ᵐ[μI 1] d.obs (d.genXm1 e (d.ιW e w)) := by
  rw [← fstV_domGen]; exact d.sndV_ae _

end ModalData

end BoundaryHeat

end DataDrivenControl
