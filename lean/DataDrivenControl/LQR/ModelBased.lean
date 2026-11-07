module

public import DataDrivenControl.System.Mild
public import DataDrivenControl.Analysis.Quadratic

/-!
# The model-based regulator

Paper: `eq:lqr-cost`, `thm:lqr-riccati` (Pritchard–Salamon, Thm 2.7; cited in the paper,
**proved** in `LQR/RiccatiExistence` as `System.riccatiTheorem`),
`eq:lqr-feedback`, and the unique minimiser of the model-based problem (`thm:lqr-riccati`,
re-proved from `hyp:H1` alone in `app:lqr-data`).

## Main declarations

* `LQRWeights U V`: the weights of `eq:lqr-cost`, `G ∈ L(V, V')` self-adjoint and nonnegative,
  as a bounded symmetric nonnegative bilinear form on `V`, and `R ∈ L(U)`
  self-adjoint (`LinearMap.IsSymmetric`) and coercive, `⟪u, R u⟫ ≥ ε_R ‖u‖²`.
  `LQRWeights.Rinv := Ring.inverse R` is `R⁻¹` (`LQRWeights.isUnit_R`: `R` is invertible).
* `System.lqrCost wts T x₀ u`: the cost `J(u; x₀)` of `eq:lqr-cost`,
  `⟨x(T), G x(T)⟩_{V,V'} + ∫₀ᵀ (‖C x(t)‖² + ⟨u(t), R u(t)⟩) dt` with `x = sys.mildW x₀ u` for
  `x₀ ∈ W`; `System.lqrCost_congr_ae` (it only depends on the class of `u` in `L²(0, T; U)`).
* `System.existsUnique_isMinOn_lqrCost`: under `hyp:H1`, `J(·; x₀)` has a unique minimiser over
  `L²(0, T; U)` (`app:lqr-data`: a continuous quadratic functional with coercive quadratic part).
* `System.bStarP P x`: `B^⋆ P x ∈ U` for a bilinear form `P` on `V` and `x ∈ W`, the Riesz
  representer of `v ↦ P(x, B v)`.
* `System.RiccatiSolution wts T`: **the conclusion of `thm:lqr-riccati` as a structure**.  It packages
  the conclusion of the cited theorem that the paper uses: a family `P : ℝ → V × V → ℝ` of
  bounded symmetric nonnegative bilinear forms on `V`, strongly continuous on `I = [0, T]`, with
  `P(T) = G`, such that for every `x₀ ∈ W` the minimiser `u_F` of `J(·; x₀)` is given by the
  feedback `u_F(t) = -R⁻¹ B^⋆ P(t) x(t)` and `J(u_F; x₀) = ⟨x₀, P(0) x₀⟩_{V,V'}`
  (`eq:lqr-feedback`).  The integral Riccati equation itself and the uniqueness of `P` are not
  recorded: no result of the paper uses them.
* `System.RiccatiTheorem wts T`: the statement of `thm:lqr-riccati` as a `Prop`,
  `H1 → H2 → Compat → Nonempty (RiccatiSolution wts T)`.  It is proved for every system in
  `LQR/RiccatiExistence` (`System.riccatiTheorem`), without using `Compat`
  (`System.nonempty_riccatiSolution`).

## Upstream results used

`existsUnique_isMinOn_quadraticFunctional_univ` (`Analysis/Quadratic`); `System.Lop_apply`,
`System.𝓕_ae_eq`, `System.mildW_congr_ae`, `memLp_μI_of_continuousOn` (`System/Mild`); for
`isUnit_R`, Lax–Milgram (`IsCoercive.continuousLinearEquivOfBilin`, Mathlib).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace DataDrivenControl

/-- The weights of the regulator (`eq:lqr-cost`, `subsec:lqr-riccati`): the terminal weight
`G ∈ L(V, V')`, self-adjoint and nonnegative, as a bounded symmetric nonnegative bilinear form
on `V` (`⟨v, G w⟩_{V,V'} = G v w`), and the input weight `R ∈ L(U)`,
self-adjoint and coercive, `⟨u, R u⟩_U ≥ ε_R ‖u‖²` with `ε_R > 0`. -/
structure LQRWeights (U V : Type*) [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The terminal weight `G`, a bounded bilinear form on `V`. -/
  G : V →L[ℝ] V →L[ℝ] ℝ
  /-- `G` is self-adjoint. -/
  G_symm : ∀ v w : V, G v w = G w v
  /-- `G` is nonnegative. -/
  G_nonneg : ∀ v : V, 0 ≤ G v v
  /-- The input weight `R ∈ L(U)`. -/
  R : U →L[ℝ] U
  /-- `R` is self-adjoint. -/
  R_isSymmetric : (R : U →ₗ[ℝ] U).IsSymmetric
  /-- `R` is coercive: `⟨u, R u⟩ ≥ ε_R ‖u‖²` for some `ε_R > 0`. -/
  R_coercive : ∃ ε > 0, ∀ u : U, ε * ‖u‖ ^ 2 ≤ ⟪u, R u⟫_ℝ

namespace LQRWeights

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `R⁻¹` (`eq:lqr-feedback`), as `Ring.inverse R`; it is the inverse of `R` by `isUnit_R`. -/
def Rinv (wts : LQRWeights U V) : U →L[ℝ] U := Ring.inverse wts.R

/-- A self-adjoint coercive `R` on a Hilbert space is invertible (Lax–Milgram), so `Rinv` is its
inverse. -/
theorem isUnit_R [CompleteSpace U] (wts : LQRWeights U V) : IsUnit wts.R := by
  obtain ⟨ε, hε, hR⟩ := wts.R_coercive
  set B : U →L[ℝ] U →L[ℝ] ℝ := (innerSL ℝ).comp wts.R with hBdef
  have hB : IsCoercive B := ⟨ε, hε, fun u => by
    simp only [hBdef, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
    rw [real_inner_comm, mul_assoc, ← sq]
    exact hR u⟩
  have he : (hB.continuousLinearEquivOfBilin : U →L[ℝ] U) = wts.R := by
    ext v
    refine ext_inner_right ℝ fun w => ?_
    simp [hBdef]
  rw [← he]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

end LQRWeights

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-- The **LQR cost** `J(u; x₀)` (`eq:lqr-cost`) for an initial state `x₀ ∈ W` and an input `u`
on `(0, T]`:
`J(u; x₀) = ⟨x(T), G x(T)⟩_{V,V'} + ∫₀ᵀ (‖C x(t)‖² + ⟨u(t), R u(t)⟩) dt`, where
`x = x(·; x₀, u)` is the mild solution, a `W`-valued function (`sys.mildW`). -/
def lqrCost (wts : LQRWeights U V) (T : ℝ) (x₀ : W) (u : ℝ → U) : ℝ :=
  wts.G (sys.ιWV (sys.mildW x₀ u T)) (sys.ιWV (sys.mildW x₀ u T)) +
    ∫ t in Ioc 0 T, (‖sys.C (sys.mildW x₀ u t)‖ ^ 2 + ⟪u t, wts.R (u t)⟫_ℝ)

/-- `B^⋆ P x ∈ U` for a bounded bilinear form `P` on `V` (`P ∈ L(V, V')`) and `x ∈ W`: the Riesz
representer in `U` of the bounded functional `v ↦ P(x, B v)`, i.e.
`⟨B^⋆ P x, v⟩_U = ⟨B v, P x⟩_{V,V'}` (`eq:lqr-feedback`). -/
def bStarP (P : V →L[ℝ] V →L[ℝ] ℝ) (x : W) : U :=
  (InnerProductSpace.toDual ℝ U).symm ((P (sys.ιWV x)).comp sys.B)

variable {sys}

/-- The defining property of `B^⋆ P x`. -/
theorem inner_bStarP (P : V →L[ℝ] V →L[ℝ] ℝ) (x : W) (v : U) :
    ⟪sys.bStarP P x, v⟫_ℝ = P (sys.ιWV x) (sys.B v) := by
  simp [bStarP, InnerProductSpace.toDual_symm_apply]

/-- The cost only depends on the input almost everywhere on `(0, T]`. -/
theorem lqrCost_congr_ae (wts : LQRWeights U V) {T : ℝ} (x₀ : W) {u v : ℝ → U}
    (h : u =ᵐ[μI T] v) : sys.lqrCost wts T x₀ u = sys.lqrCost wts T x₀ v := by
  have hx : ∀ t ≤ T, sys.mildW x₀ u t = sys.mildW x₀ v t := fun t ht =>
    mildW_congr_ae (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht) le_rfl) h) x₀
  unfold lqrCost
  rw [hx T le_rfl]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with t ht htI
  rw [ht, hx t htI.2]

/-- **Unique optimal control of the model-based problem** (`thm:lqr-riccati`, first assertion of
the last sentence; proved from `hyp:H1` alone in `app:lqr-data`): for every `x₀ ∈ W` the cost
`J(·; x₀)` of `eq:lqr-cost` has a unique minimiser over `L²(0, T; U)`. -/
theorem existsUnique_isMinOn_lqrCost {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (wts : LQRWeights U V)
    (x₀ : W) :
    ∃! u : L2 U T, IsMinOn (fun v : L2 U T => sys.lqrCost wts T x₀ v) univ u := by
  obtain ⟨ε, hε, hR⟩ := wts.R_coercive
  have hy₀ : MemLp (fun t => sys.C (sys.SW.real t x₀)) 2 (μI T) :=
    memLp_μI_of_continuousOn
      (sys.C.continuous.comp (sys.SW.continuous_real_apply x₀)).continuousOn
  set y₀ : L2 Y T := hy₀.toLp _ with hy₀def
  set w₁ : V := sys.ιWV (sys.SW.real T x₀) with hw₁
  set M : L2 U T →L[ℝ] V := sys.ιWV ∘L sys.Lop T with hM
  set F : L2 U T →L[ℝ] L2 Y T := sys.𝓕 T with hF
  set Rt : L2 U T →L[ℝ] L2 U T := wts.R.compLpL 2 (μI T) with hRt
  let ipY : L2 Y T →L[ℝ] L2 Y T →L[ℝ] ℝ := innerSL ℝ
  let ipU : L2 U T →L[ℝ] L2 U T →L[ℝ] ℝ := innerSL ℝ
  have hipY : ∀ f g : L2 Y T, ipY f g = ⟪f, g⟫_ℝ := fun _ _ => rfl
  have hipU : ∀ f g : L2 U T, ipU f g = ⟪f, g⟫_ℝ := fun _ _ => rfl
  set a : L2 U T →L[ℝ] L2 U T →L[ℝ] ℝ := wts.G.bilinearComp M M +
    ipY.bilinearComp F F + ipU.bilinearComp (ContinuousLinearMap.id ℝ _) Rt with ha
  set ℓ : L2 U T →L[ℝ] ℝ := (wts.G w₁).comp M + (ipY y₀).comp F with hℓ
  set c : ℝ := wts.G w₁ w₁ + ‖y₀‖ ^ 2 with hc
  have hRae : ∀ v : L2 U T,
      (fun t => ⟪v t, Rt v t⟫_ℝ) =ᵐ[μI T] fun t => ⟪v t, wts.R (v t)⟫_ℝ := fun v => by
    filter_upwards [wts.R.coeFn_compLpL v] with t ht
    rw [ht]
  have hRt_inner : ∀ v : L2 U T, ⟪v, Rt v⟫_ℝ = ∫ t in Ioc 0 T, ⟪v t, wts.R (v t)⟫_ℝ :=
    fun v => by rw [L2.inner_def]; exact integral_congr_ae (hRae v)
  have hJ : ∀ v : L2 U T, sys.lqrCost wts T x₀ v = quadraticFunctional a ℓ c v := by
    intro v
    have hxT : sys.ιWV (sys.mildW x₀ v T) = w₁ + M v := by
      simp only [mildW, map_add, hw₁, hM, ContinuousLinearMap.comp_apply, Lop_apply hH1 hT]
    have hyae : (fun t => ⟪(y₀ + F v) t, (y₀ + F v) t⟫_ℝ) =ᵐ[μI T]
        fun t => ‖sys.C (sys.mildW x₀ v t)‖ ^ 2 := by
      filter_upwards [Lp.coeFn_add y₀ (F v), hy₀.coeFn_toLp, 𝓕_ae_eq hH1 hT v] with t h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, real_inner_self_eq_norm_sq, mildW, map_add]
    have hint1 : Integrable (fun t => ‖sys.C (sys.mildW x₀ v t)‖ ^ 2) (μI T) :=
      (L2.integrable_inner _ _).congr hyae
    have hint2 : Integrable (fun t => ⟪v t, wts.R (v t)⟫_ℝ) (μI T) :=
      (L2.integrable_inner _ _).congr (hRae v)
    have hy : ∫ t in Ioc 0 T, ‖sys.C (sys.mildW x₀ v t)‖ ^ 2 = ‖y₀ + F v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      exact (integral_congr_ae hyae).symm
    rw [lqrCost, hxT, integral_add hint1 hint2, hy, ← hRt_inner, norm_add_sq_real]
    simp only [quadraticFunctional, ha, hℓ, hc, add_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      hipY, hipU, map_add, ContinuousLinearMap.id_apply]
    rw [wts.G_symm (M v) w₁, real_inner_self_eq_norm_sq]
    ring
  have hcoer : IsCoercive a := by
    refine ⟨ε, hε, fun v => ?_⟩
    have h1 : ε * ‖v‖ * ‖v‖ ≤ ⟪v, Rt v⟫_ℝ := by
      rw [hRt_inner, mul_assoc, ← real_inner_self_eq_norm_mul_norm, L2.inner_def,
        ← integral_const_mul]
      refine integral_mono_ae ((L2.integrable_inner v v).const_mul ε)
        ((L2.integrable_inner _ _).congr (hRae v)) (Eventually.of_forall fun t => ?_)
      simp only
      rw [real_inner_self_eq_norm_sq]
      exact hR (v t)
    have h2 : 0 ≤ wts.G (M v) (M v) := wts.G_nonneg _
    have h3 : 0 ≤ ⟪F v, F v⟫_ℝ := real_inner_self_nonneg
    simp only [ha, add_apply, ContinuousLinearMap.bilinearComp_apply,
      hipY, hipU, ContinuousLinearMap.id_apply]
    linarith
  obtain ⟨u, hu, huniq⟩ := existsUnique_isMinOn_quadraticFunctional_univ hcoer ℓ c
  refine ⟨u, isMinOn_univ_iff.2 fun v => ?_, fun v hv => huniq v fun w => ?_⟩
  · rw [hJ, hJ]; exact hu v
  · rw [← hJ, ← hJ]; exact isMinOn_univ_iff.1 hv w

variable (sys)

/-- **The conclusion of `thm:lqr-riccati` as a structure** (Pritchard–Salamon, Thm 2.7; cited in
the paper, proved in `LQR/RiccatiExistence`).  A `RiccatiSolution wts T` packages the conclusion
of the cited theorem that the paper uses:

* `P : I → L(V, V')`, as bounded bilinear forms on `V`, self-adjoint and
  nonnegative on `I = [0, T]`, strongly continuous (`t ↦ P(t) v ∈ V'` continuous on `I` for
  every `v ∈ V`), with terminal condition `P(T) = G`;
* (`eq:lqr-feedback`) for every `x₀ ∈ W` there is an optimal control `u_F` of `eq:lqr-cost` (a
  minimiser of `J(·; x₀)` over `L²(0, T; U)`; it is unique by
  `existsUnique_isMinOn_lqrCost`), given by the feedback `u_F(t) = -R⁻¹ B^⋆ P(t) x(t)` for a.e.
  `t ∈ I`, where `x = x(·; x₀, u_F)`, and with minimal cost `J(u_F; x₀) = ⟨x₀, P(0) x₀⟩_{V,V'}`.

The integral Riccati equation that `P` solves, and the uniqueness of `P`, are not recorded: no
result of the paper uses them.  The cited theorem gives a `RiccatiSolution` under `hyp:H1`,
`hyp:H2` and `hyp:compat` (`RiccatiTheorem`); `System.nonempty_riccatiSolution` gives one under
`hyp:H1` and `hyp:H2` alone. -/
structure RiccatiSolution (wts : LQRWeights U V) (T : ℝ) where
  /-- The Riccati operator `P(t) ∈ L(V, V')`, as a bounded bilinear form on `V`. -/
  P : ℝ → V →L[ℝ] V →L[ℝ] ℝ
  /-- `P(t)` is self-adjoint on `I`. -/
  symm : ∀ t ∈ Icc 0 T, ∀ v w : V, P t v w = P t w v
  /-- `P(t)` is nonnegative on `I`. -/
  nonneg : ∀ t ∈ Icc 0 T, ∀ v : V, 0 ≤ P t v v
  /-- `P` is strongly continuous on `I`: `t ↦ P(t) v ∈ V'` is continuous for every `v ∈ V`. -/
  continuousOn : ∀ v : V, ContinuousOn (fun t => P t v) (Icc 0 T)
  /-- The terminal condition `P(T) = G`. -/
  terminal : P T = wts.G
  /-- `eq:lqr-feedback`: the optimal control is the feedback `u_F(t) = -R⁻¹ B^⋆ P(t) x(t)` and
  the minimal cost is `⟨x₀, P(0) x₀⟩_{V,V'}`. -/
  optimal : ∀ x₀ : W, ∃ u : L2 U T,
    IsMinOn (fun v : L2 U T => sys.lqrCost wts T x₀ v) univ u ∧
      (∀ᵐ t ∂(μI T), u t = -wts.Rinv (sys.bStarP (P t) (sys.mildW x₀ u t))) ∧
      sys.lqrCost wts T x₀ u = P 0 (sys.ιWV x₀) (sys.ιWV x₀)

/-- The statement of **`thm:lqr-riccati`** (Pritchard–Salamon, Thm 2.7) as a `Prop`: under
Assumptions `hyp:H1`, `hyp:H2` and `hyp:compat` there is a `RiccatiSolution`.  It is cited in the
paper and proved here for every system (`System.riccatiTheorem`, `LQR/RiccatiExistence`). -/
def RiccatiTheorem (wts : LQRWeights U V) (T : ℝ) : Prop :=
  sys.H1 T → sys.H2 T → sys.Compat → Nonempty (sys.RiccatiSolution wts T)

end System

end DataDrivenControl
