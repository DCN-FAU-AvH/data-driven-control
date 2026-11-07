module

public import DataDrivenControl.LQR.TailOperators
public import DataDrivenControl.Semigroup.Adjoint

/-!
# The value operator of the finite-horizon regulator

Steps R2 and R3 of the proof of `thm:lqr-riccati` (Pritchard–Salamon Thm 2.7) through the
value operator.

## R2: an abstract quadratic control problem

For `p : Riccati.LQ V H Z` with `𝔾 = p.g` self-adjoint nonnegative and `R̃ = p.r` self-adjoint
and coercive (`LQ.WF`), the cost `J(x, u)` is minimised by completing the square:

* `K = b†𝔾b + d†d + R̃` (control Hessian, coercive), `M = b†𝔾a + d†c` (cross term),
  `Q = a†𝔾a + c†c`, `Kinv = K⁻¹`, `uopt = -K⁻¹M`, `Pop = Q - M†K⁻¹M` (the value operator);
* `LQ.cost_eq`: `J(x, u) = ⟪Pop x, x⟫ + ⟪K (u - uopt x), u - uopt x⟫`; hence `uopt x` is the
  unique minimiser (`LQ.isMinOn_cost`) and `⟪Pop x, x⟫` the value; `Pop` is self-adjoint and
  nonnegative;
* first-order characterisation: `K u + M x = 0 ↔ u = uopt x` (`LQ.eq_uopt_of_foc`), and then
  `Pop x = a†𝔾(a x + b u) + c†(c x + d u)` (`LQ.Pop_eq_of_foc`, the costate at the start).

## R3: strong continuity

`Riccati.SCont f S`: `s ↦ f s e` continuous on `S` for every `e`, and `‖f s‖` bounded on `S`.
`SCont` is stable under sums, compositions and coercive inversion (`SCont.inverse`), so
`SCont` of `a, b, c, d` **and of their adjoints** gives `SCont` of `Pop` (`LQ.scont_Pop`).

For the system (`System.lqTail wts T s`, `R1`) all eight families are strongly continuous on
`[0, T]` (`System.scont_tailA` … `System.scont_adjoint_tailD`; the adjoint of `S_V(T - s)` is
the adjoint semigroup, `C0Semigroup.continuous_adjoint_apply`).  The Riccati family is
`System.riccatiP wts T t = ⟪Pop_t ·, ·⟫`; it is symmetric, nonnegative, strongly continuous on
`[0, T]` (`System.continuousOn_riccatiP`) and `riccatiP wts T T = G`
(`System.riccatiP_terminal`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Riccati

/-! ### Coercive operators are invertible -/

section Coercive

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A coercive operator `⟪A u, u⟫ ≥ ε ‖u‖²` on a Hilbert space is invertible (Lax–Milgram). -/
theorem isUnit_of_coercive (A : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) : IsUnit A := by
  set B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp A with hBdef
  have hB : IsCoercive B := ⟨ε, hε, fun u => by
    simp only [hBdef, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
    rw [mul_assoc, ← sq]
    exact hA u⟩
  have he : (hB.continuousLinearEquivOfBilin : H →L[ℝ] H) = A := by
    ext v
    refine ext_inner_right ℝ fun w => ?_
    simp [hBdef]
  rw [← he]
  exact ⟨hB.continuousLinearEquivOfBilin.toUnit, rfl⟩

/-- `A (A⁻¹ h) = h` for a coercive `A`. -/
theorem apply_inverse_of_coercive (A : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) (h : H) : A (Ring.inverse A h) = h := by
  have := Ring.mul_inverse_cancel A (isUnit_of_coercive A hε hA)
  exact congrArg (fun F : H →L[ℝ] H => F h) this

/-- `A⁻¹ (A u) = u` for a coercive `A`. -/
theorem inverse_apply_of_coercive (A : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) (u : H) : Ring.inverse A (A u) = u := by
  have := Ring.inverse_mul_cancel A (isUnit_of_coercive A hε hA)
  exact congrArg (fun F : H →L[ℝ] H => F u) this

/-- `‖A⁻¹ h‖ ≤ ε⁻¹ ‖h‖` for a coercive `A`. -/
theorem norm_inverse_apply_le (A : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) (h : H) : ‖Ring.inverse A h‖ ≤ ε⁻¹ * ‖h‖ := by
  set v := Ring.inverse A h
  have h1 : ε * ‖v‖ ^ 2 ≤ ‖h‖ * ‖v‖ := by
    calc ε * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ := hA v
      _ = ⟪h, v⟫_ℝ := by rw [apply_inverse_of_coercive A hε hA]
      _ ≤ ‖h‖ * ‖v‖ := real_inner_le_norm _ _
  rw [le_inv_mul_iff₀ hε]
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

/-- `‖A⁻¹‖ ≤ ε⁻¹` for a coercive `A`. -/
theorem norm_inverse_le (A : H →L[ℝ] H) {ε : ℝ} (hε : 0 < ε)
    (hA : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪A u, u⟫_ℝ) : ‖Ring.inverse A‖ ≤ ε⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hε.le) (norm_inverse_apply_le A hε hA)

end Coercive

/-! ### R2: the abstract value operator -/

namespace LQ

variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

variable (p : LQ V H Z)

/-- The control Hessian `K = b†𝔾b + d†d + R̃`. -/
def K : H →L[ℝ] H := p.b† ∘L p.g ∘L p.b + p.d† ∘L p.d + p.r

/-- The cross term `M = b†𝔾a + d†c`. -/
def M : V →L[ℝ] H := p.b† ∘L p.g ∘L p.a + p.d† ∘L p.c

/-- The free-state form `Q = a†𝔾a + c†c`. -/
def Q : V →L[ℝ] V := p.a† ∘L p.g ∘L p.a + p.c† ∘L p.c

/-- `K⁻¹` (`Ring.inverse`; the inverse under `LQ.WF`). -/
def Kinv : H →L[ℝ] H := Ring.inverse p.K

/-- The optimal control `uopt x = -K⁻¹ M x`. -/
def uopt : V →L[ℝ] H := -(p.Kinv ∘L p.M)

/-- The **value operator** `Pop = Q - M† K⁻¹ M`: `⟪Pop x, x⟫ = min_u J(x, u)`. -/
def Pop : V →L[ℝ] V := p.Q - p.M† ∘L p.Kinv ∘L p.M

/-- Well-posedness of a quadratic control problem: `𝔾` self-adjoint and nonnegative, `R̃`
self-adjoint and coercive with constant `ε`. -/
structure WF (ε : ℝ) : Prop where
  /-- `𝔾` is self-adjoint. -/
  g_adj : p.g† = p.g
  /-- `𝔾` is nonnegative. -/
  g_nonneg : ∀ v, 0 ≤ ⟪p.g v, v⟫_ℝ
  /-- `R̃` is self-adjoint. -/
  r_adj : p.r† = p.r
  /-- The coercivity constant is positive. -/
  ε_pos : 0 < ε
  /-- `R̃` is coercive. -/
  r_coer : ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪p.r u, u⟫_ℝ

variable {p}

/-- Unfolding `K`. -/
theorem K_apply (u : H) : p.K u = (p.b†) (p.g (p.b u)) + (p.d†) (p.d u) + p.r u := rfl

/-- Unfolding `M`. -/
theorem M_apply (x : V) : p.M x = (p.b†) (p.g (p.a x)) + (p.d†) (p.c x) := rfl

/-- Unfolding `Q`. -/
theorem Q_apply (x : V) : p.Q x = (p.a†) (p.g (p.a x)) + (p.c†) (p.c x) := rfl

/-- `⟪K u, u⟫ = ⟪𝔾 b u, b u⟫ + ‖d u‖² + ⟪R̃ u, u⟫`. -/
theorem inner_K_self (u : H) :
    ⟪p.K u, u⟫_ℝ = ⟪p.g (p.b u), p.b u⟫_ℝ + ‖p.d u‖ ^ 2 + ⟪p.r u, u⟫_ℝ := by
  rw [K_apply, inner_add_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, real_inner_comm (p.b u)]

variable {ε : ℝ}

/-- `K` is coercive with the constant of `R̃`. -/
theorem WF.coercive (hp : p.WF ε) (u : H) : ε * ‖u‖ ^ 2 ≤ ⟪p.K u, u⟫_ℝ := by
  rw [inner_K_self]
  have := hp.g_nonneg (p.b u)
  have := hp.r_coer u
  nlinarith [sq_nonneg ‖p.d u‖]

/-- `K K⁻¹ = 1`. -/
theorem WF.K_Kinv (hp : p.WF ε) (h : H) : p.K (p.Kinv h) = h :=
  apply_inverse_of_coercive p.K hp.ε_pos hp.coercive h

/-- `K⁻¹ K = 1`. -/
theorem WF.Kinv_K (hp : p.WF ε) (u : H) : p.Kinv (p.K u) = u :=
  inverse_apply_of_coercive p.K hp.ε_pos hp.coercive u

/-- `K` is self-adjoint. -/
theorem WF.adjoint_K (hp : p.WF ε) : p.K† = p.K := by
  simp only [K, map_add, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    hp.g_adj, hp.r_adj, ContinuousLinearMap.comp_assoc]

/-- `K` is symmetric. -/
theorem WF.inner_K_comm (hp : p.WF ε) (u v : H) : ⟪p.K u, v⟫_ℝ = ⟪u, p.K v⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hp.adjoint_K]

/-- `K⁻¹` is symmetric. -/
theorem WF.inner_Kinv_comm (hp : p.WF ε) (h h' : H) :
    ⟪p.Kinv h, h'⟫_ℝ = ⟪h, p.Kinv h'⟫_ℝ := by
  conv_lhs => rw [← hp.K_Kinv h']
  rw [← hp.inner_K_comm, hp.K_Kinv]

/-- `K⁻¹` is self-adjoint. -/
theorem WF.adjoint_Kinv (hp : p.WF ε) : p.Kinv† = p.Kinv := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact hp.inner_Kinv_comm

/-- `𝔾` is symmetric. -/
theorem WF.inner_g_comm (hp : p.WF ε) (v w : V) : ⟪p.g v, w⟫_ℝ = ⟪v, p.g w⟫_ℝ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hp.g_adj]

/-- The first-order condition holds at `uopt x`: `K (uopt x) + M x = 0`. -/
theorem WF.foc (hp : p.WF ε) (x : V) : p.K (p.uopt x) + p.M x = 0 := by
  simp only [uopt, neg_apply, ContinuousLinearMap.comp_apply, map_neg,
    hp.K_Kinv, neg_add_cancel]

/-- The first-order condition characterises the optimal control. -/
theorem WF.eq_uopt_of_foc (hp : p.WF ε) {x : V} {u : H} (h : p.K u + p.M x = 0) :
    u = p.uopt x := by
  have hu : p.K u = p.K (p.uopt x) := by
    rw [eq_neg_of_add_eq_zero_left h, eq_neg_of_add_eq_zero_left (hp.foc x)]
  rw [← hp.Kinv_K u, hu, hp.Kinv_K]

/-- The first-order expression `K u + M x = b†𝔾(a x + b u) + d†(c x + d u) + R̃ u`. -/
theorem K_add_M (u : H) (x : V) :
    p.K u + p.M x = (p.b†) (p.g (p.a x + p.b u)) + (p.d†) (p.c x + p.d u) + p.r u := by
  simp only [K_apply, M_apply, map_add]
  abel

/-- `M† u = a†𝔾 b u + c† d u`. -/
theorem WF.adjoint_M_apply (hp : p.WF ε) (u : H) :
    (p.M†) u = (p.a†) (p.g (p.b u)) + (p.c†) (p.d u) := by
  simp only [M, map_add, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    hp.g_adj, add_apply, ContinuousLinearMap.comp_apply]

/-- **The value operator as costate** (`R2`): if `u` satisfies the first-order condition at
`x`, then `Pop x = a†𝔾(a x + b u) + c†(c x + d u)`. -/
theorem WF.Pop_eq_of_foc (hp : p.WF ε) {x : V} {u : H} (h : p.K u + p.M x = 0) :
    p.Pop x = (p.a†) (p.g (p.a x + p.b u)) + (p.c†) (p.c x + p.d u) := by
  have hK : p.Kinv (p.M x) = -u := by
    rw [eq_neg_of_add_eq_zero_right h, map_neg, hp.Kinv_K]
  simp only [Pop, Q, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, hK, map_neg, hp.adjoint_M_apply, map_add]
  abel

/-- `⟪Pop x, y⟫ = ⟪Q x, y⟫ - ⟪K⁻¹ M x, M y⟫`. -/
theorem inner_Pop (x y : V) :
    ⟪p.Pop x, y⟫_ℝ = ⟪p.Q x, y⟫_ℝ - ⟪p.Kinv (p.M x), p.M y⟫_ℝ := by
  simp only [Pop, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- `Pop` is self-adjoint. -/
theorem WF.inner_Pop_comm (hp : p.WF ε) (x y : V) : ⟪p.Pop x, y⟫_ℝ = ⟪x, p.Pop y⟫_ℝ := by
  rw [real_inner_comm (p.Pop y) x, inner_Pop, inner_Pop, hp.inner_Kinv_comm,
    real_inner_comm (p.M x)]
  congr 1
  simp only [Q_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rw [hp.inner_g_comm, real_inner_comm (p.a x), real_inner_comm (p.c x)]

/-- `Pop` is self-adjoint. -/
theorem WF.adjoint_Pop (hp : p.WF ε) : p.Pop† = p.Pop := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact hp.inner_Pop_comm

/-- **Completing the square** (`R2`): `J(x, u) = ⟪Pop x, x⟫ + ⟪K (u - uopt x), u - uopt x⟫`. -/
theorem WF.cost_eq (hp : p.WF ε) (x : V) (u : H) :
    p.cost x u = ⟪p.Pop x, x⟫_ℝ + ⟪p.K (u - p.uopt x), u - p.uopt x⟫_ℝ := by
  set w := p.Kinv (p.M x) with hw
  have hKw : p.K w = p.M x := hp.K_Kinv _
  have huo : u - p.uopt x = u + w := by
    rw [uopt, neg_apply, ContinuousLinearMap.comp_apply, sub_neg_eq_add]
  have e1 : ⟪p.Q x, x⟫_ℝ = ⟪p.g (p.a x), p.a x⟫_ℝ + ⟪p.c x, p.c x⟫_ℝ := by
    rw [Q_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
  have e2 := inner_K_self (p := p) u
  have e3 : ⟪p.M x, u⟫_ℝ = ⟪p.g (p.a x), p.b u⟫_ℝ + ⟪p.c x, p.d u⟫_ℝ := by
    rw [M_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
  have e4 : ⟪p.K u, w⟫_ℝ = ⟪p.M x, u⟫_ℝ := by
    rw [hp.inner_K_comm, hKw, real_inner_comm]
  have e5 : ⟪p.Pop x, x⟫_ℝ = ⟪p.Q x, x⟫_ℝ - ⟪p.M x, w⟫_ℝ := by
    rw [inner_Pop, ← hw, real_inner_comm (p.M x) w]
  have e6 : ⟪p.g (p.b u), p.a x⟫_ℝ = ⟪p.g (p.a x), p.b u⟫_ℝ := by
    rw [hp.inner_g_comm, real_inner_comm]
  rw [huo, map_add, hKw, inner_add_left, inner_add_right, inner_add_right, e4, e5, e1, e2, e3]
  simp only [cost, map_add, inner_add_left, inner_add_right, norm_add_sq_real,
    real_inner_self_eq_norm_sq]
  rw [e6]
  ring

/-- `J ≥ 0`. -/
theorem WF.cost_nonneg (hp : p.WF ε) (x : V) (u : H) : 0 ≤ p.cost x u := by
  have h1 := hp.g_nonneg (p.a x + p.b u)
  have h2 := hp.r_coer u
  have h3 : 0 ≤ ε * ‖u‖ ^ 2 := mul_nonneg hp.ε_pos.le (sq_nonneg _)
  unfold cost
  nlinarith [sq_nonneg ‖p.c x + p.d u‖]

/-- The value: `J(x, uopt x) = ⟪Pop x, x⟫`. -/
theorem WF.cost_uopt (hp : p.WF ε) (x : V) : p.cost x (p.uopt x) = ⟪p.Pop x, x⟫_ℝ := by
  rw [hp.cost_eq, sub_self, map_zero, inner_zero_left, add_zero]

/-- `uopt x` minimises `J(x, ·)`. -/
theorem WF.isMinOn_cost (hp : p.WF ε) (x : V) : IsMinOn (p.cost x) univ (p.uopt x) := by
  refine isMinOn_univ_iff.2 fun u => ?_
  rw [hp.cost_uopt, hp.cost_eq x u]
  have := hp.coercive (u - p.uopt x)
  have : 0 ≤ ε * ‖u - p.uopt x‖ ^ 2 := mul_nonneg hp.ε_pos.le (sq_nonneg _)
  linarith

/-- `Pop` is nonnegative. -/
theorem WF.inner_Pop_nonneg (hp : p.WF ε) (x : V) : 0 ≤ ⟪p.Pop x, x⟫_ℝ := by
  rw [← hp.cost_uopt]; exact hp.cost_nonneg x _

end LQ

/-! ### R3: strongly continuous families -/

section SCont

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A family of operators that is **strongly continuous** and uniformly bounded on `S`. -/
structure SCont (f : ℝ → E →L[ℝ] F) (S : Set ℝ) : Prop where
  /-- Strong continuity on `S`. -/
  cont : ∀ e, ContinuousOn (fun s => f s e) S
  /-- Uniform boundedness on `S`. -/
  bdd : ∃ C, ∀ s ∈ S, ‖f s‖ ≤ C

variable {S : Set ℝ}

/-- A constant family is strongly continuous. -/
theorem SCont.const (A : E →L[ℝ] F) : SCont (fun _ => A) S :=
  ⟨fun _ => continuousOn_const, ⟨‖A‖, fun _ _ => le_rfl⟩⟩

/-- A strongly continuous bounded family applied along a continuous path. -/
theorem SCont.continuousOn_apply {f : ℝ → E →L[ℝ] F} (hf : SCont f S) {g : ℝ → E}
    (hg : ContinuousOn g S) : ContinuousOn (fun s => f s (g s)) S := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact continuousOn_apply_of_bounded hf.cont hC hg

/-- Composition of strongly continuous bounded families. -/
theorem SCont.comp {f : ℝ → F →L[ℝ] G} {g : ℝ → E →L[ℝ] F} (hf : SCont f S)
    (hg : SCont g S) : SCont (fun s => (f s).comp (g s)) S := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  refine ⟨fun e => hf.continuousOn_apply (hg.cont e), ⟨max C 0 * max D 0, fun s hs => ?_⟩⟩
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ((hC s hs).trans (le_max_left _ _)) ((hD s hs).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _))

/-- Sum of strongly continuous bounded families. -/
theorem SCont.add {f g : ℝ → E →L[ℝ] F} (hf : SCont f S) (hg : SCont g S) :
    SCont (fun s => f s + g s) S := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨fun e => (hf.cont e).add (hg.cont e),
    ⟨C + D, fun s hs => (norm_add_le _ _).trans (add_le_add (hC s hs) (hD s hs))⟩⟩

/-- Negation of a strongly continuous bounded family. -/
theorem SCont.neg {f : ℝ → E →L[ℝ] F} (hf : SCont f S) : SCont (fun s => -f s) S := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact ⟨fun e => (hf.cont e).neg, ⟨C, fun s hs => by rw [norm_neg]; exact hC s hs⟩⟩

/-- Difference of strongly continuous bounded families. -/
theorem SCont.sub {f g : ℝ → E →L[ℝ] F} (hf : SCont f S) (hg : SCont g S) :
    SCont (fun s => f s - g s) S := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- `SCont` only depends on the family on `S`. -/
theorem SCont.congr {f g : ℝ → E →L[ℝ] F} (hf : SCont f S) (h : ∀ s ∈ S, f s = g s) :
    SCont g S := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact ⟨fun e => (hf.cont e).congr fun s hs => by simp only [h s hs],
    ⟨C, fun s hs => by rw [← h s hs]; exact hC s hs⟩⟩

/-- Inversion of a uniformly coercive, strongly continuous family on a Hilbert space:
`K_s⁻¹ - K_{s₀}⁻¹ = K_s⁻¹ (K_{s₀} - K_s) K_{s₀}⁻¹` and `‖K_s⁻¹‖ ≤ ε⁻¹` (`R3`). -/
theorem SCont.inverse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {K : ℝ → H →L[ℝ] H} (hK : SCont K S) {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ s ∈ S, ∀ u, ε * ‖u‖ ^ 2 ≤ ⟪K s u, u⟫_ℝ) :
    SCont (fun s => Ring.inverse (K s)) S := by
  refine ⟨fun h => ?_, ⟨ε⁻¹, fun s hs => norm_inverse_le (K s) hε (hc s hs)⟩⟩
  intro s₀ hs₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  set v := Ring.inverse (K s₀) h
  have key : ∀ s ∈ S, ‖Ring.inverse (K s) h - Ring.inverse (K s₀) h‖ ≤
      ε⁻¹ * ‖K s₀ v - K s v‖ := by
    intro s hs
    have e : Ring.inverse (K s) h - v = Ring.inverse (K s) (K s₀ v - K s v) := by
      rw [map_sub, inverse_apply_of_coercive (K s) hε (hc s hs),
        apply_inverse_of_coercive (K s₀) hε (hc s₀ hs₀)]
    rw [e]
    exact norm_inverse_apply_le (K s) hε (hc s hs) _
  have h1 : Tendsto (fun s => ε⁻¹ * ‖K s₀ v - K s v‖) (𝓝[S] s₀) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 (hK.cont v s₀ hs₀)).const_mul ε⁻¹
    simpa [norm_sub_rev] using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact key s hs

end SCont

namespace LQ

variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- **Strong continuity of the value operator** (`R3`): if the data of a family of quadratic
problems, together with the adjoints of `a, b, c, d`, are strongly continuous on `S`, and the
problems are uniformly well posed, then `s ↦ Pop_s` is strongly continuous on `S`. -/
theorem scont_Pop {p : ℝ → LQ V H Z} {S : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    (hwf : ∀ s ∈ S, (p s).WF ε)
    (hg : SCont (fun s => (p s).g) S) (hr : SCont (fun s => (p s).r) S)
    (ha : SCont (fun s => (p s).a) S) (ha' : SCont (fun s => (p s).a†) S)
    (hb : SCont (fun s => (p s).b) S) (hb' : SCont (fun s => (p s).b†) S)
    (hc : SCont (fun s => (p s).c) S) (hc' : SCont (fun s => (p s).c†) S)
    (hd : SCont (fun s => (p s).d) S) (hd' : SCont (fun s => (p s).d†) S) :
    SCont (fun s => (p s).Pop) S := by
  have hK : SCont (fun s => (p s).K) S := ((hb'.comp (hg.comp hb)).add (hd'.comp hd)).add hr
  have hM : SCont (fun s => (p s).M) S := (hb'.comp (hg.comp ha)).add (hd'.comp hc)
  have hM' : SCont (fun s => (p s).M†) S :=
    ((ha'.comp (hg.comp hb)).add (hc'.comp hd)).congr fun s hs =>
      ContinuousLinearMap.ext fun u => ((hwf s hs).adjoint_M_apply u).symm
  have hKinv : SCont (fun s => (p s).Kinv) S :=
    hK.inverse hε fun s hs => (hwf s hs).coercive
  have hQ : SCont (fun s => (p s).Q) S := (ha'.comp (hg.comp ha)).add (hc'.comp hc)
  exact hQ.sub (hM'.comp (hKinv.comp hM))

end LQ

/-! ### Strong continuity of the shift and cut-off families -/

section L2Families

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The cut-offs are strongly continuous. -/
theorem scont_cut (T : ℝ) (S : Set ℝ) : SCont (fun s => cut (E := E) T s) S :=
  ⟨fun f => (continuous_cut_apply T f).continuousOn, ⟨1, fun s _ => norm_cut_le T s⟩⟩

/-- The right shifts are strongly continuous. -/
theorem scont_shR (T : ℝ) (S : Set ℝ) : SCont (fun s => shR (E := E) T s) S :=
  ⟨fun f => (continuous_shR_apply T f).continuousOn, ⟨1, fun s _ => norm_shR_le T s⟩⟩

/-- The left shifts `windowL T T s` (adjoints of the right shifts) are strongly
continuous. -/
theorem scont_windowL (T : ℝ) (S : Set ℝ) : SCont (fun s => windowL (E := E) T T s) S :=
  ⟨fun f => (continuous_windowL T T f).continuousOn, ⟨1, fun s _ => norm_windowL_le T T s⟩⟩

end L2Families

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

/-! ### The tail problems are uniformly well posed and strongly continuous -/

/-- The tail problems are well posed, uniformly in the starting time (`R2`). -/
theorem exists_lqTail_wf (wts : LQRWeights U V) (T : ℝ) :
    ∃ ε > 0, ∀ s, (sys.lqTail wts T s).WF ε := by
  obtain ⟨ε, hε, hR⟩ := rOp_coercive wts T
  exact ⟨ε, hε, fun s => ⟨adjoint_gOp wts, inner_gOp_nonneg wts, adjoint_rOp wts T, hε, hR⟩⟩

/-- `s ↦ S_V(T - s)` is strongly continuous on `[0, T]`. -/
theorem scont_tailA (T : ℝ) : SCont (fun s => sys.tailA T s) (Icc 0 T) := by
  obtain ⟨M, -, hM⟩ := sys.SV.exists_norm_real_le T
  exact ⟨fun x => ((sys.SV.continuous_real_apply x).comp
    (continuous_const.sub continuous_id)).continuousOn,
    ⟨M, fun s hs => hM _ (by linarith [hs.1])⟩⟩

/-- `s ↦ S_V(T - s)†` is strongly continuous on `[0, T]` (adjoint semigroup). -/
theorem scont_adjoint_tailA (T : ℝ) : SCont (fun s => (sys.tailA T s)†) (Icc 0 T) := by
  obtain ⟨M, -, hM⟩ := sys.SV.exists_norm_real_le T
  refine ⟨fun x => ?_, ⟨M, fun s hs => ?_⟩⟩
  · have hc : Continuous fun s : ℝ => sys.SV.adjoint.real (T - s) x :=
      (sys.SV.adjoint.continuous_real_apply x).comp (continuous_const.sub continuous_id)
    refine hc.continuousOn.congr fun s _ => ?_
    simp [tailA]
  · rw [LinearIsometryEquiv.norm_map]
    exact hM _ (by linarith [hs.1])

/-- `s ↦ b_s` is strongly continuous on `[0, T]`. -/
theorem scont_tailB (T : ℝ) : SCont (fun s => sys.tailB T s) (Icc 0 T) :=
  (SCont.const sys.ιWV).comp ((SCont.const (sys.Lop T)).comp (scont_cut T _))

/-- `s ↦ b_s†` is strongly continuous on `[0, T]`. -/
theorem scont_adjoint_tailB (T : ℝ) : SCont (fun s => (sys.tailB T s)†) (Icc 0 T) :=
  ((scont_cut T _).comp ((SCont.const ((sys.Lop T)†)).comp (SCont.const (sys.ιWV†)))).congr
    fun s _ => by
      simp only [tailB, ContinuousLinearMap.adjoint_comp, adjoint_cut,
        ContinuousLinearMap.comp_assoc]

/-- `s ↦ c_s` is strongly continuous on `[0, T]`. -/
theorem scont_tailC (T : ℝ) : SCont (fun s => sys.tailC T s) (Icc 0 T) :=
  (scont_shR T _).comp (SCont.const (sys.𝓞V T))

/-- `s ↦ c_s†` is strongly continuous on `[0, T]`. -/
theorem scont_adjoint_tailC (T : ℝ) : SCont (fun s => (sys.tailC T s)†) (Icc 0 T) :=
  ((SCont.const ((sys.𝓞V T)†)).comp (scont_windowL T _)).congr fun s _ => by
    rw [tailC, ContinuousLinearMap.adjoint_comp, adjoint_shR]

/-- `s ↦ d_s` is strongly continuous on `[0, T]`. -/
theorem scont_tailD (T : ℝ) : SCont (fun s => sys.tailD T s) (Icc 0 T) :=
  (SCont.const (sys.𝓕 T)).comp (scont_cut T _)

/-- `s ↦ d_s†` is strongly continuous on `[0, T]`. -/
theorem scont_adjoint_tailD (T : ℝ) : SCont (fun s => (sys.tailD T s)†) (Icc 0 T) :=
  ((scont_cut T _).comp (SCont.const ((sys.𝓕 T)†))).congr fun s _ => by
    rw [tailD, ContinuousLinearMap.adjoint_comp, adjoint_cut]

/-- **Strong continuity of the value operator** on `[0, T]` (`R3`). -/
theorem scont_Pop_lqTail (wts : LQRWeights U V) (T : ℝ) :
    SCont (fun s => (sys.lqTail wts T s).Pop) (Icc 0 T) := by
  obtain ⟨ε, hε, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  exact LQ.scont_Pop hε (fun s _ => hwf s) (SCont.const (gOp wts)) (SCont.const (rOp wts T))
    (scont_tailA T) (scont_adjoint_tailA T) (scont_tailB T) (scont_adjoint_tailB T)
    (scont_tailC T) (scont_adjoint_tailC T) (scont_tailD T) (scont_adjoint_tailD T)

/-! ### The Riccati family -/

variable (sys) in
/-- The **Riccati operator** `P(t) ∈ L(V, V')` of `thm:lqr-riccati`, as the bounded bilinear
form `P(t)(v, w) = ⟪Pop_t v, w⟫` of the value operator of the tail problem started at `t`. -/
def riccatiP (wts : LQRWeights U V) (T t : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ).comp (sys.lqTail wts T t).Pop

/-- Unfolding `riccatiP`. -/
theorem riccatiP_apply (wts : LQRWeights U V) (T t : ℝ) (v w : V) :
    sys.riccatiP wts T t v w = ⟪(sys.lqTail wts T t).Pop v, w⟫_ℝ := rfl

/-- `P(t)` is symmetric. -/
theorem riccatiP_symm (wts : LQRWeights U V) (T t : ℝ) (v w : V) :
    sys.riccatiP wts T t v w = sys.riccatiP wts T t w v := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  rw [riccatiP_apply, riccatiP_apply, (hwf t).inner_Pop_comm, real_inner_comm]

/-- `P(t)` is nonnegative. -/
theorem riccatiP_nonneg (wts : LQRWeights U V) (T t : ℝ) (v : V) :
    0 ≤ sys.riccatiP wts T t v v := by
  obtain ⟨ε, -, hwf⟩ := exists_lqTail_wf (sys := sys) wts T
  exact (hwf t).inner_Pop_nonneg v

/-- `P` is **strongly continuous** on `[0, T]`: `t ↦ P(t) v ∈ V'` is continuous (`R3`). -/
theorem continuousOn_riccatiP (wts : LQRWeights U V) (T : ℝ) (v : V) :
    ContinuousOn (fun t => sys.riccatiP wts T t v) (Icc 0 T) :=
  (innerSL ℝ).continuous.comp_continuousOn ((scont_Pop_lqTail wts T).cont v)

/-- The terminal condition `P(T) = G` (`R3`). -/
theorem riccatiP_terminal (wts : LQRWeights U V) {T : ℝ} (hT : 0 ≤ T) :
    sys.riccatiP wts T T = wts.G := by
  ext v w
  rw [riccatiP_apply, LQ.inner_Pop, LQ.M_apply, LQ.Q_apply]
  simp [lqTail, tailB_self hT, tailC_self, tailD_self hT, ContinuousLinearMap.adjoint_inner_left,
    inner_gOp]

end System

end DataDrivenControl
