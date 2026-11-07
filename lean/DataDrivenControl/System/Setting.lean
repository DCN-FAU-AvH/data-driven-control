module

public import DataDrivenControl.Semigroup.Generator
public import DataDrivenControl.Signal.Basic

/-!
# The standing setting

Paper: `eq:hilbert-control-formal`, `eq:intro-WXV`, `hyp:H1`, `hyp:H2`, `hyp:compat`.

## Main declarations

* `System U W X V Y`: real Hilbert spaces `U` (inputs), `Y` (outputs) and `W ↪ X ↪ V`
  (states; continuous, injective, dense embeddings `ιW : W →L[ℝ] X`, `ιV : X →L[ℝ] V`),
  consistent C₀-semigroups `SW`, `SX`, `SV`, `B : U →L[ℝ] V`, `C : W →L[ℝ] Y`.
* Abbreviations `sys.A` (generator on `X`), `sys.AV`, `sys.AW`, `sys.ιWV : W →L[ℝ] V`.
* `System.H1 T`, `System.H2 T`, `System.Compat`: Assumptions `hyp:H1`, `hyp:H2`,
  `hyp:compat`, at the paper's horizon `T`.  That H1 and H2 at one `T > 0` give them at every
  horizon is `System.H1.of_pos` / `System.H2.of_pos` in `System/Mild`
  (`app:finite-horizon-output`).
* `System.bounded S B C : System U X X X Y`: the case `W = X = V` (bounded `B`, `C`), used by
  the explicit examples (`prop:hilbert-pe-necessary`, `prop:infinite-pe-insufficient`).

Convention: a variable of type `System U W X V Y` is called `sys`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal

noncomputable section

namespace DataDrivenControl

/-- The standing setting `eq:hilbert-control-formal` with the triple `W ↪ X ↪ V`
(`eq:intro-WXV`): `ẋ = A x + B u`, `y = C x`, where `A` generates `SX` on `X`, the semigroup
restricts to `SW` on `W` and extends to `SV` on `V`, `B ∈ L(U, V)` and `C ∈ L(W, Y)`.  All
spaces are real Hilbert spaces (completeness is assumed where needed). -/
structure System (U W X V Y : Type*)
    [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] where
  /-- The embedding `W ↪ X`. -/
  ιW : W →L[ℝ] X
  /-- The embedding `X ↪ V`. -/
  ιV : X →L[ℝ] V
  ιW_injective : Function.Injective ιW
  ιV_injective : Function.Injective ιV
  ιW_denseRange : DenseRange ιW
  ιV_denseRange : DenseRange ιV
  /-- The semigroup restricted to `W`. -/
  SW : C0Semigroup ℝ W
  /-- The semigroup on the state space `X`. -/
  SX : C0Semigroup ℝ X
  /-- The semigroup extended to `V`. -/
  SV : C0Semigroup ℝ V
  consistentW : C0Semigroup.Consistent ιW SW SX
  consistentV : C0Semigroup.Consistent ιV SX SV
  /-- The control operator `B ∈ L(U, V)`. -/
  B : U →L[ℝ] V
  /-- The observation operator `C ∈ L(W, Y)`. -/
  C : W →L[ℝ] Y

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

variable (sys : System U W X V Y)

/-- The generator `A` of the semigroup on `X` (the paper's `A`). -/
abbrev A : X →ₗ.[ℝ] X := sys.SX.generator

/-- The generator `A_V` of the semigroup on `V`. -/
abbrev AV : V →ₗ.[ℝ] V := sys.SV.generator

/-- The generator `A_W` of the semigroup on `W`. -/
abbrev AW : W →ₗ.[ℝ] W := sys.SW.generator

/-- The embedding `W ↪ V`. -/
abbrev ιWV : W →L[ℝ] V := sys.ιV.comp sys.ιW

theorem ιWV_apply (w : W) : sys.ιWV w = sys.ιV (sys.ιW w) := rfl

theorem ιWV_injective : Function.Injective sys.ιWV :=
  sys.ιV_injective.comp sys.ιW_injective

theorem consistentWV : C0Semigroup.Consistent sys.ιWV sys.SW sys.SV :=
  sys.consistentV.comp sys.consistentW

theorem ιW_SW (t : ℝ) (w : W) : sys.ιW (sys.SW.real t w) = sys.SX.real t (sys.ιW w) :=
  sys.consistentW.real t w

theorem ιV_SX (t : ℝ) (x : X) : sys.ιV (sys.SX.real t x) = sys.SV.real t (sys.ιV x) :=
  sys.consistentV.real t x

theorem ιWV_SW (t : ℝ) (w : W) : sys.ιWV (sys.SW.real t w) = sys.SV.real t (sys.ιWV w) :=
  sys.consistentWV.real t w

/-! ### The standing assumptions -/

/-- **Assumption `hyp:H1`** (admissibility of `B`) at horizon `T`: there is `b` such that for
every `u ∈ L²(0, T; U)` the `V`-valued integral `∫₀ᵀ S(T - r) B u(r) dr` lies in (the image of)
`W`, with `W`-norm at most `b ‖u‖`. -/
def H1 (T : ℝ) : Prop :=
  ∃ b : ℝ, ∀ u : L2 U T, ∃ w : W,
    sys.ιWV w = ∫ r in Ioc 0 T, sys.SV.real (T - r) (sys.B (u r)) ∧ ‖w‖ ≤ b * ‖u‖

/-- **Assumption `hyp:H2`** (admissibility of `C`) at horizon `T`: there is `c` such that
`‖C S(·) x‖_{L²(0, T; Y)} ≤ c ‖x‖_V` for every `x ∈ W`. -/
def H2 (T : ℝ) : Prop :=
  ∃ c : ℝ, ∀ w : W,
    eLpNorm (fun t => sys.C (sys.SW.real t w)) 2 (μI T) ≤ ENNReal.ofReal (c * ‖sys.ιWV w‖)

/-- **Assumption `hyp:compat`**: the domain `Z = D_V(A)` of the generator on `V`, with the graph
norm, embeds continuously and densely into `W`.  Continuity: every `v ∈ D(A_V)` is (the image
of) some `w ∈ W` with `‖w‖ ≤ c (‖v‖ + ‖A_V v‖)`; density: the `w ∈ W` with `w ∈ D(A_V)` are
dense in `W`. -/
def Compat : Prop :=
  (∃ c : ℝ, ∀ (v : V) (hv : v ∈ sys.AV.domain), ∃ w : W,
      sys.ιWV w = v ∧ ‖w‖ ≤ c * (‖v‖ + ‖sys.AV ⟨v, hv⟩‖)) ∧
    Dense {w : W | sys.ιWV w ∈ sys.AV.domain}

/-! ### Bounded control and observation: `W = X = V` -/

/-- The system with `W = X = V` and bounded `B ∈ L(U, X)`, `C ∈ L(X, Y)` (all embeddings the
identity).  Used for the explicit examples. -/
def bounded (S : C0Semigroup ℝ X) (B : U →L[ℝ] X) (C : X →L[ℝ] Y) : System U X X X Y where
  ιW := ContinuousLinearMap.id ℝ X
  ιV := ContinuousLinearMap.id ℝ X
  ιW_injective := Function.injective_id
  ιV_injective := Function.injective_id
  ιW_denseRange := denseRange_id
  ιV_denseRange := denseRange_id
  SW := S
  SX := S
  SV := S
  consistentW := S.consistent_id
  consistentV := S.consistent_id
  B := B
  C := C

section bounded

variable (S : C0Semigroup ℝ X) (B : U →L[ℝ] X) (C : X →L[ℝ] Y)

@[simp] theorem bounded_ιW : (bounded S B C).ιW = ContinuousLinearMap.id ℝ X := rfl
@[simp] theorem bounded_ιV : (bounded S B C).ιV = ContinuousLinearMap.id ℝ X := rfl
@[simp] theorem bounded_SW : (bounded S B C).SW = S := rfl
@[simp] theorem bounded_SX : (bounded S B C).SX = S := rfl
@[simp] theorem bounded_SV : (bounded S B C).SV = S := rfl
@[simp] theorem bounded_B : (bounded S B C).B = B := rfl
@[simp] theorem bounded_C : (bounded S B C).C = C := rfl

end bounded

end System

end DataDrivenControl
