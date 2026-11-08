module

public import DataDrivenControl.System.Controllability
public import DataDrivenControl.System.ControlRealization
public import DataDrivenControl.Analysis.Complexification
public import DataDrivenControl.Semigroup.Analytic
public import DataDrivenControl.Signal.WeakDerivative

/-!
# The Fattorini–Hautus test

Paper: `prop:fattorini-hautus` (cited in the paper from Boyer, Thm III.3.7, and
Badra–Takahashi, Thm 1.3; **proved** in `Controllability/FHSpectral` as
`System.fattoriniHautusTheorem`).

## How the cited result enters

`prop:fattorini-hautus` says: under its hypotheses (`hyp:H1`; `A` generates an analytic
semigroup; `A^⋆` has compact resolvent; `A` has a complete system of root vectors; `B^⋆` is
bounded on `D(A^⋆)` for the graph norm), `(A, B)` is approximately controllable iff
`ker B^⋆ ∩ ker (A^⋆ - λ id_{X_ℂ}) = {0}` for every `λ ∈ ℂ`; in particular approximate
controllability does not depend on `T`.

The root-vector hypothesis is on `A`, not on `A^⋆` as in Boyer's statement: completeness for
`A^⋆` does not suffice (see the README, *The cited theorems, now proved*), and completeness for `A` is what the proof uses and
what Badra–Takahashi assume (their (H2)).

* `System.IsHautusEigenvector μ η`: `η ∈ D(A^⋆)_ℂ`, `A^⋆ η = μ η` and `B^⋆ η = 0`, with
  `A^⋆ = sys.A.adjoint.complexify` on `X_ℂ` and `B^⋆ = sys.Bstar.complexify`
  (`System/ControlRealization`, `Analysis/Complexification`).
* `System.HautusCondition`: no nonzero such `η` for any `μ ∈ ℂ`.
* `System.FattoriniHautusProperty T`: the conclusion of `prop:fattorini-hautus` at time `T`,
  `ApproxControllable T ↔ HautusCondition`.  **The theorems of Section 5 take it as a
  hypothesis**, together with the other paper hypotheses their proofs use.
* `System.FattoriniHautusHypotheses T`: the hypotheses of `prop:fattorini-hautus`.  They are
  only used, through the theorem, to obtain the property; `System.FattoriniHautusTheorem`
  is the theorem for the system, as a `Prop`:
  `FattoriniHautusHypotheses T → ∀ T' > 0, FattoriniHautusProperty T'`.  It is proved for every
  system in `Controllability/FHSpectral` (`System.fattoriniHautusTheorem`).
  The graph-norm bound of `B^⋆` is not a hypothesis: it holds for every system satisfying
  `hyp:H1` (`System.exists_norm_Bstar_le`).
* `System.hautusCondition_of_approxControllable`: the easy direction (an eigenvector of `A^⋆` in
  `ker B^⋆` obstructs approximate controllability), stated for every system with `hyp:H1`.
* `System.approxControllable_iff_of_fattoriniHautusProperty`: "approximate controllability is
  independent of `T`".

## The state projection of a mild solution (`app:data-fattorini-hautus`)

* `System.hasWeakDeriv_inner_mild`: `eq:weak-mild-diff` as an `H¹` statement, for `η ∈ D(A†)`:
  `t ↦ ⟨η, x(t)⟩` has weak derivative `⟨A† η, x⟩ + ⟨B† η, u⟩` (from `System.inner_mild_eq`).
* `System.hasWeakDeriv_pairing_mild`: the same on `X_ℂ` with the bilinear pairing, for
  `η ∈ D(A^⋆)_ℂ` (real and imaginary parts).
* `System.pairing_mild_eq_of_isHautusEigenvector`: `eq:data-fh-exponential`; for a Hautus
  eigenvector the derivative is `μ ⟨η, x⟩`, so `⟨η, x(t)⟩ = ⟨η, x₀⟩ e^{μ t}`
  (`HasWeakDeriv.eq_cexp_mul`).  Restated in `Controllability/InputState` as
  `System.exp_of_isHautusEigenvector`.

The easy direction applies this with `x₀ = 0`: `⟨η, L_T u⟩ = 0` for every input, so the real
and imaginary parts of `η` are orthogonal to the reachable set (`System.approxControllable_iff`,
`Complexification.pairing_ofReal_eq_zero_iff`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-- `η ∈ X_ℂ` is an **eigenvector of `A^⋆` in `ker B^⋆`** with eigenvalue `μ`
(`prop:fattorini-hautus`): `η ∈ D(A^⋆)_ℂ`, `A^⋆ η = μ η` and `B^⋆ η = 0`, where `A^⋆` and `B^⋆`
are the complexifications of the real `A†` and `B† : D(A†) → U`. -/
def IsHautusEigenvector (μ : ℂ) (η : Complexification X) : Prop :=
  ∃ hη : η ∈ sys.A.adjoint.complexify.domain,
    sys.A.adjoint.complexify ⟨η, hη⟩ = μ • η ∧ sys.Bstar.complexify ⟨η, hη⟩ = 0

/-- The **Hautus condition** of `prop:fattorini-hautus`:
`ker B^⋆ ∩ ker (A^⋆ - μ id_{X_ℂ}) = {0}` for every `μ ∈ ℂ`. -/
def HautusCondition : Prop :=
  ∀ (μ : ℂ) (η : Complexification X), sys.IsHautusEigenvector μ η → η = 0

/-- The **Fattorini–Hautus property** at time `T`, the conclusion of `prop:fattorini-hautus`
(Boyer, Thm III.3.7, cited): `(A, B)` is approximately controllable in time `T` iff the Hautus
condition holds.  Used as a hypothesis by the theorems of Section 5. -/
def FattoriniHautusProperty (T : ℝ) : Prop :=
  sys.ApproxControllable T ↔ sys.HautusCondition

/-- The **hypotheses of `prop:fattorini-hautus`** at time `T`: `hyp:H1`, `A` generates an
analytic semigroup, `A^⋆` (on `X_ℂ`) has compact resolvent, and the generator `A` (on `X_ℂ`)
has a complete system of root vectors.  The root vectors of `A` are the generalised
eigenvectors of one resolvent `R(μ) = (μ - A_ℂ)⁻¹` (`λ ↦ (μ - λ)⁻¹`), so completeness is the
density of the span of the generalised eigenspaces of `R(μ)`; it does not depend on `μ`
(`dense_iSup_maxGenEigenspace_resolvent`).  Completeness for `A^⋆`, as in Boyer's statement,
does not suffice.  The graph-norm bound of `B^⋆` is automatic
(`exists_norm_Bstar_le`).  The theorem (`FattoriniHautusTheorem`) turns these hypotheses into
`FattoriniHautusProperty`; nothing else uses them. -/
structure FattoriniHautusHypotheses (T : ℝ) : Prop where
  /-- The paper's horizon is positive. -/
  pos : 0 < T
  /-- Assumption `hyp:H1`. -/
  H1 : sys.H1 T
  /-- `A` generates an analytic semigroup on `X`. -/
  analytic : sys.SX.IsAnalytic
  /-- `A^⋆` has compact resolvent. -/
  compactResolvent : ∃ μ ∈ resolventSet sys.A.adjoint.complexify,
    IsCompactOperator (resolvent sys.A.adjoint.complexify μ)
  /-- `A` (on `X_ℂ`) has a complete system of root vectors. -/
  completeRootVectors : ∃ μ ∈ resolventSet sys.A.complexify,
    Dense (((⨆ ν : ℂ, Module.End.maxGenEigenspace
      ((resolvent sys.A.complexify μ : Complexification X →L[ℂ] Complexification X) :
        Module.End ℂ (Complexification X)) ν : Submodule ℂ (Complexification X))) :
      Set (Complexification X))

/-- **The Fattorini–Hautus theorem**, the content of `prop:fattorini-hautus`, for this system:
its hypotheses at some time `T` give the Fattorini–Hautus property at every time `T' > 0`.
Cited in the paper; proved here for every system (`System.fattoriniHautusTheorem`,
`Controllability/FHSpectral`). -/
def FattoriniHautusTheorem : Prop :=
  ∀ T : ℝ, sys.FattoriniHautusHypotheses T → ∀ T' : ℝ, 0 < T' → sys.FattoriniHautusProperty T'

variable {sys}

/-! ### The state projection of a mild solution -/

/-- **`eq:weak-mild-diff` in `H¹` form**: under `hyp:H1`, for `η ∈ D(A†)` the state projection
`t ↦ ⟨η, x(t; x₀, u)⟩` of a mild solution is in `H¹(0, τ)` with weak derivative
`⟨A† η, x(t)⟩ + ⟨B† η, u(t)⟩` (`System.inner_mild_eq`). -/
theorem hasWeakDeriv_inner_mild {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) {η : X} (hη : η ∈ sys.A.adjoint.domain) :
    HasWeakDeriv τ (fun t => ⟪η, sys.mild x₀ u t⟫_ℝ)
      (fun t => ⟪sys.A.adjoint ⟨η, hη⟩, sys.mild x₀ u t⟫_ℝ + ⟪sys.Bstar ⟨η, hη⟩, u t⟫_ℝ) := by
  refine ⟨?_, fun t ht => ?_⟩
  · exact (memLp_μI_of_continuousOn
      (continuousOn_const.inner (continuousOn_mild hH1 hT hu x₀))).add (hu.const_inner _)
  · rw [mild_zero_time]
    exact inner_mild_eq hH1 hT hu x₀ hη t ht

open Complexification in
/-- **`eq:weak-mild-diff` on `X_ℂ`** (`app:data-fattorini-hautus`): under `hyp:H1`, for
`η ∈ D(A^⋆)_ℂ` the complex state projection `y_η(t) = ⟨η, x(t; x₀, u)⟩` (bilinear pairing) is
in `H¹(0, τ; ℂ)` with `ẏ_η = ⟨A^⋆ η, x(t)⟩ + ⟨B^⋆ η, u(t)⟩`. -/
theorem hasWeakDeriv_pairing_mild {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) {η : Complexification X}
    (hη : η ∈ sys.A.adjoint.complexify.domain) :
    HasWeakDeriv τ (fun t => ⟪η, (sys.mild x₀ u t : Complexification X)⟫_bil)
      (fun t => ⟪sys.A.adjoint.complexify ⟨η, hη⟩, (sys.mild x₀ u t : Complexification X)⟫_bil +
        ⟪sys.Bstar.complexify ⟨η, hη⟩, (u t : Complexification U)⟫_bil) := by
  have hre := hasWeakDeriv_inner_mild hH1 hT hu x₀ (Submodule.mem_complexify.1 hη).1
  have him := hasWeakDeriv_inner_mild hH1 hT hu x₀ (Submodule.mem_complexify.1 hη).2
  have h := (hre.map Complex.ofRealCLM).add ((him.map Complex.ofRealCLM).const_smul Complex.I)
  refine h.congr (fun t _ => ?_) (ae_of_all _ fun t => ?_)
  · apply Complex.ext <;> simp [pairing_ofReal_right]
  · apply Complex.ext
    · simp only [pairing_ofReal_right]
      rw [LinearPMap.complexify_apply_re, LinearPMap.complexify_apply_re]
      simp
    · simp only [pairing_ofReal_right]
      rw [LinearPMap.complexify_apply_im, LinearPMap.complexify_apply_im]
      simp

/-- **Obstructions produce exponential identities** (`eq:data-fh-exponential`,
`app:data-fattorini-hautus` Step 1): under `hyp:H1`, if `A^⋆ η = μ η` and `B^⋆ η = 0`, then
`⟨η, x(t; x₀, u)⟩ = ⟨η, x₀⟩ e^{μ t}` on `[0, τ]`.  (Restated in `Controllability/InputState`
as `System.exp_of_isHautusEigenvector`.) -/
theorem pairing_mild_eq_of_isHautusEigenvector {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {μ : ℂ}
    {η : Complexification X} (hη : sys.IsHautusEigenvector μ η) {τ : ℝ} {x₀ : X} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) :
    ∀ t ∈ Icc 0 τ, ⟪η, (sys.mild x₀ u t : Complexification X)⟫_bil =
      ⟪η, (x₀ : Complexification X)⟫_bil * Complex.exp (μ * t) := by
  obtain ⟨hD, hA, hB⟩ := hη
  have h' : HasWeakDeriv τ (fun t => ⟪η, (sys.mild x₀ u t : Complexification X)⟫_bil)
      (fun t => μ * ⟪η, (sys.mild x₀ u t : Complexification X)⟫_bil) :=
    (hasWeakDeriv_pairing_mild hH1 hT hu x₀ hD).congr (fun _ _ => rfl) (ae_of_all _ fun t => by
      simp only [hA, hB, Complexification.pairing_smul_left, Complexification.pairing_zero_left,
        add_zero])
  intro t ht
  rw [h'.eq_cexp_mul t ht, mild_zero_time, mul_comm]

/-! ### The easy direction -/

/-- **The easy direction of `prop:fattorini-hautus`**: under `hyp:H1`, if `(A, B)` is
approximately controllable in time `T`, then no eigenvector of `A^⋆` lies in `ker B^⋆`.

Proof: for such an eigenvector `η`, `⟨η, L_T u⟩ = ⟨η, x(T; 0, u)⟩ = 0` for every input
(`pairing_mild_eq_of_isHautusEigenvector` with `x₀ = 0`), so the real and imaginary parts of `η`
are orthogonal to the reachable set, hence zero. -/
theorem hautusCondition_of_approxControllable {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T)
    (h : sys.ApproxControllable T) : sys.HautusCondition := by
  intro μ η hη
  rw [approxControllable_iff hH1 hT] at h
  have key : ∀ v : L2 U T, ⟪η, (sys.ιW (sys.Lop T v) : Complexification X)⟫_bil = 0 := by
    intro v
    have := pairing_mild_eq_of_isHautusEigenvector hH1 hT hη (x₀ := 0) (Lp.memLp v) T
      ⟨hT.le, le_rfl⟩
    rw [Lop_apply hH1 hT, ← mild_zero_left, this]
    simp
  have hre : η.re = 0 :=
    h _ fun v => ((Complexification.pairing_ofReal_eq_zero_iff _ _).1 (key v)).1
  have him : η.im = 0 :=
    h _ fun v => ((Complexification.pairing_ofReal_eq_zero_iff _ _).1 (key v)).2
  exact Complexification.ext hre him

/-- Under the Fattorini–Hautus property at two times, approximate controllability does not
depend on the time (`prop:fattorini-hautus`, last sentence). -/
theorem approxControllable_iff_of_fattoriniHautusProperty {T T' : ℝ}
    (h : sys.FattoriniHautusProperty T) (h' : sys.FattoriniHautusProperty T') :
    sys.ApproxControllable T ↔ sys.ApproxControllable T' :=
  h.trans h'.symm

end System

end DataDrivenControl
