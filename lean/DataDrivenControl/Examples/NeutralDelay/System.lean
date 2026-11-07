module

public import DataDrivenControl.Examples.NeutralDelay.Semigroup

/-!
# The neutral delay system fits the framework

* `NeutralDelay.Model h E U Y`: the neutral equation (`NeutralDelay.Equation`), the input matrix
  `B₀` and the delayed output `y(t) = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` (output delays `h'ₖ ∈ [0, h]`,
  `C_d` bounded on the `L²` history), as in `Delay.Model`.
* `Model.sys : System U W X V Y` with `X = V = E × L²(-h, 0; E)` (`Delay.State`), `W = D(A)` with
  the graph norm (`C0Semigroup.Dom`), `B = (B₀, 0)` (`Model.Bop`, bounded) and
  `C = Model.Cop ∈ L(W, Y)`.
* `C` is defined on the graph.  Unlike the retarded case the first component of `v ∈ D(A)` is
  `g(h) - M g`, not `g(h)`, so the point values of the history are recovered from
  `(v₂, (A v)₂) = (g, g')` alone, by the `H¹` point evaluation (`pointEval_eq`)
  `g(a) = h⁻¹ ∫₀ʰ g + ∫₀ʰ g' - h⁻¹ ∫₀ʰ ∫₀^σ g' dσ - ∫_{(a, h]} g'`, which is bounded on
  `L² × L²` (`Model.evalOp`).  `Model.Cop_apply`: `C (g(h) - M g, g) = ∑ₖ Cₖ g(h - h'ₖ) + C_d g`.
* `Model.ctrlState_eq_conv`, `Model.ιW_L`: `L_T u = (x(T) - M x_T, x_T)` for the zero-history
  solution forced by `B₀ u`.  The state is a strong solution (regularity,
  `Equation.IsSolOn.exists_hasWeakDeriv`, and the generator characterisation), so it equals the
  mild solution (`C0Semigroup.eq_mildSol_of_strong`, Ball).
* `Model.H1`, `Model.H2` at every horizon, and `Model.compat`.  `hyp:H1`: `L_T u ∈ D(A)`, and the
  graph-norm bound comes from the closed graph theorem.  `hyp:H2`: the output along `S(t) w` is
  `C` evaluated along an `H¹` representative of the trajectory, bounded in `L²(0, T)` by the
  `L²` bound of the solution (`Equation.eLpNorm_trajOf_le`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace NeutralDelay

open Delay (State state_ext segOp segOp_apply sub_integral_Ioc_of_hasWeakDeriv
  hasWeakDeriv_comp_add traj traj_of_le traj_of_lt intervalIntegrable_of_integrableOn
  window_zero_eq_toLp traj_ae_congr)

variable {E U Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-! ### `H¹` point evaluation from `(g, g')` -/

/-- **`H¹` point evaluation from `(g, g')`**: for `g ∈ H¹(0, h)` with weak derivative `g'` and
classes `w₁ = g`, `w₂ = g'` in `L²(0, h)`,
`g(a) = h⁻¹ ∫₀ʰ w₁ + ∫₀ʰ w₂ - h⁻¹ ∫₀ʰ (∫₀^σ w₂) dσ - ∫_{(a, h]} w₂`. -/
theorem pointEval_eq {h a : ℝ} (hh : 0 < h) (ha : a ∈ Icc 0 h) {g g' : ℝ → E}
    (hg : HasWeakDeriv h g g') {w₁ w₂ : L2 E h} (h₁ : ⇑w₁ =ᵐ[μI h] g) (h₂ : ⇑w₂ =ᵐ[μI h] g') :
    h⁻¹ • segOp h 0 w₁ + (segOp h 0 w₂ - h⁻¹ • segOp h 0 (primL h w₂) - segOp h a w₂) = g a := by
  have hFc : ContinuousOn (fun σ => ∫ u in (0 : ℝ)..σ, g' u) (Icc 0 h) :=
    Delay.continuousOn_primitive_Ioc (hg.memLp_deriv.integrable one_le_two)
  have hFi : IntegrableOn (fun σ => ∫ u in (0 : ℝ)..σ, g' u) (Ioc 0 h) :=
    hFc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have e1 : segOp h 0 w₁ = h • g 0 + ∫ σ in Ioc 0 h, ∫ u in (0 : ℝ)..σ, g' u := by
    rw [segOp_apply le_rfl, integral_congr_ae h₁,
      setIntegral_congr_fun measurableSet_Ioc (g := fun σ => g 0 + ∫ u in (0 : ℝ)..σ, g' u)
        fun σ hσ => hg.eq_add_integral σ (Ioc_subset_Icc_self hσ),
      integral_add (integrableOn_const (by simp)) hFi, setIntegral_const,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
  have e2 : segOp h 0 (primL h w₂) = ∫ σ in Ioc 0 h, ∫ u in (0 : ℝ)..σ, g' u := by
    rw [segOp_apply le_rfl]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_primL h w₂, ae_restrict_mem measurableSet_Ioc] with σ e₁ e₂
    rw [e₁, intervalIntegral_congr_μI h₂ (Ioc_subset_Icc_self e₂)]
  have e3 : segOp h 0 w₂ = ∫ u in (0 : ℝ)..h, g' u := by
    rw [segOp_apply le_rfl, integral_congr_ae h₂, intervalIntegral.integral_of_le hh.le]
  have e4 : segOp h a w₂ = ∫ s in Ioc a h, g' s := by
    rw [segOp_apply ha.1]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc ha.1 le_rfl) h₂)
  rw [e1, e2, e3, e4, ← sub_integral_Ioc_of_hasWeakDeriv hg ha,
    hg.eq_add_integral h ⟨hh.le, le_rfl⟩, smul_add, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  abel

/-! ### The model -/

/-- **Data of the neutral delay system with delayed output** (`ex:intro-delay`): the neutral
equation `NeutralDelay.Equation`, the input matrix `B₀`, and the output
`y(t) = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` with finitely many output delays `h'ₖ ∈ [0, h]` and a
distributed part `C_d` bounded on the `L²` history. -/
structure Model (h : ℝ) (E U Y : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] extends toNeutral : Equation h E where
  /-- The input matrix `B₀`. -/
  B₀ : U →L[ℝ] E
  /-- The number of point delays in the output. -/
  NC : ℕ
  /-- The output coefficients `Cₖ`. -/
  Cp : Fin NC → E →L[ℝ] Y
  /-- The output delays `h'ₖ`. -/
  τC : Fin NC → ℝ
  /-- The output delays lie in `[0, h]`. -/
  τC_mem : ∀ k, τC k ∈ Icc 0 h
  /-- The distributed part of the output, acting on the history. -/
  Cd : L2 E h →L[ℝ] Y

namespace Model

variable {h : ℝ} (m : Model h E U Y)

/-- The neutral delay semigroup on `X = E × L²(-h, 0; E)`. -/
abbrev S : C0Semigroup ℝ (State h E) := m.toNeutral.semigroup

/-- The output `C x_t = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` as a delay functional. -/
def C : DelayOp h E Y := ⟨m.h_pos, m.NC, m.Cp, m.τC, m.τC_mem, m.Cd⟩

/-- The control operator `B u = (B₀ u, 0)`, bounded on `X`. -/
def Bop : U →L[ℝ] State h E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E (L2 E h)).symm.toContinuousLinearMap ∘L
    (m.B₀.prod 0)

/-- `B u = (B₀ u, 0)`. -/
@[simp] theorem Bop_apply (u : U) : m.Bop u = WithLp.toLp 2 (m.B₀ u, 0) := rfl

/-- The point evaluation `w ↦ g(a)` on `W = D(A)`, computed from `(v₂, (A v)₂) = (g, g')` for
`w = (v, A v)` (`pointEval_eq`). -/
def evalOp (a : ℝ) : m.S.Dom →L[ℝ] E :=
  h⁻¹ • (segOp h 0 ∘L (WithLp.sndL 2 ℝ E (L2 E h)) ∘L m.S.domIncl) +
    (segOp h 0 - h⁻¹ • (segOp h 0 ∘L primL h) - segOp h a) ∘L (WithLp.sndL 2 ℝ E (L2 E h)) ∘L
      m.S.domGen

/-- The observation operator on `W = D(A)` with the graph norm:
`C w = ∑ₖ Cₖ g(h - h'ₖ) + C_d g` for `w = (v, A v)`, `v₂ = g ∈ H¹`, with the point values computed
by `evalOp` (`Cop_apply`). -/
def Cop : m.S.Dom →L[ℝ] Y :=
  ∑ k, (m.Cp k) ∘L m.evalOp (h - m.τC k) + m.Cd ∘L (WithLp.sndL 2 ℝ E (L2 E h)) ∘L m.S.domIncl

/-- **The neutral delay system** `d/dt (x - M x_t) = L x_t + B₀ u`, `y = C x_t`
(`ex:intro-delay`) in the framework: `W = D(A)` with the graph norm (`C0Semigroup.Dom`),
`X = V = E × L²(-h, 0; E)`, `B = (B₀, 0)` bounded, `C ∈ L(W, Y)`. -/
def sys : System U m.S.Dom (State h E) (State h E) Y where
  ιW := m.S.domIncl
  ιV := ContinuousLinearMap.id ℝ _
  ιW_injective := m.S.domIncl_injective
  ιV_injective := Function.injective_id
  ιW_denseRange := m.S.denseRange_domIncl
  ιV_denseRange := denseRange_id
  SW := m.S.domSemigroup
  SX := m.S
  SV := m.S
  consistentW := m.S.consistent_domSemigroup
  consistentV := m.S.consistent_id
  B := m.Bop
  C := m.Cop

/-- The semigroup of the system on `X` is the neutral delay semigroup. -/
@[simp] theorem sys_SX : m.sys.SX = m.toNeutral.semigroup := rfl
/-- The semigroup of the system on `V = X` is the neutral delay semigroup. -/
@[simp] theorem sys_SV : m.sys.SV = m.toNeutral.semigroup := rfl
/-- `W ↪ X` is the inclusion of the generator domain. -/
@[simp] theorem sys_ιW : m.sys.ιW = m.S.domIncl := rfl
/-- `X ↪ V` is the identity. -/
@[simp] theorem sys_ιV : m.sys.ιV = ContinuousLinearMap.id ℝ _ := rfl
/-- The control operator of the system. -/
@[simp] theorem sys_B : m.sys.B = m.Bop := rfl
/-- The observation operator of the system. -/
@[simp] theorem sys_C : m.sys.C = m.Cop := rfl

/-- `ιWV = ιW` since `V = X`. -/
theorem sys_ιWV (w : m.S.Dom) : m.sys.ιWV w = m.S.domIncl w := rfl

/-- The point evaluation on `W` is the point value of the history. -/
theorem evalOp_apply (w : m.S.Dom) {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (h2 : ⇑(m.S.domIncl w).snd =ᵐ[μI h] g) {a : ℝ} (ha : a ∈ Icc 0 h) :
    m.evalOp a w = g a := by
  have hA : m.S.domGen w = WithLp.toLp 2 (m.L.eval g 0, hg.memLp_deriv.toLp g') := by
    rw [← m.S.generator_domIncl w]
    exact m.toNeutral.generator_apply _ hg h2
  have h2' : ⇑(m.S.domGen w).snd =ᵐ[μI h] g' := by
    rw [hA, WithLp.toLp_snd]
    exact hg.memLp_deriv.coeFn_toLp
  rw [← pointEval_eq m.h_pos ha hg h2 h2']
  simp only [evalOp, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, sub_apply, WithLp.sndL_apply]

/-- **The output on `D(A)`** is the paper's `y = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t`: for
`w = (v, A v)` with `v₂ = g`, `g ∈ H¹(0, h; E)` (so `v₁ = g(h) - M g`),
`C w = ∑ₖ Cₖ g(h - h'ₖ) + C_d g`. -/
theorem Cop_apply (w : m.S.Dom) {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (h2 : ⇑(m.S.domIncl w).snd =ᵐ[μI h] g) :
    m.Cop w = ∑ k, m.Cp k (g (h - m.τC k)) + m.Cd (hg.memLp.toLp g) := by
  have hsnd : (m.S.domIncl w).snd = hg.memLp.toLp g :=
    Lp.ext (h2.trans hg.memLp.coeFn_toLp.symm)
  simp only [Cop, FunLike.coe_add, FunLike.coe_sum, Pi.add_apply, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, WithLp.sndL_apply, hsnd]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [m.evalOp_apply w hg h2 ⟨by linarith [(m.τC_mem k).2], by linarith [(m.τC_mem k).1]⟩]

/-- The output on `D(A)` as the delay functional `C` evaluated on the history. -/
theorem Cop_apply_eval (w : m.S.Dom) {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (h2 : ⇑(m.S.domIncl w).snd =ᵐ[μI h] g) : m.Cop w = m.C.eval g 0 := by
  rw [m.Cop_apply w hg h2, DelayOp.eval, window_zero_eq_toLp hg.memLp]
  simp only [add_zero, C]
  rfl

/-- **`hyp:compat`** holds trivially: `D_V(A) = D(A) = W`. -/
theorem compat : m.sys.Compat := by
  refine ⟨⟨1, fun v hv => ⟨m.S.toDom ⟨v, hv⟩, rfl, ?_⟩⟩, ?_⟩
  · rw [one_mul]
    exact m.S.norm_toDom_le ⟨v, hv⟩
  · have : {w : m.S.Dom | m.sys.ιWV w ∈ m.sys.AV.domain} = univ :=
      eq_univ_of_forall fun w => m.S.domIncl_mem w
    rw [this]
    exact dense_univ

/-! ### The control convolution: `L_T u = (x(T) - M x_T, x_T)` -/

/-- The forcing `B₀ u` of an input on `(0, T]`, extended by `0`. -/
def forcing (T : ℝ) (u : ℝ → U) : ℝ → E := (Ioc 0 T).indicator fun s => m.B₀ (u s)

/-- The zero-history solution of `d/dt (x - M x_t) = L x_t + B₀ u`. -/
def ctrlSol (T : ℝ) (u : ℝ → U) : ℝ → E := m.toNeutral.sol 0 0 (m.forcing T u)

/-- The trajectory (in shifted time) of the zero-history solution. -/
def ctrlTraj (T : ℝ) (u : ℝ → U) : ℝ → E := traj h 0 (m.ctrlSol T u)

/-- The state `(x(t) - M x_t, x_t)` of the zero-history solution forced by `B₀ u`. -/
def ctrlState (T : ℝ) (u : ℝ → U) (t : ℝ) : State h E :=
  WithLp.toLp 2 (m.prim 0 0 (m.forcing T u) (m.ctrlSol T u) t, window h (m.ctrlTraj T u) t)

variable {T : ℝ} {u : ℝ → U}

/-- The forcing `B₀ u` (extended by `0`) is square integrable on every window. -/
theorem memLp_forcing (hu : MemLp u 2 (μI T)) (τ : ℝ) : MemLp (m.forcing T u) 2 (μI τ) :=
  (memLp_indicator_Ioc (m.B₀.comp_memLp' hu)).mono_measure Measure.restrict_le_self

/-- The forcing `B₀ u` is integrable on every window. -/
theorem integrableOn_forcing (hu : MemLp u 2 (μI T)) (τ : ℝ) :
    IntegrableOn (m.forcing T u) (Ioc 0 τ) :=
  (m.memLp_forcing hu τ).integrable one_le_two

/-- The zero-history solution solves the forced neutral equation. -/
theorem isSolOn_ctrlSol (hu : MemLp u 2 (μI T)) {τ : ℝ} (hτ : 0 ≤ τ) :
    m.toNeutral.IsSolOn τ 0 0 (m.forcing T u) (m.ctrlSol T u) :=
  m.toNeutral.isSolOn_sol MemLp.zero (m.integrableOn_forcing hu) hτ

/-- **Regularity of the control trajectory**: an `H¹` representative `X` of the zero-history
solution, with `X(0) = 0` and the integral form at every `t ∈ [0, T]`. -/
theorem exists_ctrl_regular (hu : MemLp u 2 (μI T)) (hT : 0 ≤ T) :
    ∃ X y : ℝ → E, m.ctrlSol T u =ᵐ[μI T] X ∧ X 0 = 0 ∧
      (∀ t ∈ Icc 0 T, X t = m.M.eval (traj h 0 X) t + m.prim 0 0 (m.forcing T u) X t) ∧
      HasWeakDeriv (h + T) (traj h 0 X) (traj h 0 y) := by
  have e : ((0 : ℝ → E) h - m.M.eval 0 0) = 0 := by simp
  have hs := m.isSolOn_ctrlSol hu hT
  rw [← e] at hs
  obtain ⟨X, y, h1, h2, h3, h4⟩ := hs.exists_hasWeakDeriv (g := (0 : ℝ → E)) (g' := 0) hT
    (HasWeakDeriv.const (T := h) (0 : E)) (m.memLp_forcing hu T)
  rw [e] at h3
  exact ⟨X, y, h1, h2, h3, h4⟩

/-- **The control state is in `D(A)`** and is a strong solution: with an `H¹` representative `Z`
of the trajectory (derivative `Z'`), `(ρ(t), x_t) ∈ D(A)` and `A (ρ(t), x_t) = (L Z_t, Z'_t)`,
and `(ρ(t), x_t) = ∫₀ᵗ ((L Z_s, Z'_s) + B u(s)) ds`. -/
theorem exists_ctrlState_strong (hu : MemLp u 2 (μI T)) (hT : 0 ≤ T) :
    ∃ Z Z' : ℝ → E, HasWeakDeriv (h + T) Z Z' ∧
      (∀ t ∈ Icc 0 T, ∃ hmem : m.ctrlState T u t ∈ m.S.generator.domain,
        m.S.generator ⟨_, hmem⟩ = WithLp.toLp 2 (m.L.eval Z t, window h Z' t)) ∧
      (∀ t ∈ Icc 0 T, m.ctrlState T u t =
        WithLp.toLp 2 (∫ s in (0 : ℝ)..t, (m.L.eval Z s + m.B₀ (u s)), window h Z t)) ∧
      window h Z 0 = 0 := by
  obtain ⟨X, y, hxX, hX0, hXeq, hZ⟩ := m.exists_ctrl_regular hu hT
  set Z := traj h 0 X with hZdef
  have htr : m.ctrlTraj T u =ᵐ[μI (h + T)] Z := traj_ae_congr_right 0 hxX
  have hZ0 : window h Z 0 = 0 := by
    rw [← window_zero (T := h) 0]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => by
      rw [hZdef, traj_of_le _ _ (by linarith [hσ.2])])
  have hfst : ∀ t ∈ Icc 0 T,
      m.prim 0 0 (m.forcing T u) (m.ctrlSol T u) t = X t - m.M.eval Z t := by
    intro t ht
    rw [m.prim_congr hxX ht, hXeq t ht]
    abel
  refine ⟨Z, traj h 0 y, hZ, fun t ht => ?_, fun t ht => ?_, hZ0⟩
  · have hgt := hasWeakDeriv_comp_add hZ ht.1 (by linarith [ht.2] : t + h ≤ h + T)
    have hZt : Z (t + h) = X t := by
      rcases ht.1.eq_or_lt with h0 | h0
      · rw [← h0, zero_add, hZdef, traj_of_le _ _ le_rfl, hX0]
        rfl
      · rw [hZdef, traj_of_lt _ _ (by linarith), add_sub_cancel_right]
    have hw : window h (m.ctrlTraj T u) t = window h Z t :=
      window_congr_ae htr ht.1 (by linarith [ht.2])
    have h1 : (m.ctrlState T u t).fst = Z (t + h) - m.M.eval (fun σ => Z (t + σ)) 0 := by
      rw [ctrlState, WithLp.toLp_fst, hfst t ht, hZt, m.M.eval_shift, add_zero]
    have h2 : ⇑(m.ctrlState T u t).snd =ᵐ[μI h] fun σ => Z (t + σ) := by
      rw [ctrlState, WithLp.toLp_snd, hw]
      exact coeFn_window (memLp_comp_add hZ.memLp ht.1 (by linarith [ht.2]))
    have hmem : m.ctrlState T u t ∈ m.S.generator.domain :=
      (m.toNeutral.mem_generator_domain_iff _).2 ⟨_, _, hgt, h1, h2⟩
    refine ⟨hmem, ?_⟩
    rw [m.toNeutral.generator_apply hmem hgt h2, m.L.eval_shift, add_zero,
      window_eq_toLp (memLp_comp_add hZ.memLp_deriv ht.1 (by linarith [ht.2]))]
  · refine state_ext ?_ ?_
    · rw [ctrlState, WithLp.toLp_fst, WithLp.toLp_fst, Equation.prim, zero_add]
      have hL := m.L.ae_eval_eq (τ := T) htr
      show ∫ s in (0 : ℝ)..t, (m.L.eval (m.ctrlTraj T u) s + m.forcing T u s) = _
      rw [intervalIntegral_congr_μI (x₁ := fun s => m.L.eval (m.ctrlTraj T u) s +
        m.forcing T u s) (x₂ := fun s => m.L.eval Z s + m.forcing T u s)
        (hL.mono fun s hs => by simp only [hs]) ht]
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [uIoc_of_le ht.1] at hs
      simp only [forcing, indicator_of_mem (Ioc_subset_Ioc_right ht.2 hs)]
    · rw [ctrlState, WithLp.toLp_snd, WithLp.toLp_snd]
      exact window_congr_ae htr ht.1 (by linarith [ht.2])

/-- The zero-history state vanishes at `t = 0`. -/
theorem ctrlState_zero : m.ctrlState T u 0 = 0 := by
  refine state_ext ?_ ?_
  · simp [ctrlState]
  · rw [ctrlState, WithLp.toLp_snd, WithLp.zero_snd, ← window_zero (T := h) 0]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => by
      rw [ctrlTraj, traj_of_le _ _ (by linarith [hσ.2])])

/-- **`L_T u = (x(T) - M x_T, x_T)`**: the mild solution `∫₀ᵗ S(t - r) B u(r) dr` is the state of
the zero-history solution of the neutral equation forced by `B₀ u` (strong solution and
uniqueness of weak solutions, `C0Semigroup.eq_mildSol_of_strong`). -/
theorem ctrlState_eq_conv (hu : MemLp u 2 (μI T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    m.ctrlState T u t = ∫ r in Ioc 0 t, m.S.real (t - r) (m.Bop (u r)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨Z, Z', hZ, hgen, hint, hZ0⟩ := m.exists_ctrlState_strong hu hT
  set G : ℝ → State h E := fun s => WithLp.toLp 2 (m.L.eval Z s, window h Z' s) with hGdef
  have hGc : ContinuousOn G (Icc 0 T) :=
    (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := L2 E h)).comp_continuousOn
      ((m.L.continuousOn_eval hZ.continuousOn).prodMk (continuousOn_window hZ.memLp_deriv))
  have hGi : IntegrableOn G (Ioc 0 T) := (hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hBi : IntegrableOn (fun s => m.Bop (u s)) (Ioc 0 T) :=
    m.Bop.integrable_comp (hu.integrable one_le_two)
  have hstrong := m.S.eq_mildSol_of_strong (τ := T) (x := m.ctrlState T u) (g := G)
    (f := fun s => m.Bop (u s)) (fun s hs => (hgen s hs).1) (fun s hs => (hgen s hs).2) hGi hBi
    ?_ t ht
  · rw [hstrong, C0Semigroup.mildSol, ctrlState_zero, map_zero, zero_add]
  intro t ht
  have hGBi : IntervalIntegrable (fun s => G s + m.Bop (u s)) volume 0 t :=
    intervalIntegrable_of_integrableOn (hGi.add hBi) ht
  have kf : (∫ s in (0 : ℝ)..t, (G s + m.Bop (u s))).fst =
      ∫ s in (0 : ℝ)..t, (G s + m.Bop (u s)).fst :=
    ((WithLp.fstL 2 ℝ E (L2 E h)).intervalIntegral_comp_comm hGBi).symm
  have ks : (∫ s in (0 : ℝ)..t, (G s + m.Bop (u s))).snd =
      ∫ s in (0 : ℝ)..t, (G s + m.Bop (u s)).snd :=
    ((WithLp.sndL 2 ℝ E (L2 E h)).intervalIntegral_comp_comm hGBi).symm
  rw [ctrlState_zero, zero_add, hint t ht]
  refine state_ext ?_ ?_
  · rw [kf]
    simp only [WithLp.add_fst, hGdef, WithLp.toLp_fst, Bop_apply]
  · rw [ks]
    simp only [WithLp.add_snd, hGdef, WithLp.toLp_snd, Bop_apply, add_zero]
    rw [← Delay.window_sub_window_eq_integral hZ m.h_pos.le ht.1 (by linarith [ht.2]), hZ0,
      sub_zero]

/-! ### The standing assumptions -/

/-- **`hyp:H1`** at every horizon: `L_T u = (x(T) - M x_T, x_T) ∈ D(A)` (`ctrlState_eq_conv`,
`exists_ctrlState_strong`), and the graph-norm bound follows from the closed graph theorem. -/
theorem H1 (T : ℝ) : m.sys.H1 T := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, fun u => ⟨0, ?_, by simp⟩⟩
    rw [map_zero, Ioc_eq_empty (not_lt.2 hT), Measure.restrict_empty, integral_zero_measure]
  have hb := System.bounded_H1 m.S m.Bop (0 : State h E →L[ℝ] Y) T
  obtain ⟨Lb, hLbdef⟩ : ∃ L, L = (System.bounded m.S m.Bop (0 : State h E →L[ℝ] Y)).Lop T :=
    ⟨_, rfl⟩
  have hLb : ∀ u : L2 U T, Lb u = ∫ r in Ioc 0 T, m.S.real (T - r) (m.Bop (u r)) := fun u => by
    have e1 := System.Lop_apply hb hT u
    have e2 := (System.bounded m.S m.Bop (0 : State h E →L[ℝ] Y)).ιWV_L hb hT (Lp.memLp u)
    rw [hLbdef, e1]
    exact e2
  have hmem : ∀ u : L2 U T, Lb u ∈ m.S.generator.domain := fun u => by
    rw [hLb u, ← m.ctrlState_eq_conv (Lp.memLp u) ⟨hT.le, le_rfl⟩]
    obtain ⟨Z, Z', -, hgen, -, -⟩ := m.exists_ctrlState_strong (Lp.memLp u) hT.le
    exact (hgen T ⟨hT.le, le_rfl⟩).1
  let Φ : L2 U T →ₗ[ℝ] m.S.Dom :=
    { toFun := fun u => m.S.toDom ⟨Lb u, hmem u⟩
      map_add' := fun u v => m.S.dom_ext (by simp only [map_add, m.S.domIncl_toDom])
      map_smul' := fun c u => m.S.dom_ext (by
        simp only [map_smul, m.S.domIncl_toDom, RingHom.id_apply]) }
  have hΦ : ∀ u, m.S.domIncl (Φ u) = Lb u := fun u => m.S.domIncl_toDom _
  have hcont : Continuous Φ := by
    refine Φ.continuous_of_isClosed_graph ?_
    have e : (Φ.graph : Set (L2 U T × m.S.Dom)) = {p | m.S.domIncl p.2 = Lb p.1} := by
      ext p
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq]
      exact ⟨fun hp => by rw [hp, hΦ], fun hp => m.S.dom_ext (by rw [hp, hΦ])⟩
    rw [e]
    exact isClosed_eq (m.S.domIncl.continuous.comp continuous_snd)
      (Lb.continuous.comp continuous_fst)
  let Φc : L2 U T →L[ℝ] m.S.Dom := ⟨Φ, hcont⟩
  refine ⟨‖Φc‖, fun u => ⟨Φc u, ?_, Φc.le_opNorm u⟩⟩
  rw [sys_ιWV, show Φc u = Φ u from rfl, hΦ, hLb]
  rfl

/-- **`L_T u = (x(T) - M x_T, x_T)`** (`ex:intro-delay`): the control-to-state map of the system
is the state of the zero-history solution of the neutral equation forced by `B₀ u`. -/
theorem ιW_L {T : ℝ} (hT : 0 < T) (u : L2 U T) :
    m.sys.ιW (m.sys.L T u) = m.ctrlState T u T := by
  have := m.sys.ιWV_L (m.H1 T) hT (Lp.memLp u)
  rw [sys_ιWV] at this
  rw [sys_ιW, this, m.ctrlState_eq_conv (Lp.memLp u) ⟨hT.le, le_rfl⟩]
  rfl

/-- **`hyp:H2`** at every horizon: for `w ∈ W` with `v = ιW w = (g(h) - M g, g)`, the output
`C S(t) w = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` is `C` evaluated along an `H¹` representative `Z` of the
trajectory, so `‖C S(·) w‖_{L²(0, T)} ≤ (∑ₖ ‖Cₖ‖ + √T ‖C_d‖) ‖Z‖_{L²(0, h + T)}`, and
`‖Z‖ ≤ (1 + 2 ‖(1 - 𝒦)⁻¹‖ c(T)) ‖v‖_X` (`Equation.eLpNorm_trajOf_le`). -/
theorem H2 (T : ℝ) : m.sys.H2 T := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, fun w => ?_⟩
    have : μI T = 0 := by simp [μI, Ioc_eq_empty (not_lt.2 hT)]
    simp [this]
  refine ⟨m.C.bound T * (1 + 2 * m.toNeutral.solBound T), fun w => ?_⟩
  set v := m.S.domIncl w with hvdef
  obtain ⟨g, g', hg, h1, h2⟩ :=
    m.toNeutral.exists_hasWeakDeriv_of_mem_generator_domain (m.S.domIncl_mem w)
  have hso : m.toNeutral.IsSolOn T (g h - m.M.eval g 0) g 0 (m.toNeutral.orbit v) := by
    rw [← h1]
    exact (m.toNeutral.isSolOn_orbit v hT.le).congr_hist h2
  obtain ⟨X, y, hxX, -, -, hZ⟩ := hso.exists_hasWeakDeriv hT.le hg MemLp.zero
  set Z := traj h g X with hZdef
  have htr : m.toNeutral.trajOf v =ᵐ[μI (h + T)] Z :=
    (traj_ae_congr h2 _ _).trans (traj_ae_congr_right g hxX)
  have hy : (fun t => m.sys.C (m.sys.SW.real t w)) =ᵐ[μI T] m.C.eval Z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hst : m.S.domIncl (m.sys.SW.real t w) = m.toNeutral.stateAt v t := by
      show m.S.domIncl (m.S.domSemigroup.real t w) = _
      rw [C0Semigroup.domIncl_domSemigroup_real, ← hvdef, Equation.semigroup_real_apply _ ht.1.le]
    have hgt := hasWeakDeriv_comp_add hZ ht.1.le (by linarith [ht.2] : t + h ≤ h + T)
    have h2' : ⇑(m.S.domIncl (m.sys.SW.real t w)).snd =ᵐ[μI h] fun σ => Z (t + σ) := by
      rw [hst, Equation.stateAt_snd, window_congr_ae htr ht.1.le (by linarith [ht.2])]
      exact coeFn_window (memLp_comp_add hZ.memLp ht.1.le (by linarith [ht.2]))
    rw [sys_C, m.Cop_apply_eval _ hgt h2', m.C.eval_shift, add_zero]
  have hb := m.C.eLpNorm_eval_le hT.le hZ.memLp
  have hZn : (eLpNorm Z 2 (μI (h + T))).toReal ≤ (1 + 2 * m.toNeutral.solBound T) * ‖v‖ := by
    rw [← eLpNorm_congr_ae htr]
    exact m.toNeutral.eLpNorm_trajOf_le v hT.le
  rw [eLpNorm_congr_ae hy, ← ENNReal.ofReal_toReal (m.C.memLp_eval hZ.memLp).eLpNorm_ne_top,
    sys_ιWV, ← hvdef]
  refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hZn (m.C.bound_nonneg T)

end Model

/-- The paper's setting `x(t) ∈ ℝⁿ`, `u(t) ∈ ℝᵐ`, `y(t) ∈ ℝᵖ` is an instance. -/
example (n k p : ℕ) {h : ℝ} (m : Model h (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin k))
    (EuclideanSpace ℝ (Fin p))) (T : ℝ) : m.sys.H1 T ∧ m.sys.H2 T ∧ m.sys.Compat :=
  ⟨m.H1 T, m.H2 T, m.compat⟩

end NeutralDelay

end DataDrivenControl
