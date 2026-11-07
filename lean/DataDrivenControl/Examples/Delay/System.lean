module

public import DataDrivenControl.Examples.Delay.Semigroup
public import DataDrivenControl.Semigroup.DomainSpace
public import DataDrivenControl.System.Mild

/-!
# The delay system fits the framework

* `Delay.Model h E U Y`: the retarded equation (`Delay.Equation`), the input matrix `B₀` and the
  delayed output `y(t) = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` (output delays `h'ₖ ∈ [0, h]`, `C_d`
  bounded on the `L²` history).
* `Model.sys : System U W X V Y` with `X = V = E × L²(-h, 0; E)` (`Delay.State`), `W = D(A)` with
  the graph norm (`C0Semigroup.Dom`, `SW = domSemigroup`), `B = (B₀, 0)` (`Model.Bop`, bounded by
  construction) and `C = Model.Cop ∈ L(W, Y)`, defined on the graph by
  `C (v, A v) = ∑ₖ Cₖ (v₁ - ∫_{(h - h'ₖ, h]} (A v)₂) + C_d v₂`; on `v = (g(h), g)`, `g ∈ H¹`, it is
  the paper's output `∑ₖ Cₖ g(h - h'ₖ) + C_d g` (`Cop_apply`).
* `ctrlState_eq_conv`, `ιW_L`: `L_T u = (x(T), x_T)` for the zero-history solution forced by
  `B₀ u` (`ctrlState`); the proof shows that `t ↦ (x(t), x_t)` is a strong solution
  (`ctrlState_mem_and_generator`, the generator characterisation of `Delay/Semigroup`, and the
  integrated form `window_sub_window_eq_integral`) and applies
  `C0Semigroup.eq_mildSol_of_strong` (uniqueness of weak solutions, Ball).
* `Model.H1`, `Model.H2` at every horizon, and `Model.compat`.  `hyp:H1`: `L_T u ∈ D(A)`, and the
  graph-norm bound comes from the closed graph theorem.
* Unboundedness of `C` on `X` when an output delay is positive: `Delay/Unbounded`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E U Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Translates of `H¹` signals are `H¹`. -/
theorem hasWeakDeriv_comp_add {T₁ T t : ℝ} {z z' : ℝ → E} (hz : HasWeakDeriv T₁ z z')
    (ht : 0 ≤ t) (htT : t + T ≤ T₁) :
    HasWeakDeriv T (fun σ => z (t + σ)) (fun σ => z' (t + σ)) := by
  refine ⟨memLp_comp_add hz.memLp_deriv ht htT, fun σ hσ => ?_⟩
  have hi : IntegrableOn z' (Ioc 0 T₁) := hz.memLp_deriv.integrable one_le_two
  have h1 : t + σ ∈ Icc 0 T₁ := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have h2 : t ∈ Icc 0 T₁ := ⟨ht, by linarith [hσ.1, hσ.2]⟩
  show z (t + σ) = z (t + 0) + ∫ s in (0 : ℝ)..σ, z' (t + s)
  rw [add_zero, hz.eq_add_integral _ h1, hz.eq_add_integral _ h2, add_assoc,
    ← intervalIntegral.integral_add_adjacent_intervals (b := t)
      (intervalIntegrable_of_integrableOn hi h2)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hσ.1])).2
        (hi.mono_set (Ioc_subset_Ioc ht h1.2))),
    intervalIntegral.integral_comp_add_left (fun s => z' s) t, add_zero]

/-- `‖f‖_{L²(0, T)} ≤ √T c` when `‖f‖ ≤ c` a.e. -/
theorem norm_L2_le_of_ae_bound {F : Type*} [NormedAddCommGroup F] {T : ℝ} (hT : 0 ≤ T)
    (f : L2 F T) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ᵐ t ∂(μI T), ‖f t‖ ≤ c) : ‖f‖ ≤ √T * c := by
  refine (Lp.norm_le_of_ae_bound hc hf).trans_eq ?_
  rw [measureUnivNNReal_μI hT, Real.sqrt_eq_rpow]
  norm_num

/-- The representative of a finite sum in `L²`. -/
theorem coeFn_sum_L2 {F : Type*} [NormedAddCommGroup F] {T : ℝ} {ι : Type*} (s : Finset ι)
    (f : ι → L2 F T) : ⇑(∑ i ∈ s, f i) =ᵐ[μI T] fun t => ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero F 2 (μI T)] with t ht
    rw [Finset.sum_empty, Finset.sum_empty, ht]
    rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with t h1 h2
    rw [h1, Pi.add_apply, h2]

/-- The integral over the end segment `(a, h]` of the history, a bounded operator on `L²`. -/
def segOp (h a : ℝ) : L2 E h →L[ℝ] E :=
  kernelOp h ((Ioc a h).indicator fun _ => ContinuousLinearMap.id ℝ E)

/-- `segOp h a w = ∫_{(a, h]} w` for `0 ≤ a`. -/
theorem segOp_apply {h a : ℝ} (ha : 0 ≤ a) (w : L2 E h) : segOp h a w = ∫ s in Ioc a h, w s := by
  have hA : MemLp ((Ioc a h).indicator fun _ : ℝ => ContinuousLinearMap.id ℝ E) 2 (μI h) :=
    (memLp_const _).indicator measurableSet_Ioc.nullMeasurableSet
  rw [segOp, kernelOp_apply hA]
  have e : (fun s => ((Ioc a h).indicator (fun _ : ℝ => ContinuousLinearMap.id ℝ E) s) (w s)) =
      (Ioc a h).indicator (fun s => w s) := by
    funext s
    by_cases hs : s ∈ Ioc a h <;> simp [hs]
  rw [e, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (Ioc_subset_Ioc_left ha)]

/-- The integral form of `H¹` on an end segment: `g(h) - ∫_{(a, h]} g' = g(a)`. -/
theorem sub_integral_Ioc_of_hasWeakDeriv {h a : ℝ} {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (ha : a ∈ Icc 0 h) : g h - ∫ s in Ioc a h, g' s = g a := by
  have hi : IntegrableOn g' (Ioc 0 h) := hg.memLp_deriv.integrable one_le_two
  have hh : h ∈ Icc 0 h := ⟨ha.1.trans ha.2, le_rfl⟩
  rw [← intervalIntegral.integral_of_le ha.2, hg.eq_add_integral h hh, hg.eq_add_integral a ha,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a)
      (intervalIntegrable_of_integrableOn hi ha)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.2).2
        (hi.mono_set (Ioc_subset_Ioc ha.1 le_rfl)))]
  abel

/-- **Data of the delay system with delayed output** (`ex:intro-delay`, `M = 0`): the retarded
equation `Equation`, the input matrix `B₀`, and the output
`y(t) = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` with finitely many output delays `h'ₖ ∈ [0, h]` and a
distributed part `C_d` bounded on the `L²` history (`kernelOp` gives the paper's
`∫_{-h}^0 C_d(θ) x(t + θ) dθ`). -/
structure Model (h : ℝ) (E U Y : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] extends Equation h E where
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

/-- The delay semigroup on `X = E × L²(-h, 0; E)`. -/
abbrev S : C0Semigroup ℝ (State h E) := m.toEquation.semigroup

/-- The control operator `B u = (B₀ u, 0)`, bounded on `X`. -/
def Bop : U →L[ℝ] State h E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E (L2 E h)).symm.toContinuousLinearMap ∘L
    (m.B₀.prod 0)

/-- `B u = (B₀ u, 0)`. -/
@[simp] theorem Bop_apply (u : U) : m.Bop u = WithLp.toLp 2 (m.B₀ u, 0) := rfl

/-- The observation operator on `W = D(A)` with the graph norm: for `w = (v, A v)`,
`C w = ∑ₖ Cₖ (v₁ - ∫_{(h - h'ₖ, h]} (A v)₂) + C_d v₂`.  On `v = (g(h), g)`, `g ∈ H¹`, this is
`∑ₖ Cₖ g(h - h'ₖ) + C_d g` (`Cop_apply`): the paper's `C x_t`. -/
def Cop : m.S.Dom →L[ℝ] Y :=
  ∑ k, (m.Cp k) ∘L ((WithLp.fstL 2 ℝ E (L2 E h)) ∘L m.S.domIncl -
      segOp h (h - m.τC k) ∘L (WithLp.sndL 2 ℝ E (L2 E h)) ∘L m.S.domGen) +
    m.Cd ∘L (WithLp.sndL 2 ℝ E (L2 E h)) ∘L m.S.domIncl

/-- **The delay system** `ẋ = A x + B u`, `y = C x` (`ex:intro-delay`) in the framework:
`W = D(A)` with the graph norm (`C0Semigroup.Dom`), `X = V = E × L²(-h, 0; E)`, `B = (B₀, 0)`
bounded, `C ∈ L(W, Y)`. -/
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

/-- The semigroup of the system on `X` is the delay semigroup. -/
@[simp] theorem sys_SX : m.sys.SX = m.toEquation.semigroup := rfl
@[simp] theorem sys_SV : m.sys.SV = m.toEquation.semigroup := rfl
@[simp] theorem sys_ιW : m.sys.ιW = m.S.domIncl := rfl
@[simp] theorem sys_ιV : m.sys.ιV = ContinuousLinearMap.id ℝ _ := rfl
@[simp] theorem sys_B : m.sys.B = m.Bop := rfl
@[simp] theorem sys_C : m.sys.C = m.Cop := rfl

/-- `ιWV = ιW` since `V = X`. -/
theorem sys_ιWV (w : m.S.Dom) : m.sys.ιWV w = m.S.domIncl w := rfl

/-- **The output on `D(A)`** is the paper's `y = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t`: for
`w = (v, A v)` with `v = (g(h), g)`, `g ∈ H¹(0, h; E)`, `C w = ∑ₖ Cₖ g(h - h'ₖ) + C_d g`. -/
theorem Cop_apply (w : m.S.Dom) {g g' : ℝ → E} (hg : HasWeakDeriv h g g')
    (h1 : (m.S.domIncl w).fst = g h) (h2 : ⇑(m.S.domIncl w).snd =ᵐ[μI h] g) :
    m.Cop w = ∑ k, m.Cp k (g (h - m.τC k)) + m.Cd (hg.memLp.toLp g) := by
  have hA : m.S.domGen w = WithLp.toLp 2 (m.rhs g 0, hg.memLp_deriv.toLp g') := by
    rw [← m.S.generator_domIncl w]
    exact m.toEquation.generator_apply _ hg h1 h2
  have hsnd : (m.S.domIncl w).snd = hg.memLp.toLp g :=
    Lp.ext (h2.trans hg.memLp.coeFn_toLp.symm)
  simp only [Cop, FunLike.coe_add, FunLike.coe_sum, Pi.add_apply, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, FunLike.coe_sub, Pi.sub_apply, WithLp.fstL_apply,
    WithLp.sndL_apply, hA, WithLp.toLp_snd, hsnd, h1]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : h - m.τC k ∈ Icc 0 h := ⟨by linarith [(m.τC_mem k).2], by linarith [(m.τC_mem k).1]⟩
  rw [segOp_apply hk.1]
  have e : ∫ s in Ioc (h - m.τC k) h, (hg.memLp_deriv.toLp g') s =
      ∫ s in Ioc (h - m.τC k) h, g' s :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hk.1 le_rfl)
      hg.memLp_deriv.coeFn_toLp)
  rw [e, sub_integral_Ioc_of_hasWeakDeriv hg hk]

/-- **`hyp:compat`** holds trivially: `D_V(A) = D(A) = W`. -/
theorem compat : m.sys.Compat := by
  refine ⟨⟨1, fun v hv => ⟨m.S.toDom ⟨v, hv⟩, rfl, ?_⟩⟩, ?_⟩
  · rw [one_mul]
    exact m.S.norm_toDom_le ⟨v, hv⟩
  · have : {w : m.S.Dom | m.sys.ιWV w ∈ m.sys.AV.domain} = univ :=
      eq_univ_of_forall fun w => m.S.domIncl_mem w
    rw [this]
    exact dense_univ

/-! ### The control convolution: `L_T u = (x(T), x_T)` -/

/-- The forcing `B₀ u` of an input on `(0, T]`, extended by `0`. -/
def forcing (T : ℝ) (u : ℝ → U) : ℝ → E := (Ioc 0 T).indicator fun s => m.B₀ (u s)

/-- The zero-history solution of `ẋ = L x_t + B₀ u` on `[0, T]`. -/
def ctrlSol (T : ℝ) (u : ℝ → U) : ℝ → E := m.sol 0 0 (m.forcing T u)

/-- The trajectory (in shifted time) of the zero-history solution. -/
def ctrlTraj (T : ℝ) (u : ℝ → U) : ℝ → E := traj h 0 (m.ctrlSol T u)

/-- The state `(x(t), x_t)` of the zero-history solution forced by `B₀ u`. -/
def ctrlState (T : ℝ) (u : ℝ → U) (t : ℝ) : State h E :=
  WithLp.toLp 2 (m.ctrlSol T u t, window h (m.ctrlTraj T u) t)

variable {T : ℝ} {u : ℝ → U}

/-- The forcing `B₀ u` (extended by `0`) is square integrable on every window. -/
theorem memLp_forcing (hu : MemLp u 2 (μI T)) (τ : ℝ) : MemLp (m.forcing T u) 2 (μI τ) :=
  (memLp_indicator_Ioc (m.B₀.comp_memLp' hu)).mono_measure Measure.restrict_le_self

/-- The forcing `B₀ u` is integrable on every window. -/
theorem integrableOn_forcing (hu : MemLp u 2 (μI T)) (τ : ℝ) :
    IntegrableOn (m.forcing T u) (Ioc 0 τ) :=
  (m.memLp_forcing hu τ).integrable one_le_two

/-- The zero-history solution solves the forced delay equation on every `[0, τ]`. -/
theorem isSolOn_ctrlSol (hu : MemLp u 2 (μI T)) (τ : ℝ) :
    m.IsSolOn τ ((0 : ℝ → E) h) 0 (m.forcing T u) (m.ctrlSol T u) :=
  m.isSolOn_sol MemLp.zero (m.integrableOn_forcing hu τ)

/-- The trajectory of the zero-history solution is `H¹` on `[0, h + T]`. -/
theorem hasWeakDeriv_ctrlTraj (hu : MemLp u 2 (μI T)) (hT : 0 ≤ T) :
    HasWeakDeriv (h + T) (m.ctrlTraj T u)
      (traj h 0 fun s => m.rhs (m.ctrlTraj T u) s + m.forcing T u s) :=
  m.hasWeakDeriv_traj hT (HasWeakDeriv.const (T := h) (0 : E) : HasWeakDeriv h (0 : ℝ → E) 0)
    (m.memLp_forcing hu T) (m.isSolOn_ctrlSol hu T)

/-- `z(t + h) = x(t)` for the zero-history trajectory. -/
theorem ctrlTraj_add_h (t : ℝ) (ht : 0 ≤ t) : m.ctrlTraj T u (t + h) = m.ctrlSol T u t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_add, ctrlTraj, traj_of_le _ _ le_rfl, ctrlSol, Equation.sol_zero_time]
    rfl
  · rw [ctrlTraj, traj_of_lt _ _ (by linarith), add_sub_cancel_right]

/-- **The control state is in `D(A)`**, with `A (x(t), x_t) = (L x_t, ẋ_t)`. -/
theorem ctrlState_mem_and_generator (hu : MemLp u 2 (μI T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ hmem : m.ctrlState T u t ∈ m.S.generator.domain,
      m.S.generator ⟨_, hmem⟩ = WithLp.toLp 2 (m.rhs (m.ctrlTraj T u) t,
        window h (traj h 0 fun s => m.rhs (m.ctrlTraj T u) s + m.forcing T u s) t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hz := m.hasWeakDeriv_ctrlTraj hu hT
  have hgt := hasWeakDeriv_comp_add hz ht.1 (by linarith [ht.2] : t + h ≤ h + T)
  have h1 : (m.ctrlState T u t).fst = m.ctrlTraj T u (t + h) :=
    (m.ctrlTraj_add_h t ht.1).symm
  have h2 : ⇑(m.ctrlState T u t).snd =ᵐ[μI h] fun σ => m.ctrlTraj T u (t + σ) :=
    coeFn_window (memLp_comp_add hz.memLp ht.1 (by linarith [ht.2]))
  have hmem : m.ctrlState T u t ∈ m.S.generator.domain :=
    (m.mem_generator_domain_iff _).2 ⟨_, _, hgt, h1, h2⟩
  refine ⟨hmem, ?_⟩
  rw [m.generator_apply hmem hgt h1 h2, m.rhs_shift, add_zero,
    window_eq_toLp (memLp_comp_add hz.memLp_deriv ht.1 (by linarith [ht.2]))]

/-- The zero-history state vanishes at `t = 0`. -/
theorem ctrlState_zero : m.ctrlState T u 0 = 0 := by
  refine state_ext ?_ ?_
  · simp [ctrlState, ctrlSol]
  · rw [ctrlState, WithLp.toLp_snd, WithLp.zero_snd, ← window_zero (T := h) 0]
    exact window_congr (ae_restrict_of_forall_mem measurableSet_Ioc fun σ hσ => by
      rw [ctrlTraj, traj_of_le _ _ (by linarith [hσ.2])])

/-- **`L_T u = (x(T), x_T)`**: the mild solution `∫₀ᵗ S(t - r) B u(r) dr` is the state of the
zero-history solution of the delay equation forced by `B₀ u` (integrated form and uniqueness of
weak solutions, `C0Semigroup.eq_mildSol_of_strong`). -/
theorem ctrlState_eq_conv (hu : MemLp u 2 (μI T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    m.ctrlState T u t = ∫ r in Ioc 0 t, m.S.real (t - r) (m.Bop (u r)) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hz := m.hasWeakDeriv_ctrlTraj hu hT
  set z := m.ctrlTraj T u with hzdef
  set z' := traj h 0 fun s => m.rhs z s + m.forcing T u s with hz'def
  set G : ℝ → State h E := fun s => WithLp.toLp 2 (m.rhs z s, window h z' s) with hGdef
  have hGc : ContinuousOn G (Icc 0 T) :=
    (WithLp.prod_continuous_toLp (p := 2) (α := E) (β := L2 E h)).comp_continuousOn
      ((m.continuousOn_rhs hz.continuousOn).prodMk (continuousOn_window hz.memLp_deriv))
  have hGi : IntegrableOn G (Ioc 0 T) := (hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hBi : IntegrableOn (fun s => m.Bop (u s)) (Ioc 0 T) :=
    m.Bop.integrable_comp (hu.integrable one_le_two)
  have hstrong := m.S.eq_mildSol_of_strong (τ := T) (x := m.ctrlState T u) (g := G)
    (f := fun s => m.Bop (u s)) (fun s hs => (m.ctrlState_mem_and_generator hu hs).1)
    (fun s hs => (m.ctrlState_mem_and_generator hu hs).2) hGi hBi ?_ t ht
  · rw [hstrong, C0Semigroup.mildSol, ctrlState_zero, map_zero, zero_add]
  intro t ht
  have hGBi : IntervalIntegrable (fun s => G s + m.Bop (u s)) volume 0 t :=
    intervalIntegrable_of_integrableOn (hGi.add hBi) ht
  rw [ctrlState_zero, zero_add]
  have kf : (∫ s in (0 : ℝ)..t, (G s + m.Bop (u s))).fst =
      ∫ s in (0 : ℝ)..t, (G s + m.Bop (u s)).fst :=
    ((WithLp.fstL 2 ℝ E (L2 E h)).intervalIntegral_comp_comm hGBi).symm
  have ks : (∫ s in (0 : ℝ)..t, (G s + m.Bop (u s))).snd =
      ∫ s in (0 : ℝ)..t, (G s + m.Bop (u s)).snd :=
    ((WithLp.sndL 2 ℝ E (L2 E h)).intervalIntegral_comp_comm hGBi).symm
  refine state_ext ?_ ?_
  · rw [kf]
    simp only [WithLp.add_fst, hGdef, WithLp.toLp_fst, Bop_apply, ctrlState]
    rw [(m.isSolOn_ctrlSol hu T).2 t ht, Pi.zero_apply, zero_add]
    · refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [uIoc_of_le ht.1] at hs
      simp only [forcing, indicator_of_mem (Ioc_subset_Ioc_right ht.2 hs)]
      rfl
  · rw [ks]
    simp only [WithLp.add_snd, hGdef, WithLp.toLp_snd, Bop_apply, add_zero, ctrlState]
    have hw0 : window h z 0 = 0 := by
      have := congrArg WithLp.snd (m.ctrlState_zero (T := T) (u := u))
      simpa [ctrlState] using this
    rw [← window_sub_window_eq_integral hz m.h_pos.le ht.1 (by linarith [ht.2]), hw0, sub_zero]

/-! ### The standing assumptions -/

/-- **`hyp:H1`** at every horizon: `L_T u = (x(T), x_T) ∈ D(A)` (`ctrlState_eq_conv`,
`ctrlState_mem_and_generator`), and the graph-norm bound follows from the closed graph theorem
(`u ↦ (L_T u, A L_T u)` is linear with closed graph, since `L_T ∈ L(L², X)` and `A` is closed). -/
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
    exact (m.ctrlState_mem_and_generator (Lp.memLp u) ⟨hT.le, le_rfl⟩).1
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

/-- **`L_T u = (x(T), x_T)`** (`ex:intro-delay`): the control-to-state map of the system is the
state of the zero-history solution of the delay equation forced by `B₀ u`. -/
theorem ιW_L {T : ℝ} (hT : 0 < T) (u : L2 U T) :
    m.sys.ιW (m.sys.L T u) = m.ctrlState T u T := by
  have := m.sys.ιWV_L (m.H1 T) hT (Lp.memLp u)
  rw [sys_ιWV] at this
  rw [sys_ιW, this, m.ctrlState_eq_conv (Lp.memLp u) ⟨hT.le, le_rfl⟩]
  rfl

/-- **`hyp:H2`** at every horizon: for `w = (v, A v)`, `v = (g(h), g)`, the output
`C S(t) w = ∑ₖ Cₖ x(t - h'ₖ) + C_d x_t` is bounded in `L²(0, T; Y)` by the `L²` norm of the
trajectory on `(-h, T)`, hence by `‖v‖_X` (Grönwall). -/
theorem H2 (T : ℝ) : m.sys.H2 T := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, fun w => ?_⟩
    have : μI T = 0 := by simp [μI, Ioc_eq_empty (not_lt.2 hT)]
    simp [this]
  set Kc : ℝ := ∑ k, ‖m.Cp k‖ + √T * ‖m.Cd‖ with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set c₁ : ℝ := 1 + √(h + T) * ((1 + m.Kψ T) * Real.exp (m.K * T)) with hc₁
  refine ⟨Kc * c₁, fun w => ?_⟩
  obtain ⟨g, g', hg, h1, h2⟩ :=
    m.exists_hasWeakDeriv_of_mem_generator_domain (m.S.domIncl_mem w)
  have hx : m.IsSolOn T (g h) g 0 (m.sol (g h) g 0) :=
    m.isSolOn_sol hg.memLp (Equation.integrableOn_zero_forcing T)
  have hz := m.hasWeakDeriv_traj hT.le hg MemLp.zero hx
  have hzL : MemLp (traj h g (m.sol (g h) g 0)) 2 (μI (h + T)) := hz.memLp
  set z := traj h g (m.sol (g h) g 0) with hzdef
  set Z := (eLpNorm z 2 (μI (h + T))).toReal with hZdef
  have hZ0 : 0 ≤ Z := ENNReal.toReal_nonneg
  set v := m.S.domIncl w with hvdef
  -- Step 1: `Z ≤ c₁ ‖v‖`.
  have hgv : (eLpNorm g 2 (μI h)).toReal = ‖v.snd‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae h2]
  have hv1 : ‖v.fst‖ ≤ ‖v‖ := WithLp.norm_fst_le (x := v)
  have hv2 : ‖v.snd‖ ≤ ‖v‖ := WithLp.norm_snd_le (x := v)
  have hKψ := m.Kψ_nonneg hT.le
  set M := (1 + m.Kψ T) * Real.exp (m.K * T) * ‖v‖ with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hxM : ∀ t ∈ Icc 0 T, ‖m.sol (g h) g 0 t‖ ≤ M := by
    intro t ht
    refine (m.norm_sol_le hg.memLp (Equation.integrableOn_zero_forcing T) ht).trans ?_
    simp only [Pi.zero_apply, norm_zero, integral_zero, add_zero]
    rw [hgv, ← h1]
    have : ‖v.fst‖ + m.Kψ T * ‖v.snd‖ ≤ (1 + m.Kψ T) * ‖v‖ := by nlinarith
    calc (‖v.fst‖ + m.Kψ T * ‖v.snd‖) * Real.exp (m.K * T)
        ≤ ((1 + m.Kψ T) * ‖v‖) * Real.exp (m.K * T) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = M := by rw [hMdef]; ring
  have hZ : Z ≤ c₁ * ‖v‖ := by
    have hg0 : MemLp (traj h g 0) 2 (μI (h + T)) :=
      memLp_traj m.h_pos.le hT.le hg.memLp continuous_zero.continuousOn
    have hx0 : MemLp (traj h 0 (m.sol (g h) g 0)) 2 (μI (h + T)) :=
      memLp_traj m.h_pos.le hT.le MemLp.zero hx.1
    have e : z = traj h g 0 + traj h 0 (m.sol (g h) g 0) := by
      rw [hzdef, ← traj_add, add_zero, zero_add]
    have hZe : Z = ‖hzL.toLp z‖ := by rw [Lp.norm_toLp]
    have hsplit : hzL.toLp z = hg0.toLp _ + hx0.toLp _ := by
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (ae_of_all _ fun σ => by rw [e])
    have b1 : ‖hg0.toLp (traj h g 0)‖ = ‖v.snd‖ := by
      rw [Lp.norm_toLp, Equation.eLpNorm_traj_zero hT.le, hgv]
    have b2 : ‖hx0.toLp (traj h 0 (m.sol (g h) g 0))‖ ≤ √(h + T) * M := by
      refine norm_L2_le_of_ae_bound (by linarith [m.h_pos]) _ hM0 ?_
      filter_upwards [hx0.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with σ hσ hσI
      rw [hσ]
      exact norm_traj_zero_le hM0 hxM (by linarith [hσI.2])
    rw [hZe, hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [b1]
    calc ‖v.snd‖ + ‖hx0.toLp (traj h 0 (m.sol (g h) g 0))‖ ≤ ‖v‖ + √(h + T) * M :=
          add_le_add hv2 b2
      _ = c₁ * ‖v‖ := by rw [hc₁, hMdef]; ring
  -- Step 2: the output formula.
  have hy : ∀ᵐ t ∂(μI T), m.sys.C (m.sys.SW.real t w) =
      ∑ k, m.Cp k (z (h - m.τC k + t)) + m.Cd (window h z t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hst : m.S.domIncl (m.sys.SW.real t w) =
        WithLp.toLp 2 (m.sol (g h) g 0 t, window h z t) := by
      show m.S.domIncl (m.S.domSemigroup.real t w) = _
      rw [C0Semigroup.domIncl_domSemigroup_real, ← hvdef, Equation.semigroup_real_apply _ ht.1.le,
        Equation.eq_toLp_of_hasWeakDeriv hg h1 h2, Equation.stateAt_of_hasWeakDeriv _ hg ht.1.le]
    have hgt := hasWeakDeriv_comp_add hz ht.1.le (by linarith [ht.2] : t + h ≤ h + T)
    have h1' : (m.S.domIncl (m.sys.SW.real t w)).fst = z (t + h) := by
      rw [hst, WithLp.toLp_fst, hzdef, traj_of_lt _ _ (by linarith [ht.1]), add_sub_cancel_right]
    have hzw : MemLp (fun σ => z (t + σ)) 2 (μI h) :=
      memLp_comp_add hzL ht.1.le (by linarith [ht.2])
    have h2' : ⇑(m.S.domIncl (m.sys.SW.real t w)).snd =ᵐ[μI h] fun σ => z (t + σ) := by
      rw [hst, WithLp.toLp_snd]
      exact coeFn_window hzw
    rw [sys_C, m.Cop_apply _ hgt h1' h2', ← window_eq_toLp hzw]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [add_comm t]
  -- Step 3: the output as an element of `L²(0, T; Y)`.
  have hQ : MemLp (fun t => m.Cd (window h z t)) 2 (μI T) :=
    memLp_μI_of_continuousOn (m.Cd.continuous.comp_continuousOn (continuousOn_window hzL))
  set Yw : L2 Y T := ∑ k, (m.Cp k).compLp (window T z (h - m.τC k)) + hQ.toLp _ with hYw
  have hk0 : ∀ k, 0 ≤ h - m.τC k := fun k => by linarith [(m.τC_mem k).2]
  have hkT : ∀ k, h - m.τC k + T ≤ h + T := fun k => by linarith [(m.τC_mem k).1]
  have hYe : ⇑Yw =ᵐ[μI T] fun t => ∑ k, m.Cp k (z (h - m.τC k + t)) + m.Cd (window h z t) := by
    have hc : ∀ᵐ t ∂(μI T), ∀ k,
        ((m.Cp k).compLp (window T z (h - m.τC k))) t = m.Cp k (z (h - m.τC k + t)) := by
      refine ae_all_iff.2 fun k => ?_
      filter_upwards [(m.Cp k).coeFn_compLp' (window T z (h - m.τC k)),
        coeFn_window_of_memLp hzL (hk0 k) (hkT k)] with t e1 e2
      rw [e1, e2]
    filter_upwards [Lp.coeFn_add (∑ k, (m.Cp k).compLp (window T z (h - m.τC k))) (hQ.toLp _),
      coeFn_sum_L2 Finset.univ fun k => (m.Cp k).compLp (window T z (h - m.τC k)),
      hQ.coeFn_toLp, hc] with t e1 e2 e3 e4
    rw [hYw, e1, Pi.add_apply, e2, e3]
    simp only [e4]
  have hYn : ‖Yw‖ ≤ Kc * Z := by
    have b1 : ‖∑ k, (m.Cp k).compLp (window T z (h - m.τC k))‖ ≤ ∑ k, ‖m.Cp k‖ * Z :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ =>
        ((m.Cp k).norm_compLp_le _).trans (mul_le_mul_of_nonneg_left
          (norm_window_le hzL (hk0 k) (hkT k)) (norm_nonneg _)))
    have b2 : ‖hQ.toLp (fun t => m.Cd (window h z t))‖ ≤ √T * (‖m.Cd‖ * Z) := by
      refine norm_L2_le_of_ae_bound hT.le _ (by positivity) ?_
      filter_upwards [hQ.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t e1 e2
      rw [e1]
      exact m.Cd.le_opNorm_of_le (norm_window_le hzL e2.1.le (by linarith [e2.2]))
    refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans_eq ?_)
    rw [hKc, add_mul, Finset.sum_mul]
    ring
  have hy' : (fun t => m.sys.C (m.sys.SW.real t w)) =ᵐ[μI T]
      fun t => ∑ k, m.Cp k (z (h - m.τC k + t)) + m.Cd (window h z t) := hy
  rw [eLpNorm_congr_ae (hy'.trans hYe.symm), ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top Yw),
    ← Lp.norm_def, sys_ιWV, ← hvdef]
  refine ENNReal.ofReal_le_ofReal (hYn.trans ?_)
  calc Kc * Z ≤ Kc * (c₁ * ‖v‖) := mul_le_mul_of_nonneg_left hZ hKc0
    _ = Kc * c₁ * ‖v‖ := by ring

end Model

/-- The paper's setting `x(t) ∈ ℝⁿ`, `u(t) ∈ ℝᵐ`, `y(t) ∈ ℝᵖ` is an instance. -/
example (n k p : ℕ) {h : ℝ} (m : Model h (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin k))
    (EuclideanSpace ℝ (Fin p))) (T : ℝ) : m.sys.H1 T ∧ m.sys.H2 T ∧ m.sys.Compat :=
  ⟨m.H1 T, m.H2 T, m.compat⟩

end Delay

end DataDrivenControl
