module

public import DataDrivenControl.Examples.Delay.Solution

/-!
# Regularity of the delay equation

For an `H¹` history `g` with the compatible initial value `r = g(h) - M g` and an `L²` forcing,
the solution of the delay equation of `ex:intro-delay` is `H¹`, and the trajectory
`traj h g x` is `H¹` on `[0, h + τ]` (`Equation.exists_hasWeakDeriv`,
`Equation.IsSolOn.exists_hasWeakDeriv`).  This is the regularity behind the generator domain
`D(A) = {(g(h) - M g, g) : g ∈ H¹}` and behind `hyp:H1`.

## Proof

Extend `g` by the constant `g(h)`: `G = traj h g (g(h))` is `H¹` on `[0, h + τ]`.  Writing
`x = g(h) + e`, the solution `e` of the zero-history equation `e = 𝒦 e + w` has data
`w(t) = M G_t - g(h) + r + ∫₀ᵗ (L G_s + f(s)) ds`, which is `H¹` with `w(0) = M g - g(h) + r = 0`
(compatibility) and `w' = M G'_· + L G_· + f` (`DelayOp.hasWeakDeriv_eval`: `M` commutes with the
weak derivative).  Differentiating `e = 𝒦 e + w` formally gives the `L²` equation
`y = M y_· + L (∫₀^· y)_· + w'`, i.e. `(1 - 𝒦') y = w'`, which is solvable
(`Equation.isUnit_opK'`).  Then `e := ∫₀^· y` is `H¹` with `e(0) = 0`, so `traj h 0 e` is `H¹`
with derivative `traj h 0 y` (`hasWeakDeriv_traj_of`), `M (traj h 0 e)_t = ∫₀ᵗ M (traj h 0 y)_s ds`,
and integrating the equation for `y` shows that `X = g(h) + e` satisfies the integral form at
*every* `t ∈ [0, τ]`.  By uniqueness every solution equals `X` a.e.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Delay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Equation

variable {h : ℝ} (d : Equation h E)

/-- **Regularity of the delay equation**: for an `H¹` history `g`, the compatible initial value
`r = g(h) - M g` and an `L²` forcing `f`, there is a solution `X` with `X(0) = g(h)` that satisfies
the integral form at every `t ∈ [0, τ]` and whose trajectory `traj h g X` is `H¹` on
`[0, h + τ]`. -/
theorem exists_hasWeakDeriv {τ : ℝ} (hτ : 0 ≤ τ) {g g' f : ℝ → E} (hg : HasWeakDeriv h g g')
    (hf : MemLp f 2 (μI τ)) :
    ∃ X y : ℝ → E, X 0 = g h ∧
      (∀ t ∈ Icc 0 τ, X t = d.M.eval (traj h g X) t + d.prim (g h - d.M.eval g 0) g f X t) ∧
      HasWeakDeriv (h + τ) (traj h g X) (traj h g' y) := by
  have hh : 0 ≤ h := d.h_pos.le
  set r := g h - d.M.eval g 0 with hr
  set G : ℝ → E := traj h g (fun _ => g h) with hGdef
  have hG : HasWeakDeriv (h + τ) G (traj h g' 0) :=
    hasWeakDeriv_traj_of hh hτ hg (HasWeakDeriv.const (g h)) rfl
  -- The derivative of the data and the equation for `y = ẋ`.
  set w' : ℝ → E := fun s => d.M.eval (traj h g' 0) s + d.L.eval G s + f s with hw'def
  have hw'L : MemLp w' 2 (μI τ) :=
    ((d.M.memLp_eval hG.memLp_deriv).add (d.L.memLp_eval hG.memLp)).add hf
  set Y : L2 E τ := Ring.inverse (1 - d.opK' τ) (hw'L.toLp w') with hYdef
  have hY : (1 - d.opK' τ) Y = hw'L.toLp w' := by
    have hu := Ring.mul_inverse_cancel _ (d.isUnit_opK' hτ)
    calc (1 - d.opK' τ) Y = ((1 - d.opK' τ) * Ring.inverse (1 - d.opK' τ)) (hw'L.toLp w') := rfl
      _ = hw'L.toLp w' := by rw [hu]; rfl
  set e : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, (Y : ℝ → E) s with hedef
  have he : HasWeakDeriv τ e Y := hasWeakDeriv_primitive (Lp.memLp Y)
  have he0 : e 0 = 0 := by simp [hedef]
  have hYae : ⇑Y =ᵐ[μI τ] fun s =>
      d.M.eval (traj h 0 ⇑Y) s + d.L.eval (traj h 0 e) s + w' s := by
    have h1 : ⇑((1 - d.opK' τ) Y) =ᵐ[μI τ] w' := by rw [hY]; exact hw'L.coeFn_toLp
    filter_upwards [h1, Lp.coeFn_sub Y (d.opK' τ Y), d.coeFn_opK' τ Y] with s e1 e2 e3
    rw [sub_apply, one_apply_eq_self, e2, Pi.sub_apply, e3] at e1
    rw [← e1]
    abel
  -- The candidate `X = g(h) + e`.
  set X : ℝ → E := fun t => g h + e t with hXdef
  have hX : HasWeakDeriv τ X (fun t => (0 : ℝ → E) t + Y t) := (HasWeakDeriv.const (g h)).add he
  have hX0 : X 0 = g h := by simp [hXdef, he0]
  refine ⟨X, fun t => (0 : ℝ → E) t + Y t, hX0, fun t ht => ?_,
    hasWeakDeriv_traj_of hh hτ hg hX hX0⟩
  -- The trajectory splits as `G + traj h 0 e`.
  have htr : traj h g X = G + traj h 0 e := by
    rw [hGdef, ← traj_add, add_zero]
    rfl
  have hZ0 : HasWeakDeriv (h + τ) (traj h 0 e) (traj h 0 ⇑Y) :=
    hasWeakDeriv_traj_of hh hτ (HasWeakDeriv.const (T := h) (0 : E) : HasWeakDeriv h (0 : ℝ → E) 0)
      he he0
  have hsplit : ∀ s ∈ Icc 0 τ, ∀ p : DelayOp h E E,
      p.eval (traj h g X) s = p.eval G s + p.eval (traj h 0 e) s := fun s hs p => by
    rw [htr, p.eval_add_of_continuousOn hG.continuousOn hZ0.continuousOn hs]
  -- `M (traj h 0 e)_t = ∫₀ᵗ M (traj h 0 y)_s ds` and `M G_t = M g + ∫₀ᵗ M G'_s ds`.
  have hMe : d.M.eval (traj h 0 e) t = ∫ s in (0 : ℝ)..t, d.M.eval (traj h 0 ⇑Y) s := by
    rw [(d.M.hasWeakDeriv_eval hZ0).eq_add_integral t ht, d.M.eval_traj_zero, d.M.eval_zero,
      zero_add]
  have hMG : d.M.eval G t = d.M.eval g 0 + ∫ s in (0 : ℝ)..t, d.M.eval (traj h g' 0) s := by
    rw [(d.M.hasWeakDeriv_eval hG).eq_add_integral t ht, d.M.eval_traj_zero]
  -- Integrability on `[0, t]`.
  have iA : IntervalIntegrable (d.M.eval (traj h g' 0)) volume 0 t :=
    intervalIntegrable_of_integrableOn (d.M.integrableOn_eval hG.memLp_deriv) ht
  have iB : IntervalIntegrable (d.L.eval G) volume 0 t :=
    intervalIntegrable_of_integrableOn (d.L.integrableOn_eval hG.memLp) ht
  have iF : IntervalIntegrable f volume 0 t :=
    intervalIntegrable_of_integrableOn (hf.integrable one_le_two) ht
  have iC : IntervalIntegrable (d.M.eval (traj h 0 ⇑Y)) volume 0 t :=
    intervalIntegrable_of_integrableOn (d.M.integrableOn_eval
      (memLp_traj_of_memLp hh hτ MemLp.zero (Lp.memLp Y))) ht
  have iD : IntervalIntegrable (d.L.eval (traj h 0 e)) volume 0 t :=
    intervalIntegrable_of_integrableOn (d.L.integrableOn_eval hZ0.memLp) ht
  have hint : e t = (∫ s in (0 : ℝ)..t, d.M.eval (traj h 0 ⇑Y) s) +
      (∫ s in (0 : ℝ)..t, d.L.eval (traj h 0 e) s) +
      ((∫ s in (0 : ℝ)..t, d.M.eval (traj h g' 0) s) + (∫ s in (0 : ℝ)..t, d.L.eval G s) +
        ∫ s in (0 : ℝ)..t, f s) := by
    show ∫ s in (0 : ℝ)..t, (Y : ℝ → E) s = _
    rw [intervalIntegral_congr_μI hYae ht, intervalIntegral.integral_add (iC.add iD)
      ((iA.add iB).add iF), intervalIntegral.integral_add iC iD,
      intervalIntegral.integral_add (iA.add iB) iF, intervalIntegral.integral_add iA iB]
  have hprim : d.prim r g f X t = r + ((∫ s in (0 : ℝ)..t, d.L.eval G s) +
      ∫ s in (0 : ℝ)..t, f s) + ∫ s in (0 : ℝ)..t, d.L.eval (traj h 0 e) s := by
    rw [prim, intervalIntegral.integral_congr (f := fun s => d.L.eval (traj h g X) s + f s)
      (g := fun s => (d.L.eval G s + f s) +
      d.L.eval (traj h 0 e) s) (fun s hs => ?_), intervalIntegral.integral_add (iB.add iF) iD,
      intervalIntegral.integral_add iB iF]
    · abel
    · rw [uIcc_of_le ht.1] at hs
      simp only [hsplit s ⟨hs.1, hs.2.trans ht.2⟩ d.L]
      abel
  rw [hsplit t ht d.M, hMe, hMG, hprim, hr]
  show g h + e t = _
  rw [hint]
  abel

variable {d}

/-- **Regularity of solutions**: a solution with an `H¹` history `g`, the compatible initial value
`g(h) - M g` and an `L²` forcing agrees a.e. with a function `X` with `X(0) = g(h)` that
satisfies the integral form at every `t ∈ [0, τ]` and whose trajectory is `H¹` on
`[0, h + τ]`. -/
theorem IsSolOn.exists_hasWeakDeriv {τ : ℝ} (hτ : 0 ≤ τ) {g g' f x : ℝ → E}
    (hg : HasWeakDeriv h g g') (hf : MemLp f 2 (μI τ))
    (hx : d.IsSolOn τ (g h - d.M.eval g 0) g f x) :
    ∃ X y : ℝ → E, x =ᵐ[μI τ] X ∧ X 0 = g h ∧
      (∀ t ∈ Icc 0 τ, X t = d.M.eval (traj h g X) t + d.prim (g h - d.M.eval g 0) g f X t) ∧
      HasWeakDeriv (h + τ) (traj h g X) (traj h g' y) := by
  obtain ⟨X, y, hX0, hXeq, hZ⟩ := d.exists_hasWeakDeriv hτ hg hf
  refine ⟨X, y, hx.ae_eq hτ hg.memLp (hf.integrable one_le_two) ?_, hX0, hXeq, hZ⟩
  have hXc : ContinuousOn X (Icc 0 τ) := by
    have : ContinuousOn (fun t => traj h g X (h + t)) (Icc 0 τ) :=
      hZ.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => h + t).continuousOn
        fun t ht => ⟨by linarith [ht.1, d.h_pos], by linarith [ht.2]⟩
    refine this.congr fun t ht => ?_
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      simp only [add_zero, traj_of_le _ _ le_rfl, hX0]
    · simp only [traj_of_lt _ _ (by linarith : h < h + t), add_sub_cancel_left]
  exact ⟨memLp_μI_of_continuousOn hXc,
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hXeq t (Ioc_subset_Icc_self ht)⟩

end Equation

end Delay

end DataDrivenControl
