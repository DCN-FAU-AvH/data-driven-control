module

public import DataDrivenControl.Examples.Delay.System
public import DataDrivenControl.Analysis.MeasureRepresentation

/-!
# The delay system for bounded `L`, `M`, `C` on continuous histories

Paper: `ex:intro-delay`.  The paper takes `L`, `M`, `C` to be bounded linear maps from
`C([-h, 0]; ℝⁿ)` to `ℝⁿ`, `ℝⁿ`, `ℝᵖ`, with the measure representing `M` without mass at `0`.  For
finite-dimensional `E` and `Y`, the Riesz representation of `Analysis/MeasureRepresentation`
(`exists_eq_sum_integral_delay`, and `noMassAtZero_iff` for `M`) writes them as delay functionals
(`DelayOp` with `D = 0`), so the results of `Examples/Delay` apply.

* `eval_eq_sum_integral`: the delay functional of a representation `(Pₖ, μₖ)` evaluates, on a
  history equal to `φ(· - h)` on `[0, h]`, to `∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ)`.
* `exists_model`: for bounded `L`, `M`, `C` with `NoMassAtZero M` and any `B₀`, there is a
  `Model` whose delay functionals are `L`, `M`, `C` on every history continuous on `[0, h]`; its
  system satisfies `hyp:H1`, `hyp:H2` (every horizon) and `hyp:compat`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace DataDrivenControl

namespace Delay

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {h : ℝ}

/-- The delay functional of a representation `(Pₖ, μₖ)` (`D = 0`) evaluated on a function equal
to the history `φ(· - h)` on `[0, h]` is `∑ₖ Pₖ ∫ φ(-δ) dμₖ(δ)`. -/
theorem eval_eq_sum_integral (hh : 0 < h) {N : ℕ} (P : Fin N → E →L[ℝ] F)
    (μ : Fin N → Measure ℝ) (hμ : ∀ k, IsFiniteMeasure (μ k)) (hs : ∀ k, μ k (Icc 0 h)ᶜ = 0)
    (φ : C(Icc (-h) 0, E)) {z : ℝ → E}
    (hz : ∀ s ∈ Icc 0 h, z s = IccExtend (neg_nonpos.2 hh.le) φ (s - h)) :
    (⟨hh, N, P, μ, hμ, hs, 0⟩ : DelayOp h E F).eval z 0 =
      ∑ k, P k (∫ δ, IccExtend (neg_nonpos.2 hh.le) φ (-δ) ∂μ k) := by
  simp only [DelayOp.eval, zero_apply, add_zero, mconv]
  refine Finset.sum_congr rfl fun k _ => congrArg (P k) (integral_congr_ae ?_)
  filter_upwards [show ∀ᵐ δ ∂(μ k), δ ∈ Icc 0 h from mem_ae_iff.2 (hs k)] with δ hδ
  rw [hz _ ⟨by linarith [hδ.2], by linarith [hδ.1]⟩, sub_sub_cancel_left]

variable [FiniteDimensional ℝ E] {U Y : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [CompleteSpace U] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **`ex:intro-delay` for bounded `L`, `M`, `C`**: for bounded linear maps `L`, `M` from
`C([-h, 0]; E)` to `E` and `C` to `Y` (`E`, `Y` finite-dimensional), with `M` without mass at
`0`, and any `B₀`, there is a delay model whose delay functionals are `L`, `M`, `C` on every
history that equals `φ(· - h)` on `[0, h]`, and its system on `W = D(A) ↪ X = V = E × L²` satisfies
`hyp:H1`, `hyp:H2` at every horizon and `hyp:compat`. -/
theorem exists_model (hh : 0 < h) (L M : C(Icc (-h) 0, E) →L[ℝ] E)
    (C : C(Icc (-h) 0, E) →L[ℝ] Y) (hM : NoMassAtZero M) (B₀ : U →L[ℝ] E) :
    ∃ m : Model h E U Y, m.B₀ = B₀ ∧
      (∀ (φ : C(Icc (-h) 0, E)) (z : ℝ → E),
        (∀ s ∈ Icc 0 h, z s = IccExtend (neg_nonpos.2 hh.le) φ (s - h)) →
          m.L.eval z 0 = L φ ∧ m.M.eval z 0 = M φ ∧ m.C.eval z 0 = C φ) ∧
      (∀ T, m.sys.H1 T) ∧ (∀ T, m.sys.H2 T) ∧ m.sys.Compat := by
  obtain ⟨NL, PL, μL, hfL, hsL, hL⟩ := exists_eq_sum_integral_delay hh L
  obtain ⟨NM, PM, μM, hfM, hsM, h0M, hMr⟩ := (noMassAtZero_iff hh M).1 hM
  obtain ⟨NC, PC, μC, hfC, hsC, hC⟩ := exists_eq_sum_integral_delay hh C
  let m : Model h E U Y :=
    { L := ⟨hh, NL, PL, μL, hfL, hsL, 0⟩
      M := ⟨hh, NM, PM, μM, hfM, hsM, 0⟩
      M_noAtom := h0M
      B₀ := B₀
      C := ⟨hh, NC, PC, μC, hfC, hsC, 0⟩ }
  refine ⟨m, rfl, fun φ z hz => ⟨?_, ?_, ?_⟩, m.H1, m.H2, m.compat⟩
  · rw [hL]; exact eval_eq_sum_integral hh PL μL hfL hsL φ hz
  · rw [hMr]; exact eval_eq_sum_integral hh PM μM hfM hsM φ hz
  · rw [hC]; exact eval_eq_sum_integral hh PC μC hfC hsC φ hz

end Delay

end DataDrivenControl
