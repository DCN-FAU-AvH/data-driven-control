module

public import Mathlib

/-!
# Signals on finite intervals: conventions

* `μI T := volume.restrict (Ioc 0 T)`: the measure of the window `I = (0, T]` (the paper's
  `(0, T)`; the endpoint is a null set);
* a signal on the window is a function `ℝ → E` with `MemLp f 2 (μI T)`; spaces on which
  operators act are Mathlib's `Lp E 2 (μI T)`, abbreviated `L2 E T`;
* products of Hilbert spaces are `WithLp 2 (E × F)` (see the files that need them), so that
  orthogonal complements and Gramians are those of the paper;
* "for a.e. `t ∈ I`" is `∀ᵐ t ∂(μI T)`.

Every file of the project lives in the namespace `DataDrivenControl`, opens
`MeasureTheory Set Filter Topology` as needed and works in a `noncomputable section`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace DataDrivenControl

/-- The measure of the window `I = (0, T]`: Lebesgue measure restricted to `Ioc 0 T`. -/
abbrev μI (T : ℝ) : Measure ℝ := volume.restrict (Ioc 0 T)

/-- Square-integrable `E`-valued signals on the window `(0, T]`, the paper's `L²(0, T; E)`. -/
abbrev L2 (E : Type*) [NormedAddCommGroup E] (T : ℝ) : Type _ := Lp E 2 (μI T)

instance (T : ℝ) : IsFiniteMeasure (μI T) := by
  unfold μI; infer_instance

/-- `L²(0, T; E)` is a real Hilbert space when `E` is. -/
example (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (T : ℝ) :
    InnerProductSpace ℝ (L2 E T) := inferInstance

example (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (T : ℝ) :
    CompleteSpace (L2 E T) := inferInstance

end DataDrivenControl
