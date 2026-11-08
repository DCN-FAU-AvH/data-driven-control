module

public import DataDrivenControl.Examples.Heat.Orbit
public import DataDrivenControl.Semigroup.DomainSpace

/-!
# The localised space `V` and `W = D(A_V)` of the heat equation

Paper: `app:boundary-heat-informative` (`appendix_proofs.tex`): `eq:heat-localized-V` and
`eq:heat-W-domain`.

The paper takes `χ ∈ C_c^∞(0, 1)` equal to one near `ξ₀` and
`‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)} dt`, `V = {z ∈ X₋₁ : ‖z‖_V < ∞}`,
`W = D(A_V)` with the graph norm.  Here `X = L²(0, 1)` with the cosine basis, `X₋₁ = ℓ²`
(`Examples/Heat/Modal`), and `F_z(t) = e^{-t} χ S(t) z` is `orbitH χ t z` (`Examples/Heat/Orbit`).

## Main declarations

* **`V χ`**: the graph `{(z, F) : F = F_z a.e. on (0, ∞)}` in
  `WithLp 2 (X₋₁ × L²(0, ∞; L²(0,1) × L²(0,1)))`, closed (`isClosed_Vsub`, since each
  `z ↦ F_z(t)` is bounded on `X₋₁`), hence a Hilbert space.  `fstV`, `sndV`, `mkV`, `V_ext`.
* **The norm** (`norm_V_sq_eq`): `‖v‖² = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)} dt`, with
  `‖f‖²_{H¹(0,1)} = ∫₀¹ f² + ∫₀¹ (f')²`; **membership** (`exists_fstV_eq_iff`): `z ∈ V` iff
  `t ↦ e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)}` is integrable on `(0, ∞)`.
* **`SV χ`**: the C₀-semigroup `(z, F) ↦ (S(s) z, e^s F(· + s))` (`F_{S(s)z}(t) = e^s F_z(t + s)`,
  strong continuity from continuity of right translation in `L²(0, ∞)`), `consistent_fstV`.
* **`X ↪ V`**: `ιV χ` (`memLp_orbitH_toXm1`; continuity by the closed graph theorem and the bound
  `norm_ιV_sq_le`: `‖x‖²_V ≤ (1 + c_χ/2) ‖x‖²_X`), injective, dense (`denseRange_ιV`, since
  `S_V(s) z ∈ X` for `s > 0`), consistent.
* **`W χ = D(A_V)`** (`(SV χ).Dom`), `ιW χ : W →L[ℝ] X` (`ιV_ιW`), injective, dense, consistent;
  **`eq:heat-W-domain`**: `mem_SV_generator_domain_iff` (`x ∈ W ↔ A_{X,-1} x ∈ V`),
  `SV_generator_ιV` (`A_V x = A_{X,-1} x`), `range_ιW`, `toXm1_ιW` and `fstV_domGen`
  (`w = (x, A_{X,-1} x)` for `x = ι_W w`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace BoundaryHeat

open CosineBasis

/-- `L²(0, ∞; L²(0,1) × L²(0,1))`, the home of `t ↦ F_z(t)`. -/
abbrev Gsp : Type := Lp HPair 2 (volume.restrict (Ioi (0 : ℝ)))

variable (χ : Cutoff)

/-! ### The space `V` -/

/-- The space `V` of `eq:heat-localized-V` as a submodule of `X₋₁ × L²(0, ∞; L² × L²)`: the
graph `{(z, F) : F = F_z a.e.}` of `z ↦ F_z = e^{-·} χ S(·) z`. -/
def Vsub : Submodule ℝ (WithLp 2 (Xm1 × Gsp)) where
  carrier := {p | (p.snd : ℝ → HPair) =ᵐ[volume.restrict (Ioi 0)] fun t => orbitH χ t p.fst}
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq, WithLp.add_fst, WithLp.add_snd] at *
    filter_upwards [Lp.coeFn_add p.snd q.snd, hp, hq] with t h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, map_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, WithLp.zero_fst, WithLp.zero_snd]
    filter_upwards [Lp.coeFn_zero HPair 2 (volume.restrict (Ioi (0 : ℝ)))] with t h
    rw [h, map_zero]; rfl
  smul_mem' := by
    intro r p hp
    simp only [Set.mem_ofPred_eq, WithLp.smul_fst, WithLp.smul_snd] at *
    filter_upwards [Lp.coeFn_smul r p.snd, hp] with t h1 h2
    rw [h1, Pi.smul_apply, h2, map_smul]

/-- `V` is closed: along a convergent sequence a subsequence of the second components converges
a.e., and `z ↦ F_z(t)` is continuous for each `t`. -/
theorem isClosed_Vsub : IsClosed (Vsub χ : Set (WithLp 2 (Xm1 × Gsp))) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hqV, hq⟩ := mem_closure_iff_seq_limit.1 hp
  have h1 : Tendsto (fun k => (q k).fst) atTop (𝓝 p.fst) :=
    ((WithLp.continuous_fst 2 Xm1 Gsp).tendsto p).comp hq
  have h2 : Tendsto (fun k => (q k).snd) atTop (𝓝 p.snd) :=
    ((WithLp.continuous_snd 2 Xm1 Gsp).tendsto p).comp hq
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hall : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ k, ((q k).snd : ℝ → HPair) t = orbitH χ t (q k).fst :=
    ae_all_iff.2 fun k => hqV k
  show (p.snd : ℝ → HPair) =ᵐ[volume.restrict (Ioi 0)] fun t => orbitH χ t p.fst
  filter_upwards [hae, hall] with t ht1 ht2
  have h3 : Tendsto (fun k => orbitH χ t (q (ns k)).fst) atTop (𝓝 (orbitH χ t p.fst)) :=
    ((orbitH χ t).continuous.tendsto _).comp (h1.comp hns.tendsto_atTop)
  refine tendsto_nhds_unique ht1 ?_
  simpa only [ht2] using h3

/-- **The space `V`** of `eq:heat-localized-V` (a Hilbert space):
`‖z‖²_V = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)} dt` (`norm_V_sq_eq`). -/
abbrev V : Type := ↥(Vsub χ)

instance : CompleteSpace (V χ) := (isClosed_Vsub χ).isComplete.completeSpace_coe

instance : NormedAddCommGroup (V χ) := inferInstance
instance : InnerProductSpace ℝ (V χ) := inferInstance
instance : NormedSpace ℝ (V χ) := inferInstance
instance : Module ℝ (V χ) := inferInstance

/-- The embedding `V ↪ X₋₁`. -/
def fstV : V χ →L[ℝ] Xm1 := (WithLp.fstL 2 ℝ Xm1 Gsp).comp (Vsub χ).subtypeL

/-- `v ↦ F_z ∈ L²(0, ∞; L² × L²)`. -/
def sndV : V χ →L[ℝ] Gsp := (WithLp.sndL 2 ℝ Xm1 Gsp).comp (Vsub χ).subtypeL

/-- The second component of `v ∈ V` is `F_z`, `z` its first component. -/
theorem sndV_ae (v : V χ) :
    (sndV χ v : ℝ → HPair) =ᵐ[volume.restrict (Ioi 0)] fun t => orbitH χ t (fstV χ v) := v.2

/-- `F_z ∈ L²(0, ∞)` for `z ∈ V`. -/
theorem memLp_orbitH (v : V χ) :
    MemLp (fun t => orbitH χ t (fstV χ v)) 2 (volume.restrict (Ioi 0)) :=
  (Lp.memLp _).ae_eq (sndV_ae χ v)

/-- Elements of `V` are determined by their `X₋₁` component. -/
theorem V_ext {v w : V χ} (h : fstV χ v = fstV χ w) : v = w := by
  have h2 : sndV χ v = sndV χ w :=
    Lp.ext ((sndV_ae χ v).trans (h ▸ (sndV_ae χ w).symm))
  apply Subtype.ext
  exact (WithLp.ext_iff 2).2 (Prod.ext h h2)

/-- `V ↪ X₋₁` is injective. -/
theorem fstV_injective : Function.Injective (fstV χ) := fun _ _ h => V_ext χ h

/-- `‖v‖² = ‖z‖²_{X₋₁} + ‖F_z‖²`. -/
theorem norm_V_sq (v : V χ) : ‖v‖ ^ 2 = ‖fstV χ v‖ ^ 2 + ‖sndV χ v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

/-- `‖v‖ ≤ ‖z‖_{X₋₁} + ‖F_z‖`. -/
theorem norm_V_le (v : V χ) : ‖v‖ ≤ ‖fstV χ v‖ + ‖sndV χ v‖ := by
  nlinarith [norm_V_sq χ v, norm_nonneg v, norm_nonneg (fstV χ v), norm_nonneg (sndV χ v)]

/-- `‖F_z‖² = ∫₀^∞ ‖F_z(t)‖² dt`. -/
theorem norm_sndV_sq (v : V χ) :
    ‖sndV χ v‖ ^ 2 = ∫ t in Ioi 0, ‖orbitH χ t (fstV χ v)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [sndV_ae χ v] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

/-- **The norm of `V`** (`eq:heat-localized-V`):
`‖v‖² = ‖z‖²_{X₋₁} + ∫₀^∞ e^{-2t} (∫₀¹ (χ S(t) z)² + ∫₀¹ (∂_ξ (χ S(t) z))²) dt`. -/
theorem norm_V_sq_eq (v : V χ) :
    ‖v‖ ^ 2 = ‖fstV χ v‖ ^ 2 +
      ∫ t in Ioi 0, Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit (fstV χ v) t ξ) := by
  rw [norm_V_sq, norm_sndV_sq]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => norm_orbitH_sq_eq χ ht _

/-- The element `(z, F_z)` of `V`. -/
def mkV (a : Xm1) (ha : MemLp (fun t => orbitH χ t a) 2 (volume.restrict (Ioi 0))) : V χ :=
  ⟨WithLp.toLp 2 (a, ha.toLp _), ha.coeFn_toLp⟩

/-- First component of `mkV`. -/
@[simp] theorem fstV_mkV (a : Xm1) (ha : MemLp (fun t => orbitH χ t a) 2 (volume.restrict (Ioi 0))) :
    fstV χ (mkV χ a ha) = a := rfl

/-- Second component of `mkV`. -/
theorem sndV_mkV (a : Xm1) (ha : MemLp (fun t => orbitH χ t a) 2 (volume.restrict (Ioi 0))) :
    sndV χ (mkV χ a ha) = ha.toLp _ := rfl

/-- **`V = {z ∈ X₋₁ : ‖z‖_V < ∞}`**: `z ∈ X₋₁` lies in `V` iff
`t ↦ e^{-2t} ‖χ S(t) z‖²_{H¹(0,1)}` is integrable on `(0, ∞)`. -/
theorem exists_fstV_eq_iff (a : Xm1) :
    (∃ v : V χ, fstV χ v = a) ↔
      IntegrableOn (fun t => Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit a t ξ)) (Ioi 0) := by
  have heq : (fun t => ‖orbitH χ t a‖ ^ 2) =ᵐ[volume.restrict (Ioi 0)]
      fun t => Real.exp (-2 * t) * H1sq (fun ξ => χ ξ * orbit a t ξ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => norm_orbitH_sq_eq χ ht a
  rw [IntegrableOn, ← integrable_congr heq,
    ← memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_orbitH χ a)]
  constructor
  · rintro ⟨v, rfl⟩; exact memLp_orbitH χ v
  · intro h; exact ⟨mkV χ a h, rfl⟩

/-- Closed graph: a linear map into `V` whose first component is continuous is continuous. -/
theorem continuous_of_fstV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : E →ₗ[ℝ] V χ) (M : E →L[ℝ] Xm1) (h : ∀ x, fstV χ (L x) = M x) : Continuous L := by
  refine L.continuous_of_seq_closed_graph fun u x y hu hy => V_ext χ ?_
  rw [h]
  have h1 : Tendsto (fun n => fstV χ (L (u n))) atTop (𝓝 (fstV χ y)) :=
    ((fstV χ).continuous.tendsto _).comp hy
  have h2 : Tendsto (fun n => M (u n)) atTop (𝓝 (M x)) := (M.continuous.tendsto _).comp hu
  simp only [h] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### The semigroup on `V` -/

/-- `S(s)` maps `V` into `V`: `F_{S(s) z}(t) = e^s F_z(t + s)`. -/
theorem memLp_orbitH_Sm (v : V χ) {s : ℝ} (hs : 0 ≤ s) :
    MemLp (fun t => orbitH χ t (heatModal.Sm.real s (fstV χ v))) 2 (volume.restrict (Ioi 0)) :=
  ((memLp_comp_add_Ioi (memLp_orbitH χ v) hs).const_smul (Real.exp s)).ae_eq
    (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ht => (orbitH_Sm χ ht hs _).symm)

/-- The semigroup on `V`, as a linear map: `(z, F) ↦ (S(s) z, e^s F(· + s))`. -/
def SVlin (s : ℝ≥0) : V χ →ₗ[ℝ] V χ where
  toFun v := mkV χ (heatModal.Sm.real s (fstV χ v)) (memLp_orbitH_Sm χ v s.coe_nonneg)
  map_add' v w := V_ext χ (by simp)
  map_smul' r v := V_ext χ (by simp)

/-- The semigroup on `V`, as a bounded operator (closed graph). -/
def SVop (s : ℝ≥0) : V χ →L[ℝ] V χ :=
  ⟨SVlin χ s, continuous_of_fstV χ (SVlin χ s) ((heatModal.Sm.real s).comp (fstV χ)) fun _ => rfl⟩

/-- First component of `S_V(s)`. -/
theorem fstV_SVop (s : ℝ≥0) (v : V χ) : fstV χ (SVop χ s v) = heatModal.Sm.real s (fstV χ v) :=
  rfl

/-- Strong continuity of `S_V` at `0` (continuity of right translation in `L²(0, ∞)`). -/
theorem tendsto_SVop (v : V χ) : Tendsto (fun s => SVop χ s v) (𝓝 0) (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set a := fstV χ v with ha
  set g : ℝ → HPair := fun t => orbitH χ t a with hg
  have hgm : MemLp g 2 (volume.restrict (Ioi 0)) := memLp_orbitH χ v
  have hc : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝 0) (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using NNReal.continuous_coe.tendsto 0,
      Eventually.of_forall fun s => s.coe_nonneg⟩
  have h1 : Tendsto (fun s : ℝ≥0 => ‖fstV χ (SVop χ s v) - fstV χ v‖) (𝓝 0) (𝓝 0) := by
    have := ((heatModal.Sm.continuous_real_apply a).tendsto 0).comp
      (NNReal.continuous_coe.tendsto 0)
    simp only [C0Semigroup.real_zero, one_apply_eq_self] at this
    simpa [fstV_SVop, ← ha] using (this.sub_const a).norm
  -- the second component, in `ℝ≥0∞`
  have hbound : ∀ s : ℝ≥0, eLpNorm (fun t => orbitH χ t (heatModal.Sm.real s a) - g t) 2
      (volume.restrict (Ioi 0)) ≤ ENNReal.ofReal |Real.exp s - 1| * eLpNorm g 2
        (volume.restrict (Ioi 0)) +
        eLpNorm (fun t => g (t + s) - g t) 2 (volume.restrict (Ioi 0)) := by
    intro s
    have hs := s.coe_nonneg
    have heq : (fun t => orbitH χ t (heatModal.Sm.real s a) - g t) =ᵐ[volume.restrict (Ioi 0)]
        (fun t => (Real.exp s - 1) • g (t + s)) + fun t => g (t + s) - g t :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        simp only [Pi.add_apply, hg, orbitH_Sm χ ht hs, sub_smul, one_smul]
        abel
    rw [eLpNorm_congr_ae heq]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add_left ?_ _)
    rw [show (fun t => (Real.exp s - 1) • g (t + s)) = (Real.exp s - 1) • fun t => g (t + s)
      from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    gcongr
    exact eLpNorm_comp_add_Ioi_le hgm.aestronglyMeasurable hs
  have hlim : Tendsto (fun s : ℝ≥0 => ENNReal.ofReal |Real.exp s - 1| *
      eLpNorm g 2 (volume.restrict (Ioi 0)) +
        eLpNorm (fun t => g (t + s) - g t) 2 (volume.restrict (Ioi 0))) (𝓝 0) (𝓝 0) := by
    have hA : Tendsto (fun s : ℝ≥0 => ENNReal.ofReal |Real.exp s - 1|) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ≥0 => |Real.exp s - 1|) (𝓝 0) (𝓝 |Real.exp (0 : ℝ≥0) - 1|) :=
        ((Real.continuous_exp.comp NNReal.continuous_coe).sub continuous_const).abs.tendsto 0
      simpa using ENNReal.tendsto_ofReal this
    have hA' := ENNReal.Tendsto.mul_const hA (Or.inr hgm.eLpNorm_ne_top)
    rw [zero_mul] at hA'
    simpa using hA'.add ((tendsto_eLpNorm_comp_add_sub_Ioi hgm).comp hc)
  have h2 : Tendsto (fun s : ℝ≥0 => ‖sndV χ (SVop χ s v) - sndV χ v‖) (𝓝 0) (𝓝 0) := by
    have hn : ∀ s : ℝ≥0, ‖sndV χ (SVop χ s v) - sndV χ v‖ =
        (eLpNorm (fun t => orbitH χ t (heatModal.Sm.real s a) - g t) 2
          (volume.restrict (Ioi 0))).toReal := by
      intro s
      rw [Lp.norm_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (sndV χ (SVop χ s v)) (sndV χ v), sndV_ae χ (SVop χ s v),
        sndV_ae χ v] with t h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, fstV_SVop]
    simp only [hn]
    have hle := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun s => zero_le) hbound
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hle
    rw [ENNReal.toReal_zero] at h3
    exact h3
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using h1.add h2)
  refine (norm_V_le χ _).trans (le_of_eq ?_)
  rw [map_sub, map_sub]

/-- **The semigroup `S_V` on `V`** (`app:boundary-heat-informative`). -/
def SV : C0Semigroup ℝ (V χ) :=
  C0Semigroup.ofTendsto (SVop χ)
    (ContinuousLinearMap.ext fun v => V_ext χ (by simp [fstV_SVop]))
    (fun s t => ContinuousLinearMap.ext fun v => V_ext χ (by
      simp only [fstV_SVop, ContinuousLinearMap.comp_apply, NNReal.coe_add]
      exact heatModal.Sm.real_add_apply s.coe_nonneg t.coe_nonneg _))
    (tendsto_SVop χ)

/-- `S_V(s)` is `SVop s`. -/
theorem SV_apply (s : ℝ≥0) : SV χ s = SVop χ s := C0Semigroup.ofTendsto_apply _ _ _ _ _

/-- `S_V` acts as `S_{X₋₁}` on the first component. -/
theorem fstV_SV (s : ℝ≥0) (v : V χ) : fstV χ (SV χ s v) = heatModal.Sm.real s (fstV χ v) := by
  rw [SV_apply]; rfl

/-- `S_V` acts as `S_{X₋₁}` on the first component (real times). -/
theorem fstV_SV_real {s : ℝ} (hs : 0 ≤ s) (v : V χ) :
    fstV χ (SV χ |>.real s v) = heatModal.Sm.real s (fstV χ v) := by
  show fstV χ (SV χ s.toNNReal v) = _
  rw [fstV_SV, Real.coe_toNNReal s hs]

/-- `V ↪ X₋₁` is consistent with the semigroups. -/
theorem consistent_fstV : C0Semigroup.Consistent (fstV χ) (SV χ) heatModal.Sm := fun t v => by
  rw [fstV_SV, C0Semigroup.real_coe]

/-! ### `X ↪ V` -/

/-- The embedding `X ↪ V`, as a linear map. -/
def ιVlin : L2 ℝ 1 →ₗ[ℝ] V χ where
  toFun x := mkV χ (heatModal.toXm1 cosBasis x) (memLp_orbitH_toXm1 χ x)
  map_add' x y := V_ext χ (by simp)
  map_smul' r x := V_ext χ (by simp)

/-- **The embedding `X ↪ V`**, `x ↦ (x, F_x)` (bounded by the closed graph theorem; explicitly,
`norm_ιV_sq_le`). -/
def ιV : L2 ℝ 1 →L[ℝ] V χ :=
  ⟨ιVlin χ, continuous_of_fstV χ (ιVlin χ) (heatModal.toXm1 cosBasis) fun _ => rfl⟩

/-- The `X₋₁` component of `ιV x`. -/
@[simp] theorem fstV_ιV (x : L2 ℝ 1) : fstV χ (ιV χ x) = heatModal.toXm1 cosBasis x := rfl

/-- **`X ↪ V`, the bound**: `‖x‖²_V ≤ (1 + c_χ/2) ‖x‖²_X`, from the eigenfunction identity
`∫₀^∞ e^{-2t} ‖S(t) x‖²_{H¹} dt = ½ ‖x‖²_X` and `‖χ f‖²_{H¹} ≤ c_χ ‖f‖²_{H¹}`. -/
theorem norm_ιV_sq_le (x : L2 ℝ 1) : ‖ιV χ x‖ ^ 2 ≤ (1 + cutConst χ / 2) * ‖x‖ ^ 2 := by
  rw [norm_V_sq, norm_sndV_sq, fstV_ιV]
  have h1 : ‖heatModal.toXm1 cosBasis x‖ ≤ ‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((Diagonal.norm_diagMap_le _ _ _).trans (by norm_num)))
  have h2 := integral_norm_orbitH_sq_le χ x
  have h3 : ‖heatModal.toXm1 cosBasis x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith

/-- `X ↪ V` is injective. -/
theorem ιV_injective : Function.Injective (ιV χ) := fun x y h =>
  heatModal.toXm1_injective cosBasis (by simpa using congrArg (fstV χ) h)

/-- The state-space semigroup: the heat semigroup on `L²(0, 1)`. -/
abbrev SX : C0Semigroup ℝ (L2 ℝ 1) := heatModal.SX cosBasis

/-- `X ↪ V` is consistent with the semigroups. -/
theorem consistent_ιV : C0Semigroup.Consistent (ιV χ) SX (SV χ) := fun t x =>
  V_ext χ (by
    rw [fstV_ιV, fstV_SV, fstV_ιV, C0Semigroup.real_coe, heatModal.consistent_toXm1 cosBasis t x])

/-- `S_V(s) v ∈ X` for `s > 0`. -/
theorem ιV_smoothing {s : ℝ} (hs : 0 < s) (v : V χ) :
    ιV χ (heatModal.smoothing cosBasis hs (fstV χ v)) = (SV χ).real s v :=
  V_ext χ (by rw [fstV_ιV, heatModal.toXm1_smoothing, fstV_SV_real χ hs.le])

/-- `X` is dense in `V`. -/
theorem denseRange_ιV : DenseRange (ιV χ) := by
  intro v
  have hT : Tendsto (fun s : ℝ => (SV χ).real s v) (𝓝[>] 0) (𝓝 v) := by
    have := ((SV χ).continuous_real_apply v).tendsto 0
    simp only [C0Semigroup.real_zero, one_apply_eq_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ⟨_, ιV_smoothing χ hs v⟩

/-! ### The space `W = D(A_V)` -/

/-- The generator of `S_V` acts diagonally on the first component. -/
theorem fstV_generator (v : (SV χ).generator.domain) (n : ℕ) :
    fstV χ ((SV χ).generator v) n = eig n * fstV χ v n := by
  have h := (consistent_fstV χ).generator_apply heatModal.Sm v.2
  rw [← inner_stdBasis, ← h, inner_generator_diag, inner_stdBasis]
  rfl

/-- **The space `W = D(A_V)`** with the graph norm (`app:boundary-heat-informative`). -/
abbrev W : Type := (SV χ).Dom

instance : NormedAddCommGroup (W χ) := inferInstance
instance : InnerProductSpace ℝ (W χ) := inferInstance
instance : NormedSpace ℝ (W χ) := inferInstance
instance : Module ℝ (W χ) := inferInstance
instance : CompleteSpace (W χ) := inferInstance

/-- **`W ↪ X`**: `w ↦ ∑ wₙ aₙ eₙ`, where `a` is the `X₋₁` component of `w` (`(1 - A_{-1}) a`). -/
def ιW : W χ →L[ℝ] L2 ℝ 1 :=
  (ModalData.toX cosBasis).comp ((fstV χ).comp (SV χ).domIncl - (fstV χ).comp (SV χ).domGen)

/-- Coordinates of `ι_W w`: `wₙ aₙ`. -/
theorem inner_ιW (w : W χ) (n : ℕ) :
    ⟪cosBasis n, ιW χ w⟫_ℝ = (1 - eig n) * fstV χ ((SV χ).domIncl w) n := by
  rw [ιW, ContinuousLinearMap.comp_apply, ModalData.toX, Diagonal.inner_diagMap, inner_stdBasis,
    sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← (SV χ).generator_domIncl w, lp.coeFn_sub, Pi.sub_apply,
    fstV_generator]
  ring

/-- `ι_W w` read in `X₋₁` is the first component of `w`. -/
theorem toXm1_ιW (w : W χ) : heatModal.toXm1 cosBasis (ιW χ w) = fstV χ ((SV χ).domIncl w) := by
  refine ext_Xm1 fun n => ?_
  rw [heatModal.toXm1_apply, inner_ιW, heatModal_wt]
  field_simp [(one_sub_eig_pos n).ne']

/-- `ιV ∘ ιW` is the inclusion `W = D(A_V) ↪ V`. -/
theorem ιV_ιW (w : W χ) : ιV χ (ιW χ w) = (SV χ).domIncl w :=
  V_ext χ (by rw [fstV_ιV, toXm1_ιW])

/-- `W ↪ X` is injective. -/
theorem ιW_injective : Function.Injective (ιW χ) := fun w w' h =>
  (SV χ).domIncl_injective (by rw [← ιV_ιW χ w, h, ιV_ιW χ w'])

/-- The semigroup restricted to `W`. -/
abbrev SW : C0Semigroup ℝ (W χ) := (SV χ).domSemigroup

/-- `W ↪ X` is consistent with the semigroups. -/
theorem consistent_ιW : C0Semigroup.Consistent (ιW χ) (SW χ) SX := fun t w =>
  ιV_injective χ (by
    rw [ιV_ιW, consistent_ιV χ, ιV_ιW, C0Semigroup.domIncl_domSemigroup])

/-- `D(A) ⊆ W`. -/
theorem exists_ιW_eq {x : L2 ℝ 1} (hx : x ∈ SX.generator.domain) : ∃ w : W χ, ιW χ w = x := by
  obtain ⟨w, hw⟩ := (SV χ).exists_domIncl_eq ((consistent_ιV χ).mem_generator_domain (SV χ) hx)
  exact ⟨w, ιV_injective χ (by rw [ιV_ιW, hw])⟩

/-- `W` is dense in `X` (it contains `D(A)`). -/
theorem denseRange_ιW : DenseRange (ιW χ) :=
  SX.dense_generator_domain.mono fun _ hx => exists_ιW_eq χ hx

/-- **`eq:heat-W-domain`**: `x ∈ X` lies in `W = D(A_V)` iff `A_{X,-1} x ∈ V`. -/
theorem mem_SV_generator_domain_iff (x : L2 ℝ 1) :
    ιV χ x ∈ (SV χ).generator.domain ↔
      MemLp (fun t => orbitH χ t (heatModal.genXm1 cosBasis x)) 2 (volume.restrict (Ioi 0)) := by
  constructor
  · intro h
    have h1 := (consistent_fstV χ).generator_apply heatModal.Sm h
    have h2 : fstV χ ((SV χ).generator ⟨ιV χ x, h⟩) = heatModal.genXm1 cosBasis x := by
      rw [← h1]; exact heatModal.Sm_generator_toXm1 cosBasis x
    rw [← h2]
    exact memLp_orbitH χ _
  · intro h
    obtain ⟨hv, -⟩ := (consistent_fstV χ).exists_mem_generator_domain (fstV_injective χ)
      (v := ιV χ x) (g := mkV χ (heatModal.genXm1 cosBasis x) h)
      (heatModal.toXm1_mem_generator_domain cosBasis x) (heatModal.Sm_generator_toXm1 cosBasis x)
    exact hv

/-- **`eq:heat-W-domain`**, the generator: `A_V x = A_{X,-1} x` for `x ∈ W`. -/
theorem SV_generator_ιV (x : L2 ℝ 1)
    (h : MemLp (fun t => orbitH χ t (heatModal.genXm1 cosBasis x)) 2 (volume.restrict (Ioi 0))) :
    (SV χ).generator ⟨ιV χ x, (mem_SV_generator_domain_iff χ x).2 h⟩ =
      mkV χ (heatModal.genXm1 cosBasis x) h := by
  obtain ⟨hv, h2⟩ := (consistent_fstV χ).exists_mem_generator_domain (fstV_injective χ)
    (v := ιV χ x) (g := mkV χ (heatModal.genXm1 cosBasis x) h)
    (heatModal.toXm1_mem_generator_domain cosBasis x) (heatModal.Sm_generator_toXm1 cosBasis x)
  exact h2

/-- The components of `w ∈ W` in terms of `x = ι_W w`: `w = (x, A_{X,-1} x)`. -/
theorem fstV_domGen (w : W χ) :
    fstV χ ((SV χ).domGen w) = heatModal.genXm1 cosBasis (ιW χ w) := by
  refine ext_Xm1 fun n => ?_
  have hw := (one_sub_eig_pos n).ne'
  rw [← (SV χ).generator_domIncl w, fstV_generator, heatModal.genXm1_apply, inner_ιW,
    heatModal_wt, heatModal_lam]
  field_simp

/-- **`eq:heat-W-domain`** as a set: `W = {x ∈ X : A_{X,-1} x ∈ V}`, i.e. the `x ∈ L²(0, 1)` with
`∫₀^∞ e^{-2t} ‖χ S(t) A_{X,-1} x‖²_{H¹(0,1)} dt < ∞`. -/
theorem range_ιW : Set.range (ιW χ) =
    {x | IntegrableOn (fun t => Real.exp (-2 * t) *
      H1sq (fun ξ => χ ξ * orbit (heatModal.genXm1 cosBasis x) t ξ)) (Ioi 0)} := by
  ext x
  rw [Set.mem_ofPred_eq, ← exists_fstV_eq_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(SV χ).domGen w, fstV_domGen χ w⟩
  · rintro ⟨v, hv⟩
    have h : MemLp (fun t => orbitH χ t (heatModal.genXm1 cosBasis x)) 2
        (volume.restrict (Ioi 0)) := hv ▸ memLp_orbitH χ v
    obtain ⟨w, hw⟩ := (SV χ).exists_domIncl_eq ((mem_SV_generator_domain_iff χ x).2 h)
    exact ⟨w, ιV_injective χ (by rw [ιV_ιW, hw])⟩

end BoundaryHeat

end DataDrivenControl
