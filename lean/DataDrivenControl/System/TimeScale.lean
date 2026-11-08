module

public import DataDrivenControl.Semigroup.TimeScale
public import DataDrivenControl.System.Controllability
public import DataDrivenControl.System.ControlRealization

/-!
# Time rescaling of a system

For `ν > 0`, the system `ẋ = ν (A x + B u)`, `y = C x` on the same spaces `W ↪ X ↪ V`: the
semigroups become `t ↦ S(ν t)` and the control operator `ν B`.  Its trajectories are those of
`(A, B, C)` in the time `ν t`, driven by `u(·/ν)`.  This reduces the heat equation with
diffusivity `ν` (`ex:intro-pde`) to `ν = 1`.

## Main declarations

* `map_mul_μI`, `memLp_comp_mul_iff`, `memLp_comp_div_iff`, `eLpNorm_comp_mul`,
  `eLpNorm_comp_div`: the substitution `t = a s` on the windows `(0, T]`.
* `System.timeScale sys ν`; `timeScale_A` (`A_ν = ν A`, same domain), `timeScale_AV`,
  `mem_resolventSet_complexify_timeScale` (`s ∈ ρ((ν A)_ℂ) ↔ s / ν ∈ ρ(A_ℂ)`).
* `convV_timeScale`, `L_timeScale`, `mild_timeScale`: `x_ν(t; x₀, u) = x(ν t; x₀, u(·/ν))`.
* `H1.timeScale`, `H2.timeScale` (`hyp:H1`, `hyp:H2` at `ν T` give them at `T`) and
  `Compat.timeScale` (`hyp:compat`).
* `reachable_timeScale`, `approxControllable_timeScale`: the rescaled system is approximately
  controllable in time `T` iff `(A, B)` is in time `ν T`.
* `adjoint_A_timeScale` (`A_ν† = ν A†`), `Bstar_timeScale` (`B_ν† = ν B†` on `D(A†)`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

/-! ### The substitution `t = a s` on a window -/

section Substitution

variable {F : Type*} [NormedAddCommGroup F] {a : ℝ}

private theorem measurableEmbedding_mul (ha : 0 < a) : MeasurableEmbedding (a * ·) :=
  (Homeomorph.mulLeft₀ a ha.ne').measurableEmbedding

/-- `t ↦ a t` maps `(0, T]` onto `(0, a T]`, scaling the Lebesgue measure by `a⁻¹`. -/
theorem map_mul_μI (ha : 0 < a) (T : ℝ) :
    Measure.map (a * ·) (μI T) = ENNReal.ofReal a⁻¹ • μI (a * T) := by
  have hpre : (a * ·) ⁻¹' Ioc 0 (a * T) = Ioc 0 T := by
    rw [preimage_const_mul_Ioc₀ _ _ ha, zero_div, mul_div_cancel_left₀ _ ha.ne']
  show Measure.map (a * ·) (volume.restrict (Ioc 0 T)) = _ • volume.restrict (Ioc 0 (a * T))
  rw [← hpre, ← (measurableEmbedding_mul ha).restrict_map, Real.map_volume_mul_left ha.ne',
    Measure.restrict_smul, abs_of_pos (inv_pos.2 ha)]

theorem memLp_comp_mul_iff (ha : 0 < a) {g : ℝ → F} {p : ℝ≥0∞} {T : ℝ} :
    MemLp (fun t => g (a * t)) p (μI T) ↔ MemLp g p (μI (a * T)) := by
  refine (measurableEmbedding_mul ha).memLp_map_measure_iff.symm.trans ?_
  rw [map_mul_μI ha]
  refine ⟨fun h => ?_, fun h => h.smul_measure ENNReal.ofReal_ne_top⟩
  have := h.smul_measure (c := ENNReal.ofReal a) ENNReal.ofReal_ne_top
  rwa [smul_smul, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one,
    one_smul] at this

theorem memLp_comp_div_iff (ha : 0 < a) {g : ℝ → F} {p : ℝ≥0∞} {T : ℝ} :
    MemLp (fun s => g (s / a)) p (μI (a * T)) ↔ MemLp g p (μI T) := by
  simp_rw [div_eq_inv_mul]
  rw [memLp_comp_mul_iff (inv_pos.2 ha), inv_mul_cancel_left₀ ha.ne']

theorem eLpNorm_comp_mul (ha : 0 < a) (g : ℝ → F) (T : ℝ) :
    eLpNorm (fun t => g (a * t)) 2 (μI T) =
      ENNReal.ofReal (Real.sqrt a⁻¹) * eLpNorm g 2 (μI (a * T)) := by
  refine ((measurableEmbedding_mul ha).eLpNorm_map_measure (g := g)).symm.trans ?_
  rw [map_mul_μI ha, eLpNorm_smul_measure_of_ne_zero_of_ne_top two_ne_zero ENNReal.ofNat_ne_top,
    smul_eq_mul, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 ha.le)
      (by norm_num)]
  norm_num

theorem eLpNorm_comp_div (ha : 0 < a) (g : ℝ → F) (T : ℝ) :
    eLpNorm (fun s => g (s / a)) 2 (μI (a * T)) =
      ENNReal.ofReal (Real.sqrt a) * eLpNorm g 2 (μI T) := by
  simp_rw [div_eq_inv_mul]
  rw [eLpNorm_comp_mul (inv_pos.2 ha), inv_inv, inv_mul_cancel_left₀ ha.ne']

end Substitution

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y) {ν : ℝ}

/-- **The time-rescaled system** `ẋ = ν (A x + B u)`, `y = C x`: the semigroups `t ↦ S(ν t)` on
`W`, `X`, `V`, the control operator `ν B`, the same embeddings and the same `C`. -/
def timeScale (ν : ℝ) : System U W X V Y :=
  { sys with
    SW := sys.SW.timeScale ν
    SX := sys.SX.timeScale ν
    SV := sys.SV.timeScale ν
    consistentW := sys.consistentW.timeScale ν
    consistentV := sys.consistentV.timeScale ν
    B := ν • sys.B }

@[simp] theorem timeScale_ιW : (sys.timeScale ν).ιW = sys.ιW := rfl
@[simp] theorem timeScale_ιV : (sys.timeScale ν).ιV = sys.ιV := rfl
@[simp] theorem timeScale_SW : (sys.timeScale ν).SW = sys.SW.timeScale ν := rfl
@[simp] theorem timeScale_SX : (sys.timeScale ν).SX = sys.SX.timeScale ν := rfl
@[simp] theorem timeScale_SV : (sys.timeScale ν).SV = sys.SV.timeScale ν := rfl
@[simp] theorem timeScale_B : (sys.timeScale ν).B = ν • sys.B := rfl
@[simp] theorem timeScale_C : (sys.timeScale ν).C = sys.C := rfl

variable {sys}

/-- `A_ν = ν A`, with the domain of `A`. -/
theorem timeScale_A (hν : 0 < ν) : (sys.timeScale ν).A = ν • sys.A :=
  sys.SX.generator_timeScale hν

/-- `A_{V,ν} = ν A_V`. -/
theorem timeScale_AV (hν : 0 < ν) : (sys.timeScale ν).AV = ν • sys.AV :=
  sys.SV.generator_timeScale hν

/-- `s ∈ ρ((ν A)_ℂ) ↔ s / ν ∈ ρ(A_ℂ)`. -/
theorem mem_resolventSet_complexify_timeScale (hν : 0 < ν) (s : ℂ) :
    s ∈ resolventSet (sys.timeScale ν).A.complexify ↔ s / ν ∈ resolventSet sys.A.complexify := by
  rw [timeScale_A hν, LinearPMap.complexify_smul]
  exact mem_resolventSet_smul_iff (Complex.ofReal_ne_zero.2 hν.ne')

/-! ### Trajectories -/

/-- `∫₀ᵗ S_V(ν (t - r)) ν B u(r) dr = ∫₀^{ν t} S_V(ν t - s) B u(s/ν) ds`. -/
theorem convV_timeScale (hν : 0 < ν) (t : ℝ) (u : ℝ → U) :
    (sys.timeScale ν).convV t u = sys.convV (ν * t) (fun s => u (s / ν)) := by
  rcases le_or_gt t 0 with ht | ht
  · rw [convV_of_nonpos ht, convV_of_nonpos (by nlinarith)]
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := t)
    (fun s => sys.SV.real (ν * t - s) (sys.B (u (s / ν)))) ν
  rw [mul_zero, ← intervalIntegral.integral_smul] at h
  rw [convV, convV, ← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_of_le (mul_pos hν ht).le, ← h]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [timeScale_SV, timeScale_B, C0Semigroup.timeScale_real _ hν.le, smul_apply, map_smul]
  rw [mul_sub, mul_div_cancel_left₀ _ hν.ne']

theorem L_timeScale (hν : 0 < ν) (t : ℝ) (u : ℝ → U) :
    (sys.timeScale ν).L t u = sys.L (ν * t) (fun s => u (s / ν)) := by
  rw [L, L, convV_timeScale hν]
  rfl

/-- **The trajectories of the rescaled system**: `x_ν(t; x₀, u) = x(ν t; x₀, u(·/ν))`. -/
theorem mild_timeScale (hν : 0 < ν) (x₀ : X) (u : ℝ → U) (t : ℝ) :
    (sys.timeScale ν).mild x₀ u t = sys.mild x₀ (fun s => u (s / ν)) (ν * t) := by
  rw [mild, mild, L_timeScale hν, timeScale_SX, C0Semigroup.timeScale_real _ hν.le]
  rfl

/-- `ℛ_T(x₀)` of the rescaled system is `ℛ_{ν T}(x₀)` of the original one. -/
theorem reachable_timeScale (hν : 0 < ν) (T : ℝ) (x₀ : X) :
    (sys.timeScale ν).reachable T x₀ = sys.reachable (ν * T) x₀ := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, (memLp_comp_div_iff hν).2 hu, (mild_timeScale hν x₀ u T).symm⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun t => v (ν * t), (memLp_comp_mul_iff hν).2 hv, ?_⟩
    rw [mild_timeScale hν]
    simp_rw [mul_div_cancel₀ _ hν.ne']

/-- **Approximate controllability** of the rescaled system in time `T` is that of `(A, B)` in
time `ν T`. -/
theorem approxControllable_timeScale (hν : 0 < ν) (T : ℝ) :
    (sys.timeScale ν).ApproxControllable T ↔ sys.ApproxControllable (ν * T) := by
  rw [ApproxControllable, ApproxControllable, reachable_timeScale hν]

/-! ### The standing assumptions -/

/-- **`hyp:H1`** at `ν T` gives `hyp:H1` for the rescaled system at `T`. -/
theorem H1.timeScale (hν : 0 < ν) {T : ℝ} (h : sys.H1 (ν * T)) : (sys.timeScale ν).H1 T := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b * Real.sqrt ν, fun u => ?_⟩
  have hm : MemLp (fun s => u (s / ν)) 2 (μI (ν * T)) := (memLp_comp_div_iff hν).2 (Lp.memLp u)
  obtain ⟨w, hw, hwn⟩ := hb (hm.toLp _)
  refine ⟨w, ?_, ?_⟩
  · change sys.ιWV w = (sys.timeScale ν).convV T u
    rw [convV_timeScale hν, hw]
    exact convV_congr_ae hm.coeFn_toLp
  · rw [Lp.norm_toLp, eLpNorm_comp_div hν, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.sqrt_nonneg _), ← Lp.norm_def] at hwn
    linarith

/-- **`hyp:H2`** at `ν T` gives `hyp:H2` for the rescaled system at `T`. -/
theorem H2.timeScale (hν : 0 < ν) {T : ℝ} (h : sys.H2 (ν * T)) : (sys.timeScale ν).H2 T := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Real.sqrt ν⁻¹ * c, fun w => ?_⟩
  simp only [timeScale_C, timeScale_SW, C0Semigroup.timeScale_real _ hν.le]
  rw [eLpNorm_comp_mul hν (fun s => sys.C (sys.SW.real s w)), mul_assoc,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact mul_le_mul' le_rfl (hc w)

/-- **`hyp:compat`** passes to the rescaled system (`D(A_{V,ν}) = D(A_V)`). -/
theorem Compat.timeScale (hν : 0 < ν) (h : sys.Compat) : (sys.timeScale ν).Compat := by
  obtain ⟨⟨c, hc⟩, hd⟩ := h
  have hD : ∀ v : V, v ∈ (sys.timeScale ν).AV.domain ↔ v ∈ sys.AV.domain := fun _ =>
    sys.SV.mem_generator_domain_timeScale hν
  refine ⟨⟨|c| * (1 + ν⁻¹), fun v hv => ?_⟩, hd.mono fun w hw => (hD _).2 hw⟩
  obtain ⟨w, hw, hwn⟩ := hc v ((hD v).1 hv)
  refine ⟨w, hw, hwn.trans ?_⟩
  rw [show (sys.timeScale ν).AV ⟨v, hv⟩ = ν • sys.AV ⟨v, (hD v).1 hv⟩ from
    sys.SV.generator_timeScale_apply hν ⟨v, hv⟩, norm_smul, Real.norm_of_nonneg hν.le]
  have h1 := norm_nonneg v
  have h2 := norm_nonneg (sys.AV ⟨v, (hD v).1 hv⟩)
  have e : (1 + ν⁻¹) * (‖v‖ + ν * ‖sys.AV ⟨v, (hD v).1 hv⟩‖) =
      ‖v‖ + ‖sys.AV ⟨v, (hD v).1 hv⟩‖ + (ν * ‖sys.AV ⟨v, (hD v).1 hv⟩‖ + ν⁻¹ * ‖v‖) := by
    field_simp
    ring
  rw [mul_assoc, e]
  calc c * (‖v‖ + ‖sys.AV ⟨v, _⟩‖) ≤ |c| * (‖v‖ + ‖sys.AV ⟨v, _⟩‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (abs_nonneg c)

/-! ### The adjoint control operator -/

/-- `A_ν† = ν A†`, with the domain of `A†`. -/
theorem adjoint_A_timeScale (hν : 0 < ν) : (sys.timeScale ν).A.adjoint = ν • sys.A.adjoint := by
  rw [timeScale_A hν, LinearPMap.adjoint_smul hν.ne']

theorem mem_adjoint_domain_timeScale (hν : 0 < ν) {η : X} :
    η ∈ (sys.timeScale ν).A.adjoint.domain ↔ η ∈ sys.A.adjoint.domain := by
  rw [adjoint_A_timeScale hν]
  rfl

/-- **`B_ν† = ν B†`**: for an admissible `a`, `Q_{ν, a} = Q_{a/ν}` (`(a - ν A_V)⁻¹ ν B =
(a/ν - A_V)⁻¹ B`) and `⟪B_ν† η, v⟫ = ⟪Q_{ν, a} v, (a - ν A†) η⟫ = ν ⟪Q_{a/ν} v, (a/ν - A†) η⟫`
(`inner_Bstar_eq`). -/
theorem Bstar_timeScale {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (hν : 0 < ν)
    (η : (sys.timeScale ν).A.adjoint.domain) :
    (sys.timeScale ν).Bstar η =
      ν • sys.Bstar (⟨η, (mem_adjoint_domain_timeScale hν).1 η.2⟩ : sys.A.adjoint.domain) := by
  obtain ⟨a₀, ha₀⟩ := exists_QSpec hH1 hT
  obtain ⟨a₁, ha₁⟩ := exists_QSpec ((H1.of_pos sys hH1 hT (ν * T)).timeScale hν) hT
  set a := max a₁ (ν * a₀)
  have hA := ha₁ a (le_max_left _ _)
  have hB := ha₀ (a / ν) (by rw [ge_iff_le, le_div_iff₀ hν, mul_comm]; exact le_max_right _ _)
  have hQ : ∀ v, (sys.timeScale ν).Q a v = sys.Q (a / ν) v := fun v => sys.ιWV_injective (by
    refine (hA.2.2 v).trans ?_
    rw [hB.2.2 v, timeScale_AV hν, resolvent_smul hν.ne' hB.2.1, timeScale_B, smul_apply,
      smul_apply, map_smul, smul_smul, inv_mul_cancel₀ hν.ne', one_smul])
  have hη : (sys.timeScale ν).A.adjoint η =
      ν • sys.A.adjoint ⟨η, (mem_adjoint_domain_timeScale hν).1 η.2⟩ :=
    (LinearPMap.ext_iff.1 (adjoint_A_timeScale (sys := sys) hν)).2 (x := (η : X)) (hf := η.2)
      (hg := (mem_adjoint_domain_timeScale hν).1 η.2)
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_Bstar_eq hA, hQ, hη, real_inner_smul_left, inner_Bstar_eq hB,
    ← real_inner_smul_right, smul_sub, smul_smul, mul_div_cancel₀ _ hν.ne']
  rfl

end System

end DataDrivenControl
