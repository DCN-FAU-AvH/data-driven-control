module

public import DataDrivenControl.Examples.NeutralDelay.Weighted

/-!
# The neutral delay equation of `ex:intro-delay`: existence and uniqueness

The neutral equation (`ex:intro-delay` with `M ≠ 0`)

`d/dt (x(t) - M x_t) = L x_t + f(t)`,  `x(0) - M x_0 = r`,  `x_0 = φ`,

in integral form

`x(t) = M x_t + r + ∫₀ᵗ (L x_s + f(s)) ds`  for a.e. `t ∈ (0, τ]`,

with the retarded `L` of `Delay.Equation` (point delays `Aₖ`, `hₖ ∈ [0, h]`, and `L_d`) and
`M x_t = ∑ₖ Mₖ x(t - mₖ) + M_d x_t` with point delays `mₖ ∈ (0, h]` and `M_d` bounded on the `L²`
history.  The delays `mₖ` are strictly positive: this is the paper's "the measure representing `M`
has no mass at `0`".

## Conventions

The conventions of `Delay/Solution`: the history lives on `(0, h]`, `ψ(s) = φ(s - h)`, the
trajectory is `traj h ψ x`, and `x_t = window h (traj h ψ x) t`.  `L` and `M` are the delay
functionals `Equation.L`, `Equation.M` (`DelayOp`); `Equation.L_eval` identifies `L` with
`Delay.Equation.rhs`.  Solutions are only square integrable, so the solution concept is a.e.:
`Equation.IsSolOn τ r ψ f x` asks `x ∈ L²(0, τ)` and the integral form a.e. on `(0, τ]`.  The
first component of the state, `Equation.prim r ψ f x t = r + ∫₀ᵗ (L x_s + f(s)) ds`
(`= x(t) - M x_t`), is continuous (`continuousOn_prim`).

## Main results

* `Equation.isUnit_opK`: with zero history the equation is `x = 𝒦 x + w`,
  `𝒦 x = M x_· + ∫₀^· L x_s ds` (`Equation.opK`), and `1 - 𝒦` is invertible on `L²(0, τ; E)`:
  in the weighted norm `‖x‖_γ` the point delays of `M` contribute `‖Mₖ‖ e^{-γ mₖ}`, `M_d`
  contributes `‖M_d‖ / √(2γ)` and the integral `O(1/√γ)` (`Equation.qconst`,
  `Equation.exists_qconst_lt_one`).  The same holds for `𝒦' x = M x_· + L (∫₀^· x)_·`
  (`Equation.isUnit_opK'`), used for regularity.
* Existence `Equation.isSolOn_solL`, `Equation.isSolOn_sol`; uniqueness `Equation.IsSolOn.ae_eq`;
  the global solution `Equation.sol` (glued from the solutions on `(0, n]`,
  `Equation.sol_ae_eq_solL`).
* Linearity `IsSolOn.add`, `IsSolOn.smul`; dependence on classes only `IsSolOn.congr`,
  `IsSolOn.congr_hist`, `IsSolOn.congr_forcing`; causality `IsSolOn.mono`; time shift
  `IsSolOn.shift`.
* `L²` bound `Equation.norm_solL_le`: `‖x‖_{L²(0, τ)} ≤ c(τ) (‖r‖ + ‖ψ‖ + ∫₀^τ ‖f‖)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace NeutralDelay

open Delay (traj traj_of_le traj_of_lt traj_add traj_smul traj_zero traj_ae_congr traj_shift
  intervalIntegrable_of_integrableOn continuousOn_primitive_Ioc integral_norm_le_sqrt_mul
  norm_L2_le_of_ae_bound)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Data of a neutral delay equation** (`ex:intro-delay`):
`d/dt (x(t) - M x_t) = L x_t + f(t)` with the retarded `L` of `Delay.Equation` and
`M x_t = ∑ₖ Mₖ x(t - mₖ) + M_d x_t`, finitely many point delays `mₖ ∈ (0, h]` ("no mass at `0`")
and `M_d` bounded on the `L²` history. -/
structure Equation (h : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] extends
    Delay.Equation h E where
  /-- The number of point delays of the neutral term. -/
  NM : ℕ
  /-- The coefficients `Mₖ` of the neutral point delays. -/
  Mp : Fin NM → E →L[ℝ] E
  /-- The neutral point delays `mₖ`. -/
  τM : Fin NM → ℝ
  /-- The neutral point delays lie in `(0, h]`: `M` has no mass at `0`. -/
  τM_mem : ∀ k, τM k ∈ Ioc 0 h
  /-- The distributed part `M_d` of the neutral term, acting on the history in `L²(0, h; E)`. -/
  Md : L2 E h →L[ℝ] E

namespace Equation

variable {h : ℝ} (d : Equation h E)

/-- The retarded part `L x_t = ∑ₖ Aₖ x(t - hₖ) + L_d x_t` as a delay functional. -/
def L : DelayOp h E E := ⟨d.h_pos, d.N, d.A, d.τ, d.τ_mem, d.Ad⟩

/-- The neutral part `M x_t = ∑ₖ Mₖ x(t - mₖ) + M_d x_t` as a delay functional. -/
def M : DelayOp h E E :=
  ⟨d.h_pos, d.NM, d.Mp, d.τM, fun k => Ioc_subset_Icc_self (d.τM_mem k), d.Md⟩

/-- `L` is the right-hand side of the retarded equation. -/
theorem L_eval (z : ℝ → E) (s : ℝ) : d.L.eval z s = d.rhs z s := rfl

/-- The neutral point delays are positive. -/
theorem M_δ_pos (k : Fin d.M.N) : 0 < d.M.δ k := (d.τM_mem k).1

/-- The first state component `x(t) - M x_t = r + ∫₀ᵗ (L x_s + f(s)) ds`. -/
def prim (r : E) (ψ f x : ℝ → E) (t : ℝ) : E :=
  r + ∫ s in (0 : ℝ)..t, (d.L.eval (traj h ψ x) s + f s)

/-- `x` solves the neutral equation on `(0, τ]` with initial value `r = x(0) - M x_0`, history `ψ`
and forcing `f` (integral form, a.e.): `x ∈ L²(0, τ)` and
`x(t) = M x_t + r + ∫₀ᵗ (L x_s + f(s)) ds` for a.e. `t ∈ (0, τ]`. -/
def IsSolOn (τ : ℝ) (r : E) (ψ f x : ℝ → E) : Prop :=
  MemLp x 2 (μI τ) ∧ ∀ᵐ t ∂(μI τ), x t = d.M.eval (traj h ψ x) t + d.prim r ψ f x t

/-! ### The first state component -/

variable {τ : ℝ} {r : E} {ψ f x : ℝ → E}

/-- The integrand `L x_s + f(s)` of an `L²` solution is integrable. -/
theorem integrableOn_integrand (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hx : MemLp x 2 (μI τ))
    (hf : IntegrableOn f (Ioc 0 τ)) :
    IntegrableOn (fun s => d.L.eval (traj h ψ x) s + f s) (Ioc 0 τ) :=
  (d.L.integrableOn_eval (memLp_traj_of_memLp d.h_pos.le hτ hψ hx)).add hf

/-- The first state component is continuous. -/
theorem continuousOn_prim (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hx : MemLp x 2 (μI τ))
    (hf : IntegrableOn f (Ioc 0 τ)) : ContinuousOn (d.prim r ψ f x) (Icc 0 τ) :=
  continuousOn_const.add (continuousOn_primitive_Ioc (d.integrableOn_integrand hτ hψ hx hf))

/-- `prim` at time `0` is the initial value. -/
@[simp] theorem prim_zero (r : E) (ψ f x : ℝ → E) : d.prim r ψ f x 0 = r := by simp [prim]

/-- `prim` only sees the class of the solution. -/
theorem prim_congr {x₁ x₂ : ℝ → E} (hx : x₁ =ᵐ[μI τ] x₂) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    d.prim r ψ f x₁ t = d.prim r ψ f x₂ t := by
  have hL := d.L.ae_eval_eq (traj_ae_congr_right ψ hx)
  rw [prim, prim, intervalIntegral_congr_μI (x₁ := fun s => d.L.eval (traj h ψ x₁) s + f s)
    (x₂ := fun s => d.L.eval (traj h ψ x₂) s + f s) (hL.mono fun s hs => by simp only [hs]) ht]

/-- `prim` only sees the class of the history. -/
theorem prim_congr_hist {ψ₁ ψ₂ : ℝ → E} (hψ : ψ₁ =ᵐ[μI h] ψ₂) {t : ℝ} (ht : 0 ≤ t) :
    d.prim r ψ₁ f x t = d.prim r ψ₂ f x t := by
  have hL := d.L.ae_eval_eq (traj_ae_congr hψ x (h + t))
  rw [prim, prim, intervalIntegral_congr_μI (x₁ := fun s => d.L.eval (traj h ψ₁ x) s + f s)
    (x₂ := fun s => d.L.eval (traj h ψ₂ x) s + f s) (hL.mono fun s hs => by simp only [hs])
    ⟨ht, le_rfl⟩]

/-- `prim` only sees the class of the forcing. -/
theorem prim_congr_forcing {f₁ f₂ : ℝ → E} (hf : f₁ =ᵐ[μI τ] f₂) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    d.prim r ψ f₁ x t = d.prim r ψ f₂ x t := by
  rw [prim, prim, intervalIntegral_congr_μI (x₁ := fun s => d.L.eval (traj h ψ x) s + f₁ s)
    (x₂ := fun s => d.L.eval (traj h ψ x) s + f₂ s) (hf.mono fun s hs => by simp only [hs]) ht]

/-! ### Elementary properties of solutions -/

variable {d}

/-- A solution on `(0, τ]` is a solution on `(0, τ']`, `τ' ≤ τ`. -/
theorem IsSolOn.mono {τ' : ℝ} (hx : d.IsSolOn τ r ψ f x) (hτ : τ' ≤ τ) :
    d.IsSolOn τ' r ψ f x :=
  ⟨memLp_μI_of_le hx.1 hτ, ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hτ) hx.2⟩

/-- A function equal a.e. to a solution is a solution. -/
theorem IsSolOn.congr {y : ℝ → E} (hx : d.IsSolOn τ r ψ f x) (hxy : x =ᵐ[μI τ] y) :
    d.IsSolOn τ r ψ f y := by
  refine ⟨hx.1.ae_eq hxy, ?_⟩
  filter_upwards [hx.2, hxy, d.M.ae_eval_eq (traj_ae_congr_right ψ hxy),
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 h4
  rw [← h2, h1, h3, d.prim_congr hxy (Ioc_subset_Icc_self h4)]

/-- Changing the history on a null set does not change the solutions. -/
theorem IsSolOn.congr_hist {ψ₁ ψ₂ : ℝ → E} (hψ : ψ₁ =ᵐ[μI h] ψ₂) (hx : d.IsSolOn τ r ψ₁ f x) :
    d.IsSolOn τ r ψ₂ f x := by
  refine ⟨hx.1, ?_⟩
  filter_upwards [hx.2, d.M.ae_eval_eq (traj_ae_congr hψ x (h + τ)),
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3
  rw [h1, h2, d.prim_congr_hist hψ h3.1.le]

/-- Changing the forcing on a null set does not change the solutions. -/
theorem IsSolOn.congr_forcing {f₁ f₂ : ℝ → E} (hf : f₁ =ᵐ[μI τ] f₂)
    (hx : d.IsSolOn τ r ψ f₁ x) : d.IsSolOn τ r ψ f₂ x := by
  refine ⟨hx.1, ?_⟩
  filter_upwards [hx.2, ae_restrict_mem measurableSet_Ioc] with t h1 h2
  rw [h1, d.prim_congr_forcing hf (Ioc_subset_Icc_self h2)]

/-- **Superposition.** -/
theorem IsSolOn.add (hτ : 0 ≤ τ) {r₁ r₂ : E} {ψ₁ ψ₂ f₁ f₂ x₁ x₂ : ℝ → E}
    (hψ₁ : MemLp ψ₁ 2 (μI h)) (hψ₂ : MemLp ψ₂ 2 (μI h)) (hf₁ : IntegrableOn f₁ (Ioc 0 τ))
    (hf₂ : IntegrableOn f₂ (Ioc 0 τ)) (hx₁ : d.IsSolOn τ r₁ ψ₁ f₁ x₁)
    (hx₂ : d.IsSolOn τ r₂ ψ₂ f₂ x₂) :
    d.IsSolOn τ (r₁ + r₂) (ψ₁ + ψ₂) (f₁ + f₂) (x₁ + x₂) := by
  have m₁ := memLp_traj_of_memLp d.h_pos.le hτ hψ₁ hx₁.1
  have m₂ := memLp_traj_of_memLp d.h_pos.le hτ hψ₂ hx₂.1
  have hw : ∀ s ∈ Icc 0 τ, ∀ (p : DelayOp h E E),
      p.eval (traj h (ψ₁ + ψ₂) (x₁ + x₂)) s = p.eval (traj h ψ₁ x₁) s + p.eval (traj h ψ₂ x₂) s :=
    fun s hs p => by
      rw [traj_add, p.eval_add (memLp_comp_add m₁ hs.1 (by linarith [hs.2]))
        (memLp_comp_add m₂ hs.1 (by linarith [hs.2]))]
  refine ⟨hx₁.1.add hx₂.1, ?_⟩
  filter_upwards [hx₁.2, hx₂.2, ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
  have ht' : t ∈ Icc 0 τ := Ioc_subset_Icc_self ht
  have hi : ∀ (r : E) (ψ x f : ℝ → E), MemLp ψ 2 (μI h) → MemLp x 2 (μI τ) →
      IntegrableOn f (Ioc 0 τ) →
      IntervalIntegrable (fun s => d.L.eval (traj h ψ x) s + f s) volume 0 t :=
    fun _ ψ x f hψ hx hf => intervalIntegrable_of_integrableOn
      (d.integrableOn_integrand hτ hψ hx hf) ht'
  rw [Pi.add_apply, h1, h2, hw t ht' d.M, prim, prim, prim,
    intervalIntegral.integral_congr
      (f := fun s => d.L.eval (traj h (ψ₁ + ψ₂) (x₁ + x₂)) s + (f₁ + f₂) s)
      (g := fun s => (d.L.eval (traj h ψ₁ x₁) s + f₁ s) +
      (d.L.eval (traj h ψ₂ x₂) s + f₂ s)) (fun s hs => ?_),
    intervalIntegral.integral_add (hi r₁ ψ₁ x₁ f₁ hψ₁ hx₁.1 hf₁) (hi r₂ ψ₂ x₂ f₂ hψ₂ hx₂.1 hf₂)]
  · abel
  · rw [uIcc_of_le ht'.1] at hs
    simp only [hw s ⟨hs.1, hs.2.trans ht'.2⟩ d.L, Pi.add_apply]
    abel

/-- **Homogeneity.** -/
theorem IsSolOn.smul (hx : d.IsSolOn τ r ψ f x) (c : ℝ) :
    d.IsSolOn τ (c • r) (c • ψ) (c • f) (c • x) := by
  refine ⟨hx.1.const_smul c, ?_⟩
  filter_upwards [hx.2] with t h1
  have e : (fun s => d.L.eval (traj h (c • ψ) (c • x)) s + (c • f) s) =
      fun s => c • (d.L.eval (traj h ψ x) s + f s) := by
    funext s
    rw [traj_smul, d.L.eval_smul, Pi.smul_apply, smul_add]
  rw [Pi.smul_apply, h1, traj_smul, d.M.eval_smul, prim, prim, e, intervalIntegral.integral_smul,
    smul_add, smul_add]

/-! ### The operator form -/

variable (d)

/-- The zero-history part `𝒦 x = M x_· + ∫₀^· L x_s ds` of the integral form. -/
def kfun (x : ℝ → E) (t : ℝ) : E :=
  d.M.eval (traj h 0 x) t + ∫ s in (0 : ℝ)..t, d.L.eval (traj h 0 x) s

/-- The data part `w = r + M (ψ, 0)_· + ∫₀^· (L (ψ, 0)_s + f(s)) ds` of the integral form. -/
def forc (r : E) (ψ f : ℝ → E) (t : ℝ) : E :=
  r + d.M.eval (traj h ψ 0) t + ∫ s in (0 : ℝ)..t, (d.L.eval (traj h ψ 0) s + f s)

/-- **The neutral Volterra operator** `𝒦 x = M x_· + ∫₀^· L x_s ds` (zero history) on
`L²(0, τ; E)`. -/
def opK (τ : ℝ) : L2 E τ →L[ℝ] L2 E τ := d.M.opL τ + primL τ ∘L d.L.opL τ

/-- The differentiated operator `𝒦' y = M y_· + L (∫₀^· y)_·` (zero history), used for
regularity. -/
def opK' (τ : ℝ) : L2 E τ →L[ℝ] L2 E τ := d.M.opL τ + d.L.opL τ ∘L primL τ

/-- The weighted contraction constant `wconst M γ + √τ / √(2γ) (∑ₖ ‖Aₖ‖ + ‖L_d‖)`. -/
def qconst (τ γ : ℝ) : ℝ := d.M.wconst γ + √τ / √(2 * γ) * (∑ k, ‖d.L.P k‖ + ‖d.L.D‖)

/-- `𝒦` acts by `kfun` on representatives. -/
theorem coeFn_opK (τ : ℝ) (x : L2 E τ) : ⇑(d.opK τ x) =ᵐ[μI τ] d.kfun ⇑x := by
  rw [opK]
  filter_upwards [Lp.coeFn_add (d.M.opL τ x) (primL τ (d.L.opL τ x)), d.M.coeFn_opL τ x,
    coeFn_primL τ (d.L.opL τ x), ae_restrict_mem measurableSet_Ioc] with t h1 h2 h3 h4
  rw [add_apply, ContinuousLinearMap.comp_apply, h1, Pi.add_apply, h2, h3,
    kfun, intervalIntegral_congr_μI (d.L.coeFn_opL τ x) (Ioc_subset_Icc_self h4)]

/-- `𝒦'` acts by `y ↦ M y_· + L (∫₀^· y)_·` on representatives. -/
theorem coeFn_opK' (τ : ℝ) (y : L2 E τ) :
    ⇑(d.opK' τ y) =ᵐ[μI τ] fun t => d.M.eval (traj h 0 ⇑y) t +
      d.L.eval (traj h 0 fun t => ∫ s in (0 : ℝ)..t, y s) t := by
  rw [opK']
  filter_upwards [Lp.coeFn_add (d.M.opL τ y) (d.L.opL τ (primL τ y)), d.M.coeFn_opL τ y,
    d.L.coeFn_opL τ (primL τ y), d.L.ae_eval_traj_zero_congr (coeFn_primL τ y)]
    with t h1 h2 h3 h4
  rw [add_apply, ContinuousLinearMap.comp_apply, h1, Pi.add_apply, h2, h3, h4]

/-- **Weighted bound of `𝒦`** for `γ ≥ 1/2`. -/
theorem wnorm_opK_le {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 1 / 2 ≤ γ) (x : L2 E τ) :
    wnorm γ τ (d.opK τ x) ≤ ENNReal.ofReal (d.qconst τ γ) * wnorm γ τ x := by
  have hγ0 : 0 < γ := by linarith
  have e : ⇑(d.opK τ x) =ᵐ[μI τ] fun t => (d.M.opL τ x) t + (primL τ (d.L.opL τ x)) t :=
    Lp.coeFn_add _ _
  rw [wnorm_congr_ae e, qconst]
  refine wnorm_add_le_of_le (d.M.wconst_nonneg γ)
    (b := √τ / √(2 * γ) * (∑ k, ‖d.L.P k‖ + ‖d.L.D‖)) (by positivity)
    (d.M.wnorm_opL_le hτ hγ0 x) ?_
  refine (wnorm_primL_le hτ hγ0 _).trans ?_
  refine (mul_le_mul_right (d.L.wnorm_opL_le hτ hγ0 x) _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (d.L.wconst_le hγ) (by positivity))) _

/-- **Weighted bound of `𝒦'`** for `γ ≥ 1/2`. -/
theorem wnorm_opK'_le {τ γ : ℝ} (hτ : 0 ≤ τ) (hγ : 1 / 2 ≤ γ) (x : L2 E τ) :
    wnorm γ τ (d.opK' τ x) ≤ ENNReal.ofReal (d.qconst τ γ) * wnorm γ τ x := by
  have hγ0 : 0 < γ := by linarith
  have e : ⇑(d.opK' τ x) =ᵐ[μI τ] fun t => (d.M.opL τ x) t + (d.L.opL τ (primL τ x)) t :=
    Lp.coeFn_add _ _
  rw [wnorm_congr_ae e, qconst]
  refine wnorm_add_le_of_le (d.M.wconst_nonneg γ)
    (b := √τ / √(2 * γ) * (∑ k, ‖d.L.P k‖ + ‖d.L.D‖)) (by positivity)
    (d.M.wnorm_opL_le hτ hγ0 x) ?_
  refine (d.L.wnorm_opL_le hτ hγ0 _).trans ?_
  refine (mul_le_mul_right (wnorm_primL_le hτ hγ0 x) _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (d.L.wconst_nonneg γ), mul_comm (d.L.wconst γ)]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (d.L.wconst_le hγ) (by positivity))) _

/-- For `γ` large the weighted constant is `< 1` (`mₖ > 0`: no mass at `0`). -/
theorem exists_qconst_lt_one (τ : ℝ) : ∃ γ, 1 / 2 ≤ γ ∧ d.qconst τ γ < 1 := by
  have ht : Tendsto (d.qconst τ) atTop (𝓝 0) := by
    have := (d.M.tendsto_wconst d.M_δ_pos).add
      ((tendsto_sqrt_div_sqrt τ).mul_const (∑ k, ‖d.L.P k‖ + ‖d.L.D‖))
    rw [zero_mul, add_zero] at this
    exact this
  obtain ⟨γ, h1, h2⟩ :=
    ((eventually_ge_atTop (1 / 2)).and (ht.eventually (gt_mem_nhds one_pos))).exists
  exact ⟨γ, h1, h2⟩

/-- The weighted contraction constant is nonnegative. -/
theorem qconst_nonneg (τ γ : ℝ) : 0 ≤ d.qconst τ γ := by
  unfold qconst
  have := d.M.wconst_nonneg γ
  positivity

/-- **`1 - 𝒦` is invertible** on `L²(0, τ; E)` (weighted contraction). -/
theorem isUnit_opK {τ : ℝ} (hτ : 0 ≤ τ) : IsUnit (1 - d.opK τ) := by
  obtain ⟨γ, hγ, hq⟩ := d.exists_qconst_lt_one τ
  exact isUnit_one_sub_of_wnorm_le (by linarith) (d.qconst_nonneg τ γ) hq _ (d.wnorm_opK_le hτ hγ)

/-- **`1 - 𝒦'` is invertible** on `L²(0, τ; E)`. -/
theorem isUnit_opK' {τ : ℝ} (hτ : 0 ≤ τ) : IsUnit (1 - d.opK' τ) := by
  obtain ⟨γ, hγ, hq⟩ := d.exists_qconst_lt_one τ
  exact isUnit_one_sub_of_wnorm_le (by linarith) (d.qconst_nonneg τ γ) hq _ (d.wnorm_opK'_le hτ hγ)

/-- The data part is square integrable. -/
theorem memLp_forc (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ)) :
    MemLp (d.forc r ψ f) 2 (μI τ) :=
  ((memLp_μI_of_continuousOn continuousOn_const).add
    (d.M.memLp_eval (memLp_traj_of_memLp d.h_pos.le hτ hψ MemLp.zero))).add
    (memLp_μI_of_continuousOn (continuousOn_primitive_Ioc
      (d.integrableOn_integrand hτ hψ MemLp.zero hf)))

/-- **Splitting the integral form** into the zero-history part and the data part. -/
theorem eval_add_prim (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hx : MemLp x 2 (μI τ))
    (hf : IntegrableOn f (Ioc 0 τ)) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    d.M.eval (traj h ψ x) t + d.prim r ψ f x t = d.kfun x t + d.forc r ψ f t := by
  have m₁ := memLp_traj_of_memLp d.h_pos.le hτ hψ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI τ))
  have m₂ := memLp_traj_of_memLp d.h_pos.le hτ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI h)) hx
  have e : traj h ψ x = traj h ψ 0 + traj h 0 x := by rw [← traj_add, add_zero, zero_add]
  have hw : ∀ s ∈ Icc 0 τ, ∀ (p : DelayOp h E E),
      p.eval (traj h ψ x) s = p.eval (traj h ψ 0) s + p.eval (traj h 0 x) s := fun s hs p => by
    rw [e, p.eval_add (memLp_comp_add m₁ hs.1 (by linarith [hs.2]))
      (memLp_comp_add m₂ hs.1 (by linarith [hs.2]))]
  have i₁ := intervalIntegrable_of_integrableOn
    (d.integrableOn_integrand hτ hψ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI τ)) hf) ht
  have i₂ := intervalIntegrable_of_integrableOn (d.L.integrableOn_eval m₂) ht
  rw [prim, kfun, forc, hw t ht d.M,
    intervalIntegral.integral_congr (f := fun s => d.L.eval (traj h ψ x) s + f s)
      (g := fun s => (d.L.eval (traj h ψ 0) s + f s) +
      d.L.eval (traj h 0 x) s) (fun s hs => ?_), intervalIntegral.integral_add i₁ i₂]
  · abel
  · rw [uIcc_of_le ht.1] at hs
    simp only [hw s ⟨hs.1, hs.2.trans ht.2⟩ d.L]
    abel

open scoped Classical in
/-- The data part as an element of `L²(0, τ; E)` (junk value `0` off its hypotheses). -/
def forcL (τ : ℝ) (r : E) (ψ f : ℝ → E) : L2 E τ :=
  if hm : MemLp (d.forc r ψ f) 2 (μI τ) then hm.toLp _ else 0

/-- The representative of the data part. -/
theorem coeFn_forcL (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ)) :
    ⇑(d.forcL τ r ψ f) =ᵐ[μI τ] d.forc r ψ f := by
  have hm := d.memLp_forc (r := r) hτ hψ hf
  rw [forcL, dite_eq_left hm]
  exact hm.coeFn_toLp

/-- **Solutions are the solutions of `(1 - 𝒦) x = w`.** -/
theorem isSolOn_iff (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ))
    (hx : MemLp x 2 (μI τ)) :
    d.IsSolOn τ r ψ f x ↔ (1 - d.opK τ) (hx.toLp x) = d.forcL τ r ψ f := by
  have hK : ⇑((1 - d.opK τ) (hx.toLp x)) =ᵐ[μI τ] fun t => x t - d.kfun x t := by
    have h1 : d.kfun ⇑(hx.toLp x) =ᵐ[μI τ] d.kfun x := by
      filter_upwards [d.M.ae_eval_traj_zero_congr hx.coeFn_toLp, ae_restrict_mem measurableSet_Ioc]
        with t h2 h3
      rw [kfun, kfun, h2, intervalIntegral_congr_μI (d.L.ae_eval_traj_zero_congr hx.coeFn_toLp)
        (Ioc_subset_Icc_self h3)]
    filter_upwards [Lp.coeFn_sub (hx.toLp x) (d.opK τ (hx.toLp x)), hx.coeFn_toLp,
      d.coeFn_opK τ (hx.toLp x), h1] with t e1 e2 e3 e4
    rw [sub_apply, one_apply_eq_self, e1, Pi.sub_apply, e2, e3, e4]
  have hsplit : ∀ᵐ t ∂(μI τ),
      d.M.eval (traj h ψ x) t + d.prim r ψ f x t = d.kfun x t + d.forc r ψ f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact d.eval_add_prim hτ hψ hx hf (Ioc_subset_Icc_self ht)
  constructor
  · intro hs
    refine Lp.ext ?_
    filter_upwards [hK, hs.2, hsplit, d.coeFn_forcL (r := r) hτ hψ hf] with t e1 e2 e3 e4
    rw [e1, e4, e2, e3]
    abel
  · intro heq
    refine ⟨hx, ?_⟩
    have hF := d.coeFn_forcL (r := r) hτ hψ hf
    rw [← heq] at hF
    filter_upwards [hK, hF, hsplit] with t e1 e2 e3
    rw [e3, ← e2, e1]
    abel

/-- The solution on `(0, τ]`, as an element of `L²(0, τ; E)`: `(1 - 𝒦)⁻¹ w`. -/
def solL (τ : ℝ) (r : E) (ψ f : ℝ → E) : L2 E τ :=
  Ring.inverse (1 - d.opK τ) (d.forcL τ r ψ f)

/-- **Existence** on `(0, τ]`. -/
theorem isSolOn_solL (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ)) :
    d.IsSolOn τ r ψ f (d.solL τ r ψ f) := by
  rw [d.isSolOn_iff hτ hψ hf (Lp.memLp _), Lp.toLp_coeFn, solL]
  have hu := Ring.mul_inverse_cancel _ (d.isUnit_opK hτ)
  calc (1 - d.opK τ) (Ring.inverse (1 - d.opK τ) (d.forcL τ r ψ f))
      = ((1 - d.opK τ) * Ring.inverse (1 - d.opK τ)) (d.forcL τ r ψ f) := rfl
    _ = d.forcL τ r ψ f := by rw [hu]; rfl

variable {d}

/-- Every solution is `(1 - 𝒦)⁻¹ w`. -/
theorem IsSolOn.ae_eq_solL (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ))
    (hx : d.IsSolOn τ r ψ f x) : x =ᵐ[μI τ] d.solL τ r ψ f := by
  have h1 := (d.isSolOn_iff hτ hψ hf hx.1).1 hx
  have h2 : hx.1.toLp x = d.solL τ r ψ f := by
    have hu := Ring.inverse_mul_cancel _ (d.isUnit_opK hτ)
    rw [solL, ← h1]
    calc hx.1.toLp x = (Ring.inverse (1 - d.opK τ) * (1 - d.opK τ)) (hx.1.toLp x) := by
          rw [hu]; rfl
      _ = _ := rfl
  rw [← h2]
  exact hx.1.coeFn_toLp.symm

/-- **Uniqueness** of solutions on `(0, τ]`. -/
theorem IsSolOn.ae_eq {y : ℝ → E} (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h))
    (hf : IntegrableOn f (Ioc 0 τ)) (hx : d.IsSolOn τ r ψ f x) (hy : d.IsSolOn τ r ψ f y) :
    x =ᵐ[μI τ] y :=
  (hx.ae_eq_solL hτ hψ hf).trans (hy.ae_eq_solL hτ hψ hf).symm

variable (d)

/-- **The solution** of the neutral equation, glued from the solutions on `(0, n + 1]`:
`x(t)` is (a representative of) the solution on `(0, ⌊t⌋ + 1]` at `t`. -/
def sol (r : E) (ψ f : ℝ → E) (t : ℝ) : E := d.solL ((⌊t⌋₊ : ℝ) + 1) r ψ f t

/-- The glued solution agrees a.e. with the solution on `(0, τ]`. -/
theorem sol_ae_eq_solL (hψ : MemLp ψ 2 (μI h)) (hf : ∀ τ, IntegrableOn f (Ioc 0 τ))
    (hτ : 0 ≤ τ) : d.sol r ψ f =ᵐ[μI τ] d.solL τ r ψ f := by
  have hn : ∀ n : ℕ, ∀ᵐ t ∂(μI τ), t ≤ (n : ℝ) + 1 →
      d.solL ((n : ℝ) + 1) r ψ f t = d.solL τ r ψ f t := by
    intro n
    set τ' := min ((n : ℝ) + 1) τ
    have hτ' : 0 ≤ τ' := le_min (by positivity) hτ
    have h1 := ((d.isSolOn_solL (r := r) (by positivity) hψ (hf _)).mono
      (min_le_left ((n : ℝ) + 1) τ)).ae_eq hτ' hψ (hf τ')
      ((d.isSolOn_solL (r := r) hτ hψ (hf τ)).mono (min_le_right ((n : ℝ) + 1) τ))
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h1
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1] with t ht htI htn
    exact ht ⟨htI.1, le_min htn htI.2⟩
  filter_upwards [ae_all_iff.2 hn] with t ht
  exact ht _ (Nat.lt_floor_add_one t).le

/-- **Existence**: the glued solution solves the equation on every `(0, τ]`. -/
theorem isSolOn_sol (hψ : MemLp ψ 2 (μI h)) (hf : ∀ τ, IntegrableOn f (Ioc 0 τ))
    (hτ : 0 ≤ τ) : d.IsSolOn τ r ψ f (d.sol r ψ f) :=
  (d.isSolOn_solL hτ hψ (hf τ)).congr (d.sol_ae_eq_solL hψ hf hτ).symm

/-- Every solution on `(0, τ]` is the glued solution there. -/
theorem ae_eq_sol (hψ : MemLp ψ 2 (μI h)) (hf : ∀ τ, IntegrableOn f (Ioc 0 τ)) (hτ : 0 ≤ τ)
    (hx : d.IsSolOn τ r ψ f x) : x =ᵐ[μI τ] d.sol r ψ f :=
  hx.ae_eq hτ hψ (hf τ) (d.isSolOn_sol hψ hf hτ)

/-! ### Time shift -/

/-- **Restarting the first state component** at time `s`:
`prim(s) + ∫₀ᵗ (L x_{s+u} + f(s + u)) du = prim(s + t)`. -/
theorem prim_shift {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hψ : MemLp ψ 2 (μI h))
    (hx : MemLp x 2 (μI (s + t))) (hf : IntegrableOn f (Ioc 0 (s + t))) :
    d.prim (d.prim r ψ f x s) (fun σ => traj h ψ x (s + σ)) (fun σ => f (s + σ))
      (fun σ => x (s + σ)) t = d.prim r ψ f x (s + t) := by
  have hts := traj_shift (h := h) hs ψ x
  have hI := d.integrableOn_integrand (by linarith) hψ hx hf
  have e := intervalIntegral.integral_comp_add_left
    (fun u => d.L.eval (traj h ψ x) u + f u) s (a := 0) (b := t)
  rw [prim, prim, prim, hts]
  simp only [d.L.eval_shift]
  rw [e, add_zero, add_assoc, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_integrableOn hI ⟨hs, by linarith⟩)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hI.mono_set (Ioc_subset_Ioc hs le_rfl)))]

variable {d}

/-- **Time shift**: restarted at time `s`, a solution solves the equation with initial value
`prim(s) = x(s) - M x_s`, history `x_s` and forcing `f(s + ·)`. -/
theorem IsSolOn.shift {s : ℝ} (hs : 0 ≤ s) (hψ : MemLp ψ 2 (μI h))
    (hf : IntegrableOn f (Ioc 0 (s + τ))) (hx : d.IsSolOn (s + τ) r ψ f x) :
    d.IsSolOn τ (d.prim r ψ f x s) (fun σ => traj h ψ x (s + σ)) (fun σ => f (s + σ))
      (fun σ => x (s + σ)) := by
  have hts := traj_shift (h := h) hs ψ x
  refine ⟨memLp_comp_add hx.1 hs le_rfl, ?_⟩
  filter_upwards [ae_comp_add hx.2 hs le_rfl, ae_restrict_mem measurableSet_Ioc] with t h1 ht
  show x (s + t) = _
  rw [h1, hts, d.M.eval_shift, d.prim_shift hs ht.1.le hψ (memLp_μI_of_le hx.1 (by linarith [ht.2]))
    (hf.mono_set (Ioc_subset_Ioc_right (by linarith [ht.2])))]

/-! ### Bounds -/

variable (d)

/-- The constant `√τ + bound M τ + τ bound L τ` of the data. -/
def cforc (τ : ℝ) : ℝ := √τ + d.M.bound τ + τ * d.L.bound τ

/-- **Bound on the data**: `‖w‖_{L²(0, τ)} ≤ c (‖r‖ + ‖ψ‖ + ∫₀^τ ‖f‖)`. -/
theorem norm_forcL_le (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ)) :
    ‖d.forcL τ r ψ f‖ ≤
      d.cforc τ * (‖r‖ + (eLpNorm ψ 2 (μI h)).toReal + ∫ s in Ioc 0 τ, ‖f s‖) := by
  set Ψ := (eLpNorm ψ 2 (μI h)).toReal with hΨdef
  set F := ∫ s in Ioc 0 τ, ‖f s‖ with hFdef
  have hΨ : 0 ≤ Ψ := ENNReal.toReal_nonneg
  have hF : 0 ≤ F := integral_nonneg fun _ => norm_nonneg _
  have hz := memLp_traj_of_memLp d.h_pos.le hτ hψ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI τ))
  have hzn : (eLpNorm (traj h ψ 0) 2 (μI (h + τ))).toReal = Ψ := by
    rw [Delay.Equation.eLpNorm_traj_zero hτ]
  have m1 : MemLp (fun _ : ℝ => r) 2 (μI τ) := memLp_μI_of_continuousOn continuousOn_const
  have m2 : MemLp (d.M.eval (traj h ψ 0)) 2 (μI τ) := d.M.memLp_eval hz
  have hI := d.integrableOn_integrand hτ hψ (MemLp.zero : MemLp (0 : ℝ → E) 2 (μI τ)) hf
  have m3 : MemLp (fun t => ∫ s in (0 : ℝ)..t, (d.L.eval (traj h ψ 0) s + f s)) 2 (μI τ) :=
    memLp_μI_of_continuousOn (continuousOn_primitive_Ioc hI)
  have e : d.forcL τ r ψ f = m1.toLp _ + m2.toLp _ + m3.toLp _ := by
    rw [← MemLp.toLp_add, ← MemLp.toLp_add, forcL, dite_eq_left (d.memLp_forc hτ hψ hf)]
    rfl
  have b1 : ‖m1.toLp (fun _ : ℝ => r)‖ ≤ √τ * ‖r‖ :=
    norm_L2_le_of_ae_bound hτ _ (norm_nonneg _) (m1.coeFn_toLp.mono fun t ht => by rw [ht])
  have b2 : ‖m2.toLp _‖ ≤ d.M.bound τ * Ψ := by
    rw [Lp.norm_toLp, ← hzn]
    exact d.M.eLpNorm_eval_le hτ hz
  have b3 : ‖m3.toLp _‖ ≤ √τ * (√τ * (d.L.bound τ * Ψ) + F) := by
    have hL := d.L.bound_nonneg τ
    refine norm_L2_le_of_ae_bound hτ _ (by positivity) ?_
    filter_upwards [m3.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t e1 e2
    rw [e1, intervalIntegral.integral_of_le e2.1.le]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_set hI.norm (ae_of_all _ fun _ => norm_nonneg _)
      (Ioc_subset_Ioc_right e2.2).eventuallyLE).trans ?_
    refine (integral_mono hI.norm ((d.L.integrableOn_eval hz).norm.add hf.norm)
      fun s => norm_add_le _ _).trans ?_
    rw [integral_add' (d.L.integrableOn_eval hz).norm hf.norm]
    refine add_le_add ?_ le_rfl
    refine (integral_norm_le_sqrt_mul hτ (d.L.memLp_eval hz)).trans ?_
    exact mul_le_mul_of_nonneg_left ((d.L.eLpNorm_eval_le hτ hz).trans_eq (by rw [hzn]))
      (Real.sqrt_nonneg _)
  rw [e]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) b3).trans ?_)
  have hs : √τ * √τ = τ := Real.mul_self_sqrt hτ
  have hM := d.M.bound_nonneg τ
  have hL := d.L.bound_nonneg τ
  have hsq := Real.sqrt_nonneg τ
  have hr := norm_nonneg r
  calc ‖m1.toLp (fun _ : ℝ => r)‖ + ‖m2.toLp _‖ + √τ * (√τ * (d.L.bound τ * Ψ) + F)
      ≤ √τ * ‖r‖ + d.M.bound τ * Ψ + (τ * d.L.bound τ * Ψ + √τ * F) := by
        rw [mul_add, ← mul_assoc, hs, ← mul_assoc]
        linarith
    _ ≤ d.cforc τ * (‖r‖ + Ψ + F) := by
        rw [cforc]
        nlinarith [mul_nonneg hsq hΨ, mul_nonneg hM hr, mul_nonneg hM hF,
          mul_nonneg (mul_nonneg hτ hL) hr, mul_nonneg (mul_nonneg hτ hL) hF]

/-- **`L²` bound of the solution**:
`‖x‖_{L²(0, τ)} ≤ ‖(1 - 𝒦)⁻¹‖ c(τ) (‖r‖ + ‖ψ‖ + ∫₀^τ ‖f‖)`. -/
theorem norm_solL_le (hτ : 0 ≤ τ) (hψ : MemLp ψ 2 (μI h)) (hf : IntegrableOn f (Ioc 0 τ)) :
    ‖d.solL τ r ψ f‖ ≤ ‖Ring.inverse (1 - d.opK τ)‖ * d.cforc τ *
      (‖r‖ + (eLpNorm ψ 2 (μI h)).toReal + ∫ s in Ioc 0 τ, ‖f s‖) := by
  rw [solL, mul_assoc]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (d.norm_forcL_le hτ hψ hf) (norm_nonneg _))

end Equation

end NeutralDelay

end DataDrivenControl
