module

public import DataDrivenControl.System.Mild
public import DataDrivenControl.Semigroup.Resolvent
public import DataDrivenControl.Semigroup.Extrapolation

/-!
# The compatible control operator

Paper: `app:control-realization`, `eq:control-resolvent-decay`, `eq:weak-mild-diff`, the
paragraph after `lem:finite-horizon-output`.  `A` is the generator on `X`, `X₋₁` is the dual
model `sys.SX.Extrap` (`Semigroup/Extrapolation`), `A_{X,-1}` is `sys.SX.genExtrap` on `X` and
the extended semigroup `sys.SX.extrapSemigroup` on `X₋₁`.

## Main declarations

* `sys.Q r : U →L[ℝ] W`, `Q_r = (r - A_V)⁻¹ B` (junk `0` where not representable in `W`);
  `sys.QSpec r`: `r ∈ ρ(A) ∩ ρ(A_V)` and `ιWV (Q r v) = (r - A_V)⁻¹ B v`;
  `exists_QSpec` (all large real `r`), `Q_decay` (`eq:control-resolvent-decay`,
  `‖Q_r‖ = O(r^{-1/2})`), `L_exp` (the finite-time Laplace identity
  `L_t e^{-r(t - ·)} v = Q_r v - e^{-r t} S(t) Q_r v`).
* `sys.BXat a = (a - A_{X,-1}) ι_W Q_a` and `sys.BX : U →L[ℝ] X₋₁` (`B_X`); `BX_eq`
  (independent of `a`), `toExtrap_L` (same control convolution in `X₋₁`).
* `sys.Bstar : X →ₗ.[ℝ] U`, `B† : D(A†) → U` (`B† η = B_X† (η, A† η)`), with
  `Bstar_domain : D(B†) = D(A†)`, the graph-norm bound `exists_norm_Bstar_le`, agreement with
  the `V'`-adjoint `inner_Bstar_of_dual`, and the duality formula
  `(L_t† η)(r) = B† S(t - r)† η` (`inner_L_eq_integral`, `adjoint_Lop_ae_eq`).
* `inner_mild_eq` (`eq:weak-mild-diff`): `⟪η, x̄ t⟫ = ⟪η, x̄ 0⟫ + ∫₀ᵗ (⟪A† η, x̄⟫ + ⟪B† η, ū⟫)`
  for `η ∈ D(A†)`.

## Proof notes

* `Q_r ∈ L(U, W)` follows the paper: the finite-time Laplace identity gives
  `(id - e^{-rT} S(T)) Q_r v = L_T u_r`, and for `r` so large that `‖e^{-rT} S(T)‖ ≤ 1/2` on
  `W` and on `V`, `id - e^{-rT} S(T)` is onto on `W` (Neumann series) and injective on `V`;
  `‖u_r‖_{L²} ≤ ‖v‖ / √r` gives the decay (`exists_Q_bound`).
* The control convolution is identified without Laplace transforms: commuting the resolvent
  with the `V`-valued convolution gives `R(a, A) L_t u = ∫₀ᵗ S(t - r) Q_a u(r) dr` in `X`
  (`resolvent_ιW_L`), hence `⟪η, L_t u⟫ = ∫₀ᵗ ⟪(a - A†) η, S(t - r) Q_a u(r)⟫ dr` for
  `η ∈ D(A†)` (`inner_ιW_L_eq_integral`), which is the pairing of both sides of `toExtrap_L`
  and of the duality formula with `(η, A† η)`.
* Agreement with the `V'`-adjoint: `B v = (a - A_V) Q_a v`, and `ζ (A_V x) = ⟪A† η, x⟫` for
  `x ∈ X` with `x ∈ D(A_V)` (limit of difference quotients, `dual_generator`).
* `eq:weak-mild-diff`: `z = ∫₀^· S(· - r) Q_a u(r) dr = R(a, A) L_· u` takes values in `D(A)`;
  Ball's theorem and density of `D(A†)` give `z t = ∫₀ᵗ (A z + Q_a u)`, which is paired with
  `(a - A†) η`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

/-! ### Semigroup facts used below -/

namespace C0Semigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (S : C0Semigroup ℝ E)

/-- `⟪A† η, x⟫ = ⟪η, A x⟫` for `η ∈ D(A†)`, `x ∈ D(A)`. -/
private theorem inner_generator_adjoint_apply (η : S.generator.adjoint.domain)
    (x : S.generator.domain) :
    ⟪S.generator.adjoint η, (x : E)⟫_ℝ = ⟪(η : E), S.generator x⟫_ℝ :=
  LinearPMap.adjoint_isFormalAdjoint S.dense_generator_domain η x

/-- The resolvent commutes with the semigroup. -/
private theorem resolvent_real_apply_comm {μ : ℝ} (hμ : μ ∈ resolventSet S.generator) (s : ℝ)
    (y : E) : resolvent S.generator μ (S.real s y) = S.real s (resolvent S.generator μ y) := by
  show resolvent S.generator μ (S s.toNNReal y) = S s.toNNReal (resolvent S.generator μ y)
  set x := resolvent S.generator μ y
  have hx : x ∈ S.generator.domain := resolvent_mem_domain hμ y
  have key := resolvent_sub hμ ⟨S s.toNNReal x, S.mem_generator_domain_apply hx s.toNNReal⟩
  simp only at key
  rw [S.generator_apply_apply hx s.toNNReal] at key
  have h2 : μ • S s.toNNReal x - S s.toNNReal (S.generator ⟨x, hx⟩) = S s.toNNReal y := by
    rw [← sub_resolvent hμ y, map_sub, map_smul]
  rw [h2] at key
  exact key

/-- `(a - A₋₁) R(a, A) y = y` in `E₋₁`. -/
private theorem smul_toExtrap_sub_genExtrap_resolvent {a : ℝ}
    (ha : a ∈ resolventSet S.generator) (y : E) :
    a • S.toExtrap (resolvent S.generator a y) - S.genExtrap (resolvent S.generator a y) =
      S.toExtrap y := by
  refine S.extrap_ext fun η => ?_
  have hd := resolvent_mem_domain ha y
  rw [← map_smul, inner_sub_left, S.inner_toExtrap_graphVec,
    S.inner_genExtrap_graphVec, S.inner_toExtrap_graphVec, real_inner_smul_left,
    real_inner_comm (S.generator.adjoint η) (resolvent S.generator a y),
    S.inner_generator_adjoint_apply η ⟨_, hd⟩]
  conv_rhs => rw [← sub_resolvent ha y]
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm (η : E)]
  congr 1
  exact real_inner_comm _ _

/-- The extended semigroup on `E₋₁` is dual to the adjoint semigroup on `D(A†)`:
`⟪S₋₁(s) φ, (η, A† η)⟫ = ⟪φ, (S(s)† η, A† S(s)† η)⟫`. -/
private theorem inner_extrapSemigroup_real_graphVec_adjoint (s : ℝ) (φ : S.Extrap)
    (η : S.generator.adjoint.domain) :
    ⟪S.extrapSemigroup.real s φ, S.graphVec η⟫_ℝ =
      ⟪φ, S.graphVec ⟨S.adjoint.real s η, S.adjoint_real_mem_adjoint_domain η.2 s⟩⟫_ℝ := by
  have h := S.denseRange_toExtrap.equalizer
    (g := fun φ => ⟪S.extrapSemigroup.real s φ, S.graphVec η⟫_ℝ)
    (h := fun φ => ⟪φ, S.graphVec ⟨S.adjoint.real s η, S.adjoint_real_mem_adjoint_domain η.2 s⟩⟫_ℝ)
    (by fun_prop) (by fun_prop) (funext fun x => ?_)
  · exact congrFun h φ
  simp only [Function.comp_apply]
  rw [← S.consistent_extrapSemigroup.real s x, S.inner_toExtrap_graphVec,
    S.inner_toExtrap_graphVec]
  change _ = ⟪x, S.adjoint.real s η⟫_ℝ
  rw [real_inner_comm _ x, S.inner_adjoint_real_apply, real_inner_comm]

end C0Semigroup

namespace System

variable {U W X V Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

variable (sys : System U W X V Y)

/-! ### `Q_r = (r - A_V)⁻¹ B ∈ L(U, W)` -/

open scoped Classical in
/-- `Q_r = (r - A_V)⁻¹ B` as an operator into `W` (`app:control-realization`); junk `0` if
`(r - A_V)⁻¹ B` is not a bounded operator into `W`. -/
def Q (r : ℝ) : U →L[ℝ] W :=
  if h : ∃ Q : U →L[ℝ] W, ∀ v, sys.ιWV (Q v) = resolvent sys.AV r (sys.B v) then h.choose else 0

/-- `r` is admissible for the construction of `B_X`: `r ∈ ρ(A) ∩ ρ(A_V)` and `Q_r` represents
`(r - A_V)⁻¹ B` in `W`. -/
def QSpec (r : ℝ) : Prop :=
  r ∈ resolventSet sys.A ∧ r ∈ resolventSet sys.AV ∧
    ∀ v : U, sys.ιWV (sys.Q r v) = resolvent sys.AV r (sys.B v)

variable {sys}

theorem ιWV_Q_of_exists {r : ℝ}
    (h : ∃ Q : U →L[ℝ] W, ∀ v, sys.ιWV (Q v) = resolvent sys.AV r (sys.B v)) (v : U) :
    sys.ιWV (sys.Q r v) = resolvent sys.AV r (sys.B v) := by
  rw [Q, dite_eq_left h]; exact h.choose_spec v

/-- `Q_r` is the only representation of `(r - A_V)⁻¹ B` in `L(U, W)`. -/
theorem Q_eq_of_forall {r : ℝ} {Q : U →L[ℝ] W}
    (hQ : ∀ v, sys.ιWV (Q v) = resolvent sys.AV r (sys.B v)) : sys.Q r = Q :=
  ContinuousLinearMap.ext fun v =>
    sys.ιWV_injective ((ιWV_Q_of_exists ⟨Q, hQ⟩ v).trans (hQ v).symm)

/-- The `V`-valued control convolution of the exponential input `s ↦ e^{-r(t - s)} v` is the
finite-time Laplace integral `∫₀ᵗ e^{-s r} S_V(s) B v ds`. -/
theorem convV_exp_smul {r t : ℝ} (ht : 0 ≤ t) (v : U) :
    sys.convV t (fun s => Real.exp (-(r * (t - s))) • v) =
      ∫ s in (0 : ℝ)..t, Real.exp (-(s * r)) • sys.SV.real s (sys.B v) := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
    (fun s => Real.exp (-(s * r)) • sys.SV.real s (sys.B v)) t
  rw [sub_self, sub_zero] at h
  rw [convV, ← intervalIntegral.integral_of_le ht, ← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [map_smul, mul_comm r]

/-- The exponential input `s ↦ e^{-r(T - s)} v` (`r ≥ 0`) is square integrable on `(0, T]`. -/
theorem memLp_exp_smul {r : ℝ} (T : ℝ) (hr : 0 ≤ r) (v : U) :
    MemLp (fun s => Real.exp (-(r * (T - s))) • v) 2 (μI T) := by
  refine MemLp.of_bound (by fun_prop) ‖v‖ ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
  have : 0 ≤ T - s := by linarith [hs.2]
  nlinarith

private theorem integral_exp_sq_le {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T) :
    ∫ s in Ioc 0 T, Real.exp (-(r * (T - s))) ^ 2 ≤ 1 / (2 * r) := by
  rw [← intervalIntegral.integral_of_le hT]
  have hderiv : ∀ s ∈ uIcc 0 T, HasDerivAt (fun s => Real.exp (2 * r * (s - T)) / (2 * r))
      (Real.exp (-(r * (T - s))) ^ 2) s := by
    intro s _
    have h1 : HasDerivAt (fun s => 2 * r * (s - T)) (2 * r) s := by
      simpa using ((hasDerivAt_id s).sub_const T).const_mul (2 * r)
    convert (h1.exp).div_const (2 * r) using 1
    rw [sq, ← Real.exp_add]
    field_simp
    ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have : 0 < Real.exp (2 * r * (0 - T)) := Real.exp_pos _
  rw [div_sub_div_same]
  gcongr
  linarith

/-- `‖s ↦ e^{-r(T - s)} v‖_{L²(0, T; U)} ≤ ‖v‖ / √r` (`eq:control-resolvent-decay`). -/
theorem norm_toLp_exp_smul_le {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T) (v : U) :
    ‖(memLp_exp_smul T hr.le v).toLp _‖ ≤ ‖v‖ / Real.sqrt r := by
  have hmem := memLp_exp_smul T hr.le v
  have h2 : ‖hmem.toLp _‖ ^ 2 = ∫ s in Ioc 0 T, Real.exp (-(r * (T - s))) ^ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with s hs
    rw [hs, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [integral_mul_const] at h2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [h2, div_pow, Real.sq_sqrt hr.le]
  calc (∫ s in Ioc 0 T, Real.exp (-(r * (T - s))) ^ 2) * ‖v‖ ^ 2 ≤ 1 / (2 * r) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (integral_exp_sq_le hr hT) (by positivity)
    _ ≤ ‖v‖ ^ 2 / r := by
        rw [one_div, ← div_eq_inv_mul]
        exact div_le_div_of_nonneg_left (by positivity) hr (by linarith)

/-- **`app:control-realization`, first step**: for all large real `r`, `r ∈ ρ(A) ∩ ρ(A_V)` and
`(r - A_V)⁻¹ B` is represented by some `Q ∈ L(U, W)` with `‖Q‖ ≤ K / √r`
(`eq:control-resolvent-decay`).  The finite-time Laplace identity gives
`(id - e^{-rT} S(T)) (r - A_V)⁻¹ B v = L_T u_r`, `u_r(s) = e^{-r(T - s)} v`, and
`id - e^{-rT} S(T)` is invertible on `W` and on `V` once `‖e^{-rT} S(T)‖ ≤ 1/2`. -/
theorem exists_Q_bound {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ r ≥ r₀, r ∈ resolventSet sys.A ∧ r ∈ resolventSet sys.AV ∧
      ∃ Q : U →L[ℝ] W, (∀ v, sys.ιWV (Q v) = resolvent sys.AV r (sys.B v)) ∧
        ‖Q‖ ≤ K / Real.sqrt r := by
  obtain ⟨b, hb⟩ := hH1
  obtain ⟨MX, ωX, -, hX⟩ := sys.SX.exists_norm_le_exp
  obtain ⟨MV, ωV, -, hV⟩ := sys.SV.exists_norm_le_exp
  set cW := ‖sys.SW.real T‖
  set cV := ‖sys.SV.real T‖
  set b' := max b 0
  refine ⟨2 * b', max (max 1 (max (ωX + 1) (ωV + 1))) (max (2 * cW / T) (2 * cV / T)),
    lt_max_of_lt_left (lt_max_of_lt_left one_pos), fun r hr => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hr
  obtain ⟨⟨hr1, hrX, hrV⟩, hrW', hrV'⟩ := hr
  have hr0 : 0 < r := by linarith
  have hAX : r ∈ resolventSet sys.A := sys.SX.mem_resolventSet hX (μ := r) (by simp; linarith)
  have hAV : r ∈ resolventSet sys.AV := sys.SV.mem_resolventSet hV (μ := r) (by simp; linarith)
  refine ⟨hAX, hAV, ?_⟩
  -- the contraction `k S(T)`, `k = e^{-rT}`
  set k := Real.exp (-(r * T))
  have hk0 : 0 < k := Real.exp_pos _
  have hkrT : k * (r * T) ≤ 1 := by
    have h := Real.add_one_le_exp (r * T)
    have : k * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_pos hr0 hT]
  have hsmall : ∀ c : ℝ, 0 ≤ c → 2 * c / T ≤ r → k * c ≤ 1 / 2 := by
    intro c hc hcr
    rw [div_le_iff₀ hT] at hcr
    nlinarith
  have hKW : ‖k • sys.SW.real T‖ ≤ 1 / 2 :=
    (norm_smul_le k (sys.SW.real T)).trans (by
      rw [Real.norm_of_nonneg hk0.le]; exact hsmall _ (norm_nonneg _) hrW')
  have hKV : ‖k • sys.SV.real T‖ ≤ 1 / 2 :=
    (norm_smul_le k (sys.SV.real T)).trans (by
      rw [Real.norm_of_nonneg hk0.le]; exact hsmall _ (norm_nonneg _) hrV')
  -- pointwise representation with the bound
  have hpt : ∀ v : U, ∃ w : W, sys.ιWV w = resolvent sys.AV r (sys.B v) ∧
      ‖w‖ ≤ 2 * b' / Real.sqrt r * ‖v‖ := by
    intro v
    set y := resolvent sys.AV r (sys.B v)
    have hmem := memLp_exp_smul T hr0.le v
    obtain ⟨w₀, hw₀, hw₀b⟩ := hb (hmem.toLp _)
    have hconv : sys.ιWV w₀ = y - k • sys.SV.real T y := by
      have hL := sys.SV.integral_exp_smul_eq_real (𝕜 := ℝ) (μ := r) hAV hT.le (sys.B v)
      rw [hw₀, ← convV, convV_congr_ae hmem.coeFn_toLp, convV_exp_smul hT.le, hL, mul_comm T r]
      rfl
    -- `1 - k S_W(T)` is onto on `W`
    obtain ⟨w, hw⟩ : ∃ w : W, w - k • sys.SW.real T w = w₀ := by
      obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (hKW.trans_lt (by norm_num))
      refine ⟨(↑u⁻¹ : W →L[ℝ] W) w₀, ?_⟩
      have h1 : ((↑u : W →L[ℝ] W) * ↑u⁻¹) w₀ = w₀ := by rw [u.mul_inv]; rfl
      rw [hu] at h1
      simpa using h1
    -- `1 - k S_V(T)` is injective on `V`
    have hwy : sys.ιWV w = y := by
      have h1 : sys.ιWV w - k • sys.SV.real T (sys.ιWV w) = y - k • sys.SV.real T y := by
        rw [← hconv, ← hw, map_sub, map_smul, ιWV_SW]
      have h2 : sys.ιWV w - y = (k • sys.SV.real T) (sys.ιWV w - y) := by
        rw [FunLike.coe_smul, Pi.smul_apply, map_sub, smul_sub]
        calc sys.ιWV w - y = (sys.ιWV w - k • sys.SV.real T (sys.ιWV w)) -
              (y - k • sys.SV.real T y) +
              (k • sys.SV.real T (sys.ιWV w) - k • sys.SV.real T y) := by abel
          _ = k • sys.SV.real T (sys.ιWV w) - k • sys.SV.real T y := by
              rw [h1, sub_self, zero_add]
      have h3 : ‖sys.ιWV w - y‖ ≤ 1 / 2 * ‖sys.ιWV w - y‖ := by
        conv_lhs => rw [h2]
        exact ((k • sys.SV.real T).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hKV (norm_nonneg _))
      have : ‖sys.ιWV w - y‖ = 0 := by linarith [norm_nonneg (sys.ιWV w - y)]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    refine ⟨w, hwy, ?_⟩
    have hww : ‖w‖ ≤ 2 * ‖w₀‖ := by
      have h1 : w = w₀ + (k • sys.SW.real T) w := by
        rw [← hw, FunLike.coe_smul, Pi.smul_apply]; abel
      have h2 : ‖w‖ ≤ ‖w₀‖ + 1 / 2 * ‖w‖ := by
        conv_lhs => rw [h1]
        exact (norm_add_le _ _).trans (add_le_add_right (((k • sys.SW.real T).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hKW (norm_nonneg _))) _)
      linarith
    have hu := norm_toLp_exp_smul_le (T := T) hr0 hT.le v
    calc ‖w‖ ≤ 2 * ‖w₀‖ := hww
      _ ≤ 2 * (b' * ‖hmem.toLp _‖) := by
          gcongr
          exact hw₀b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      _ ≤ 2 * (b' * (‖v‖ / Real.sqrt r)) := by gcongr
      _ = 2 * b' / Real.sqrt r * ‖v‖ := by ring
  -- assemble the operator
  choose q hq hqb using hpt
  have hadd : ∀ v₁ v₂, q (v₁ + v₂) = q v₁ + q v₂ := fun v₁ v₂ =>
    sys.ιWV_injective (by rw [hq, map_add, map_add, map_add, hq, hq])
  have hsmul : ∀ (c : ℝ) v, q (c • v) = c • q v := fun c v =>
    sys.ιWV_injective (by rw [hq, map_smul, map_smul, map_smul, hq])
  let Q : U →L[ℝ] W := LinearMap.mkContinuous ⟨⟨q, hadd⟩, hsmul⟩ (2 * b' / Real.sqrt r) hqb
  refine ⟨Q, hq, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Under `hyp:H1`, every large real `r` is admissible (`app:control-realization`). -/
theorem exists_QSpec {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) : ∃ r₀ : ℝ, ∀ r ≥ r₀, sys.QSpec r := by
  obtain ⟨K, r₀, -, h⟩ := exists_Q_bound hH1 hT
  refine ⟨r₀, fun r hr => ?_⟩
  obtain ⟨hA, hAV, Q, hQ, -⟩ := h r hr
  exact ⟨hA, hAV, ιWV_Q_of_exists ⟨Q, hQ⟩⟩

/-- **`eq:control-resolvent-decay`**: `‖Q_r‖_{L(U, W)} = O(r^{-1/2})` as `r → ∞`. -/
theorem Q_decay {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) :
    ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ r ≥ r₀, ‖sys.Q r‖ ≤ K / Real.sqrt r := by
  obtain ⟨K, r₀, hr₀, h⟩ := exists_Q_bound hH1 hT
  refine ⟨K, r₀, hr₀, fun r hr => ?_⟩
  obtain ⟨-, -, Q, hQ, hQb⟩ := h r hr
  rw [Q_eq_of_forall hQ]; exact hQb

set_option linter.unusedVariables false in
/-- The **finite-time Laplace identity** (`app:control-realization`):
`L_t u_r = Q_r v - e^{-r t} S(t) Q_r v` for `u_r(s) = e^{-r (t - s)} v`, in `W`. -/
theorem L_exp {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {r : ℝ} (hr : sys.QSpec r) {t : ℝ}
    (ht : 0 ≤ t) (v : U) :
    sys.L t (fun s => Real.exp (-(r * (t - s))) • v) =
      sys.Q r v - Real.exp (-(r * t)) • sys.SW.real t (sys.Q r v) := by
  refine L_eq_of_ιWV ?_
  rw [map_sub, map_smul, ιWV_SW, hr.2.2, convV_exp_smul ht,
    sys.SV.integral_exp_smul_eq_real (𝕜 := ℝ) hr.2.1 ht, mul_comm t r]
  rfl

/-! ### `B_X ∈ L(U, X₋₁)` -/

variable (sys)

/-- `(a - A_{X,-1}) ι_W Q_a ∈ L(U, X₋₁)`. -/
def BXat (a : ℝ) : U →L[ℝ] sys.SX.Extrap :=
  (a • sys.SX.toExtrap - sys.SX.genExtrap).comp (sys.ιW.comp (sys.Q a))

open scoped Classical in
/-- The **compatible control operator** `B_X = (a - A_{X,-1}) Q_a ∈ L(U, X₋₁)` for an
admissible `a` (independent of `a` by `BX_eq`; junk `0` if there is none). -/
def BX : U →L[ℝ] sys.SX.Extrap := if h : ∃ a, sys.QSpec a then sys.BXat h.choose else 0

variable {sys}

theorem BXat_apply (a : ℝ) (v : U) :
    sys.BXat a v = a • sys.SX.toExtrap (sys.ιW (sys.Q a v)) - sys.SX.genExtrap (sys.ιW (sys.Q a v)) :=
  rfl

/-- The resolvent identity for `Q`: `Q_a - Q_b = (b - a) R(a, A) Q_b` in `X`. -/
theorem ιW_Q_sub_ιW_Q {a b : ℝ} (ha : sys.QSpec a) (hb : sys.QSpec b) (v : U) :
    sys.ιW (sys.Q a v) - sys.ιW (sys.Q b v) =
      (b - a) • resolvent sys.A a (sys.ιW (sys.Q b v)) := by
  apply sys.ιV_injective
  have h := congrArg (fun L : V →L[ℝ] V => L (sys.B v)) (resolvent_sub_resolvent ha.2.1 hb.2.1)
  simp only [sub_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at h
  rw [map_sub, map_smul, sys.consistentV.resolvent sys.SV ha.1 ha.2.1, ← ιWV_apply, ← ιWV_apply,
    ha.2.2, hb.2.2]
  exact h

/-- `(a - A_{X,-1}) Q_a` does not depend on the admissible `a` (resolvent identity). -/
theorem BXat_eq_BXat {a b : ℝ} (ha : sys.QSpec a) (hb : sys.QSpec b) : sys.BXat a = sys.BXat b := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [BXat_apply, BXat_apply]
  have h1 := ιW_Q_sub_ιW_Q ha hb v
  rw [sub_eq_iff_eq_add] at h1
  have h2 := sys.SX.smul_toExtrap_sub_genExtrap_resolvent ha.1 (sys.ιW (sys.Q b v))
  rw [h1, map_add, map_add, map_smul, map_smul]
  set z := resolvent sys.A a (sys.ιW (sys.Q b v))
  set qb := sys.ιW (sys.Q b v)
  calc a • ((b - a) • sys.SX.toExtrap z + sys.SX.toExtrap qb) -
        ((b - a) • sys.SX.genExtrap z + sys.SX.genExtrap qb)
      = (b - a) • (a • sys.SX.toExtrap z - sys.SX.genExtrap z) +
          (a • sys.SX.toExtrap qb - sys.SX.genExtrap qb) := by module
    _ = b • sys.SX.toExtrap qb - sys.SX.genExtrap qb := by rw [h2]; module

/-- `B_X = (a - A_{X,-1}) Q_a` for every admissible `a`; equivalently
`(a - A_{X,-1})⁻¹ B_X = Q_a`. -/
theorem BX_eq {a : ℝ} (ha : sys.QSpec a) : sys.BX = sys.BXat a := by
  have h : ∃ a, sys.QSpec a := ⟨a, ha⟩
  rw [BX, dite_eq_left h]
  exact BXat_eq_BXat h.choose_spec ha

/-- The pairing of `(a - A_{X,-1}) Q_a v ∈ X₋₁` with `(ξ, A† ξ)`, `ξ ∈ D(A†)`:
`⟪Q_a v, (a - A†) ξ⟫`. -/
theorem inner_BXat_graphVec (a : ℝ) (ξ : sys.A.adjoint.domain) (v : U) :
    ⟪sys.BXat a v, sys.SX.graphVec ξ⟫_ℝ =
      ⟪sys.ιW (sys.Q a v), a • (ξ : X) - sys.A.adjoint ξ⟫_ℝ := by
  rw [BXat_apply, ← map_smul, inner_sub_left, sys.SX.inner_toExtrap_graphVec,
    sys.SX.inner_genExtrap_graphVec, inner_sub_right, real_inner_smul_left, real_inner_smul_right]

/-- `⟪B_X v, (ξ, A† ξ)⟫ = ⟪Q_a v, (a - A†) ξ⟫` for every admissible `a`. -/
theorem inner_BX_graphVec {a : ℝ} (ha : sys.QSpec a) (ξ : sys.A.adjoint.domain) (v : U) :
    ⟪sys.BX v, sys.SX.graphVec ξ⟫_ℝ = ⟪sys.ιW (sys.Q a v), a • (ξ : X) - sys.A.adjoint ξ⟫_ℝ := by
  rw [BX_eq ha, inner_BXat_graphVec]

/-- `⟪η, y⟫ = ⟪(a - A†) η, R(a, A) y⟫` for `η ∈ D(A†)` and `a ∈ ρ(A)`. -/
theorem inner_eq_inner_resolvent {a : ℝ} (ha : a ∈ resolventSet sys.A) {η : X}
    (hη : η ∈ sys.A.adjoint.domain) (y : X) :
    ⟪η, y⟫_ℝ = ⟪a • η - sys.A.adjoint ⟨η, hη⟩, resolvent sys.A a y⟫_ℝ := by
  have hd := resolvent_mem_domain ha y
  conv_lhs => rw [← sub_resolvent ha y]
  rw [inner_sub_right, inner_sub_left, real_inner_smul_right, real_inner_smul_left,
    sys.SX.inner_generator_adjoint_apply ⟨η, hη⟩ ⟨_, hd⟩]

/-- `A R(a, A) y = a R(a, A) y - y`. -/
theorem generator_resolvent {a : ℝ} (ha : a ∈ resolventSet sys.A) (y : X) :
    sys.A ⟨resolvent sys.A a y, resolvent_mem_domain ha y⟩ = a • resolvent sys.A a y - y :=
  eq_sub_of_add_eq (sub_eq_iff_eq_add'.1 (sub_resolvent ha y)).symm

/-- **The control convolution through the resolvent**: for admissible `a`,
`R(a, A) L_t u = ∫₀ᵗ S(t - r) Q_a u(r) dr` in `X` (checked in `V`, where `R(a, A_V)` commutes
with the convolution and `R(a, A_V) B = Q_a`). -/
theorem resolvent_ιW_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {a : ℝ} (ha : sys.QSpec a)
    {t : ℝ} {u : ℝ → U} (hu : MemLp u 2 (μI t)) :
    resolvent sys.A a (sys.ιW (sys.L t u)) =
      ∫ r in Ioc 0 t, sys.SX.real (t - r) (sys.ιW (sys.Q a (u r))) := by
  apply sys.ιV_injective
  have hint : IntegrableOn (fun r => sys.SX.real (t - r) (sys.ιW (sys.Q a (u r)))) (Ioc 0 t) :=
    sys.SX.integrableOn_conv (f := fun r => sys.ιW (sys.Q a (u r)))
      ((sys.ιW.comp (sys.Q a)).integrable_comp (hu.integrable one_le_two))
  rw [sys.consistentV.resolvent sys.SV ha.1 ha.2.1, ← ιWV_apply, ιWV_L hH1 hT hu, convV,
    ← sys.ιV.integral_comp_comm hint,
    ← (resolvent sys.AV a).integral_comp_comm (integrableOn_convV hu)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [sys.SV.resolvent_real_apply_comm ha.2.1, ← ha.2.2 (u r), ιWV_apply, ← ιV_SX]

/-- `A† S(s)† η = S(s)† A† η` for `η ∈ D(A†)`, at a real time. -/
theorem generator_adjoint_adjoint_real {η : X} (hη : η ∈ sys.A.adjoint.domain) (s : ℝ) :
    sys.A.adjoint ⟨sys.SX.adjoint.real s η, sys.SX.adjoint_real_mem_adjoint_domain hη s⟩ =
      sys.SX.adjoint.real s (sys.A.adjoint ⟨η, hη⟩) :=
  sys.SX.generator_adjoint_apply_adjoint hη s.toNNReal

/-- `⟪B_X v, (S(s)† η, A† S(s)† η)⟫ = ⟪(a - A†) η, S(s) Q_a v⟫`. -/
theorem inner_BX_graphVec_adjoint {a : ℝ} (ha : sys.QSpec a) {η : X}
    (hη : η ∈ sys.A.adjoint.domain) (s : ℝ) (v : U) :
    ⟪sys.BX v, sys.SX.graphVec
        ⟨sys.SX.adjoint.real s η, sys.SX.adjoint_real_mem_adjoint_domain hη s⟩⟫_ℝ =
      ⟪a • η - sys.A.adjoint ⟨η, hη⟩, sys.SX.real s (sys.ιW (sys.Q a v))⟫_ℝ := by
  rw [inner_BX_graphVec ha]
  simp only
  rw [generator_adjoint_adjoint_real hη s, ← map_smul, ← map_sub, real_inner_comm,
    sys.SX.inner_adjoint_real_apply]

/-- **Duality for `B_X`**: for `η ∈ D(A†)`,
`⟪η, L_t u⟫ = ∫₀ᵗ ⟪B_X u(r), (S(t - r)† η, A† S(t - r)† η)⟫ dr`. -/
theorem inner_ιW_L_eq_integral {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) {η : X} (hη : η ∈ sys.A.adjoint.domain) :
    ⟪η, sys.ιW (sys.L t u)⟫_ℝ =
      ∫ r in Ioc 0 t, ⟪sys.BX (u r), sys.SX.graphVec ⟨sys.SX.adjoint.real (t - r) η,
        sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩⟫_ℝ := by
  obtain ⟨a, ha⟩ := exists_QSpec hH1 hT
  have ha := ha a le_rfl
  have hint : IntegrableOn (fun r => sys.SX.real (t - r) (sys.ιW (sys.Q a (u r)))) (Ioc 0 t) :=
    sys.SX.integrableOn_conv (f := fun r => sys.ιW (sys.Q a (u r)))
      ((sys.ιW.comp (sys.Q a)).integrable_comp (hu.integrable one_le_two))
  rw [inner_eq_inner_resolvent ha.1 hη, resolvent_ιW_L hH1 hT ha hu, ← integral_inner hint]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [inner_BX_graphVec_adjoint ha hη]

/-- `B_X` has the same control convolution as `B`: `L_t u = ∫₀ᵗ S_{-1}(t - r) B_X u(r) dr` in
`X₋₁`. -/
theorem toExtrap_L {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) :
    sys.SX.toExtrap (sys.ιW (sys.L t u)) =
      ∫ r in Ioc 0 t, sys.SX.extrapSemigroup.real (t - r) (sys.BX (u r)) := by
  refine sys.SX.extrap_ext fun η => ?_
  have hint : IntegrableOn (fun r => sys.SX.extrapSemigroup.real (t - r) (sys.BX (u r)))
      (Ioc 0 t) :=
    sys.SX.extrapSemigroup.integrableOn_conv (f := fun r => sys.BX (u r))
      (sys.BX.integrable_comp (hu.integrable one_le_two))
  rw [sys.SX.inner_toExtrap_graphVec, real_inner_comm (η : X),
    inner_ιW_L_eq_integral hH1 hT hu η.2, real_inner_comm (sys.SX.graphVec η),
    ← integral_inner hint]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [real_inner_comm _ (sys.SX.graphVec η), sys.SX.inner_extrapSemigroup_real_graphVec_adjoint]

/-! ### `B† : D(A†) → U` -/

variable (sys)

/-- **`B† : D(A†) → U`**, the adjoint of `B_X` read through the dual model:
`B† η = B_X† (η, A† η)`.  Bounded for the graph norm (`exists_norm_Bstar_le`). -/
def Bstar : X →ₗ.[ℝ] U where
  domain := sys.A.adjoint.domain
  toFun := (ContinuousLinearMap.adjoint sys.BX).toLinearMap ∘ₗ sys.SX.graphVec

variable {sys}

theorem Bstar_domain : sys.Bstar.domain = sys.A.adjoint.domain := rfl

theorem Bstar_apply (η : sys.A.adjoint.domain) :
    sys.Bstar η = ContinuousLinearMap.adjoint sys.BX (sys.SX.graphVec η) := rfl

/-- `⟪B† η, v⟫ = ⟪B_X v, η⟫` (the `X₋₁`–`D(A†)` pairing). -/
theorem inner_Bstar (η : sys.A.adjoint.domain) (v : U) :
    ⟪sys.Bstar η, v⟫_ℝ = ⟪sys.BX v, sys.SX.graphVec η⟫_ℝ := by
  rw [Bstar_apply, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

/-- `B†` is bounded for the graph norm of `D(A†)`. -/
theorem exists_norm_Bstar_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ η : sys.A.adjoint.domain,
      ‖sys.Bstar η‖ ≤ c * (‖(η : X)‖ + ‖sys.A.adjoint η‖) := by
  refine ⟨‖ContinuousLinearMap.adjoint sys.BX‖, ContinuousLinearMap.opNorm_nonneg _,
    fun η => ?_⟩
  rw [Bstar_apply]
  refine (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [C0Semigroup.norm_graphVec_sq]
  nlinarith [norm_nonneg (η : X), norm_nonneg (sys.A.adjoint η)]

/-- `⟪B† η, v⟫ = ⟪Q_a v, (a - A†) η⟫` for every admissible `a`. -/
theorem inner_Bstar_eq {a : ℝ} (ha : sys.QSpec a) (η : sys.A.adjoint.domain) (v : U) :
    ⟪sys.Bstar η, v⟫_ℝ = ⟪sys.ιW (sys.Q a v), a • (η : X) - sys.A.adjoint η⟫_ℝ := by
  rw [inner_Bstar, inner_BX_graphVec ha]

/-- If `ζ ∈ V'` extends `x ↦ ⟪η, x⟫` (`η ∈ D(A†)`), then `ζ (A_V x) = ⟪A† η, x⟫` for every
`x ∈ X` with `x ∈ D(A_V)`: both are limits of the difference quotients `⟪η, h⁻¹ (S(h) x - x)⟫`. -/
theorem dual_generator (η : sys.A.adjoint.domain) (ζ : V →L[ℝ] ℝ)
    (hζ : ∀ x : X, ζ (sys.ιV x) = ⟪(η : X), x⟫_ℝ) {x : X} {y : V} (hxy : sys.ιV x = y)
    (hd : y ∈ sys.AV.domain) : ζ (sys.AV ⟨y, hd⟩) = ⟪sys.A.adjoint η, x⟫_ℝ := by
  subst hxy
  have h1 := (ζ.continuous.tendsto _).comp (sys.SV.tendsto_generator ⟨sys.ιV x, hd⟩)
  have h2 := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1
    (hasDerivWithinAt_Ioi_iff_Ici.2 (sys.SX.hasDerivWithinAt_inner η.2 x (le_refl (0 : ℝ))))
  simp only [C0Semigroup.real_zero, one_apply_eq_self] at h2
  refine tendsto_nhds_unique h1 (h2.congr fun h => ?_)
  show slope _ 0 h = ζ (sys.SV.diffQuot (sys.ιV x) h)
  rw [← sys.consistentV.diffQuot sys.SV x h, hζ, C0Semigroup.diffQuot, slope_def_module,
    real_inner_smul_right, inner_sub_right, C0Semigroup.real_zero, one_apply_eq_self, sub_zero,
    smul_eq_mul]

/-- `B†` agrees with the adjoint of `B ∈ L(U, V)` on `D(A†) ∩ V'`: if `x ↦ ⟪η, x⟫` extends to
`ζ ∈ V'`, then `⟪B† η, v⟫ = ζ (B v)`. -/
theorem inner_Bstar_of_dual {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (η : sys.A.adjoint.domain)
    (ζ : V →L[ℝ] ℝ) (hζ : ∀ x : X, ζ (sys.ιV x) = ⟪(η : X), x⟫_ℝ) (v : U) :
    ⟪sys.Bstar η, v⟫_ℝ = ζ (sys.B v) := by
  obtain ⟨a, ha⟩ := exists_QSpec hH1 hT
  have ha := ha a le_rfl
  rw [inner_Bstar_eq ha]
  conv_rhs => rw [← sub_resolvent ha.2.1 (sys.B v)]
  rw [map_sub, map_smul, dual_generator η ζ hζ (ha.2.2 v), ← ha.2.2 v, ιWV_apply, hζ,
    inner_sub_right, real_inner_smul_right, real_inner_comm, real_inner_comm (sys.A.adjoint η)]
  rfl

/-- `⟪B† S(s)† η, v⟫ = ⟪B_X v, (S(s)† η, A† S(s)† η)⟫` (`inner_Bstar` at `S(s)† η`). -/
theorem inner_Bstar_adjoint_real (η : sys.A.adjoint.domain) (s : ℝ) (v : U) :
    ⟪sys.Bstar ⟨sys.SX.adjoint.real s η, sys.SX.adjoint_real_mem_adjoint_domain η.2 s⟩, v⟫_ℝ =
      ⟪sys.BX v, sys.SX.graphVec
        ⟨sys.SX.adjoint.real s η, sys.SX.adjoint_real_mem_adjoint_domain η.2 s⟩⟫_ℝ :=
  inner_Bstar _ v

/-- **Duality** `(L_t† η)(r) = B† S(t - r)† η` (weak form): for `η ∈ D(A†)`,
`⟪η, L_t u⟫ = ∫₀ᵗ ⟪B† S(t - r)† η, u(r)⟫ dr`. -/
theorem inner_L_eq_integral {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {t : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI t)) {η : X} (hη : η ∈ sys.A.adjoint.domain) :
    ⟪η, sys.ιW (sys.L t u)⟫_ℝ =
      ∫ r in Ioc 0 t, ⟪sys.Bstar ⟨sys.SX.adjoint.real (t - r) η,
        sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩, u r⟫_ℝ := by
  rw [inner_ιW_L_eq_integral hH1 hT hu hη]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  exact (inner_Bstar_adjoint_real ⟨η, hη⟩ (t - r) (u r)).symm

/-- **Duality** `(L_t† η)(r) = B† S(t - r)† η` in `L²(0, t; U)`, for `η ∈ D(A†)`. -/
theorem adjoint_Lop_ae_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) (t : ℝ) {η : X}
    (hη : η ∈ sys.A.adjoint.domain) :
    ⇑(ContinuousLinearMap.adjoint (sys.ιW.comp (sys.Lop t)) η) =ᵐ[μI t]
      fun r => sys.Bstar ⟨sys.SX.adjoint.real (t - r) η,
        sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩ := by
  set h : ℝ → U := fun r => sys.Bstar ⟨sys.SX.adjoint.real (t - r) η,
    sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩ with h_def
  -- `r ↦ (S(t - r)† η, A† S(t - r)† η)` is continuous into `X₋₁`
  have hgc : Continuous fun r : ℝ => sys.SX.graphVec ⟨sys.SX.adjoint.real (t - r) η,
      sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩ := by
    refine continuous_induced_rng.2 ?_
    have : (Subtype.val ∘ fun r : ℝ => sys.SX.graphVec ⟨sys.SX.adjoint.real (t - r) η,
        sys.SX.adjoint_real_mem_adjoint_domain hη (t - r)⟩) =
        fun r => WithLp.toLp 2 (sys.SX.adjoint.real (t - r) η,
          sys.SX.adjoint.real (t - r) (sys.A.adjoint ⟨η, hη⟩)) := by
      funext r
      simp only [Function.comp_apply, C0Semigroup.coe_graphVec]
      rw [← generator_adjoint_adjoint_real hη (t - r)]
    rw [this]
    have h1 := (sys.SX.adjoint.continuous_real_apply η).comp
      (continuous_const.sub continuous_id : Continuous fun r : ℝ => t - r)
    have h2 := (sys.SX.adjoint.continuous_real_apply (sys.A.adjoint ⟨η, hη⟩)).comp
      (continuous_const.sub continuous_id : Continuous fun r : ℝ => t - r)
    exact (WithLp.prod_continuous_toLp 2 X X).comp (h1.prodMk h2)
  have hcont : Continuous h := (ContinuousLinearMap.adjoint sys.BX).continuous.comp hgc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hmem : MemLp h 2 (μI t) := MemLp.of_bound hcont.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun r hr => hC r (Ioc_subset_Icc_self hr)))
  have key : ContinuousLinearMap.adjoint (sys.ιW.comp (sys.Lop t)) η = hmem.toLp h := by
    refine ext_inner_right ℝ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, Lop_apply hH1 hT,
      inner_L_eq_integral hH1 hT (Lp.memLp w) hη, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with r hr
    rw [hr]
  rw [key]
  exact hmem.coeFn_toLp

/-- **`eq:weak-mild-diff`**: for `η ∈ D(A†)` the state projection `t ↦ ⟪η, x̄ t⟫` of a mild
solution satisfies `⟪η, x̄ t⟫ = ⟪η, x̄ 0⟫ + ∫₀ᵗ (⟪A† η, x̄ s⟫ + ⟪B† η, ū s⟫) ds`, i.e. it is in
`H¹` with derivative `⟪A† η, x̄⟫ + ⟪B† η, ū⟫`. -/
theorem inner_mild_eq {T : ℝ} (hH1 : sys.H1 T) (hT : 0 < T) {τ : ℝ} {u : ℝ → U}
    (hu : MemLp u 2 (μI τ)) (x₀ : X) {η : X} (hη : η ∈ sys.A.adjoint.domain) :
    ∀ t ∈ Icc 0 τ, ⟪η, sys.mild x₀ u t⟫_ℝ = ⟪η, x₀⟫_ℝ +
      ∫ s in (0 : ℝ)..t, (⟪sys.A.adjoint ⟨η, hη⟩, sys.mild x₀ u s⟫_ℝ +
        ⟪sys.Bstar ⟨η, hη⟩, u s⟫_ℝ) := by
  intro t ht
  obtain ⟨a, ha⟩ := exists_QSpec hH1 hT
  have ha := ha a le_rfl
  obtain ⟨ζ, hζ⟩ : ∃ ζ : X, ζ = a • η - sys.A.adjoint ⟨η, hη⟩ := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ → X, f = fun r => sys.ιW (sys.Q a (u r)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ → X, y = fun s => sys.ιW (sys.L s u) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → X, g = fun s => a • resolvent sys.A a (y s) - y s + f s :=
    ⟨_, rfl⟩
  have hfi : IntegrableOn f (Ioc 0 τ) := by
    rw [hf]; exact (sys.ιW.comp (sys.Q a)).integrable_comp (hu.integrable one_le_two)
  have huτ : ∀ s ∈ Icc 0 τ, MemLp u 2 (μI s) := fun s hs =>
    hu.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hs.2) le_rfl)
  -- the mild solution `z = ∫₀^· S(· - r) f(r) dr` of `ż = A z + f` is `R(a, A) y`
  have hz : ∀ s ∈ Icc 0 τ, sys.SX.mildSol 0 f s = resolvent sys.A a (y s) := fun s hs => by
    rw [hy, resolvent_ιW_L hH1 hT ha (huτ s hs), hf]
    simp [C0Semigroup.mildSol]
  have hsub : uIcc 0 t ⊆ Icc 0 τ := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
  have hyc : ContinuousOn y (Icc 0 τ) := by
    rw [hy]; exact sys.ιW.continuous.comp_continuousOn (continuousOn_L hH1 hT hu)
  have hzc : ContinuousOn (fun s => resolvent sys.A a (y s)) (Icc 0 τ) :=
    (resolvent sys.A a).continuous.comp_continuousOn hyc
  have hfi' : IntegrableOn f (Ioc 0 t) := hfi.mono_set (Ioc_subset_Ioc_right ht.2)
  have hgi : IntegrableOn g (Ioc 0 t) := by
    rw [hg]
    refine IntegrableOn.add ?_ hfi'
    exact (((hzc.const_smul a).sub hyc).mono (Icc_subset_Icc_right ht.2)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  -- strong form `z t = ∫₀ᵗ (A z + f)`: Ball's theorem and density of `D(A†)`
  have hstrong : resolvent sys.A a (y t) = ∫ s in (0 : ℝ)..t, g s := by
    obtain ⟨d, hd⟩ : ∃ d : X, d = resolvent sys.A a (y t) - ∫ s in (0 : ℝ)..t, g s := ⟨_, rfl⟩
    have hsubd : (sys.A.adjoint.domain : Set X) ⊆ {ξ | ⟪ξ, d⟫_ℝ = 0} := by
      intro ξ hξ
      have hball := (sys.SX.isWeakSol_mildSol hfi 0).2.2 ξ hξ t ht
      rw [hz t ht, inner_zero_right, zero_add] at hball
      have hcongr : EqOn (fun s => ⟪sys.A.adjoint ⟨ξ, hξ⟩, sys.SX.mildSol 0 f s⟫_ℝ + ⟪ξ, f s⟫_ℝ)
          (fun s => ⟪ξ, g s⟫_ℝ) (uIcc 0 t) := by
        intro s hs
        simp only
        rw [hz s (hsub hs), sys.SX.inner_generator_adjoint_apply ⟨ξ, hξ⟩
          ⟨_, resolvent_mem_domain ha.1 (y s)⟩, generator_resolvent ha.1, hg,
          inner_add_right]
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_of_le ht.1,
        integral_inner hgi] at hball
      show ⟪ξ, d⟫_ℝ = 0
      rw [hd, inner_sub_right, hball, intervalIntegral.integral_of_le ht.1, sub_self]
    have hcl : IsClosed {ξ : X | ⟪ξ, d⟫_ℝ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hd0 : ⟪d, d⟫_ℝ = 0 := hcl.closure_subset_iff.2 hsubd (sys.SX.dense_adjoint_domain d)
    rw [← sub_eq_zero, ← hd]
    exact inner_self_eq_zero.1 hd0
  -- pointwise: `⟪(a - A†) η, A z + f⟫ = ⟪A† η, y⟫ + ⟪B† η, u⟫`
  have hpt : ∀ s, ⟪ζ, g s⟫_ℝ =
      ⟪sys.A.adjoint ⟨η, hη⟩, y s⟫_ℝ + ⟪sys.Bstar ⟨η, hη⟩, u s⟫_ℝ := by
    intro s
    have h1 := inner_eq_inner_resolvent ha.1 hη (y s)
    rw [← hζ] at h1
    have h2 : ⟪sys.Bstar ⟨η, hη⟩, u s⟫_ℝ = ⟪f s, ζ⟫_ℝ := by
      rw [hf, hζ]; exact inner_Bstar_eq ha ⟨η, hη⟩ (u s)
    rw [h2, hg]
    simp only
    rw [inner_add_right, inner_sub_right, real_inner_smul_right, ← h1, hζ, inner_sub_left,
      real_inner_smul_left, real_inner_comm (f s)]
    ring
  -- the free response
  have hSc : Continuous fun s => ⟪sys.A.adjoint ⟨η, hη⟩, sys.SX.real s x₀⟫_ℝ :=
    continuous_const.inner (sys.SX.continuous_real_apply x₀)
  have hfree : ⟪η, sys.SX.real t x₀⟫_ℝ =
      ⟪η, x₀⟫_ℝ + ∫ s in (0 : ℝ)..t, ⟪sys.A.adjoint ⟨η, hη⟩, sys.SX.real s x₀⟫_ℝ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
      ((continuous_const.inner (sys.SX.continuous_real_apply x₀)).continuousOn)
      (fun s hs => (sys.SX.hasDerivAt_inner hη x₀ hs.1).hasDerivWithinAt)
      (hSc.intervalIntegrable 0 t)]
    simp
  -- assemble
  have hEq : EqOn (fun s => ⟪sys.A.adjoint ⟨η, hη⟩, sys.mild x₀ u s⟫_ℝ +
        ⟪sys.Bstar ⟨η, hη⟩, u s⟫_ℝ)
      (fun s => ⟪sys.A.adjoint ⟨η, hη⟩, sys.SX.real s x₀⟫_ℝ + ⟪ζ, g s⟫_ℝ) (uIcc 0 t) := by
    intro s _
    simp only
    rw [hpt, mild, inner_add_right, hy, add_assoc]
  have hgi' : IntervalIntegrable (fun s => ⟪ζ, g s⟫_ℝ) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 (hgi.const_inner ζ)
  have hforced : ⟪η, y t⟫_ℝ = ∫ s in (0 : ℝ)..t, ⟪ζ, g s⟫_ℝ := by
    rw [inner_eq_inner_resolvent ha.1 hη, ← hζ, hstrong, intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_of_le ht.1, integral_inner hgi]
  rw [intervalIntegral.integral_congr hEq,
    intervalIntegral.integral_add (hSc.intervalIntegrable 0 t) hgi', mild, inner_add_right, hfree,
    ← hforced, hy]
  ring

end System

end DataDrivenControl
