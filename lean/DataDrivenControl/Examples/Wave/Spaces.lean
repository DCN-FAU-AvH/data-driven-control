module

public import DataDrivenControl.Semigroup.Rotation
public import DataDrivenControl.Examples.Wave.Fourier

/-!
# The wave equation with Dirichlet control: spaces and system

Paper: `ex:intro-wave` (`introduction.tex`).  The paper's example is
`∂ₜₜw = c² ∂ξξ w` on `(0, 1)`, `w(t, 0) = u(t)`, `w(t, 1) = 0`, `y(t) = ∫₀¹ q(ξ) w(t, ξ) dξ`,
as a first-order system for `x = (w, ∂ₜw)` on `X = L²(0, 1) × H⁻¹(0, 1)`.

## Modal model

With the Dirichlet eigenfunctions `sₙ(ξ) = √2 sin(nπξ)` and `ωₙ = c n π` (paper's `n ≥ 1`), the
energy coordinates of `x = (w, v)` are `aₙ = ⟨w, sₙ⟩` and `bₙ = ⟨v, sₙ⟩ / ωₙ`, and
`∑ₙ (aₙ² + bₙ²) = ‖w‖²_{L²} + c⁻² ‖v‖²_{H⁻¹}`, a norm equivalent to that of `L² × H⁻¹`.
Integrating by parts twice with `w(0) = u`, `w(1) = 0` gives `⟨∂ξξw, sₙ⟩ = √2 nπ u - (nπ)² aₙ`,
hence the modal equations
`aₙ' = ωₙ bₙ`, `bₙ' = -ωₙ aₙ + c √2 u`, `y = ∑ₙ qₙ aₙ`, `qₙ = ⟨q, sₙ⟩`.

The formalisation takes `X = WithLp 2 (X₁ × X₂)` for real Hilbert spaces `X₁` (the displacement
space `L²(0, 1)`) and `X₂` (the velocity space `H⁻¹(0, 1)` with the norm `c⁻¹ ‖·‖_{H⁻¹}`) with
Hilbert bases `s` and `f` (the paper's `sₙ` and `ωₙ sₙ`), so that `aₙ = ⟪s n, x₁⟫` and
`bₙ = ⟪f n, x₂⟫`, and `q ∈ X₁`.  The theorems therefore concern a unitarily equivalent copy of
the PDE; the dictionary to functions on `(0, 1)` is in `Examples/Wave/PDE`.

**Indexing.**  Modes are numbered from `0`: Lean's mode `n` is the paper's mode `n + 1`, with
`ωₙ = freq c n = c (n + 1) π` (`Examples/Wave/Fourier`).

## Main declarations

* `ell2 = ℓ²(ℕ, ℝ)` with `stdBasis`, `mkL2`; **`V = Vsp = WithLp 2 (ℓ² × ℓ²)`**, the weighted `ℓ²`
  in the energy modes: `x ↦ (√vₙ aₙ, √vₙ bₙ)ₙ` with the weight
  `vₙ = (1 + ωₙ²)⁻¹ + qₙ²` (`vwt`, `sw = √vwt`) on both coordinates of mode `n`.  The term
  `(1 + ωₙ²)⁻¹` makes `B` bounded into `V`; the term `qₙ²` makes `hyp:H2` hold (with the
  extrapolation space `X₋₁` alone, weights `(1 + ωₙ²)⁻¹`, `hyp:H2` fails for some `q ∈ L²`).
* `ιV : X →L[ℝ] V` (`Rotation.blockDiag`), injective with dense range;
* `ctrlVec = B 1`, with energy coordinates `(0, c √2)` in every mode (`inner_fst_ctrlVec`,
  `inner_snd_ctrlVec`), `Bop`; `Cop x = ⟪q, x₁⟫`;
* **`waveSystem s f c q : System ℝ X X V ℝ`** with `W = X` (`ιW = id`), `S_W = S_X` the
  block-rotation group with the frequencies `ωₙ` (`Rotation.rotGroup`) and `S_V` the rotation
  group on `V`.  `W = X` is forced: the wave equation is exactly controllable for `T ≥ 2/c`, and
  `hyp:H1` maps `L_T` into `W` boundedly, so `W` must contain every state of `X`.
* the ties to the PDE that need no estimate: `waveSystem_SX`, `inner_fst_waveSystem_SX`,
  `inner_snd_waveSystem_SX` (the modal solution of the free equation),
  `hasSum_waveSystem_C` (`C x = ∑ₙ qₙ aₙ`), `norm_waveSystem_C_le` (`C` is bounded on `X`),
  `waveSystem_B_not_mem_range` (`B` is unbounded on `X`);
* **`waveSystem_compat`** (`hyp:compat`): `D(A_V)` has the weights
  `vₙ (1 + ωₙ²) ≥ 1`, so it embeds into `X = W` with constant `1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace lp

noncomputable section

set_option linter.unusedSectionVars false

namespace DataDrivenControl

namespace Wave

/-! ### `ℓ²` -/

/-- `ℓ²(ℕ, ℝ)`, each component of `V`. -/
abbrev ell2 : Type := ℓ²(ℕ, ℝ)

/-- The standard Hilbert basis of `ℓ²`. -/
def stdBasis : HilbertBasis ℕ ℝ ell2 := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ ell2)

/-- Coordinates in the standard basis: `⟪δₙ, a⟫ = aₙ`. -/
theorem inner_stdBasis (a : ell2) (n : ℕ) : ⟪stdBasis n, a⟫_ℝ = a n := by
  rw [← HilbertBasis.repr_apply_apply]; rfl

/-- The element of `ℓ²` with the given square-summable coordinates. -/
def mkL2 (g : ℕ → ℝ) (hg : Summable fun n => g n ^ 2) : ell2 :=
  ⟨g, show Memℓp g 2 from (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
    (by simpa [Real.norm_eq_abs, sq_abs] using hg)⟩

theorem inner_stdBasis_mkL2 (g : ℕ → ℝ) (hg : Summable fun n => g n ^ 2) (n : ℕ) :
    ⟪stdBasis n, mkL2 g hg⟫_ℝ = g n := by
  rw [inner_stdBasis]; rfl

/-- The space `V` of the wave equation: two copies of `ℓ²`, the weighted energy coordinates. -/
abbrev Vsp : Type := WithLp 2 (ell2 × ell2)

/-- First `V`-coordinates of a `V`-valued integral. -/
theorem inner_fst_integral {G : ℝ → Vsp} {μ : Measure ℝ} (hG : Integrable G μ) (n : ℕ) :
    ⟪stdBasis n, (∫ r, G r ∂μ).fst⟫_ℝ = ∫ r, ⟪stdBasis n, (G r).fst⟫_ℝ ∂μ :=
  (((innerSL ℝ (stdBasis n)).comp (WithLp.fstL 2 ℝ ell2 ell2)).integral_comp_comm hG).symm

/-- Second `V`-coordinates of a `V`-valued integral. -/
theorem inner_snd_integral {G : ℝ → Vsp} {μ : Measure ℝ} (hG : Integrable G μ) (n : ℕ) :
    ⟪stdBasis n, (∫ r, G r ∂μ).snd⟫_ℝ = ∫ r, ⟪stdBasis n, (G r).snd⟫_ℝ ∂μ :=
  (((innerSL ℝ (stdBasis n)).comp (WithLp.sndL 2 ℝ ell2 ell2)).integral_comp_comm hG).symm

/-! ### The weights of `V` -/

variable {X₁ X₂ : Type*} [NormedAddCommGroup X₁] [InnerProductSpace ℝ X₁] [CompleteSpace X₁]
  [NormedAddCommGroup X₂] [InnerProductSpace ℝ X₂] [CompleteSpace X₂]
  (s : HilbertBasis ℕ ℝ X₁) (f : HilbertBasis ℕ ℝ X₂) (c : ℝ) (q : X₁)

/-- The weight of `V` on both coordinates of mode `n`: `vₙ = (1 + ωₙ²)⁻¹ + qₙ²`,
`qₙ = ⟪sₙ, q⟫`. -/
def vwt (n : ℕ) : ℝ := (1 + freq c n ^ 2)⁻¹ + ⟪s n, q⟫_ℝ ^ 2

/-- The `ℓ²` multiplier `√vₙ` of `X ↪ V`. -/
def sw (n : ℕ) : ℝ := Real.sqrt (vwt s c q n)

theorem vwt_pos (n : ℕ) : 0 < vwt s c q n := by unfold vwt; positivity

theorem sw_pos (n : ℕ) : 0 < sw s c q n := Real.sqrt_pos.2 (vwt_pos s c q n)

theorem sw_sq (n : ℕ) : sw s c q n ^ 2 = vwt s c q n := Real.sq_sqrt (vwt_pos s c q n).le

/-- `|qₙ| ≤ ‖q‖`. -/
theorem abs_inner_le_norm (n : ℕ) : |⟪s n, q⟫_ℝ| ≤ ‖q‖ := by
  have h := abs_real_inner_le_norm (s n) q
  rwa [s.orthonormal.1 n, one_mul] at h

theorem vwt_le (n : ℕ) : vwt s c q n ≤ (1 + ‖q‖) ^ 2 := by
  unfold vwt
  have h1 : (1 + freq c n ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _))
  have h2 : ⟪s n, q⟫_ℝ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_inner_le_norm s q n) 2
  nlinarith [norm_nonneg q]

theorem abs_sw_le (n : ℕ) : |sw s c q n| ≤ 1 + ‖q‖ := by
  rw [abs_of_pos (sw_pos s c q n), sw]
  calc Real.sqrt (vwt s c q n) ≤ Real.sqrt ((1 + ‖q‖) ^ 2) := Real.sqrt_le_sqrt (vwt_le s c q n)
    _ = 1 + ‖q‖ := Real.sqrt_sq (by positivity)

/-- `qₙ² ≤ vₙ`: the observation weights are dominated by the weights of `V`. -/
theorem sq_inner_le_vwt (n : ℕ) : ⟪s n, q⟫_ℝ ^ 2 ≤ vwt s c q n := by
  unfold vwt
  have : 0 < (1 + freq c n ^ 2)⁻¹ := by positivity
  linarith

/-- `1/vₙ ≤ 1 + ωₙ²`: the weights of `D(A_V)` are at least `1`. -/
theorem inv_vwt_le (n : ℕ) : (vwt s c q n)⁻¹ ≤ 1 + freq c n ^ 2 := by
  have h : (1 + freq c n ^ 2)⁻¹ ≤ vwt s c q n := by
    unfold vwt; nlinarith [sq_nonneg ⟪s n, q⟫_ℝ]
  calc (vwt s c q n)⁻¹ ≤ ((1 + freq c n ^ 2)⁻¹)⁻¹ := inv_anti₀ (by positivity) h
    _ = 1 + freq c n ^ 2 := inv_inv _

/-- `(g / √vₙ)² ≤ g² + ωₙ² g²`. -/
theorem div_sw_sq_le (g : ℝ) (n : ℕ) :
    (g / sw s c q n) ^ 2 ≤ g ^ 2 + freq c n ^ 2 * g ^ 2 := by
  rw [div_pow, sw_sq, div_eq_mul_inv]
  calc g ^ 2 * (vwt s c q n)⁻¹ ≤ g ^ 2 * (1 + freq c n ^ 2) :=
        mul_le_mul_of_nonneg_left (inv_vwt_le s c q n) (sq_nonneg _)
    _ = _ := by ring

/-- `∑ₙ (1 + ωₙ²)⁻¹ < ∞` for `c ≠ 0`. -/
theorem summable_inv_one_add_freq_sq (hc : c ≠ 0) : Summable fun n => (1 + freq c n ^ 2)⁻¹ := by
  have hs : Summable fun n : ℕ => ((c * Real.pi) ^ 2)⁻¹ * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left _
  refine hs.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hpi : (c * Real.pi) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hc Real.pi_ne_zero)
  have e : freq c n ^ 2 = (c * Real.pi) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2) := by
    unfold freq; push_cast; ring
  have hpos : 0 < freq c n ^ 2 := by
    rw [e]; exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm hpi)) (by positivity)
  calc (1 + freq c n ^ 2)⁻¹ ≤ (freq c n ^ 2)⁻¹ := inv_anti₀ hpos (by linarith)
    _ = _ := by rw [e, mul_inv]

/-- `∑ₙ vₙ < ∞` for `c ≠ 0`. -/
theorem summable_vwt (hc : c ≠ 0) : Summable (vwt s c q) :=
  (summable_inv_one_add_freq_sq c hc).add (Diagonal.summable_inner_sq s q)

/-! ### The embedding `X ↪ V`, `B` and `C` -/

/-- The embedding `X ↪ V`, `(aₙ, bₙ) ↦ (√vₙ aₙ, √vₙ bₙ)`. -/
def ιV : WithLp 2 (X₁ × X₂) →L[ℝ] Vsp :=
  Rotation.blockDiag s f stdBasis stdBasis (sw s c q) (1 + ‖q‖) (abs_sw_le s c q)

theorem inner_fst_ιV (x : WithLp 2 (X₁ × X₂)) (n : ℕ) :
    ⟪stdBasis n, (ιV s f c q x).fst⟫_ℝ = sw s c q n * ⟪s n, x.fst⟫_ℝ :=
  Rotation.inner_fst_blockDiag s f stdBasis stdBasis (abs_sw_le s c q) x n

theorem inner_snd_ιV (x : WithLp 2 (X₁ × X₂)) (n : ℕ) :
    ⟪stdBasis n, (ιV s f c q x).snd⟫_ℝ = sw s c q n * ⟪f n, x.snd⟫_ℝ :=
  Rotation.inner_snd_blockDiag s f stdBasis stdBasis (abs_sw_le s c q) x n

/-- `‖ι_V x‖² = ∑ₙ vₙ (aₙ² + bₙ²)`. -/
theorem hasSum_norm_ιV_sq (x : WithLp 2 (X₁ × X₂)) :
    HasSum (fun n => vwt s c q n * (⟪s n, x.fst⟫_ℝ ^ 2 + ⟪f n, x.snd⟫_ℝ ^ 2))
      (‖ιV s f c q x‖ ^ 2) := by
  convert Rotation.hasSum_coord_sq stdBasis stdBasis (ιV s f c q x) using 1
  funext n
  rw [inner_fst_ιV, inner_snd_ιV, mul_pow, mul_pow, sw_sq]
  ring

theorem summable_ctrl_sq : Summable fun n => (sw s c q n * (c * Real.sqrt 2)) ^ 2 := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · refine ((summable_vwt s c q h).mul_right (2 * c ^ 2)).congr fun n => ?_
    rw [mul_pow, sw_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- The control vector `B 1 ∈ V`: in the energy coordinates it is `(0, c √2)` in every mode
(`bₙ' = -ωₙ aₙ + c √2 u`); its `V`-coordinates are `(0, √vₙ c √2)`, square summable because
`∑ vₙ < ∞`. -/
def ctrlVec : Vsp :=
  WithLp.toLp 2 (0, mkL2 (fun n => sw s c q n * (c * Real.sqrt 2)) (summable_ctrl_sq s c q))

theorem inner_fst_ctrlVec (n : ℕ) : ⟪stdBasis n, (ctrlVec s c q).fst⟫_ℝ = 0 := by
  simp [ctrlVec]

theorem inner_snd_ctrlVec (n : ℕ) :
    ⟪stdBasis n, (ctrlVec s c q).snd⟫_ℝ = sw s c q n * (c * Real.sqrt 2) := by
  simp only [ctrlVec, WithLp.toLp_snd, inner_stdBasis_mkL2]

/-- The control operator `B ∈ L(ℝ, V)`, `u ↦ u · B 1`. -/
def Bop : ℝ →L[ℝ] Vsp := ContinuousLinearMap.toSpanSingleton ℝ (ctrlVec s c q)

theorem Bop_apply (r : ℝ) : Bop s c q r = r • ctrlVec s c q := rfl

/-- The observation operator `C ∈ L(X, ℝ)`, `x ↦ ⟪q, x₁⟫` (`y = ∫₀¹ q w`). -/
def Cop : WithLp 2 (X₁ × X₂) →L[ℝ] ℝ := (innerSL ℝ q).comp (WithLp.fstL 2 ℝ X₁ X₂)

omit [CompleteSpace X₁] [CompleteSpace X₂] in
theorem Cop_apply (x : WithLp 2 (X₁ × X₂)) : Cop q x = ⟪q, x.fst⟫_ℝ := rfl

/-! ### The system -/

/-- **The wave equation with Dirichlet control** (`ex:intro-wave`) in modal form, on
`W = X ↪ V`: `S_W = S_X` is the block-rotation group with the frequencies `ωₙ = c (n + 1) π`,
`S_V` the rotation group on the weighted `ℓ²` space `V`, `B 1` the Dirichlet control vector
and `C x = ⟪q, x₁⟫`. -/
def waveSystem : System ℝ (WithLp 2 (X₁ × X₂)) (WithLp 2 (X₁ × X₂)) Vsp ℝ where
  ιW := ContinuousLinearMap.id ℝ _
  ιV := ιV s f c q
  ιW_injective := Function.injective_id
  ιV_injective := Rotation.injective_blockDiag s f stdBasis stdBasis (abs_sw_le s c q)
    fun n => (sw_pos s c q n).ne'
  ιW_denseRange := denseRange_id
  ιV_denseRange := Rotation.denseRange_blockDiag s f stdBasis stdBasis (abs_sw_le s c q)
    fun n => (sw_pos s c q n).ne'
  SW := Rotation.rotGroup s f (freq c)
  SX := Rotation.rotGroup s f (freq c)
  SV := Rotation.rotGroup stdBasis stdBasis (freq c)
  consistentW := (Rotation.rotGroup s f (freq c)).consistent_id
  consistentV := Rotation.consistent_blockDiag s f stdBasis stdBasis (abs_sw_le s c q) (freq c)
  B := Bop s c q
  C := Cop q

/-- `W = X`. -/
@[simp] theorem waveSystem_ιW : (waveSystem s f c q).ιW = ContinuousLinearMap.id ℝ _ := rfl
@[simp] theorem waveSystem_ιV : (waveSystem s f c q).ιV = ιV s f c q := rfl
@[simp] theorem waveSystem_SW :
    (waveSystem s f c q).SW = Rotation.rotGroup s f (freq c) := rfl
/-- **`S_X` is the block-rotation group** with the frequencies `ωₙ = c (n + 1) π`. -/
@[simp] theorem waveSystem_SX :
    (waveSystem s f c q).SX = Rotation.rotGroup s f (freq c) := rfl
@[simp] theorem waveSystem_SV :
    (waveSystem s f c q).SV = Rotation.rotGroup stdBasis stdBasis (freq c) := rfl
@[simp] theorem waveSystem_B : (waveSystem s f c q).B = Bop s c q := rfl
@[simp] theorem waveSystem_C : (waveSystem s f c q).C = Cop q := rfl

theorem waveSystem_ιWV (x : WithLp 2 (X₁ × X₂)) : (waveSystem s f c q).ιWV x = ιV s f c q x := rfl

/-- The free modal motion, displacement coordinates: for `t ≥ 0`,
`aₙ(t) = cos(ωₙ t) aₙ + sin(ωₙ t) bₙ`. -/
theorem inner_fst_waveSystem_SX {t : ℝ} (ht : 0 ≤ t) (x : WithLp 2 (X₁ × X₂)) (n : ℕ) :
    ⟪s n, ((waveSystem s f c q).SX.real t x).fst⟫_ℝ =
      Real.cos (freq c n * t) * ⟪s n, x.fst⟫_ℝ + Real.sin (freq c n * t) * ⟪f n, x.snd⟫_ℝ :=
  Rotation.inner_fst_rotGroup_real s f (freq c) ht x n

/-- The free modal motion, velocity coordinates: for `t ≥ 0`,
`bₙ(t) = -sin(ωₙ t) aₙ + cos(ωₙ t) bₙ`. -/
theorem inner_snd_waveSystem_SX {t : ℝ} (ht : 0 ≤ t) (x : WithLp 2 (X₁ × X₂)) (n : ℕ) :
    ⟪f n, ((waveSystem s f c q).SX.real t x).snd⟫_ℝ =
      -Real.sin (freq c n * t) * ⟪s n, x.fst⟫_ℝ + Real.cos (freq c n * t) * ⟪f n, x.snd⟫_ℝ :=
  Rotation.inner_snd_rotGroup_real s f (freq c) ht x n

/-- **`C` is the weighted integral observation** `y = ∫₀¹ q w = ∑ₙ qₙ aₙ`, `qₙ = ⟪sₙ, q⟫`. -/
theorem hasSum_waveSystem_C (x : WithLp 2 (X₁ × X₂)) :
    HasSum (fun n => ⟪s n, q⟫_ℝ * ⟪s n, x.fst⟫_ℝ) ((waveSystem s f c q).C x) := by
  rw [waveSystem_C, Cop_apply]
  convert s.hasSum_inner_mul_inner q x.fst using 1
  funext n
  rw [real_inner_comm (s n) q]

/-- **`C` is bounded on `X`**: `|C x| ≤ ‖q‖ ‖x‖`.  This is automatic here, since `W = X` and
`C ∈ L(W, Y)`. -/
theorem norm_waveSystem_C_le (x : WithLp 2 (X₁ × X₂)) :
    ‖(waveSystem s f c q).C x‖ ≤ ‖q‖ * ‖(waveSystem s f c q).ιW x‖ := by
  rw [waveSystem_C, waveSystem_ιW, Cop_apply, ContinuousLinearMap.id_apply, Real.norm_eq_abs]
  exact (abs_real_inner_le_norm q x.fst).trans
    (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ x) (norm_nonneg q))

/-- **`B` is unbounded on `X`** (Dirichlet control, `c ≠ 0`): `B 1 ∉ X`, since its energy
coordinates `(0, c √2)` are not square summable. -/
theorem waveSystem_B_not_mem_range (hc : c ≠ 0) :
    (waveSystem s f c q).B 1 ∉ Set.range (waveSystem s f c q).ιV := by
  rintro ⟨x, hx⟩
  have hb : ∀ n, ⟪f n, x.snd⟫_ℝ = c * Real.sqrt 2 := fun n => by
    have h := congrArg (fun v : Vsp => ⟪stdBasis n, v.snd⟫_ℝ) hx
    simp only [waveSystem_ιV, waveSystem_B, Bop_apply, one_smul, inner_snd_ιV,
      inner_snd_ctrlVec] at h
    exact mul_left_cancel₀ (sw_pos s c q n).ne' h
  have hs := Diagonal.summable_inner_sq f x.snd
  simp only [hb] at hs
  have h0 : (c * Real.sqrt 2) ^ 2 = 0 := tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero
  have h1 := (mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)).resolve_right
    (Real.sqrt_ne_zero'.2 two_pos)
  exact hc h1

/-! ### `hyp:compat` -/

/-- **`hyp:compat`**: `D(A_V)` embeds into `W = X` with constant `1`, since
`1/vₙ ≤ 1 + ωₙ²` (`inv_vwt_le`) gives `‖x‖² ≤ ‖v‖² + ‖A_V v‖²` for `ι_V x = v`; density holds
because `ι_V` maps `D(A)` (dense in `X`) into `D(A_V)`. -/
theorem waveSystem_compat : (waveSystem s f c q).Compat := by
  refine ⟨⟨1, fun v hv => ?_⟩, ?_⟩
  · have hgen : HasSum (fun n => freq c n ^ 2 * (⟪stdBasis n, v.fst⟫_ℝ ^ 2 +
        ⟪stdBasis n, v.snd⟫_ℝ ^ 2)) (‖(waveSystem s f c q).AV ⟨v, hv⟩‖ ^ 2) :=
      Rotation.hasSum_sq_generator stdBasis stdBasis (freq c) ⟨v, hv⟩
    have hcoord := Rotation.hasSum_coord_sq stdBasis stdBasis v
    have hbd : ∀ n, (⟪stdBasis n, v.fst⟫_ℝ / sw s c q n) ^ 2 +
        (⟪stdBasis n, v.snd⟫_ℝ / sw s c q n) ^ 2 ≤
        (⟪stdBasis n, v.fst⟫_ℝ ^ 2 + ⟪stdBasis n, v.snd⟫_ℝ ^ 2) +
          freq c n ^ 2 * (⟪stdBasis n, v.fst⟫_ℝ ^ 2 + ⟪stdBasis n, v.snd⟫_ℝ ^ 2) := fun n => by
      have h1 := div_sw_sq_le s c q ⟪stdBasis n, v.fst⟫_ℝ n
      have h2 := div_sw_sq_le s c q ⟪stdBasis n, v.snd⟫_ℝ n
      nlinarith
    have hsum := (hcoord.add hgen).summable
    have ha : Summable fun n => (⟪stdBasis n, v.fst⟫_ℝ / sw s c q n) ^ 2 :=
      hsum.of_nonneg_of_le (fun n => sq_nonneg _) fun n =>
        (le_add_of_nonneg_right (sq_nonneg _)).trans (hbd n)
    have hb : Summable fun n => (⟪stdBasis n, v.snd⟫_ℝ / sw s c q n) ^ 2 :=
      hsum.of_nonneg_of_le (fun n => sq_nonneg _) fun n =>
        (le_add_of_nonneg_left (sq_nonneg _)).trans (hbd n)
    obtain ⟨w, hw⟩ := Rotation.exists_coord_eq s f _ _ ha hb
    refine ⟨w, ?_, ?_⟩
    · rw [waveSystem_ιWV]
      refine Rotation.ext_coord stdBasis stdBasis (fun n => ?_) fun n => ?_
      · rw [inner_fst_ιV, (hw n).1]; field_simp [(sw_pos s c q n).ne']
      · rw [inner_snd_ιV, (hw n).2]; field_simp [(sw_pos s c q n).ne']
    · have hw2 : ‖w‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖(waveSystem s f c q).AV ⟨v, hv⟩‖ ^ 2 :=
        hasSum_le (fun n => by rw [(hw n).1, (hw n).2]; exact hbd n)
          (Rotation.hasSum_coord_sq s f w) (hcoord.add hgen)
      rw [one_mul]
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      nlinarith [norm_nonneg v, norm_nonneg ((waveSystem s f c q).AV ⟨v, hv⟩)]
  · refine Dense.mono (fun x hx => ?_)
      (Rotation.rotGroup s f (freq c)).dense_generator_domain
    exact (waveSystem s f c q).consistentV.mem_generator_domain _ hx

end Wave

end DataDrivenControl
