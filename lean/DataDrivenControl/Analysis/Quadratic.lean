module

public import Mathlib

/-!
# Minimisers of coercive quadratic functionals

Used by `thm:lqr-data` (`app:lqr-data`) and `thm:lqr-data-io`
(`app:lqr-data-io`): the model-based cost is a continuous quadratic functional of the input with
coercive quadratic part, hence has a unique minimiser, and the data-driven problems are
identified with it through a bijection between feasible sets.

## Transport of minimisers
* `isMinOn_iff_of_bijOn`, `existsUnique_isMinOn_iff_of_bijOn`: minimisers (and unique
  minimisers) correspond under a bijection of feasible sets that intertwines the costs;
* `isMinOn_comp_equiv_iff`, `existsUnique_isMinOn_comp_equiv_iff`: the same for a global
  bijection (`Equiv`); `isMinOn_comp_continuousLinearEquiv_iff` and `isMinOn_comp_affine_iff`
  for continuous linear equivalences and affine reparametrisations `v ↦ u₀ + e v`.

## Quadratic functionals
* `quadraticFunctional a ℓ c u = a u u + 2 ℓ u + c`, with `a` a bounded bilinear form;
  continuity, the expansion along a line, the midpoint identity
  `J u + J v - 2 J ((u + v) / 2) = a (u - v) (u - v) / 2`, and composition with an affine map
  (`quadraticFunctional_comp_add`);
* `existsUnique_isMinOn_of_midpoint`: on a Banach space, a continuous function that is bounded
  below and strongly midpoint convex on a nonempty closed convex set has a unique minimiser
  there (minimising sequences are Cauchy);
* `existsUnique_isMinOn_quadraticFunctional`: unique minimiser on a nonempty closed convex set
  on whose differences `a` is coercive; variants for a coercive `a`
  (`…_of_isCoercive`, `…_univ`), a closed affine subspace (`…_affineSubspace`) and the fibre
  `L ⁻¹' {w}` of a continuous linear map (`…_preimage`);
* `isMinOn_quadraticFunctional_affineSubspace_iff`: first-order characterisation of the
  minimiser on an affine subspace.

The direct minimising-sequence argument replaces Lax–Milgram; no symmetry of `a` is needed,
since only `a h h` enters.
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace DataDrivenControl

/-! ### Transport of minimisers -/

section Transport

variable {α β γ : Type*} [Preorder γ]

/-- Minimisers transport along a bijection `f : A → B` of feasible sets that intertwines the
costs (`app:lqr-data`, `app:lqr-data-io`). -/
theorem isMinOn_iff_of_bijOn {f : α → β} {A : Set α} {B : Set β} (hf : BijOn f A B)
    {J₁ : α → γ} {J₂ : β → γ} (hJ : ∀ x ∈ A, J₁ x = J₂ (f x)) {x : α} (hx : x ∈ A) :
    IsMinOn J₁ A x ↔ IsMinOn J₂ B (f x) := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h y hy
    obtain ⟨x', hx', rfl⟩ := hf.surjOn hy
    rw [← hJ x hx, ← hJ x' hx']
    exact h x' hx'
  · intro h x' hx'
    rw [hJ x hx, hJ x' hx']
    exact h _ (hf.mapsTo hx')

/-- Unique minimisers transport along a bijection of feasible sets that intertwines the costs
(`app:lqr-data`, `app:lqr-data-io`). -/
theorem existsUnique_isMinOn_iff_of_bijOn {f : α → β} {A : Set α} {B : Set β}
    (hf : BijOn f A B) {J₁ : α → γ} {J₂ : β → γ} (hJ : ∀ x ∈ A, J₁ x = J₂ (f x)) :
    (∃! x, x ∈ A ∧ IsMinOn J₁ A x) ↔ ∃! y, y ∈ B ∧ IsMinOn J₂ B y := by
  constructor
  · rintro ⟨x, ⟨hx, hmin⟩, huniq⟩
    refine ⟨f x, ⟨hf.mapsTo hx, (isMinOn_iff_of_bijOn hf hJ hx).1 hmin⟩, ?_⟩
    rintro y ⟨hy, hymin⟩
    obtain ⟨x', hx', rfl⟩ := hf.surjOn hy
    rw [huniq x' ⟨hx', (isMinOn_iff_of_bijOn hf hJ hx').2 hymin⟩]
  · rintro ⟨y, ⟨hy, hmin⟩, huniq⟩
    obtain ⟨x, hx, rfl⟩ := hf.surjOn hy
    refine ⟨x, ⟨hx, (isMinOn_iff_of_bijOn hf hJ hx).2 hmin⟩, ?_⟩
    rintro x' ⟨hx', hx'min⟩
    exact hf.injOn hx' hx
      (huniq _ ⟨hf.mapsTo hx', (isMinOn_iff_of_bijOn hf hJ hx').1 hx'min⟩)

/-- Minimisers transport along a global bijection. -/
theorem isMinOn_comp_equiv_iff (e : α ≃ β) {B : Set β} {J : β → γ} {x : α} :
    IsMinOn (J ∘ e) (e ⁻¹' B) x ↔ IsMinOn J B (e x) := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h y hy
    have := h (e.symm y) (by simpa [mem_preimage] using hy)
    simpa using this
  · intro h x' hx'
    exact h _ hx'

/-- Unique minimisers transport along a global bijection. -/
theorem existsUnique_isMinOn_comp_equiv_iff (e : α ≃ β) {B : Set β} {J : β → γ} :
    (∃! x, x ∈ e ⁻¹' B ∧ IsMinOn (J ∘ e) (e ⁻¹' B) x) ↔ ∃! y, y ∈ B ∧ IsMinOn J B y := by
  have hb : BijOn e (e ⁻¹' B) B :=
    ⟨fun x hx => hx, e.injective.injOn, fun y hy => ⟨e.symm y, by simpa using hy, by simp⟩⟩
  exact existsUnique_isMinOn_iff_of_bijOn hb fun x _ => rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Minimisers transport along a continuous linear equivalence. -/
theorem isMinOn_comp_continuousLinearEquiv_iff (e : E ≃L[ℝ] F) {B : Set F} {J : F → γ}
    {x : E} : IsMinOn (J ∘ e) (e ⁻¹' B) x ↔ IsMinOn J B (e x) := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h y hy
    have := h (e.symm y) (by simpa [mem_preimage] using hy)
    simpa using this
  · intro h x' hx'
    exact h _ hx'

/-- Minimisers transport along an affine reparametrisation `v ↦ u₀ + e v`. -/
theorem isMinOn_comp_affine_iff (e : E ≃L[ℝ] F) (u₀ : F) {B : Set F} {J : F → γ} {x : E} :
    IsMinOn (fun v => J (u₀ + e v)) ((fun v => u₀ + e v) ⁻¹' B) x ↔ IsMinOn J B (u₀ + e x) := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro h y hy
    have := h (e.symm (y - u₀)) (by simpa [mem_preimage] using hy)
    simpa using this
  · intro h x' hx'
    exact h _ hx'

/-- Unique minimisers transport along an affine reparametrisation `v ↦ u₀ + e v`. -/
theorem existsUnique_isMinOn_comp_affine_iff (e : E ≃L[ℝ] F) (u₀ : F) {B : Set F}
    {J : F → γ} :
    (∃! x, x ∈ (fun v => u₀ + e v) ⁻¹' B ∧
        IsMinOn (fun v => J (u₀ + e v)) ((fun v => u₀ + e v) ⁻¹' B) x) ↔
      ∃! y, y ∈ B ∧ IsMinOn J B y := by
  have hb : BijOn (fun v => u₀ + e v) ((fun v => u₀ + e v) ⁻¹' B) B := by
    refine ⟨fun x hx => hx, ?_, fun y hy => ⟨e.symm (y - u₀), by simpa using hy, by simp⟩⟩
    intro x _ x' _ hxx'
    exact e.injective (add_left_cancel hxx')
  exact existsUnique_isMinOn_iff_of_bijOn hb fun x _ => rfl

end Transport

/-! ### Quadratic functionals -/

section Quadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The quadratic functional `u ↦ a(u, u) + 2 ℓ(u) + c` of a bounded bilinear form `a`, a bounded
linear functional `ℓ` and a constant `c`. -/
def quadraticFunctional (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ) (u : E) : ℝ :=
  a u u + 2 * ℓ u + c

/-- A quadratic functional is continuous. -/
theorem continuous_quadraticFunctional (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    Continuous (quadraticFunctional a ℓ c) := by
  unfold quadraticFunctional
  fun_prop

/-- Expansion of a quadratic functional along the line `s ↦ u + s h`. -/
theorem quadraticFunctional_add_smul (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ)
    (u h : E) (s : ℝ) :
    quadraticFunctional a ℓ c (u + s • h) =
      quadraticFunctional a ℓ c u + s * (a u h + a h u + 2 * ℓ h) + s ^ 2 * a h h := by
  simp only [quadraticFunctional, map_add, map_smul, add_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The midpoint identity `J u + J v - 2 J ((u + v) / 2) = a (u - v) (u - v) / 2`. -/
theorem quadraticFunctional_midpoint (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ)
    (u v : E) :
    quadraticFunctional a ℓ c u + quadraticFunctional a ℓ c v -
        2 * quadraticFunctional a ℓ c (midpoint ℝ u v) = a (u - v) (u - v) / 2 := by
  rw [midpoint_eq_smul_add]
  simp only [quadraticFunctional, map_add, map_sub, map_smul, add_apply,
    sub_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    invOf_eq_inv]
  ring

/-- A quadratic functional composed with an affine map `v ↦ L v + w` is a quadratic functional,
with bilinear form `a (L ·) (L ·)`. -/
theorem quadraticFunctional_comp_add (a : F →L[ℝ] F →L[ℝ] ℝ) (ℓ : F →L[ℝ] ℝ) (c : ℝ)
    (L : E →L[ℝ] F) (w : F) (v : E) :
    quadraticFunctional a ℓ c (L v + w) =
      quadraticFunctional (a.bilinearComp L L)
        ((2⁻¹ : ℝ) • ((a.flip w).comp L + (a w).comp L) + ℓ.comp L)
        (quadraticFunctional a ℓ c w) v := by
  simp only [quadraticFunctional, ContinuousLinearMap.bilinearComp_apply,
    add_apply, FunLike.coe_smul, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.flip_apply, map_add, Pi.smul_apply, smul_eq_mul,
    add_apply]
  ring

/-- **Unique minimiser of a strongly midpoint-convex function.**  On a Banach space, a function
that is continuous and bounded below on a nonempty closed convex set `C`, and satisfies
`κ ‖u - v‖² ≤ J u + J v - 2 J ((u + v) / 2)` on `C` for some `κ > 0`, has a unique minimiser
on `C`. -/
theorem existsUnique_isMinOn_of_midpoint [CompleteSpace E] {J : E → ℝ} {C : Set E}
    (hCc : Convex ℝ C) (hCl : IsClosed C) (hne : C.Nonempty) (hJ : ContinuousOn J C)
    (hbdd : BddBelow (J '' C)) {κ : ℝ} (hκ : 0 < κ)
    (hmid : ∀ u ∈ C, ∀ v ∈ C, κ * ‖u - v‖ ^ 2 ≤ J u + J v - 2 * J (midpoint ℝ u v)) :
    ∃! u, u ∈ C ∧ IsMinOn J C u := by
  set m := sInf (J '' C) with hm
  have hne' : (J '' C).Nonempty := hne.image J
  have hmle : ∀ v ∈ C, m ≤ J v := fun v hv => csInf_le hbdd (mem_image_of_mem J hv)
  have key : ∀ u ∈ C, ∀ v ∈ C, κ * ‖u - v‖ ^ 2 ≤ (J u - m) + (J v - m) := by
    intro u hu v hv
    have h1 := hmid u hu v hv
    have h2 := hmle _ (hCc.midpoint_mem hu hv)
    linarith
  have hseq : ∀ n : ℕ, ∃ u ∈ C, J u < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne' this
    exact ⟨u, hu, hlt⟩
  choose u huC hu using hseq
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt (2 / κ * (1 / ((N : ℝ) + 1))))
      ?_ ?_
    · intro n k N hn hk
      rw [dist_eq_norm]
      apply Real.le_sqrt_of_sq_le
      have h1 := key _ (huC n) _ (huC k)
      have h2 : J (u n) - m < 1 / ((N : ℝ) + 1) := by
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          gcongr
        linarith [hu n]
      have h3 : J (u k) - m < 1 / ((N : ℝ) + 1) := by
        have : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          gcongr
        linarith [hu k]
      rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
      nlinarith
    · have h : Tendsto (fun N : ℕ => 2 / κ * (1 / ((N : ℝ) + 1))) atTop (𝓝 (2 / κ * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
      rw [mul_zero] at h
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h
  obtain ⟨u₀, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hu₀C : u₀ ∈ C := hCl.mem_of_tendsto hlim (Eventually.of_forall huC)
  have hJlim : Tendsto (fun n => J (u n)) atTop (𝓝 (J u₀)) :=
    (hJ u₀ hu₀C).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall huC⟩)
  have hJm : Tendsto (fun n => J (u n)) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => hmle _ (huC n)) (fun n => (hu n).le)
    simpa using (tendsto_const_nhds (x := m)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hJu₀ : J u₀ = m := tendsto_nhds_unique hJlim hJm
  refine ⟨u₀, ⟨hu₀C, ?_⟩, ?_⟩
  · rw [isMinOn_iff]
    intro v hv
    rw [hJu₀]
    exact hmle v hv
  · rintro v ⟨hv, hvmin⟩
    have h1 := key v hv u₀ hu₀C
    have h2 : J v = m :=
      le_antisymm (by rw [← hJu₀]; exact (isMinOn_iff.1 hvmin) u₀ hu₀C) (hmle v hv)
    rw [h2, hJu₀, sub_self, add_zero] at h1
    have h3 : ‖v - u₀‖ ^ 2 ≤ 0 := by nlinarith
    have h4 : ‖v - u₀‖ = 0 := by nlinarith [norm_nonneg (v - u₀)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)

/-- **Unique minimiser of a coercive quadratic functional** on a nonempty closed convex set `C`,
when `a` is coercive on the differences of points of `C` (`app:lqr-data`). -/
theorem existsUnique_isMinOn_quadraticFunctional [CompleteSpace E] (a : E →L[ℝ] E →L[ℝ] ℝ)
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) {C : Set E} (hCc : Convex ℝ C) (hCl : IsClosed C)
    (hne : C.Nonempty) {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ u ∈ C, ∀ v ∈ C, κ * ‖u - v‖ ^ 2 ≤ a (u - v) (u - v)) :
    ∃! u, u ∈ C ∧ IsMinOn (quadraticFunctional a ℓ c) C u := by
  obtain ⟨u₀, hu₀⟩ := hne
  set K := 2 * ‖a‖ * ‖u₀‖ + 2 * ‖ℓ‖ with hK
  have hb : ∀ u ∈ C, quadraticFunctional a ℓ c u₀ - K ^ 2 / (4 * κ) ≤
      quadraticFunctional a ℓ c u := by
    intro u hu
    have hexp := quadraticFunctional_add_smul a ℓ c u₀ (u - u₀) 1
    rw [one_smul, add_sub_cancel] at hexp
    rw [hexp]
    set h := u - u₀
    have h1 : |a u₀ h| ≤ ‖a‖ * ‖u₀‖ * ‖h‖ := by
      rw [← Real.norm_eq_abs]; exact a.le_opNorm₂ u₀ h
    have h2 : |a h u₀| ≤ ‖a‖ * ‖h‖ * ‖u₀‖ := by
      rw [← Real.norm_eq_abs]; exact a.le_opNorm₂ h u₀
    have h3 : |ℓ h| ≤ ‖ℓ‖ * ‖h‖ := by
      rw [← Real.norm_eq_abs]; exact ℓ.le_opNorm h
    have h4 : κ * ‖h‖ ^ 2 ≤ a h h := hcoer u hu u₀ hu₀
    have h5 : K * ‖h‖ - κ * ‖h‖ ^ 2 ≤ K ^ 2 / (4 * κ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * κ * ‖h‖ - K)]
    rw [abs_le] at h1 h2 h3
    nlinarith
  refine existsUnique_isMinOn_of_midpoint hCc hCl ⟨u₀, hu₀⟩
    (continuous_quadraticFunctional a ℓ c).continuousOn ?_ (half_pos hκ) ?_
  · refine ⟨quadraticFunctional a ℓ c u₀ - K ^ 2 / (4 * κ), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hb u hu
  · intro u hu v hv
    have h1 := quadraticFunctional_midpoint a ℓ c u v
    have h2 := hcoer u hu v hv
    linarith

/-- Unique minimiser of a quadratic functional with coercive `a` on a nonempty closed convex
set. -/
theorem existsUnique_isMinOn_quadraticFunctional_of_isCoercive [CompleteSpace E]
    {a : E →L[ℝ] E →L[ℝ] ℝ} (ha : IsCoercive a) (ℓ : E →L[ℝ] ℝ) (c : ℝ) {C : Set E}
    (hCc : Convex ℝ C) (hCl : IsClosed C) (hne : C.Nonempty) :
    ∃! u, u ∈ C ∧ IsMinOn (quadraticFunctional a ℓ c) C u := by
  obtain ⟨κ, hκ, hcoer⟩ := ha
  refine existsUnique_isMinOn_quadraticFunctional a ℓ c hCc hCl hne hκ fun u _ v _ => ?_
  rw [sq, ← mul_assoc]
  exact hcoer _

/-- Unique global minimiser of a quadratic functional with coercive `a`. -/
theorem existsUnique_isMinOn_quadraticFunctional_univ [CompleteSpace E]
    {a : E →L[ℝ] E →L[ℝ] ℝ} (ha : IsCoercive a) (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    ∃! u, ∀ v, quadraticFunctional a ℓ c u ≤ quadraticFunctional a ℓ c v := by
  obtain ⟨u, ⟨-, hu⟩, huniq⟩ := existsUnique_isMinOn_quadraticFunctional_of_isCoercive ha ℓ c
    convex_univ isClosed_univ univ_nonempty
  exact ⟨u, isMinOn_univ_iff.1 hu, fun w hw => huniq w ⟨mem_univ _, isMinOn_univ_iff.2 hw⟩⟩

/-- Unique minimiser of a quadratic functional on a nonempty closed affine subspace on whose
direction `a` is coercive. -/
theorem existsUnique_isMinOn_quadraticFunctional_affineSubspace [CompleteSpace E]
    (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ) (s : AffineSubspace ℝ E)
    (hs : IsClosed (s : Set E)) (hne : (s : Set E).Nonempty) {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ h ∈ s.direction, κ * ‖h‖ ^ 2 ≤ a h h) :
    ∃! u, u ∈ s ∧ IsMinOn (quadraticFunctional a ℓ c) (s : Set E) u := by
  refine existsUnique_isMinOn_quadraticFunctional a ℓ c s.convex hs hne hκ fun u hu v hv => ?_
  have := AffineSubspace.vsub_mem_direction hu hv
  rw [vsub_eq_sub] at this
  exact hcoer _ this

/-- Unique minimiser of a quadratic functional on a nonempty fibre `L ⁻¹' {w}` of a continuous
linear map, when `a` is coercive on `ker L` (for instance, inputs with a prescribed restriction
to a conditioning window). -/
theorem existsUnique_isMinOn_quadraticFunctional_preimage [CompleteSpace E]
    (a : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ) (L : E →L[ℝ] F) (w : F)
    (hne : ∃ u, L u = w) {κ : ℝ} (hκ : 0 < κ) (hcoer : ∀ h, L h = 0 → κ * ‖h‖ ^ 2 ≤ a h h) :
    ∃! u, L u = w ∧ IsMinOn (quadraticFunctional a ℓ c) (L ⁻¹' {w}) u := by
  have hconv : Convex ℝ (L ⁻¹' {w}) := by
    simpa using (convex_singleton w).linear_preimage (L : E →ₗ[ℝ] F)
  have hcl : IsClosed (L ⁻¹' {w}) := isClosed_singleton.preimage L.continuous
  obtain ⟨u₀, hu₀⟩ := hne
  have := existsUnique_isMinOn_quadraticFunctional a ℓ c hconv hcl ⟨u₀, hu₀⟩ hκ
    fun u hu v hv => hcoer _ (by
      simp only [mem_preimage, mem_singleton_iff] at hu hv
      rw [map_sub, hu, hv, sub_self])
  simpa only [mem_preimage, mem_singleton_iff] using this

/-- First-order characterisation: if `a` is nonnegative on the direction of an affine subspace
`s`, a point `u ∈ s` minimises the quadratic functional on `s` if and only if
`a u h + a h u + 2 ℓ h = 0` for every direction `h`. -/
theorem isMinOn_quadraticFunctional_affineSubspace_iff (a : E →L[ℝ] E →L[ℝ] ℝ)
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) (s : AffineSubspace ℝ E) (hpos : ∀ h ∈ s.direction, 0 ≤ a h h)
    {u : E} (hu : u ∈ s) :
    IsMinOn (quadraticFunctional a ℓ c) (s : Set E) u ↔
      ∀ h ∈ s.direction, a u h + a h u + 2 * ℓ h = 0 := by
  constructor
  · intro hmin h hh
    have hQ : 0 ≤ a h h := hpos h hh
    have key : ∀ t : ℝ, 0 ≤ t * (a u h + a h u + 2 * ℓ h) + t ^ 2 * a h h := by
      intro t
      have hmem : u + t • h ∈ s := by
        rw [add_comm, ← vadd_eq_add]
        exact AffineSubspace.vadd_mem_of_mem_direction (s.direction.smul_mem t hh) hu
      have := (isMinOn_iff.1 hmin) _ hmem
      rw [quadraticFunctional_add_smul] at this
      linarith
    set L := a u h + a h u + 2 * ℓ h
    have hQ1 : 0 < a h h + 1 := by linarith
    have h1 := key (-L / (a h h + 1))
    have h2 : 0 ≤ -L ^ 2 * (a h h + 1) + L ^ 2 * a h h := by
      have : 0 ≤ (-L / (a h h + 1) * L + (-L / (a h h + 1)) ^ 2 * a h h) * (a h h + 1) ^ 2 :=
        mul_nonneg h1 (sq_nonneg _)
      have e : (-L / (a h h + 1) * L + (-L / (a h h + 1)) ^ 2 * a h h) * (a h h + 1) ^ 2 =
          -L ^ 2 * (a h h + 1) + L ^ 2 * a h h := by
        field_simp
      linarith
    nlinarith [sq_nonneg L]
  · intro hcrit
    rw [isMinOn_iff]
    intro v hv
    have hh : v - u ∈ s.direction := by
      have := AffineSubspace.vsub_mem_direction hv hu
      rwa [vsub_eq_sub] at this
    have hexp := quadraticFunctional_add_smul a ℓ c u (v - u) 1
    rw [one_smul, add_sub_cancel, hcrit _ hh] at hexp
    have := hpos _ hh
    rw [hexp]
    nlinarith

end Quadratic

end DataDrivenControl
