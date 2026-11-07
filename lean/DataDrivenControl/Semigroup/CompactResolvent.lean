module

public import DataDrivenControl.Semigroup.Resolvent

/-!
# Compact resolvents: the spectral facts used by the Fattorini–Hautus proof

The proof of `prop:fattorini-hautus` in `Controllability/FHSpectral` is contour-free: it never
forms Riesz projections.  It works with one compact resolvent `K = R(μ₀, A⋆)` at a real point
`μ₀`, the Fredholm alternative of Mathlib
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), and the adjoint `K† = R(μ₀, A_ℂ)`.
The facts below are what it needs about resolvents of a closed operator; they are stated for a
general `A : E →ₗ.[𝕜] E` (`resolventSet`, `resolvent` from `Semigroup/Resolvent`).

## Main statements

* `isCompactOperator_resolvent`: compactness of `R(μ)` at one point of `ρ(A)` gives it at every
  point (resolvent identity `R(ν) = R(μ) + (μ - ν) R(ν) R(μ)`).
* `mem_domain_of_resolvent_eq_smul`: the eigenvalue map `ν ↦ μ - ν⁻¹`: if `R(μ) x = ν x` with
  `ν ≠ 0`, then `x ∈ D(A)` and `A x = (μ - ν⁻¹) x`.
* `maxGenEigenspace_resolvent_le` and `iSup_maxGenEigenspace_resolvent_le`: the generalised
  eigenspace of `R(μ)` at `ν` lies in that of `R(μ')` at `ν / (1 + (μ' - μ) ν)`, so the span of
  all root vectors of `R(μ)` does not depend on `μ ∈ ρ(A)` (`dense_iSup_maxGenEigenspace_resolvent`).
  This is the statement "completeness of the root vectors of `A`" independent of the chosen
  resolvent point.
* `IsResolvent.adjoint`, `mem_resolventSet_adjoint`, `resolvent_adjoint`: for densely defined `A`
  on a Hilbert space, `R(μ, A)† = R(conj μ, A†)`.
* `le_orthogonal_iSup_maxGenEigenspace_adjoint` (Fredholm alternative on an invariant subspace):
  if `K` is compact, `K†` injective, and the closed `K`-invariant subspace `N` contains no
  eigenvector of `K` for a nonzero eigenvalue, then `N` is orthogonal to every root vector of
  `K†`; `eq_bot_of_dense_iSup_maxGenEigenspace_adjoint`: if these root vectors are complete,
  `N = 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace DataDrivenControl

section Banach

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {A : E →ₗ.[𝕜] E}

/-- **Compact resolvent at every point**: if `R(μ)` is compact for one `μ ∈ ρ(A)`, then `R(ν)` is
compact for every `ν ∈ ρ(A)` (`R(ν) = R(μ) + (μ - ν) R(ν) R(μ)`). -/
theorem isCompactOperator_resolvent {μ ν : 𝕜} (hμ : μ ∈ resolventSet A)
    (hν : ν ∈ resolventSet A) (h : IsCompactOperator (resolvent A μ)) :
    IsCompactOperator (resolvent A ν) := by
  have e : resolvent A ν =
      resolvent A μ - (ν - μ) • (resolvent A μ).comp (resolvent A ν) := by
    rw [← resolvent_sub_resolvent hμ hν, sub_sub_cancel]
  rw [e, FunLike.coe_sub, FunLike.coe_smul, ContinuousLinearMap.coe_comp]
  exact h.sub ((h.comp_clm (resolvent A ν)).smul (ν - μ))

/-- **The eigenvalue map `ν ↦ μ - ν⁻¹`**: an eigenvector of `R(μ)` for a nonzero eigenvalue `ν`
lies in `D(A)` and is an eigenvector of `A` with eigenvalue `μ - ν⁻¹`. -/
theorem mem_domain_of_resolvent_eq_smul {μ ν : 𝕜} (hμ : μ ∈ resolventSet A) (hν : ν ≠ 0)
    {x : E} (hx : resolvent A μ x = ν • x) :
    ∃ h : x ∈ A.domain, A ⟨x, h⟩ = (μ - ν⁻¹) • x := by
  have hxd : x ∈ A.domain := by
    have h1 := resolvent_mem_domain hμ x
    rw [hx] at h1
    have h2 := A.domain.smul_mem ν⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hν, one_smul] at h2
  refine ⟨hxd, ?_⟩
  have h2 := sub_resolvent hμ x
  have h3 : A ⟨resolvent A μ x, resolvent_mem_domain hμ x⟩ = ν • A ⟨x, hxd⟩ := by
    rw [← LinearPMap.map_smul]
    congr 1
    exact Subtype.ext hx
  rw [h3, hx] at h2
  have h4 : ν • A ⟨x, hxd⟩ = ν • ((μ - ν⁻¹) • x) := by
    rw [smul_smul, mul_sub, mul_inv_cancel₀ hν, sub_smul, one_smul, mul_comm, mul_smul]
    linear_combination (norm := module) -h2
  exact smul_right_injective E hν h4

/-- **Root spaces do not depend on the resolvent point**: the generalised eigenspace of `R(μ)` at
`ν` lies in the generalised eigenspace of `R(μ')` at `ν / (1 + (μ' - μ) ν)`, since
`R(μ') - ν' = (1 - (μ' - μ) ν') (R(μ) - ν) (1 + (μ' - μ) R(μ))⁻¹` with commuting factors (and the
space is `0` when `1 + (μ' - μ) ν = 0`). -/
theorem maxGenEigenspace_resolvent_le {μ μ' : 𝕜} (hμ : μ ∈ resolventSet A)
    (hμ' : μ' ∈ resolventSet A) (ν : 𝕜) :
    Module.End.maxGenEigenspace ((resolvent A μ : E →L[𝕜] E) : Module.End 𝕜 E) ν ≤
      Module.End.maxGenEigenspace ((resolvent A μ' : E →L[𝕜] E) : Module.End 𝕜 E)
        (ν / (1 + (μ' - μ) * ν)) := by
  set R : Module.End 𝕜 E := ((resolvent A μ : E →L[𝕜] E) : Module.End 𝕜 E) with hR
  set R' : Module.End 𝕜 E := ((resolvent A μ' : E →L[𝕜] E) : Module.End 𝕜 E) with hR'
  have hid : R - R' = (μ' - μ) • (R * R') := by
    ext y
    have := DFunLike.congr_fun (resolvent_sub_resolvent hμ hμ') y
    simpa [hR, hR'] using this
  have hcomm : Commute R R' := by
    ext y
    have := DFunLike.congr_fun (resolvent_comm hμ hμ') y
    simpa [hR, hR'] using this
  have hkey : (1 - (μ' - μ) • R') * (R - ν • 1) = (1 + (μ' - μ) * ν) • R' - ν • 1 := by
    have h1 : (μ' - μ) • (R' * R) = R - R' := by rw [← hcomm.eq, hid]
    have h2 : (1 - (μ' - μ) • R') * (R - ν • 1) =
        R - ν • 1 - ((μ' - μ) • (R' * R) - ((μ' - μ) * ν) • R') := by
      rw [sub_mul, one_mul, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_one,
        smul_smul]
    rw [h2, h1]
    module
  have hc : Commute (1 - (μ' - μ) • R') (R - ν • 1) :=
    (Commute.one_left _).sub_left
      ((hcomm.symm.sub_right ((Commute.one_right R').smul_right ν)).smul_left (μ' - μ))
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have h0 : (((1 + (μ' - μ) * ν) • R' - ν • 1) ^ k) x = 0 := by
    rw [← hkey, hc.mul_pow, Module.End.mul_apply, hk, map_zero]
  by_cases h1 : 1 + (μ' - μ) * ν = 0
  · have hν : ν ≠ 0 := by
      rintro rfl
      simp at h1
    rw [h1, zero_smul, zero_sub, ← neg_smul, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply] at h0
    have hx0 : x = 0 := (smul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (neg_ne_zero.2 hν))
    exact ⟨0, by simp [hx0]⟩
  · refine ⟨k, ?_⟩
    have e : (1 + (μ' - μ) * ν) • R' - ν • 1 =
        (1 + (μ' - μ) * ν) • (R' - (ν / (1 + (μ' - μ) * ν)) • 1) := by
      rw [smul_sub, smul_smul, mul_div_cancel₀ _ h1]
    rw [e, smul_pow, LinearMap.smul_apply] at h0
    exact (smul_eq_zero.1 h0).resolve_left (pow_ne_zero _ h1)

/-- The span of the root vectors of `R(μ)` does not depend on `μ ∈ ρ(A)` (one inclusion; swap
`μ` and `μ'` for the other). -/
theorem iSup_maxGenEigenspace_resolvent_le {μ μ' : 𝕜} (hμ : μ ∈ resolventSet A)
    (hμ' : μ' ∈ resolventSet A) :
    (⨆ ν : 𝕜, Module.End.maxGenEigenspace ((resolvent A μ : E →L[𝕜] E) : Module.End 𝕜 E) ν) ≤
      ⨆ ν : 𝕜, Module.End.maxGenEigenspace ((resolvent A μ' : E →L[𝕜] E) : Module.End 𝕜 E) ν :=
  iSup_le fun ν => (maxGenEigenspace_resolvent_le hμ hμ' ν).trans
    (le_iSup (fun ν' => Module.End.maxGenEigenspace
      ((resolvent A μ' : E →L[𝕜] E) : Module.End 𝕜 E) ν') _)

/-- **Completeness of root vectors is independent of the resolvent point**: if the root vectors
of `R(μ)` span a dense subspace, so do those of `R(μ')` for every `μ' ∈ ρ(A)`. -/
theorem dense_iSup_maxGenEigenspace_resolvent {μ μ' : 𝕜} (hμ : μ ∈ resolventSet A)
    (hμ' : μ' ∈ resolventSet A)
    (h : Dense (((⨆ ν : 𝕜, Module.End.maxGenEigenspace
      ((resolvent A μ : E →L[𝕜] E) : Module.End 𝕜 E) ν : Submodule 𝕜 E)) : Set E)) :
    Dense (((⨆ ν : 𝕜, Module.End.maxGenEigenspace
      ((resolvent A μ' : E →L[𝕜] E) : Module.End 𝕜 E) ν : Submodule 𝕜 E)) : Set E) :=
  h.mono (SetLike.coe_subset_coe.2 (iSup_maxGenEigenspace_resolvent_le hμ hμ'))

end Banach

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

variable {A : E →ₗ.[𝕜] E}

/-- **The resolvent of the adjoint**: for densely defined `A` on a Hilbert space, if `R` is the
resolvent of `A` at `μ`, then `R†` is the resolvent of `A†` at `conj μ`. -/
theorem IsResolvent.adjoint (hA : Dense (A.domain : Set E)) {μ : 𝕜} {R : E →L[𝕜] E}
    (hR : IsResolvent A μ R) :
    IsResolvent A.adjoint (starRingEnd 𝕜 μ) (ContinuousLinearMap.adjoint R) := by
  -- `R (A z) = μ R z - z` on `D(A)` and `A (R y) = μ R y - y`.
  have hRA : ∀ z : A.domain, R (A z) = μ • R z - z := fun z => by
    have := hR.2 z
    rw [map_sub, map_smul] at this
    linear_combination (norm := module) -this
  refine ⟨fun y => ?_, fun x => ?_⟩
  · set w : E := starRingEnd 𝕜 μ • ContinuousLinearMap.adjoint R y - y with hw
    have key : ∀ z : A.domain, ⟪w, (z : E)⟫_𝕜 = ⟪ContinuousLinearMap.adjoint R y, A z⟫_𝕜 := by
      intro z
      rw [hw, ContinuousLinearMap.adjoint_inner_left, hRA, inner_sub_left, inner_smul_left,
        RCLike.conj_conj, ContinuousLinearMap.adjoint_inner_left, inner_sub_right,
        inner_smul_right]
    have hdom : ContinuousLinearMap.adjoint R y ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, key⟩
    refine ⟨hdom, ?_⟩
    rw [LinearPMap.adjoint_apply_eq hA (y := ⟨_, hdom⟩) key, hw, sub_sub_cancel]
  · refine ext_inner_right 𝕜 fun v => ?_
    obtain ⟨hv, hAv⟩ := hR.1 v
    have hARv : A ⟨R v, hv⟩ = μ • R v - v := by
      linear_combination (norm := module) -hAv
    have hfa : ⟪A.adjoint x, R v⟫_𝕜 = ⟪(x : E), A ⟨R v, hv⟩⟫_𝕜 :=
      LinearPMap.adjoint_isFormalAdjoint hA x ⟨R v, hv⟩
    rw [ContinuousLinearMap.adjoint_inner_left, inner_sub_left, inner_smul_left,
      RCLike.conj_conj, hfa, hARv, inner_sub_right, inner_smul_right]
    ring

/-- `conj μ ∈ ρ(A†)` for `μ ∈ ρ(A)` (`A` densely defined). -/
theorem mem_resolventSet_adjoint (hA : Dense (A.domain : Set E)) {μ : 𝕜}
    (hμ : μ ∈ resolventSet A) : starRingEnd 𝕜 μ ∈ resolventSet A.adjoint :=
  ⟨_, (isResolvent_resolvent hμ).adjoint hA⟩

/-- `R(conj μ, A†) = R(μ, A)†` for `μ ∈ ρ(A)` (`A` densely defined). -/
theorem resolvent_adjoint (hA : Dense (A.domain : Set E)) {μ : 𝕜}
    (hμ : μ ∈ resolventSet A) :
    resolvent A.adjoint (starRingEnd 𝕜 μ) = ContinuousLinearMap.adjoint (resolvent A μ) :=
  resolvent_eq ((isResolvent_resolvent hμ).adjoint hA)

end Hilbert

section Fredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Fredholm alternative on an invariant subspace**: let `K` be compact with `K†` injective,
and let `N` be a closed `K`-invariant subspace containing no eigenvector of `K` for a nonzero
eigenvalue.  Then `N` is orthogonal to every root vector of `K†`.

Proof idea: `K|_N` is compact on the Banach space `N`, so `(K - ν)|_N` is onto `N` for `ν ≠ 0`
(Mathlib's `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`); hence
`N ⊆ ran (K - conj ν)ᵏ ⊆ (ker (K† - ν)ᵏ)ᗮ`, and `ker (K†)ᵏ = 0`. -/
theorem le_orthogonal_iSup_maxGenEigenspace_adjoint {K : H →L[ℂ] H} (hK : IsCompactOperator K)
    (hinj : Function.Injective (ContinuousLinearMap.adjoint K)) {N : Submodule ℂ H}
    (hN : IsClosed (N : Set H)) (hKN : ∀ x ∈ N, K x ∈ N)
    (heig : ∀ ν : ℂ, ν ≠ 0 → ∀ x ∈ N, K x = ν • x → x = 0) :
    N ≤ (⨆ ν : ℂ, Module.End.maxGenEigenspace
      ((ContinuousLinearMap.adjoint K : H →L[ℂ] H) : Module.End ℂ H) ν)ᗮ := by
  -- `K - μ` maps `N` onto `N` for `μ ≠ 0` (Fredholm alternative for `K|_N`).
  have hsurj : ∀ μ : ℂ, μ ≠ 0 → ∀ x ∈ N, ∃ z ∈ N, (K - μ • 1) z = x := by
    intro μ hμ x hx
    set KN : N →L[ℂ] N := (K.comp N.subtypeL).codRestrict N (fun y => hKN y y.2) with hKNdef
    have hcomp : IsCompactOperator KN :=
      (hK.comp_clm N.subtypeL).codRestrict (fun y => hKN y y.2) hN
    rcases hcomp.hasEigenvalue_or_mem_resolventSet hμ with hev | hres
    · exfalso
      obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
      have h1 : KN v = μ • v := hv.apply_eq_smul
      have h2 : K v = μ • (v : H) := congrArg Subtype.val h1
      exact hv.2 (Subtype.ext (heig μ hμ v v.2 h2))
    · rw [spectrum.mem_resolventSet_iff] at hres
      obtain ⟨u, hu⟩ := hres
      have hz : (algebraMap ℂ (N →L[ℂ] N) μ - KN) ((↑u⁻¹ : N →L[ℂ] N) ⟨x, hx⟩) = ⟨x, hx⟩ := by
        rw [← hu]
        exact DFunLike.congr_fun u.mul_inv ⟨x, hx⟩
      set z : N := (↑u⁻¹ : N →L[ℂ] N) ⟨x, hx⟩
      rw [Algebra.algebraMap_eq_smul_one] at hz
      have hz' : μ • (z : H) - K z = x := congrArg Subtype.val hz
      refine ⟨-(z : H), N.neg_mem z.2, ?_⟩
      rw [sub_apply, smul_apply, one_apply_eq_self, map_neg, smul_neg, ← hz']
      module
  -- Hence `N ⊆ ran (K - μ)ᵏ`.
  have hiter : ∀ μ : ℂ, μ ≠ 0 → ∀ k : ℕ, ∀ x ∈ N, ∃ z, ((K - μ • 1) ^ k) z = x := by
    intro μ hμ k
    induction k with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hsurj μ hμ x hx
      obtain ⟨z, hz⟩ := ih y hy
      exact ⟨z, by rw [pow_succ', ← hyx, ← hz]; rfl⟩
  -- The adjoint of `(K - μ)ᵏ` is `(K† - conj μ)ᵏ`.
  have hadj : ∀ (μ : ℂ) (k : ℕ), ContinuousLinearMap.adjoint ((K - μ • 1) ^ k) =
      (ContinuousLinearMap.adjoint K - starRingEnd ℂ μ • 1) ^ k := by
    intro μ k
    rw [← ContinuousLinearMap.star_eq_adjoint, star_pow, star_sub, star_smul, star_one,
      ContinuousLinearMap.star_eq_adjoint]
    rfl
  -- Powers in `Module.End` and in `H →L[ℂ] H`.
  have hcoe : ∀ (T : H →L[ℂ] H) (c : ℂ) (k : ℕ) (u : H),
      (((T : Module.End ℂ H) - c • 1) ^ k) u = ((T - c • 1) ^ k) u := by
    intro T c k u
    have e : ((T : Module.End ℂ H) - c • 1) = ((T - c • 1 : H →L[ℂ] H) : Module.End ℂ H) := by
      simp
    rw [e, ← ContinuousLinearMap.toLinearMap_pow]
    rfl
  -- `K†` has no root vectors at `0`.
  have hinjk : ∀ k : ℕ, Function.Injective ((ContinuousLinearMap.adjoint K) ^ k) := by
    intro k
    induction k with
    | zero => simpa using Function.injective_id
    | succ k ih =>
      rw [pow_succ]
      exact ih.comp hinj
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.iSup_induction _ (motive := fun u => ⟪u, x⟫_ℂ = 0) hu ?_ ?_ ?_
  · intro ν u hu
    rw [Module.End.mem_maxGenEigenspace] at hu
    obtain ⟨k, hk⟩ := hu
    rw [hcoe] at hk
    by_cases hν : ν = 0
    · subst hν
      have hu0 : u = 0 := by
        apply hinjk k
        rw [map_zero, ← hk]
        simp
      simp [hu0]
    · have hμ : starRingEnd ℂ ν ≠ 0 := by simpa using hν
      obtain ⟨z, hz⟩ := hiter _ hμ k x hx
      rw [← hz, ← ContinuousLinearMap.adjoint_inner_left, hadj, RCLike.conj_conj, hk,
        inner_zero_left]
  · exact inner_zero_left _
  · intro u v hu hv
    rw [inner_add_left, hu, hv, add_zero]

/-- If moreover the root vectors of `K†` are complete, the invariant subspace `N` is `0`. -/
theorem eq_bot_of_dense_iSup_maxGenEigenspace_adjoint {K : H →L[ℂ] H}
    (hK : IsCompactOperator K) (hinj : Function.Injective (ContinuousLinearMap.adjoint K))
    {N : Submodule ℂ H} (hN : IsClosed (N : Set H)) (hKN : ∀ x ∈ N, K x ∈ N)
    (heig : ∀ ν : ℂ, ν ≠ 0 → ∀ x ∈ N, K x = ν • x → x = 0)
    (hdense : Dense (((⨆ ν : ℂ, Module.End.maxGenEigenspace
      ((ContinuousLinearMap.adjoint K : H →L[ℂ] H) : Module.End ℂ H) ν :
        Submodule ℂ H)) : Set H)) :
    N = ⊥ := by
  have hle := le_orthogonal_iSup_maxGenEigenspace_adjoint hK hinj hN hKN heig
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have hx' := hle hx
  rw [Submodule.mem_orthogonal'] at hx'
  exact hdense.eq_zero_of_inner_left ℂ fun v hv => hx' v hv

end Fredholm

end DataDrivenControl
