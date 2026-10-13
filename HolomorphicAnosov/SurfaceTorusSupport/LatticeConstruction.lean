import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Basic
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.FullLattice

open scoped Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.SurfaceTorusSupport
/-- An integer submodule of a finite-dimensional real normed space with compact additive quotient
spans the whole real space. (Ghys, p. 600) -/
theorem compact_quotient_real_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E)
    [CompactSpace (E ⧸ Λ.toAddSubgroup)] :
    Submodule.span ℝ (Λ : Set (E)) = ⊤ := by
  by_contra hspan
  obtain ⟨ell, hell, hzero⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hspan) inferInstance
  have hvanish : Λ.toAddSubgroup ≤ ell.toAddMonoidHom.ker := by
    intro z hz
    change ell z = 0
    have hm : ell z ∈ (Submodule.span ℝ (Λ : Set (E))).map ell :=
      ⟨z, Submodule.subset_span hz, rfl⟩
    rw [hzero] at hm
    exact hm
  let descended := QuotientAddGroup.lift Λ.toAddSubgroup ell.toAddMonoidHom hvanish
  have hc : Continuous descended :=
    (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous_iff.mpr
      ell.continuous_of_finiteDimensional
  have hs : Function.Surjective descended := by
    obtain ⟨v, hv⟩ : ∃ v, ell v ≠ 0 := by
      by_contra h
      push Not at h
      exact hell (LinearMap.ext h)
    intro t
    refine ⟨QuotientAddGroup.mk ((t / ell v) • v), ?_⟩
    change ell ((t / ell v) • v) = t
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hcompact : CompactSpace ℝ := hs.compactSpace hc
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) hcompact



/-- The translation subgroup of a covering action conjugate to translations is discrete. (Ghys, p.
600; Hatcher, §1.3, p. 72) -/
theorem translation_range_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U S : Type*} [TopologicalSpace U] [TopologicalSpace S]
    (p : U → S) (hp : IsCoveringMap p) (D : U ≃ₜ E)
    (τ : Additive (deck p) →+ E)
    (hτ : ∀ (g : deck p) u, D (g • u) = D u + τ (Additive.ofMul g)) :
    DiscreteTopology τ.range.toIntSubmodule := by
  let u₀ := D.symm 0
  let e := hp.isLocalHomeomorph.localInverseAt u₀
  let V := D '' e.target
  have hV : IsOpen V := D.isOpenMap _ e.open_target
  have h₀ : (0 : E) ∈ V := by
    exact ⟨u₀, hp.isLocalHomeomorph.self_mem_localInverseAt_target, D.apply_symm_apply 0⟩
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have heq : (Subtype.val : τ.range.toIntSubmodule → E) ⁻¹' V = {0} := by
    ext z
    constructor
    · intro hz
      obtain ⟨g, hg⟩ := z.property
      have hDz : D (Additive.toMul g • u₀) = z.val := by
        rw [hτ]
        simpa [u₀] using hg
      obtain ⟨v, hv, hvz⟩ := hz
      have hv' : v = Additive.toMul g • u₀ := D.injective (hvz.trans hDz.symm)
      have hfixed : Additive.toMul g • u₀ = u₀ :=
        hp.isLocalHomeomorph.injOn_localInverseAt_target
          (hv' ▸ hv) hp.isLocalHomeomorph.self_mem_localInverseAt_target
          (deck.proj_smul _ _)
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      change z.val = 0
      rw [← hDz, hfixed]
      exact D.apply_symm_apply 0
    · rintro rfl
      exact h₀
  rw [← heq]
  exact hV.preimage continuous_subtype_val


/-- A covering of a compact space identified with an additive group induces a compact additive
quotient when covering fibres lie in quotient classes. -/
theorem normalized_quotient_compact
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    {U S : Type*} [TopologicalSpace U] [TopologicalSpace S] [CompactSpace S]
    (p : U → S) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (D : U ≃ₜ E) (Λ : AddSubgroup E)
    (hfib : ∀ u v, p u = p v →
      (QuotientAddGroup.mk (D u) : E ⧸ Λ) = QuotientAddGroup.mk (D v)) :
    CompactSpace (E ⧸ Λ) := by
  classical
  let s := hs.hasRightInverse.choose
  have hs' : Function.RightInverse s p := hs.hasRightInverse.choose_spec
  let h : S → E ⧸ Λ := fun x ↦ QuotientAddGroup.mk (D (s x))
  have hrep (u : U) : h (p u) = QuotientAddGroup.mk (D u) :=
    hfib (s (p u)) u (hs' (p u))
  have hc : Continuous h :=
    (hp.isOpenMap.isQuotientMap hp.continuous hs).continuous_iff.mpr (by
      have heq : h ∘ p = fun u ↦ (QuotientAddGroup.mk (D u) : E ⧸ Λ) := funext hrep
      rw [heq]
      exact continuous_quotient_mk'.comp D.continuous)
  have hsurj : Function.Surjective h := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    refine ⟨p (D.symm z), ?_⟩
    rw [hrep, D.apply_symm_apply]
  exact hsurj.compactSpace hc


/-- The translation subgroup of a covering of a compact space, normalized to `ℂ²` and satisfying the
quotient fibre relation, is a full real lattice. -/
theorem full_lattice_from_normalized_translation
    {U S : Type*} [TopologicalSpace U] [TopologicalSpace S] [CompactSpace S]
    (p : U → S) (hp : IsCoveringMap p) (hs : Function.Surjective p)
    (D : U ≃ₜ ComplexModel 2) (τ : Additive (deck p) →+ ComplexModel 2)
    (hτ : ∀ (g : deck p) u, D (g • u) = D u + τ (Additive.ofMul g))
    (hfib : ∀ u v, p u = p v →
      (QuotientAddGroup.mk (D u) : ComplexModel 2 ⧸ τ.range) = QuotientAddGroup.mk (D v)) :
    ∃ L : FullComplexLattice 2,
      Set.range τ = (L.lattice : Set (ComplexModel 2)) ∧
      Submodule.span ℝ (L.lattice : Set (ComplexModel 2)) = ⊤ := by
  let Λ := τ.range.toIntSubmodule
  let : DiscreteTopology Λ := translation_range_discrete p hp D τ hτ
  let : CompactSpace (ComplexModel 2 ⧸ Λ.toAddSubgroup) :=
    normalized_quotient_compact p hp hs D Λ.toAddSubgroup hfib
  have hfull : Submodule.span ℝ (Λ : Set (ComplexModel 2)) = ⊤ :=
    compact_quotient_real_span Λ
  let L : FullComplexLattice 2 := { lattice := Λ, discrete := inferInstance, full := ⟨hfull⟩ }
  exact ⟨L, rfl, hfull⟩

end HolomorphicAnosov.SurfaceTorusSupport
