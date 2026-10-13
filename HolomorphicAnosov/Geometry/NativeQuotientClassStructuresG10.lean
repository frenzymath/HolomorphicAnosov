import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Geometry.ComplexToRealManifold

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- The quotient classes of a native leaf partition inherit intrinsic topologies and real atlases
with point-preserving diffeomorphisms to the native leaves. Their inclusions are smooth
immersions with the prescribed tangent images. (HPS, p. 116) -/
theorem native_quotient_class_structures_g10 {s : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin s → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (L i)]
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (F : HPS.LeafPartition P ι L (fun _ ↦ s)) (R : Setoid M)
    (hR : ∀ x y, R x y ↔ ∃ i a b,
      (F.leaf i).inclusion a = x ∧ (F.leaf i).inclusion b = y)
    (q : Quotient R) :
    ∃ topology : TopologicalSpace (IntrinsicFoliationLeaf R q), letI := topology
      ∃ charts : ChartedSpace (Fin s → ℝ) (IntrinsicFoliationLeaf R q), letI := charts
        IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (IntrinsicFoliationLeaf R q) ∧
        ConnectedSpace (IntrinsicFoliationLeaf R q) ∧
        ContMDiff 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) ∞
          (Subtype.val : IntrinsicFoliationLeaf R q → M) ∧
        (∀ z : IntrinsicFoliationLeaf R q,
          Manifold.IsImmersionAt 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) ∞ Subtype.val z) ∧
        (∀ z : IntrinsicFoliationLeaf R q, LinearMap.range
          (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, E) Subtype.val z).toLinearMap = P z.val) ∧
        ∃ i : ι, ∃ e : Diffeomorph 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ, Fin s → ℝ)
          (L i) (IntrinsicFoliationLeaf R q) ∞,
          ∀ z : L i, (e z).val = (F.leaf i).inclusion z := by
  classical
  obtain ⟨i, x, hx⟩ := F.cover q.out
  have hrange : Set.range (F.leaf i).inclusion = {y | Quotient.mk R y = q} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have h := (hR ((F.leaf i).inclusion z) q.out).mpr ⟨i, z, x, rfl, hx⟩
      exact (Quotient.sound h).trans q.out_eq
    · intro hy
      have h : R y q.out := Quotient.exact (hy.trans q.out_eq.symm)
      obtain ⟨j, a, b, ha, hb⟩ := (hR y q.out).mp h
      have hji : j = i := F.disjoint j i b x (hb.trans hx.symm)
      subst j
      exact ⟨a, ha⟩
  obtain ⟨topology, h, hh⟩ := native_carrier_homeomorph_g15
    (F.leaf i).inclusion (F.leaf i).injective {y | Quotient.mk R y = q} hrange
  let := topology
  let := (F.leaf i).connected
  obtain ⟨charts, hm, e, he⟩ := carrier_smooth_transport_g15 (r := s) h.symm
  let := charts
  let := hm
  have hval : (Subtype.val : IntrinsicFoliationLeaf R q → M) =
      (F.leaf i).inclusion ∘ e := by
    funext z
    rw [Function.comp_apply, he]
    simpa using hh (h.symm z)
  have he' : ∀ z : L i, (e.symm z).val = (F.leaf i).inclusion z := by
    intro z
    have hz := congrFun hval (e.symm z)
    simpa using hz
  have ht := carrier_tangent_image_g15 𝓘(ℝ, E) (F.leaf i).inclusion
    (F.leaf i).immersion.contMDiff {y | Quotient.mk R y = q} e.symm he' P (F.leaf i).tangent
  refine ⟨topology, charts, hm, h.connectedSpace_iff.mp (F.leaf i).connected,
    ht.1, ?_, ht.2, i, e.symm, he'⟩
  intro z
  rw [hval]
  exact immersion_precompose_diffeomorph_g15 𝓘(ℝ, E) (F.leaf i).inclusion e z
    ((F.leaf i).immersion.isImmersionAt (e z))



end HolomorphicAnosov
