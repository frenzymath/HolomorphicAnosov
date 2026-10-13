import HolomorphicAnosov.Paper.Ghys.NativeAffinePresentationLeafMapG1
import Mathlib.Topology.UniformSpace.Compact

/-! This file identifies the unstable leaves of a supplied presentation with native invariant affine
leaves by point-preserving biholomorphisms. (HPS, §7, pp. 115–116; Ghys, Prop. 3.1, pp. 590–593) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- Every unstable leaf of the supplied presentation is point-preservingly biholomorphic to a native
invariant affine leaf. (HPS, §7, pp. 115–116; Ghys, Prop. 3.1, pp. 590–593) -/
theorem native_affine_presentation_identification_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    : letI := P.realCharts
    ∀ q : Quotient P.foliations.unstablePartition,
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      ∃ (i : ι) (E : Diffeomorph 𝓘(ℂ) (complexModel 1) (L i)
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
        ∀ z, (E z).val = (U.leaf i).inclusion z := by
  classical
  let := P.realCharts
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  obtain ⟨m, hm, hasym⟩ := G.asymptotic
  have hu : m.toUniformSpace = P.metric.toUniformSpace :=
    unique_uniformity_of_compact hm P.metric_topology
  have hrel (x y : M) : @ForwardAsymptotic M m (f.symm : M → M) x y ↔
      @ForwardAsymptotic M P.metric (f.symm : M → M) x y := by
    have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
      (fun n ↦ (((f.symm : M → M)^[n]) y, ((f.symm : M → M)^[n]) x)) atTop
    have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ P.metric.toPseudoMetricSpace
      (fun n ↦ (((f.symm : M → M)^[n]) y, ((f.symm : M → M)^[n]) x)) atTop
    unfold ForwardAsymptotic
    rw [← h₁, ← h₂]
    change Tendsto _ _ m.toUniformSpace.uniformity ↔
      Tendsto _ _ P.metric.toUniformSpace.uniformity
    rw [hu]
  obtain ⟨i, z₀, hz₀⟩ := U.cover q.out
  have hrange (y : M) : (∃ z, (U.leaf i).inclusion z = y) ↔
      Quotient.mk P.foliations.unstablePartition y = q := by
    rw [hasym i z₀ y, hrel, hz₀, ← P.unstable_asymptotic]
    rw [← Quotient.eq]
    exact ⟨fun h ↦ h.symm.trans (Quotient.out_eq q),
      fun h ↦ (Quotient.out_eq q).trans h.symm⟩
  let g : L i → IntrinsicFoliationLeaf P.foliations.unstablePartition q :=
    fun z ↦ ⟨(U.leaf i).inclusion z, (hrange _).mp ⟨z, rfl⟩⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro x y h
      exact (U.leaf i).injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨z, hz⟩ := (hrange y.val).mpr y.property
      exact ⟨z, Subtype.ext hz⟩
  let e := Equiv.ofBijective g hbij
  obtain ⟨E, hE⟩ := native_affine_presentation_leaf_equiv_biholomorphic_g1
    f a P L U G i q e (fun _ ↦ rfl)
  refine ⟨i, E, ?_⟩
  intro z
  change (E.toEquiv z).val = _
  rw [hE]
  rfl

end HolomorphicAnosov.Ghys
