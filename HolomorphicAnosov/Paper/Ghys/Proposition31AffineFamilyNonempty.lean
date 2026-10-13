import HolomorphicAnosov.Ghys.AffineCompleteness
import HolomorphicAnosov.Paper.Ghys.NativeInvariantJetAffineFamilyExistenceG1
import HolomorphicAnosov.Paper.Ghys.NativeInvariantAffinePresentationG1

/-! On a nonempty compact holomorphic Anosov manifold, the intrinsic unstable leaves carry a unique
invariant complete affine family continuous along stable holonomy. (Ghys, Prop.3.1 and Lemmas
3.2–3.3) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- On a nonempty compact manifold with complex unstable rank one, an intrinsic foliation
presentation admits a unique affine family invariant under `f` and continuous along stable
holonomy, with complete leaf structures. (Ghys, Prop.3.1 and Lemmas 3.2–3.3) -/
theorem proposition31_affine_family_nonempty
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    letI := P.realCharts
    ∃ A : AffineUnstableLeafStructures P.foliations P.complexLeaves,
      A.ActsAffinely P.foliations P.complexLeaves f ∧
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves ∧
      (∀ B : AffineUnstableLeafStructures P.foliations P.complexLeaves,
        B.ActsAffinely P.foliations P.complexLeaves f →
        B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves → B = A) ∧
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ComplexAffineStructure.Complete
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q)) := by
  obtain ⟨ι, L, top, h⟩ := native_invariant_jet_affine_family_exists_g1 f a hRank
  let := top
  obtain ⟨realChart, h⟩ := h
  let := realChart
  obtain ⟨realSmooth, h⟩ := h
  let := realSmooth
  obtain ⟨U, complexChart, h⟩ := h
  let := complexChart
  obtain ⟨complexSmooth, ⟨G⟩⟩ := h
  let := complexSmooth
  exact native_invariant_affine_family_on_presentation_g1 f a P L U G
    (fun i ↦ (affine_completeness f a L U G i).1)


end HolomorphicAnosov.Ghys
