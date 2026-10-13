import HolomorphicAnosov.Ghys.AffineCompleteness
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.JetAffineEquivalence
import HolomorphicAnosov.Paper.Ghys.InvariantJetSection
import HolomorphicAnosov.Paper.Ghys.Proposition31AffineFamilyNonempty
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Paper.Zhang.Anosov

/-! The intrinsic unstable leaves carry a unique invariant complete affine family continuous along
stable holonomy. (Ghys, Prop.3.1) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

universe u

attribute [local instance] complex_isManifold_real

/-- An intrinsic foliation presentation with complex unstable rank one admits a unique affine family
invariant under `f` and continuous along stable holonomy, and every leaf structure is complete.
(Ghys, Prop.3.1 and Lemmas 3.2–3.3) -/
theorem proposition31_affine_family
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
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
  let := P.realCharts
  classical
  by_cases hM : IsEmpty M
  · let := hM
    let : IsEmpty (Quotient P.foliations.unstablePartition) :=
      ⟨fun q => Quotient.inductionOn q (fun x => isEmptyElim x)⟩
    let A : AffineUnstableLeafStructures P.foliations P.complexLeaves := {
      structureAt := fun q ↦ isEmptyElim q }
    refine ⟨A, ?_, ?_, ?_, ?_⟩
    · intro x
      exact isEmptyElim x
    · intro q
      exact isEmptyElim q
    · intro B _ _
      cases B with
      | mk b =>
        have hb : b = A.structureAt := funext fun q ↦ isEmptyElim q
        cases hb
        rfl
    · intro q
      exact isEmptyElim q
  · 
    let : Nonempty M := not_isEmpty_iff.mp hM
    exact proposition31_affine_family_nonempty f a hRank P


end HolomorphicAnosov.Ghys
