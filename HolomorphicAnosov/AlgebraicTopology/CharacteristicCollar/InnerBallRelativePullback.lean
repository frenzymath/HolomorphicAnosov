import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallCharacteristic
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollar
import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallHomeomorph
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyHomeomorph

/-! The inner-ball side of the characteristic excision square.
Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217 and pp.199–201.
The asserted map is the canonical relative pullback, without an excision premise. -/

open CategoryTheory Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
open SingularCochain

/-- The actual inner characteristic map induces relative cohomology isomorphisms
for the inner-annulus pairs, also after ordinary product with any topological Y.

Source: Hatcher p.217. The proved characteristic homeomorphism has precisely this
forward map and identifies the inner annulus with the collar intersection.
Apply the canonical relative pullback theorem for pair homeomorphisms.
Its product with the identity has the exact characteristic-product formula,
so the same argument works on the ordinary product without restrictions on Y. -/
theorem innerBallCharacteristic_relative_pullback_isIso
    (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (R : Type u) [CommRing R] (m k : ℕ) :
    ∃ hpair : MapsTo (innerBallCharacteristic X m)
        {z | (1 / 2 : ℝ) < ‖z.1.2.down.1‖}
        {z | z.1 ∈ skeletonCollar X m},
      IsIso (relativeCohomologyPullback R (TopCat.ofHom (innerBallCharacteristic X m)) hpair k) ∧
      ∀ (Y : Type u) (_ : TopologicalSpace Y),
        ∃ hprod : MapsTo ((innerBallCharacteristic X m).prodMap (ContinuousMap.id Y))
            {z | (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖}
            {z | z.1.1 ∈ skeletonCollar X m},
          IsIso (relativeCohomologyPullback R
            (TopCat.ofHom ((innerBallCharacteristic X m).prodMap (ContinuousMap.id Y))) hprod k) := by
  let V0 := ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
    ‖z.2.down.1‖ < (3 / 4 : ℝ)}
  let V := ↥(innerBallImage X m)
  obtain ⟨e, he, hpair, hprod⟩ := characteristic_innerBall_homeomorph X m
  have heq : (e : C(_, _)) = innerBallCharacteristic X m := by
    ext z : 1
    exact Subtype.ext (he z)
  have hp : MapsTo (innerBallCharacteristic X m)
      {z | (1 / 2 : ℝ) < ‖z.1.2.down.1‖} {z | z.1 ∈ skeletonCollar X m} := by
    intro z hz
    rw [← heq]
    exact (hpair z).mpr hz
  refine ⟨hp, ?_, ?_⟩
  · have h : ∀ hf : MapsTo (e : C(V0, V))
          {z | (1 / 2 : ℝ) < ‖z.1.2.down.1‖} {z | z.1 ∈ skeletonCollar X m},
          IsIso (relativeCohomologyPullback R (X := TopCat.of V0) (Y := TopCat.of V) (A := {z | (1 / 2 : ℝ) < ‖z.1.2.down.1‖}) (B := {z | z.1 ∈ skeletonCollar X m}) (TopCat.ofHom (e : C(V0, V))) hf k) :=
        fun _ ↦ relativeCohomologyPullback_isIso_of_homeomorph R (X := TopCat.of V0) (Y := TopCat.of V)
          {z | (1 / 2 : ℝ) < ‖z.1.2.down.1‖} {z | z.1 ∈ skeletonCollar X m} e
          (fun z ↦ (hpair z).symm) k
    rw [heq] at h
    exact h hp
  · intro Y _
    obtain ⟨ep, hep⟩ := hprod Y inferInstance
    have hepq : (ep : C(_, _)) = (innerBallCharacteristic X m).prodMap (ContinuousMap.id Y) := by
      ext z : 1
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst (hep z).1)
      · exact congrArg (fun p : Skeleton X m × Y ↦ p.2) (hep z).1
    have hpp : MapsTo ((innerBallCharacteristic X m).prodMap (ContinuousMap.id Y))
        {z | (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖} {z | z.1.1 ∈ skeletonCollar X m} := by
      intro z hz
      rw [← hepq]
      exact (hep z).2.mpr hz
    refine ⟨hpp, ?_⟩
    have h : ∀ hf : MapsTo (ep : C(V0 × Y, V × Y))
        {z | (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖} {z | z.1.1 ∈ skeletonCollar X m},
        IsIso (relativeCohomologyPullback R (X := TopCat.of (V0 × Y)) (Y := TopCat.of (V × Y)) (A := {z | (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖}) (B := {z | z.1.1 ∈ skeletonCollar X m}) (TopCat.ofHom (ep : C(V0 × Y, V × Y))) hf k) :=
      fun _ ↦ relativeCohomologyPullback_isIso_of_homeomorph R (X := TopCat.of (V0 × Y)) (Y := TopCat.of (V × Y))
        {z | (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖} {z | z.1.1 ∈ skeletonCollar X m} ep
        (fun z ↦ (hep z).2.symm) k
    rw [hepq] at h
    exact h hpp

end HolomorphicAnosov.CharacteristicCellComparison
