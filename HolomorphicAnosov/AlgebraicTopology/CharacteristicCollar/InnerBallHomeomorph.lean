import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallGeometry
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicInteriorFiber
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellMapsTo
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMapIsQuotientMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicPreimageSkeletonCollar
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The inner characteristic balls map homeomorphically onto their image

Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217 and Appendix A.2
p.521. Only disk interior injectivity is used; attaching boundary maps need not
be injective. Products carry their ordinary product topologies.
-/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- The restriction of the characteristic attachment to the disjoint inner balls
is a homeomorphism, and its ordinary product with the identity is a homeomorphism
for every topological space.

Source: Hatcher p.217, using Appendix A.2 p.521. Interior-fibre uniqueness and
the absence of lower-skeleton points in the image show that every attachment
fibre over an inner point is a singleton. The inner source is open in the disk
sum; its inclusion into the attachment sum is open. For any open subset of
that source, the full attachment preimage of its image is exactly its inclusion
into the attachment sum, hence is open. The quotient criterion gives openness
of the restricted characteristic map. It is continuous and bijective by its
definition and interior-fibre uniqueness, so it is a homeomorphism. The exact
collar preimage identifies the intersection pair, and taking its product with
the identity preserves the formula with no condition on the second factor. -/
theorem characteristic_innerBall_homeomorph [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    ∃ e : ↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
        ‖z.2.down.1‖ < (3 / 4 : ℝ)} ≃ₜ ↥(innerBallImage X m),
      (∀ z, (e z).1 = characteristicCell X m z.1.1 z.1.2) ∧
      (∀ z, (e z).1 ∈ skeletonCollar X m ↔ (1 / 2 : ℝ) < ‖z.1.2.down.1‖) ∧
      ∀ (Y : Type u) (_ : TopologicalSpace Y),
        ∃ ep : (↥{z : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m |
            ‖z.2.down.1‖ < (3 / 4 : ℝ)} × Y) ≃ₜ (↥(innerBallImage X m) × Y),
          ∀ z, ((ep z).1.1, (ep z).2) =
            (characteristicCell X m z.1.1.1 z.1.1.2, z.2) ∧
            ((ep z).1.1 ∈ skeletonCollar X m ↔
              (1 / 2 : ℝ) < ‖z.1.1.2.down.1‖) := by
  classical
  let D := Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m
  let V0 : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
  have hV0 : IsOpen V0 := by
    rw [isOpen_sigma_iff]
    intro i
    exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
  obtain ⟨hdis, _, hV, _⟩ := innerBallImage_geometry X m
  let f : C(V0, Skeleton X m) :=
    ⟨fun z ↦ characteristicCell X m z.1.1 z.1.2, by
      have h : Continuous (fun z : D ↦ characteristicCell X m z.1 z.2) :=
        continuous_sigma fun i ↦ (characteristicCell X m i).continuous
      exact h.comp continuous_subtype_val⟩
  let q : C(V0, ↥(innerBallImage X m)) :=
    ⟨fun z ↦ ⟨f z, ⟨z.1.1, z.1.2, z.2, rfl⟩⟩, f.continuous.subtype_mk _⟩
  let inc : V0 → AttachmentSource X m := fun z ↦ Sum.inr z.1
  have hinc : IsOpenMap inc := isOpenMap_inr.comp hV0.isOpenMap_subtype_val
  have hfiber (a : AttachmentSource X m) (z : V0)
      (he : attachmentMap X m a = f z) : a = inc z := by
    have hzmem : f z ∈ innerBallImage X m := (q z).2
    rcases a with a | ⟨j, w⟩
    · have ha : f z ∈ lowerSkeleton X m := he ▸ a.2
      exact (Set.disjoint_left.mp hdis ha hzmem).elim
    · have hw : w ∉ cellBoundary m := by
        intro hw
        have ha : f z ∈ lowerSkeleton X m := he ▸ characteristicCell_mapsTo X m j hw
        exact Set.disjoint_left.mp hdis ha hzmem
      have hz : z.1.2 ∉ cellBoundary m := by
        intro hz
        have hn : ‖z.1.2.down.1‖ = 1 := by
          simpa only [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hz
        have := z.2
        dsimp [V0] at this
        linarith
      exact congrArg Sum.inr (characteristic_interior_fiber X m j z.1.1 w z.1.2 hw hz he)
  have hfopen : IsOpenMap f := by
    intro s hs
    apply (attachmentMap_isQuotientMap X m).isCoinducing.isOpen_preimage.mp
    have he : (attachmentMap X m) ⁻¹' (f '' s) = inc '' s := by
      ext a
      constructor
      · rintro ⟨z, hz, he⟩
        exact ⟨z, hz, (hfiber a z he.symm).symm⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [he]
    exact hinc s hs
  have hqopen : IsOpenMap q := hV.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr hfopen
  have hqbij : Function.Bijective q := by
    constructor
    · intro a b he
      apply Subtype.ext
      exact Sum.inr.inj (hfiber (inc a) b (congrArg Subtype.val he))
    · rintro ⟨y, i, z, hz, he⟩
      exact ⟨⟨⟨i, z⟩, hz⟩, Subtype.ext he⟩
  let e : V0 ≃ₜ ↥(innerBallImage X m) :=
    (Equiv.ofBijective q hqbij).toHomeomorphOfContinuousOpen q.continuous hqopen
  refine ⟨e, fun _ ↦ rfl, ?_, ?_⟩
  · intro z
    exact Set.ext_iff.mp (characteristic_preimage_skeletonCollar X m z.1.1) z.1.2
  · intro Y _
    refine ⟨e.prodCongr (Homeomorph.refl Y), fun z ↦ ⟨rfl, ?_⟩⟩
    exact Set.ext_iff.mp (characteristic_preimage_skeletonCollar X m z.1.1.1) z.1.1.2

end HolomorphicAnosov.CharacteristicCellComparison
