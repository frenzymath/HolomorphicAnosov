import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallImage
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicInteriorFiber
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCellPreimageLowerSkeleton
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.AttachmentMapIsQuotientMap
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.IsOpenSkeletonCollar

/-!
# Inner-ball open cover for characteristic-cell excision

Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217, the
characteristic-map excision reduction, and Appendix A.2 p.521.
-/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- Hatcher p.217 and Appendix A.2 p.521: inner balls miss all attaching
boundaries. Equal characteristic images therefore have unique interior
representatives, so their full disk preimages are exactly the inner balls.
The attachment quotient tests openness by these disk preimages and the empty
lower-skeleton preimage. Surjectivity of attachment and the inequalities
one half less than three quarters show the inner balls and outer collar cover.
This includes degree zero and an empty family of cells. -/
theorem innerBallImage_geometry [CWComplex.Finite (univ : Set X)] (m : ℕ) :
    Disjoint (lowerSkeleton X m) (innerBallImage X m) ∧
    (∀ i, (characteristicCell X m i) ⁻¹' innerBallImage X m =
      {z | ‖z.down.1‖ < (3 / 4 : ℝ)}) ∧
    IsOpen (innerBallImage X m) ∧ skeletonCollar X m ∪ innerBallImage X m = univ := by
  have hnot (z : CellDisk.{u} m) (hz : ‖z.down.1‖ < (3 / 4 : ℝ)) :
      z ∉ cellBoundary m := by
    intro hb
    have hn : ‖z.down.1‖ = 1 := by
      simpa only [cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using hb
    linarith
  have hdis : Disjoint (lowerSkeleton X m) (innerBallImage X m) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨i, z, hz, rfl⟩
    exact hnot z hz ((Set.ext_iff.mp (characteristicCell_preimage_lowerSkeleton X m i) z).mp hx)
  have hpre : ∀ i, (characteristicCell X m i) ⁻¹' innerBallImage X m =
      {z | ‖z.down.1‖ < (3 / 4 : ℝ)} := by
    intro i
    ext z
    constructor
    · rintro ⟨j, w, hw, he⟩
      have hz : z ∉ cellBoundary m := by
        intro hb
        exact Set.disjoint_left.mp hdis (characteristicCell_mapsTo X m i hb)
          ⟨j, w, hw, he⟩
      have heq := characteristic_interior_fiber X m j i w z (hnot w hw) hz he
      have hwz : w = z := congrArg (fun a ↦ a.2) heq
      exact hwz ▸ hw
    · intro hz
      exact ⟨i, z, hz, rfl⟩
  refine ⟨hdis, hpre, ?_, ?_⟩
  · apply (attachmentMap_isQuotientMap X m).isCoinducing.isOpen_preimage.mp
    rw [isOpen_sum_iff]
    constructor
    · have he : Sum.inl ⁻¹' ((attachmentMap X m) ⁻¹' innerBallImage X m) = ∅ := by
        ext z
        exact iff_false_intro (Set.disjoint_left.mp hdis z.2)
      rw [he]
      exact isOpen_empty
    · rw [isOpen_sigma_iff]
      intro i
      change IsOpen ((characteristicCell X m i) ⁻¹' innerBallImage X m)
      rw [hpre]
      exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, rfl⟩ := attachmentMap_surjective X m x
    rcases a with a | ⟨i, z⟩
    · exact Or.inl (Or.inl a.2)
    · by_cases hz : ‖z.down.1‖ < (3 / 4 : ℝ)
      · exact Or.inr ⟨i, z, hz, rfl⟩
      · exact Or.inl (Or.inr ⟨⟨i, ⟨z, by linarith⟩⟩, rfl⟩)

end HolomorphicAnosov.CharacteristicCellComparison
