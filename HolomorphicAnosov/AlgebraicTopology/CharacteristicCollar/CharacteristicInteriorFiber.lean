import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellDisk
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CharacteristicCell

/-! Public characteristic-cell collar construction. Source: Hatcher, Algebraic Topology,
Appendix A.2 p.521, A.4–A.5 pp.522–523, A.17 pp.532–533. -/


open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison
variable (X : Type u) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

/-- In a Hausdorff CW space, equal characteristic-map images of two disk-interior points imply equality of their cell indices and of their lifted disk points.

Proof: Both images lie in their open cells. Equality of the images makes these open cells intersect, forcing equal cell indices by CW disjointness. The characteristic map is injective on the open disk, forcing equal coordinates and thus equal lifted representatives.

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, A.4–A.5 pp.522–523, and A.17 pp.532–533; radial-collar specialization to one skeleton attachment. -/
theorem characteristic_interior_fiber (m : ℕ)
    (i j : RelCWComplex.cell (univ : Set X) m) (z w : CellDisk.{u} m)
    (hz : z ∉ cellBoundary m) (hw : w ∉ cellBoundary m)
    (he : characteristicCell X m i z = characteristicCell X m j w) :
    (⟨i, z⟩ : Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{u} m) = ⟨j, w⟩ := by
  have hbz : z.down.1 ∈ Metric.ball (0 : Fin m → ℝ) 1 :=
    lt_of_le_of_ne z.down.2 hz
  have hbw : w.down.1 ∈ Metric.ball (0 : Fin m → ℝ) 1 :=
    lt_of_le_of_ne w.down.2 hw
  have he' : RelCWComplex.map m i z.down.1 = RelCWComplex.map m j w.down.1 :=
    congrArg Subtype.val he
  have hi : i = j := by
    have hs := CWComplex.eq_of_not_disjoint_openCell (C := (univ : Set X))
      (n := m) (m := m) (j := i) (i := j) (by
        intro hd
        exact Set.disjoint_left.mp hd ⟨z.down.1, hbz, rfl⟩ ⟨w.down.1, hbw, he'.symm⟩)
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs
  subst j
  have hv := (RelCWComplex.map m i).injOn
    (by simpa only [RelCWComplex.source_eq] using hbz)
    (by simpa only [RelCWComplex.source_eq] using hbw) he'
  have hzw : z = w := ULift.ext (Subtype.ext hv)
  subst w
  rfl

end HolomorphicAnosov.CharacteristicCellComparison
