import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationOneBoundary
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformationFixed
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CollarDeformation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.DiskCollar
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.CellBoundary

/-! Hatcher, Algebraic Topology, Proposition 2.22 p.124 and Proposition 3.17 p.217:
radial retraction from one open disk collar to its boundary. -/

open Set _root_.Topology
universe u
noncomputable section
namespace HolomorphicAnosov.CharacteristicCellComparison

/-- The time-one radial deformation is the continuous boundary retraction on one
characteristic disk collar.

Source: Hatcher, Algebraic Topology, Proposition 2.22 p.124 and Proposition 3.17
p.217. Evaluate the existing continuous collar deformation at time one. Its
boundary endpoint theorem permits the codomain restriction to the boundary
subtype. The projection to the disk followed by this subtype restriction is
continuous. In dimension zero both the collar and boundary are empty, so the
same construction remains defined. -/
def cellBoundaryRetraction (m : ℕ) :
    C(DiskCollar.{u} m, ↥(cellBoundary m)) where
  toFun z := ⟨(collarDeformation m (1, z)).1, collarDeformation_one_boundary m z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hpair : Continuous (fun z : DiskCollar.{u} m =>
        ((1 : unitInterval), z)) := continuous_const.prodMk continuous_id
    exact (collarDeformation m).continuous.subtype_val.comp hpair

/-- The boundary retraction preserves every boundary point.

Source: Hatcher, Algebraic Topology, Proposition 2.22 p.124 and Proposition 3.17
p.217, radial collar deformation. Subtype extensionality reduces the equality
to its disk values. Apply the existing theorem that the collar deformation fixes
every boundary point, specialized to time one. -/
theorem cellBoundaryRetraction_fixed (m : ℕ) (z : DiskCollar.{u} m)
    (hz : z.1 ∈ cellBoundary m) :
    cellBoundaryRetraction m z = ⟨z.1, hz⟩ := by
  apply Subtype.ext
  change (collarDeformation m (1, z)).1 = z.1
  exact congrArg Subtype.val (collarDeformation_fixed m 1 z hz)

/-- The same retraction after ordinary product with an arbitrary topological Y.

Source: Hatcher, Algebraic Topology, Proposition 3.17 p.217, characteristic-disk
collar comparison after taking products. The continuous product map uses the
boundary retraction in the first coordinate and the identity in the second;
there is no separation, compactness or nonemptiness assumption on Y. -/
def cellBoundaryRetractionProd (m : ℕ) (Y : Type u) [TopologicalSpace Y] :
    C(DiskCollar.{u} m × Y, ↥(cellBoundary m) × Y) :=
  (cellBoundaryRetraction m).prodMap (ContinuousMap.id Y)

end HolomorphicAnosov.CharacteristicCellComparison
