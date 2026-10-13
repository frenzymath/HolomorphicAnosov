import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction
import HolomorphicAnosov.Topology.CWComplex.AttachmentTower

/-!
# Original cells of a finite attachment tower

Source: Hatcher, *Algebraic Topology*, Appendix pp.519–520, the original
zero-cells, attached open disks, characteristic maps, and their boundary images.
This module defines DAG node `topo.def_finite_attachment_cells_g2`.
-/

noncomputable section

open scoped TopCat

universe u

namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Original cell labels indexed by their dimension and the actual tower.

Source: Hatcher, Appendix pp.519–520. A zero-stage point labels a zero-cell;
each attachment retains preceding labels with unchanged dimension and adds
one new label of the attachment dimension for each attached disk. These are
labels of the original construction, independent of any categorical CW witness.
Empty zero-stages and empty attachment families contribute no new labels.
-/
inductive Cell : {d : ℕ} → {X : TopCat.{u}} → Tower d X → ℕ → Type (u + 1)
  | point {X : TopCat.{u}} {finite : Finite X} {discrete : DiscreteTopology X} (x : X) :
      Cell (Tower.points X finite discrete) 0
  | old {d n : ℕ} {X : TopCat.{u}} {T : Tower d X} {k : ℕ}
      {a : Fin k → C(∂𝔻 (d + 1), X)} (c : Cell T n) : Cell (T.attach k a) n
  | fresh {d : ℕ} {X : TopCat.{u}} {T : Tower d X} {k : ℕ}
      {a : Fin k → C(∂𝔻 (d + 1), X)} (i : Fin k) : Cell (T.attach k a) (d + 1)

/-- The original characteristic disk map, followed by all later quotient inclusions.

Source: Hatcher, Appendix p.519. For a zero-cell the zero-disk maps constantly
to its labeled point. A new cell uses its original disk quotient projection;
a retained cell's map is followed by the old-space projection at the next stage.
No boundary injectivity or embedding certificate is included in this definition.
-/
def characteristic : {d : ℕ} → {X : TopCat.{u}} → {T : Tower d X} →
    {n : ℕ} → Cell T n → 𝔻 n → X
  | _, _, _, _, .point x => fun _ ↦ x
  | _, _, _, _, .old c => fun z ↦ oldInclusion (characteristic c z)
  | _, _, _, _, .fresh i => newCharacteristic i

/-- The image of the original open disk under its characteristic map.
Source: Hatcher, Appendix p.519. This is the open cell, rather than its closure. -/
def openCell {d : ℕ} {X : TopCat.{u}} {T : Tower d X} {n : ℕ} (c : Cell T n) : Set X :=
  Set.range (fun z : 𝔹 n ↦ characteristic c (TopCat.ballInclusion n z))

/-- The image of the original disk boundary, retaining any self-identifications.
Source: Hatcher, Appendix pp.519–520. The zero-cell boundary is empty. -/
def boundaryImage {d : ℕ} {X : TopCat.{u}} {T : Tower d X} {n : ℕ}
    (c : Cell T n) : Set X :=
  Set.range (fun z : ∂𝔻 n ↦ characteristic c (TopCat.diskBoundaryInclusion n z))

end HolomorphicAnosov.FiniteCellAdjunction
