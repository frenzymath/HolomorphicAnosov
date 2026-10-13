import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction
import HolomorphicAnosov.Topology.CWComplex.AttachmentTower

/-!
# Original stages of a finite disk-attachment tower

Source: Hatcher, *Algebraic Topology*, Appendix printed p.519: the spaces
X⁰, X¹, … retain their original quotient topologies, and their maps into later
stages are the composites of the original old-space quotient maps.
DAG node: `topo.def_finite_attachment_skeleton_g2`.

This datatype identifies an intermediate stage of a given tower together with
its dimension and its original bundled topological space. It supplies no
embedding, continuity, Hausdorffness or CW conclusion. The tower itself allows
empty spaces, empty attachment families and noninjective attaching maps.
-/

noncomputable section

open scoped TopCat

universe u

namespace HolomorphicAnosov.FiniteCellAdjunction

/-- An original preceding skeleton, retaining its dimension and topology.
Source: Hatcher, Appendix printed p.519. `last` selects the current endpoint;
`previous` retains an earlier selection after one further disk attachment.
The zero-stage is included; no cells or additional geometric witnesses occur.
-/
inductive Stage : {d : ℕ} → {X : TopCat.{u}} → Tower d X → ℕ → TopCat.{u} → Type (u + 1)
  | last {d : ℕ} {X : TopCat.{u}} (T : Tower d X) : Stage T d X
  | previous {d m : ℕ} {X Y : TopCat.{u}} {T : Tower d X} {k : ℕ}
      {a : Fin k → C(∂𝔻 (d + 1), X)} (S : Stage T m Y) : Stage (T.attach k a) m Y

/-- The composite of the original quotient maps from a selected stage.
Source: Hatcher, Appendix printed p.519. At the current endpoint it is the
identity; passing through a later attachment composes with `oldInclusion`.
The definition does not assume that these maps are embeddings or continuous.
-/
def stageInclusion : {d : ℕ} → {X : TopCat.{u}} → {T : Tower d X} →
    {m : ℕ} → {Y : TopCat.{u}} → Stage T m Y → Y → X
  | _, _, _, _, _, .last _ => id
  | _, _, _, _, _, .previous S => fun y ↦ oldInclusion (stageInclusion S y)

end HolomorphicAnosov.FiniteCellAdjunction
