import HolomorphicAnosov.Topology.CWComplex.AdjunctionOldEmbedding
import HolomorphicAnosov.Topology.CWComplex.AdjunctionOpenCellEmbedding
import HolomorphicAnosov.Topology.CWComplex.AttachmentCells

/-! Embeddings of original open cells. Source: Hatcher, Appendix p.519. -/
open TopCat Topology _root_.Topology
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Original characteristic maps embed their open balls. A zero-ball is a
singleton. A fresh cell uses the quotient interior embedding, and a retained
cell composes its preceding embedding with the old-space closed embedding. -/
theorem characteristic_openCell_isEmbedding {d : ℕ} {X : TopCat.{u}}
    {T : Tower d X} {n : ℕ} (c : Cell T n) :
    IsEmbedding (fun z : 𝔹 n ↦ characteristic c (ballInclusion n z)) := by
  induction c with
  | point x =>
    let : Subsingleton (TopCat.ball.{u} 0) := by unfold TopCat.ball; infer_instance
    exact IsEmbedding.of_subsingleton _
  | old c ih => exact adjunction_old_isClosedEmbedding.isEmbedding.comp ih
  | fresh i => exact (adjunction_new_openCell_isOpenEmbedding i).isEmbedding

end HolomorphicAnosov.FiniteCellAdjunction
