import HolomorphicAnosov.Topology.GallierXuFaceMapGenerators

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- An injective face chart with the prescribed native side values has exactly
the canonical side representative over a prescribed edge point. This is the
edge-interior calculation in Lee Proposition 6.14, p.173, with the boundary
parameters of Gallier–Xu Proposition 3.2, p.31. Compare q x with the canonical
side value and apply injectivity on the same face. The argument also includes
endpoint parameters. -/
lemma face_map_eq_side_of_edge_value {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hinj : ∀ f, Function.Injective (fun z : Disk ↦ q (f, z)))
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t)
    (x : FaceDisks (trianglePresentation K o))
    (i : Fin ((trianglePresentation K o).get x.1).length)
    {u v : Fin N} {t : ℝ} (huv : u ≠ v) (ht : t ∈ Icc (0 : ℝ) 1)
    (hl : (((trianglePresentation K o).get x.1).get i).1 = edgeLabel u v)
    (hx : (q x : Fin N → ℝ) = originalEdgePoint u v t) :
    x.2 = sidePointDisk x.1 i t := by
  apply hinj x.1
  exact Subtype.ext (hx.trans (hside x.1 i u v t huv ht hl).symm)

/-- If a common geometric value is on an edge appearing in both original face
words, equality of face-map images is one literal edge-identification step.
Source: Lee Proposition 6.14, p.173. Recover each canonical representative by
face injectivity and prescribed boundary values, then use the defining
edgeIdentification witness at the same label and interval parameter. -/
lemma face_map_edge_value_identification {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hinj : ∀ f, Function.Injective (fun z : Disk ↦ q (f, z)))
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t)
    {x y : FaceDisks (trianglePresentation K o)}
    (hxy : q x = q y)
    (i : Fin ((trianglePresentation K o).get x.1).length)
    (j : Fin ((trianglePresentation K o).get y.1).length)
    {u v : Fin N} {t : ℝ} (huv : u ≠ v) (ht : t ∈ Icc (0 : ℝ) 1)
    (hi : (((trianglePresentation K o).get x.1).get i).1 = edgeLabel u v)
    (hj : (((trianglePresentation K o).get y.1).get j).1 = edgeLabel u v)
    (hx : (q x : Fin N → ℝ) = originalEdgePoint u v t) :
    edgeIdentification (trianglePresentation K o) x y := by
  have hy : (q y : Fin N → ℝ) = originalEdgePoint u v t := by rw [← hxy]; exact hx
  refine ⟨i, j, t, ht, hi.trans hj.symm, ?_, ?_⟩
  · exact congrArg Subtype.val (face_map_eq_side_of_edge_value K o q hinj hside x i huv ht hi hx)
  · exact congrArg Subtype.val (face_map_eq_side_of_edge_value K o q hinj hside y j huv ht hj hy)

end HolomorphicAnosov.Topology.GallierXu
