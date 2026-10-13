import HolomorphicAnosov.Topology.GallierXuEdgeIdentificationEqvGen

noncomputable section
namespace HolomorphicAnosov.Topology.GallierXu

/-- Literal paired-edge witnesses have equal projections in the generated disk quotient. -/
lemma project_eq_of_edgeIdentification {P : Presentation}
    {x y : FaceDisks P} (hxy : edgeIdentification P x y) :
    project P x = project P y := by
  exact Quotient.sound (edgeIdentification_eqvGen hxy)

end HolomorphicAnosov.Topology.GallierXu

namespace HolomorphicAnosov.Topology.GallierXu

/-- Projection equality propagates along every generated edge-identification path. -/
lemma project_eq_of_edgeIdentification_eqvGen {P : Presentation}
    {x y : FaceDisks P}
    (hxy : Relation.EqvGen (edgeIdentification P) x y) :
    project P x = project P y := by
  induction hxy with
  | rel x y h => exact project_eq_of_edgeIdentification h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

end HolomorphicAnosov.Topology.GallierXu
