import HolomorphicAnosov.Topology.GallierXuEdgeIdentificationSymm

noncomputable section
namespace HolomorphicAnosov.Topology.GallierXu

/-- Every literal paired-edge witness is a generated quotient relation step. -/
lemma edgeIdentification_eqvGen {P : Presentation} {x y : FaceDisks P}
    (hxy : edgeIdentification P x y) :
    Relation.EqvGen (edgeIdentification P) x y :=
  Relation.EqvGen.rel _ _ hxy

end HolomorphicAnosov.Topology.GallierXu
