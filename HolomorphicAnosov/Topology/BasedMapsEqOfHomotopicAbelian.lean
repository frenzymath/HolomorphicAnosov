import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

universe u v

namespace HolomorphicAnosov.Topology

open CategoryTheory

/-!
# Fundamental-group maps invariant under an unbased homotopy

Source: Hatcher, *Algebraic Topology*, Lemma 1.19 and its proof, pp.37–38.
DAG node: `topo.based_maps_eq_of_homotopic_abelian_g18`.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Homotopic based maps into a space with abelian fundamental group induce the same
based homomorphism, including when the homotopy moves the basepoint.

Source: Hatcher, *Algebraic Topology*, Lemma 1.19, pp.37–38. Its basepoint-trace
naturality equation is implemented by Mathlib's `homotopicMapsNatIso`.

Proof: transport the two endpoint images of the source basepoint to the common target
basepoint using the given equalities. The homotopy trace then gives a loop class t there.
Naturality states that the image of any source loop under f followed by t equals t
followed by its image under g. With Mathlib's reversed path-product convention this is
t * f_*(a) = g_*(a) * t. Commutativity changes the right side to t * g_*(a), and left
cancellation gives equality of the images. Extensionality proves equality of the
homomorphisms. No path connectedness, separation, CW structure, or based homotopy
assumption is used. -/
theorem based_maps_eq_of_homotopic_abelian
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (f g : C(X, Y)) (hf : f x₀ = y₀) (hg : g x₀ = y₀)
    (H : f.Homotopy g)
    (hcomm : ∀ a b : FundamentalGroup Y y₀, a * b = b * a) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  let ef := eqToIso (congrArg FundamentalGroupoid.mk hf)
  let eg := eqToIso (congrArg FundamentalGroupoid.mk hg)
  let T := FundamentalGroupoidFunctor.homotopicMapsNatIso H
  let t : FundamentalGroup Y y₀ := ef.inv ≫ T.app (FundamentalGroupoid.mk x₀) ≫ eg.hom
  ext a
  have hn := T.naturality a
  have he : FundamentalGroup.mapOfEq f hf a ≫ t =
      t ≫ FundamentalGroup.mapOfEq g hg a := by
    change (ef.inv ≫ (FundamentalGroupoid.map f).map a ≫ ef.hom) ≫
        (ef.inv ≫ T.app (FundamentalGroupoid.mk x₀) ≫ eg.hom) =
      (ef.inv ≫ T.app (FundamentalGroupoid.mk x₀) ≫ eg.hom) ≫
        (eg.inv ≫ (FundamentalGroupoid.map g).map a ≫ eg.hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun b ↦ ef.inv ≫ b) (by
      simpa only [Category.assoc] using congrArg (fun b ↦ b ≫ eg.hom) hn)
  change t * FundamentalGroup.mapOfEq f hf a =
    FundamentalGroup.mapOfEq g hg a * t at he
  exact mul_left_cancel (he.trans (hcomm _ _))


end HolomorphicAnosov.Topology
