import HolomorphicAnosov.AlgebraicTopology.SingularCohomologyDeformationRetraction
import Mathlib.Topology.Homotopy.Basic

/-! # Cohomology of an ordinary product deformation retraction

Source: Hatcher, *Algebraic Topology*, homotopy invariance p.201 and
the characteristic-cell product excision argument in Proposition 3.17, p.217.
-/

open CategoryTheory
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- The product with an arbitrary topological space of a deformation-retract
inclusion induces a cohomology isomorphism with any commutative coefficients.

Agent product construction for Hatcher, *Algebraic Topology*, pp.201 and217.
Proof: take the product
of the retraction and the identity of Y. The retraction identity holds
componentwise, and the given deformation times the constant identity homotopy
is a homotopy of the other composite to the identity in the ordinary product
topology. Apply cohomology invariance of the resulting deformation retraction.
No local compactness, nonemptiness, or CW topology assumption on Y is needed. -/
theorem cohomologyPullback_prod_isIso_of_deformationRetraction
    (R : Type u) [CommRing R] {A U : TopCat.{u}}
    (i : A ⟶ U) (r : U ⟶ A) (hri : i ≫ r = 𝟙 A)
    (H : TopCat.Homotopy (𝟙 U) (r ≫ i))
    (Y : Type u) [TopologicalSpace Y] (n : ℕ) :
    IsIso (cohomologyPullback R
      (TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y))) n) := by
  let ip : TopCat.of (A × Y) ⟶ TopCat.of (U × Y) :=
    TopCat.ofHom (i.hom.prodMap (ContinuousMap.id Y))
  let rp : TopCat.of (U × Y) ⟶ TopCat.of (A × Y) :=
    TopCat.ofHom (r.hom.prodMap (ContinuousMap.id Y))
  have hpr : ip ≫ rp = 𝟙 _ := by
    ext z : 1
    apply Prod.ext
    · exact congrArg (fun f : A ⟶ A ↦ f z.1) hri
    · rfl
  let Hp : TopCat.Homotopy (𝟙 (TopCat.of (U × Y))) (rp ≫ ip) := {
    toFun := fun z ↦ (H (z.1, z.2.1), z.2.2)
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
    map_zero_left := by intro z; exact Prod.ext (H.map_zero_left z.1) rfl
    map_one_left := by intro z; exact Prod.ext (H.map_one_left z.1) rfl }
  exact cohomologyPullback_isIso_of_deformationRetraction R ip rp hpr Hp n

end HolomorphicAnosov.SingularCochain

