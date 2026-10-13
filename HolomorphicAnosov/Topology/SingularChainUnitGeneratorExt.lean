import HolomorphicAnosov.Topology.SignedSingularCrossProduct
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-! Extensionality on positive unit generators of native integral singular chains.
Source: Hatcher, Algebraic Topology, pp.108 and 278; the free summand interface is
Mathlib SSet.chainComplex_hom_ext. -/

open CategoryTheory
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- Equality on all positive unit singular generators determines an integral chain morphism.
Source: Hatcher pp.108 and 278, expanded for Mathlib's native lifted coefficients.
Apply coproduct extensionality to each singular-simplex summand. Every lifted integer
is its underlying integer times the lifted unit. The inclusion and both linear maps
preserve this scalar multiplication, so equality on the unit implies equality on the
whole summand. The argument applies in degree zero and to an empty simplex set. -/
theorem singularChain_unitGenerator_ext (X : TopCat.{u}) (p : ℕ)
    (M : ModuleCat.{u} ℤ) (f g : Chain X p ⟶ M)
    (h : ∀ σ : Simplex X p,
      f (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up 1)) =
      g (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up 1))) : f = g := by
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z⟩ := z
  have hz : (ULift.up z : ULift.{u} ℤ) = z • (ULift.up 1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  change f (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up z)) =
    g (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up z))
  rw [hz]
  simpa only [map_zsmul] using congrArg (fun t ↦ z • t) (h σ)


end HolomorphicAnosov.Topology
