import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Algebra.Homology.HomologySequence
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- The explicit quotient maps associated to a short exact cochain row have exact
image/kernel at each degree. This transports Mathlib homology exactness through
the canonical `moduleCatHomologyIso` used by the project quotient definition.
Source: Hatcher, *Algebraic Topology*, pp.199–200, together with Mathlib's
short-exact homology sequence. -/
theorem cochain_quotient_exact_of_shortExact (R : Type u) [CommRing R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ))
    (hS : S.ShortExact) (n : ℕ) :
    LinearMap.range (quotientMap R S.f n).hom =
      LinearMap.ker (quotientMap R S.g n).hom := by
  have hz : quotientMap R S.f n ≫ quotientMap R S.g n = 0 := by
    simp only [quotientMap, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (HomologicalComplex.homologyMap S.f n),
      ← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
    simp
  let T := ShortComplex.mk (quotientMap R S.f n) (quotientMap R S.g n) hz
  let U := S.map (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
  have hu : U.Exact := hS.homology_exact₂ n
  have e : U ≅ T := ShortComplex.isoMk
    (S.X₁.sc n).moduleCatHomologyIso (S.X₂.sc n).moduleCatHomologyIso
    (S.X₃.sc n).moduleCatHomologyIso (by simp [T, U, quotientMap])
    (by simp [T, U, quotientMap])
  exact (ShortComplex.exact_of_iso e hu).moduleCat_range_eq_ker
end HolomorphicAnosov.SingularCochain

