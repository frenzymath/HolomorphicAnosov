import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKroneckerRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKroneckerNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackComp
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackId
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateProjection
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateInclusion
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateCycle

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The exact coordinate Kronecker matrix follows from the actual compositions of projections
and inclusions: identity on the chosen coordinate and the constant zero map otherwise. This
proof also applies to n=0, where both quantified families are empty. -/
theorem coordinate_kronecker (n : ℕ)
    (a : SingularCochain.cycles ℚ
      (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1)
    (z : LinearMap.ker (((SingularCochain.chainFunctor ℚ).obj
      (TopCat.of UnitAddCircle)).sc 1).g.hom)
    (hnorm : (show ((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).X 1 ⟶
      ModuleCat.of ℚ ℚ from a.val) z.val = 1)
    (hconst : ∀ (Z : TopCat) (b : UnitAddCircle),
      (SingularCochain.cohomologyPullback ℚ
        (TopCat.ofHom (ContinuousMap.const Z b)) 1)
        (SingularCochain.cocycleClass ℚ
          (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a) = 0) :
    ∀ i j : Fin n,
      singularKronecker (TopCat.of (UnitAddTorus (Fin n))) 1
        ((SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1)
          (SingularCochain.cocycleClass ℚ
            (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a))
        ((((SingularCochain.chainFunctor ℚ).obj
          (TopCat.of (UnitAddTorus (Fin n)))).sc 1).moduleCatLeftHomologyData.π
          (coordinateCycle n z j)) = if i = j then 1 else 0 := by
  intro i j
  have hp := quotient_map_representative
    ((SingularCochain.chainFunctor ℚ).map (coordinateInclusion n j)) 1
      z (coordinateCycle n z j) rfl
  have hn := singularKronecker_naturality (coordinateInclusion n j) 1
    ((SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1)
      (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a))
    (((((SingularCochain.chainFunctor ℚ).obj (TopCat.of UnitAddCircle)).sc 1).moduleCatLeftHomologyData.π) z)
  rw [hp] at hn
  rw [← hn, ← ConcreteCategory.comp_apply, ← singularPullback_comp]
  by_cases hij : i = j
  · have he : coordinateInclusion n j ≫ coordinateProjection n i = 𝟙 _ := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      simp [coordinateInclusion, coordinateProjection, hij]
    rw [he, singularPullback_id]
    simpa only [CategoryTheory.id_apply, ite_eq_left hij] using
      (singularKronecker_representative (TopCat.of UnitAddCircle) 1 a z).trans hnorm
  · have he : coordinateInclusion n j ≫ coordinateProjection n i =
        TopCat.ofHom (ContinuousMap.const (TopCat.of UnitAddCircle) 0) := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      simp [coordinateInclusion, coordinateProjection, hij]
    rw [he, hconst]
    simp [hij]

end HolomorphicAnosov.TorusRationalCupBasisKronecker
