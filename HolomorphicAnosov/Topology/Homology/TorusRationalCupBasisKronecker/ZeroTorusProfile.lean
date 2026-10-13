import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import Mathlib.Topology.Instances.AddCircle.Real
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackHomeomorph
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.ZeroCochainEqOne
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.PullbackOneCochain
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.EmptySubsetIndex

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The initial torus in the Künneth induction is the actual point, with the
specified native constant-one class as basis and zero positive-degree groups.
Source: Hatcher pp.197–201 and the point calculation used in Proposition 3.17
p.217, supplied by the circle-and-point source profile. The unique-space
homeomorphism uses the original torus topology; unit preservation is proved on
cochains, so no arbitrary nonzero scalar is substituted for the specified unit. -/
theorem zero_torus_profile
    (one : SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) 0)
    (hu : ∃ hu : SingularCochain.oneCochain ℚ (TopCat.of (UnitAddTorus (Fin 0))) ∈
        SingularCochain.cycles ℚ
          (SingularCochain.complex ℚ (TopCat.of (UnitAddTorus (Fin 0)))) 0,
      one = SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of (UnitAddTorus (Fin 0)))) 0
        ⟨SingularCochain.oneCochain ℚ (TopCat.of (UnitAddTorus (Fin 0))), hu⟩) :
    (∃ B : Module.Basis {S : Finset (Fin 0) // S.card = 0} ℚ
        (SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) 0),
      ∀ S, B S = one) ∧
    (∀ k : ℕ, 0 < k → Subsingleton
      (SingularCochain.cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) k)) := by
  obtain ⟨zc, ac, uc, up, B₁, Bc1, Bc0, Bp, hz, hrest⟩ :=
    CircleSingularCohomology.circle_singular_cohomology_winding ℚ
  have hBp := hrest.2.2.2.1
  have hup := hrest.2.2.2.2.2.1
  have hzp := hrest.2.2.2.2.2.2.2.2.2.1
  let e : TopCat.of (UnitAddTorus (Fin 0)) ≃ₜ CircleSingularCohomology.pointSpace :=
    Homeomorph.homeomorphOfUnique _ _
  let E := singularPullbackHomeomorph e 0
  constructor
  · obtain ⟨hu, hone⟩ := hu
    let u : SingularCochain.cycles ℚ
        (SingularCochain.complex ℚ (TopCat.of (UnitAddTorus (Fin 0)))) 0 :=
      ⟨SingularCochain.oneCochain ℚ _, hu⟩
    have hp : up.val = SingularCochain.oneCochain ℚ CircleSingularCohomology.pointSpace :=
      zeroCochain_eq_one _ up.val hup
    have hv : (SingularCochain.pullback ℚ (TopCat.isoOfHomeo e).hom).f 0 up.val = u.val := by
      rw [hp, pullback_oneCochain]
    have hb : (Bp.map E) () = one := by
      rw [Module.Basis.map_apply, hBp]
      exact (quotient_map_representative
        (SingularCochain.pullback ℚ (TopCat.isoOfHomeo e).hom) 0 up u hv).trans hone.symm
    refine ⟨(Bp.map E).reindex (emptySubsetIndex 0), ?_⟩
    intro S
    rw [Module.Basis.reindex_apply]
    exact hb
  · intro k hk
    have := hzp k hk
    exact ⟨fun x y => (singularPullbackHomeomorph e k).symm.injective (Subsingleton.elim _ _)⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
