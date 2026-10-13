import HolomorphicAnosov.AlgebraicTopology.SingularCochainRestrictionSurjective
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
/-- Relative cochains, ambient cochains and subspace cochains form a short exact
sequence. Source: Hatcher, *Algebraic Topology*, pp.199–200.
Restriction is degreewise surjective by extension by zero, and therefore an
epimorphism of complexes. Relative cochains are its categorical kernel, whose
inclusion is monic and whose image is the kernel of restriction. -/
theorem singular_cochain_pair_shortExact (R : Type u) [CommRing R]
    (X : TopCat.{u}) (A : Set X) :
    (ShortComplex.kernelSequence (pullback R (subspaceInclusion X A))).ShortExact := by
  have : Epi (pullback R (subspaceInclusion X A)) :=
    HomologicalComplex.epi_of_epi_f _ (fun n =>
      (ModuleCat.epi_iff_surjective _).mpr (singular_cochain_restriction_surjective R X A n))
  exact {
    exact := ShortComplex.kernelSequence_exact _
    epi_g := by
      change Epi (pullback R (subspaceInclusion X A))
      infer_instance }
end HolomorphicAnosov.SingularCochain
