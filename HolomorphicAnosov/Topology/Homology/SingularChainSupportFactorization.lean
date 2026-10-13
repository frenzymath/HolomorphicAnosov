import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport
import HolomorphicAnosov.Topology.Homology.SingularChainCoefficientsGenerator
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Singular chains factor through their literal image support

Source: Hatcher, *Algebraic Topology*, singular chain basis p.108,
relative chains pp.115–117, and Lemma 3.27 step (4), pp.237–238.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace HolomorphicAnosov

universe u

/-- A chain whose literal simplex-image support lies in A comes from a chain
in the subspace A. Source: Hatcher, relative chains pp.115–117 and the boundary
support enlargement in Lemma 3.27 step (4), pp.237–238.

Proof: expand the chain into its finitely many nonzero simplex generators.
Each continuous simplex has image in A and therefore corestricts to A.
Naturality of the chain generator maps shows that its generator, with the
same coefficient, maps to the original generator. The range of the inclusion
chain map is a submodule and contains the sum. Empty supports and degree zero
are included; no compactness or separation condition on A is needed. -/
theorem integralSingularChain_lift_of_imageSupport_subset (X : TopCat.{u}) (n : ℕ) (c : IntegralSingularChain X n)
    (A : Set X) (hc : integralSingularChainImageSupport X n c ⊆ A) :
    ∃ b : IntegralSingularChain (TopCat.of A) n,
      (SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X))
        (ModuleCat.of ℤ (ULift.{u} ℤ))).f n b = c := by
  classical
  let i : TopCat.of A ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let f := (SSet.chainComplexMap (TopCat.toSSet.map i)
    (ModuleCat.of ℤ (ULift.{u} ℤ))).f n
  change c ∈ LinearMap.range f.hom
  rw [← (integralSingularChainCoefficients X n).symm_apply_apply c,
    ← (integralSingularChainCoefficients X n c).sum_single, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro σ hσ
  rw [← integralSingularChainCoefficients_ι X n σ _,
    LinearEquiv.symm_apply_apply]
  have hs (t) : X.toSSetObjEquiv (Opposite.op ⦋n⦌) σ t ∈ A := by
    apply hc
    exact Set.mem_iUnion_of_mem σ (Set.mem_iUnion_of_mem hσ (Set.mem_range_self t))
  let τ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋n⦌) :=
    ((TopCat.of A).toSSetObjEquiv _).symm
      ⟨fun t ↦ ⟨X.toSSetObjEquiv _ σ t, hs t⟩,
        (X.toSSetObjEquiv _ σ).continuous.subtype_mk _⟩
  have hτ : (TopCat.toSSet.map i).app (Opposite.op ⦋n⦌) τ = σ := by
    apply (X.toSSetObjEquiv _).injective
    ext t
    rfl
  refine ⟨(TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
    (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ (integralSingularChainCoefficients X n c σ), ?_⟩
  have he := congrArg (fun g ↦ g (integralSingularChainCoefficients X n c σ))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X) (TopCat.toSSet.map i)
      (ModuleCat.of ℤ (ULift.{u} ℤ)) τ)
  change f ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ
    (integralSingularChainCoefficients X n c σ)) = _
  exact he.trans (by rw [hτ])


end HolomorphicAnosov
