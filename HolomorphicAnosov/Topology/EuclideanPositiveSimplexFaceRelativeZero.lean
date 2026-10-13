import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceAvoidsZero
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology

/-!
# Affine simplex faces vanish in the punctured relative chain complex

Source: Hatcher, *Algebraic Topology*, p.108 (singular boundary), p.115
(relative quotient), and p.269 (ordered affine simplex). DAG node:
`topo.euclidean_positive_simplex_face_relative_zero_g15`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section
namespace HolomorphicAnosov

/-- The native relative projection kills every codimension-one face of the
prescribed positive affine simplex. The face avoids the origin, so its actual
singular simplex factors through the punctured subspace; the relative cokernel
projection therefore sends its chain to zero. -/
theorem euclideanPositiveSimplex_face_relative_zero (n : ℕ) (i : Fin (n + 2)) :
    let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
    let A : Set X := ({0} : Set _)ᶜ
    let P := singularSubspacePair X A
    let R := reducedSingularIntegralCoefficients
    let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
      (euclideanPositiveSimplex (n + 1))
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((TopCat.toSSet.obj X).δ i σ) ≫ (P.chainComplexπ R).f n = 0 := by
  dsimp only
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := ({0} : Set _)ᶜ
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
    (euclideanPositiveSimplex (n + 1))
  let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun t ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t,
      euclideanPositiveSimplex_face_avoids_zero n i t⟩,
      (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩
  let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm τ
  have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
      (TopCat.toSSet.obj X).δ i σ := by
    apply (X.toSSetObjEquiv _).injective
    ext t
    rfl
  change (TopCat.toSSet.obj X).ιChainComplex (R := R)
      ((TopCat.toSSet.obj X).δ i σ) ≫ (P.chainComplexπ R).f n = 0
  have hchain : (TopCat.toSSet.obj X).chainComplex R = P.right.chainComplex R := by rfl
  cases hchain
  rw [← hα]
  rw [← SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A))
    (TopCat.toSSet.obj X) (TopCat.toSSet.map (singularSubspaceInclusion X A)) R α]
  change (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) α ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A)) R).f n ≫
      (P.chainComplexπ R).f n = 0
  have hz := congrArg (fun q ↦ (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) α ≫ q)
    (P.chainComplex_condition_f R n)
  have hmap : (SSet.chainComplexMap P.hom R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A)) R).f n := by
    rfl
  have hzero : (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) α ≫
      (0 : ((TopCat.toSSet.obj (TopCat.of A)).chainComplex R).X n ⟶
        (P.chainComplex R).X n) = 0 := by
    exact comp_zero
  have hz0 : (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) α ≫
      (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0 := by
    calc
      _ = (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) α ≫ 0 := hz
      _ = 0 := hzero
  exact hz0

end HolomorphicAnosov

