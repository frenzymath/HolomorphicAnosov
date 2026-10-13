import HolomorphicAnosov.Topology.SingularChainBoundary

noncomputable section
open CategoryTheory
open scoped Simplicial BigOperators
namespace HolomorphicAnosov
universe u

/-- The boundary of a signed finite triangle chain is its signed ordered-edge
occurrence sum, as a finitely supported function on continuous singular edges.
Source: Hatcher, Algebraic Topology, §2.1 p.108 and Theorem 2A.1 proof p.167.

Proof: Apply the canonical singular-chain generator comparison to the boundary
equality. Linearity distributes the differential and comparison over the signed
sum. The simplicial differential formula gives the alternating three faces of
each triangle. The generator comparison sends each face to its single function.
Lower the lifted integer coefficients, distribute the signs, and reindex the
iterated sum by the product of triangle labels and face labels. The face map
is the order-preserving barycentric inclusion, with no parameter reversal.
Repeated triangles and faces cause no problem; the empty expansion cannot have
a unit generator as boundary. No endpoint or separation assumption is needed. -/
theorem singularTwoChainBoundaryOccurrences (X : TopCat.{u})
    (f : C(Convexity.StdSimplex ℝ (Fin 2), X)) (m : ℕ)
    (τ : Fin m → (TopCat.toSSet.obj X).obj (Opposite.op ⦋2⦌)) (ε : Fin m → ℤ)
    (hc : (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).d 2 1)
      (∑ i, ε i • ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) (τ i)).hom (ULift.up (1 : ℤ))) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ))
        ((TopCat.toSSetObjEquiv X (Opposite.op ⦋1⦌)).symm f)).hom (ULift.up (1 : ℤ))) :
    (∑ o : Fin m × Fin 3, (ε o.1 * (-1 : ℤ)^o.2.val) •
      Finsupp.single ((TopCat.toSSetObjEquiv X (Opposite.op ⦋2⦌) (τ o.1)).comp
        ⟨Convexity.StdSimplex.map o.2.succAbove,
          Convexity.StdSimplex.continuous_map ℝ o.2.succAbove⟩) (1 : ℤ)) =
      Finsupp.single f (1 : ℤ) := by
  have he := congrArg (fun z ↦ (singularChainGeneratorIso X 1).hom z) hc
  simp only [map_sum, map_zsmul] at he
  simp_rw [singularChainGeneratorIso_hom_boundary X 1] at he
  rw [singularChainGeneratorIso_hom_generator, Equiv.apply_symm_apply] at he
  have he' := congrArg
    (Finsupp.lcongr (Equiv.refl _) (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ)) he
  simp only [map_sum, map_zsmul, Finsupp.lcongr_single, Equiv.refl_apply,
    ULift.moduleEquiv_apply, Finset.smul_sum, smul_smul] at he'
  rw [Fintype.sum_prod_type]
  exact he'

end HolomorphicAnosov
