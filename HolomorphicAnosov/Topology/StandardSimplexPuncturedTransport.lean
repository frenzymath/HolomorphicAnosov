import HolomorphicAnosov.Topology.StandardSimplexRadialDeformation
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence

/-!
# The punctured standard-simplex comparison provider

DAG node: `topo.standard_simplex_punctured_transport_g20`.
Source: Hatcher, *Algebraic Topology*, Example 2.23 p.125 and the radial
pair comparison used in the local orientation construction pp.233–234.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The coefficient-one identity simplex class in the pair obtained by deleting
an interior point t from the standard simplex. -/
def standardSimplexPuncturedClass (n : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (hfaces : ∀ (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))),
      t ≠ Convexity.StdSimplex.map i.succAbove u) :
    (singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      ({t} : Set _)ᶜ).homology (C := ModuleCat ℤ)
        reducedSingularIntegralCoefficients (n + 1) :=
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let P := singularSubspacePair X ({t} : Set _)ᶜ
  let K := P.chainComplex reducedSingularIntegralCoefficients
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2))))
  have hcycle : (K.sc (n + 1)).g.hom
      ((P.chainComplexπ R).f (n + 1)
        (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))) = 0 := by
    classical
    let A : Set X := ({t} : Set _)ᶜ
    have hface (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))) :
        X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) u ∈ A := by
      change X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) u ≠ t
      change Convexity.StdSimplex.map i.succAbove u ≠ t
      exact Ne.symm (hfaces i u)
    have hkill (i : Fin (n + 2)) :
        (TopCat.toSSet.obj X).ιChainComplex (R := R) ((TopCat.toSSet.obj X).δ i σ) ≫
          (P.chainComplexπ R).f n = 0 := by
      let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
        ⟨fun u ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) u, hface i u⟩,
          (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩
      let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm τ
      have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
          (TopCat.toSSet.obj X).δ i σ := by
        apply (X.toSSetObjEquiv _).injective
        ext u
        rfl
      rw [← hα, ← SSet.ι_chainComplexMap_f, Category.assoc]
      change _ ≫ (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0
      rw [P.chainComplex_condition_f]
      simp
    change (P.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1))
      ((P.chainComplexπ R).f (n + 1)
        (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))) = 0
    rw [ChainComplex.next_nat_succ]
    have hm : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (P.chainComplexπ R).f (n + 1) ≫ (P.chainComplex R).d (n + 1) n = 0 := by
      rw [(P.chainComplexπ R).comm]
      change (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ (P.chainComplexπ R).f n = 0
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hkill, smul_zero,
        Finset.sum_const_zero]
    exact congrArg (fun f ↦ f.hom (ULift.up 1)) hm
  (K.sc (n + 1)).moduleCatHomologyIso.inv
    ((K.sc (n + 1)).moduleCatLeftHomologyData.π
      ⟨(P.chainComplexπ R).f (n + 1)
          (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1)), hcycle⟩)

/-- Radial projection from an interior point identifies the standard-simplex
relative identity class with the same identity simplex in the punctured pair.
Source: Hatcher pp.233–234, radial comparison, and the pair sequence pp.116–118.
Avoiding every face makes all center coordinates positive. The explicit radial
strong deformation retracts the punctured simplex onto the boundary. Relative
homology comparison for this deformation makes the pair enlargement an
isomorphism. Its ambient chain map is the identity, so naturality of the
relative quotient projection carries the coefficient-one identity chain to
the same chain in the punctured pair. Naturality of cycle classes gives the
stated equality. This does not use the separate primitive-generator theorem. -/
theorem standardSimplex_punctured_transport_provider (n : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (hfaces : ∀ (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))),
      t ≠ Convexity.StdSimplex.map i.succAbove u) :
    ∃ e :
      (singularSubspacePair
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
        (standardSimplexBoundary n)).homology (C := ModuleCat ℤ)
          reducedSingularIntegralCoefficients (n + 1) ≃ₗ[ℤ]
      (singularSubspacePair
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
        ({t} : Set _)ᶜ).homology (C := ModuleCat ℤ)
          reducedSingularIntegralCoefficients (n + 1),
      e (standardSimplexIdentityClass n) = standardSimplexPuncturedClass n t hfaces := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let A := standardSimplexBoundary n
  let V : Set X := ({t} : Set _)ᶜ
  have ht := SimplexRadial.weights_pos t hfaces
  have hAV : A ⊆ V := SimplexRadial.boundary_subset t ht
  let f := GoodPair.singularPairEnlargement X hAV
  let R := reducedSingularIntegralCoefficients
  obtain ⟨d⟩ := standardSimplex_radial_deformation n t ht
  have hiso : IsIso (SSetPair.homologyMap f R (n + 1)) :=
    GoodPair.enlargement_homology_isIso_of_deformation X A V hAV
      d R (n + 1)
  refine ⟨(asIso (SSetPair.homologyMap f R (n + 1))).toLinearEquiv, ?_⟩
  change SSetPair.homologyMap f R (n + 1) (standardSimplexIdentityClass n) = _
  unfold standardSimplexIdentityClass standardSimplexPuncturedClass
  apply GoodPair.shortComplex_homologyMap_cycle
  change (SSetPair.chainComplexMap f R).f (n + 1)
    (((singularSubspacePair X A).chainComplexπ R).f (n + 1)
      (((TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (ContinuousMap.id _))) (ULift.up 1))) = _
  have hn := ((SSetPair.chainComplexFunctorπ (ModuleCat ℤ)).app R).naturality f
  change SSet.chainComplexMap f.right R ≫ (singularSubspacePair X V).chainComplexπ R =
    (singularSubspacePair X A).chainComplexπ R ≫ SSetPair.chainComplexMap f R at hn
  have hr : f.right = 𝟙 (TopCat.toSSet.obj X) := by
    exact TopCat.toSSet.map_id X
  rw [hr] at hn
  have hid : SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X)) R = 𝟙 _ :=
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj R).map_id _
  rw [hid] at hn
  have hn' := congrArg (fun g ↦ g.f (n + 1)) hn
  exact (congrArg (fun g ↦ g
    (((TopCat.toSSet.obj X).ιChainComplex (R := R)
      ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (ContinuousMap.id _))) (ULift.up 1))) hn').symm

end HolomorphicAnosov

