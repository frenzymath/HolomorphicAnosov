import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Topology.ZeroCocyclePathConstancyG10
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.ZeroCohomologyCycleEquivG10
import Mathlib.LinearAlgebra.Basis.Defs
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- A normalized degree-zero cocycle on the path-connected circle gives the singleton
cohomology basis. The proof uses literal singular cocycle evaluations and the
zero-degree quotient equivalence. -/
theorem circle_degree_zero_basis_of_unit_cocycle (K : Type) [Field K]
    (u : cocycles K circleSpace 0)
    (hu : ∀ σ : singularSet circleSpace _⦋0⦌,
      cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) :
    ∃ Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0),
      Bcoh0 () = cocycleClass K circleSpace 0 u := by
  let x₀ : Circle := 1
  let σ₀ : singularSet circleSpace _⦋0⦌ :=
    TopCat.toSSetObj₀Equiv.symm x₀
  let ev0 : ((chain K circleSpace).X 0 ⟶ ModuleCat.of K K) →ₗ[K] K :=
    { toFun := fun a => LinearMap.applyₗ (simplexChain K circleSpace 0 σ₀) (ModuleCat.Hom.hom a)
      map_add' := by intro a b; simp [ModuleCat.Hom.hom]
      map_smul' := by intro c a; simp [ModuleCat.Hom.hom] }
  let ev : cocycles K circleSpace 0 →ₗ[K] K :=
    { toFun := fun a => ev0 a.val
      map_add' := by intro a b; exact map_add ev0 _ _
      map_smul' := by intro c a; exact map_smul ev0 _ _ }
  have hev : ev u = 1 := by simpa [ev, ev0, cocycleEval] using hu σ₀
  let inv : K →ₗ[K] cocycles K circleSpace 0 :=
    { toFun := fun c => c • u
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro c a; simp [mul_smul] }
  have hinv : Function.LeftInverse inv ev := by
    intro c
    apply Subtype.ext
    apply SSet.chainComplex_hom_ext
    intro σ
    have hconst (a : cocycles K circleSpace 0) :
        cocycleEval K circleSpace 0 a (simplexChain K circleSpace 0 σ₀) =
        cocycleEval K circleSpace 0 a (simplexChain K circleSpace 0 σ) := by
      have h := SingularCochain.zero_cocycle_eval_eq_of_path K circleSpace a
        x₀ (TopCat.toSSetObj₀Equiv σ)
      rw [Equiv.symm_apply_apply] at h
      exact h
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    calc
      cocycleEval K circleSpace 0 (inv (ev c)) (simplexChain K circleSpace 0 σ) =
          cocycleEval K circleSpace 0 (inv (ev c)) (simplexChain K circleSpace 0 σ₀) :=
        (hconst (inv (ev c))).symm
      _ = ev c := by
        change ev c • cocycleEval K circleSpace 0 u
          (simplexChain K circleSpace 0 σ₀) = ev c
        rw [show cocycleEval K circleSpace 0 u
          (simplexChain K circleSpace 0 σ₀) = 1 by exact hev]
        simp
      _ = cocycleEval K circleSpace 0 c (simplexChain K circleSpace 0 σ) := by
        rw [← hconst c]
        rfl
  have hleft : Function.LeftInverse ev inv := by
    intro a
    change ev (a • u) = a
    rw [map_smul, hev, smul_eq_mul, mul_one]
  obtain ⟨e0, he0⟩ := SingularCochain.exists_zero_cohomology_cycle_equiv K
    (SingularCochain.complex K circleSpace)
  let E : K ≃ₗ[K] cohomology K circleSpace 0 :=
    (LinearEquiv.ofBijective inv ⟨hleft.injective, hinv.surjective⟩).trans e0
  refine ⟨(Module.Basis.singleton Unit K).map E, ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
  dsimp [E]
  rw [he0]
  apply congrArg (fun x => cocycleClass K circleSpace 0 x)
  change (1 : K) • u = u
  exact one_smul K u

end
end HolomorphicAnosov.CircleSingularCohomology
