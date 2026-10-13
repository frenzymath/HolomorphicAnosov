import HolomorphicAnosov.Topology.ZeroCohomologyCycleEquivG10
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingExplicitBase
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Topology.PointPositiveCohomologyProviderG12
import HolomorphicAnosov.Topology.CircleDegreeOneProfileProviderG12
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.LinearAlgebra.Basis.Defs

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-!
This file isolates the source-level computations needed by the circle profile.
The statements are deliberately independent of the packaging theorem: they can
be reused by the additive-circle transport and torus induction modules.
-/

/-- The one-cell circle computation over an arbitrary field, with the chosen
positive cycle and normalized degree-zero cocycle held fixed.

Source: Hatcher, *Algebraic Topology*, Example 2.2 p.105, pp.197--201,
Proposition 3.17 p.217 and Appendix A.2 p.521.  The proof compares the
actual singular relative complex of the characteristic interval with the
circle pair and then applies the field Kronecker evaluation theorem. -/
theorem circle_degree_one_profile_core (K : Type) [Field K]
    (z : chainCycles K circleSpace 1) (u : cocycles K circleSpace 0)
    (hz : z.val = simplexChain K circleSpace 1 positiveSimplex)
    (hu : ∀ σ : singularSet circleSpace _⦋0⦌,
      cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) :
    ∃ (a : cocycles K circleSpace 1)
      (B₁ : Module.Basis Unit K (chainClass K circleSpace 1))
      (Bcoh1 : Module.Basis Unit K (cohomology K circleSpace 1))
      (Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0)),
      B₁ () = cycleClass K circleSpace 1 z ∧
      Bcoh1 () = cocycleClass K circleSpace 1 a ∧
      Bcoh0 () = cocycleClass K circleSpace 0 u ∧
      cocycleEval K circleSpace 1 a z.val = 1 ∧
      (∀ a' : cocycles K circleSpace 1,
        cocycleEval K circleSpace 1 a' z.val = 1 →
          cocycleClass K circleSpace 1 a' = cocycleClass K circleSpace 1 a) ∧
      (∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n)) := by
  exact circle_degree_one_profile_provider K z u hz hu

/-- The point's degree-zero class has the singleton basis normalized by any
constant-one cocycle.

Source: Hatcher, pp.105 and 197--198.  The point singular complex is the
one-simplex complex, so its degree-zero cocycle quotient is one-dimensional. -/
theorem point_degree_zero_basis_core (K : Type) [Field K]
    (up : cocycles K pointSpace 0)
    (hup : ∀ σ : singularSet pointSpace _⦋0⦌,
      cocycleEval K pointSpace 0 up (simplexChain K pointSpace 0 σ) = 1) :
    ∃ Bp : Module.Basis Unit K (cohomology K pointSpace 0),
      Bp () = cocycleClass K pointSpace 0 up := by
  let σ : singularSet pointSpace _⦋0⦌ := (TopCat.toSSetObjEquiv pointSpace (op ⦋0⦌)).symm
    (ContinuousMap.const _ PUnit.unit)
  let z : (chain K pointSpace).X 0 := simplexChain K pointSpace 0 σ
  let ev0 : ((chain K pointSpace).X 0 ⟶ ModuleCat.of K K) →ₗ[K] K :=
    { toFun := fun a => LinearMap.applyₗ z (ModuleCat.Hom.hom a)
      map_add' := by intro a b; simp [ModuleCat.Hom.hom]
      map_smul' := by intro c a; simp [ModuleCat.Hom.hom] }
  let ev : cocycles K pointSpace 0 →ₗ[K] K :=
    { toFun := fun a => ev0 a.val
      map_add' := by intro a b; exact map_add ev0 _ _
      map_smul' := by intro c a; exact map_smul ev0 _ _ }
  have hev : ev up = 1 := by simpa [ev, ev0, z, cocycleEval] using hup σ
  let inv : K →ₗ[K] cocycles K pointSpace 0 :=
    { toFun := fun c => c • up
      map_add' := by intro a b; simp [add_smul]
      map_smul' := by intro c a; simp [mul_smul] }
  have hs (τ : singularSet pointSpace _⦋0⦌) : τ = σ := by
    apply (TopCat.toSSetObjEquiv pointSpace (op ⦋0⦌)).injective
    exact Subsingleton.elim _ _
  have hinv : Function.LeftInverse inv ev := by
    intro c
    apply Subtype.ext
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [show τ = σ from hs τ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ev (inv (ev c)) = ev c
    change ev ((ev c) • up) = ev c
    rw [map_smul, hev, smul_eq_mul, mul_one]
  have hleft : Function.LeftInverse ev inv := by
    intro a
    change ev (a • up) = a
    rw [map_smul, hev, smul_eq_mul, mul_one]
  obtain ⟨e0, he0⟩ := SingularCochain.exists_zero_cohomology_cycle_equiv K
    (SingularCochain.complex K pointSpace)
  let E : K ≃ₗ[K] cohomology K pointSpace 0 :=
    (LinearEquiv.ofBijective inv ⟨hleft.injective, hinv.surjective⟩).trans e0
  refine ⟨(Module.Basis.singleton Unit K).map E, ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
  dsimp [E]
  rw [he0]
  apply congrArg (fun x => cocycleClass K pointSpace 0 x)
  change (1 : K) • up = up
  exact one_smul K up

/-- Every positive-degree point singular cohomology group is zero.

Source: Hatcher, Proposition 2.8 p.110 and pp.197--198.  The unique
singular simplex in each degree gives the alternating identity differential,
so the positive quotient groups are subsingletons in every characteristic. -/
theorem point_positive_cohomology_core (K : Type) [Field K] :
    ∀ n : ℕ, 0 < n → Subsingleton (cohomology K pointSpace n) := by
  exact point_positive_cohomology_provider K

/-- The Alexander--Whitney square of the normalized degree-one circle class.

Source: Hatcher, cup formula pp.206--207 and the circle one-cell profile
pp.197--201.  The displayed cocycle is the literal front/back product; its
class vanishes because the circle has no degree-two cohomology. -/
theorem circle_cup_square_core (K : Type) [Field K]
    (a : cocycles K circleSpace 1)
    (ha : ∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n)) :
    ∃ c : cocycles K circleSpace 2,
      (∀ σ : singularSet circleSpace _⦋2⦌,
        cocycleEval K circleSpace 2 c (simplexChain K circleSpace 2 σ) =
          cocycleEval K circleSpace 1 a
            (simplexChain K circleSpace 1 ((singularSet circleSpace).δ 2 σ)) *
          cocycleEval K circleSpace 1 a
            (simplexChain K circleSpace 1 ((singularSet circleSpace).δ 0 σ))) ∧
      cocycleClass K circleSpace 2 c = 0 := by
  let c : cocycles K circleSpace 2 :=
    ⟨SingularCochain.cupCochain K circleSpace a.val a.val,
      SingularCochain.cupCochain_mem_cycles K circleSpace a a⟩
  refine ⟨c, ?_, ?_⟩
  · intro σ
    have hfront : (SingularCochain.cupFront 1 1).op = (SimplexCategory.δ 2).op := by
      ext i
      fin_cases i <;> rfl
    have hback : (SingularCochain.cupBack 1 1).op = (SimplexCategory.δ 0).op := by
      ext i
      fin_cases i <;> rfl
    change SingularCochain.simplexValue K circleSpace c.val σ =
      SingularCochain.simplexValue K circleSpace a.val ((singularSet circleSpace).δ 2 σ) *
      SingularCochain.simplexValue K circleSpace a.val ((singularSet circleSpace).δ 0 σ)
    change SingularCochain.simplexValue K circleSpace (SingularCochain.cupCochain K circleSpace a.val a.val) σ =
      SingularCochain.simplexValue K circleSpace a.val
        (((singularSet circleSpace).map (SimplexCategory.δ 2).op) σ) *
      SingularCochain.simplexValue K circleSpace a.val
        (((singularSet circleSpace).map (SimplexCategory.δ 0).op) σ)
    simpa [hfront, hback] using
      (SingularCochain.cup_simplex_value K circleSpace a.val a.val σ)
  · let _ := ha 2 (by omega)
    exact Subsingleton.elim _ _

end
end HolomorphicAnosov.CircleSingularCohomology

