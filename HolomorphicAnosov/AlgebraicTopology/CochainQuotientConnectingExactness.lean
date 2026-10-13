import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Algebra.Homology.HomologySequence
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- The quotient connecting map of a short exact cochain row has exact
image/kernel at both adjacent positions. It is obtained by transporting
Mathlib's snake-lemma connecting map through the canonical module homology
quotient isomorphisms. Source: Hatcher, *Algebraic Topology*, pp.199–200,
and Mathlib's homology sequence. -/
theorem cochain_quotient_connecting_exact (R : Type u) [CommRing R]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ))
    (hS : S.ShortExact) (n : ℕ) :
    let q : quotient R S.X₃ n ⟶ quotient R S.X₁ (n+1) :=
      (S.X₃.sc n).moduleCatHomologyIso.inv ≫ hS.δ n (n+1) rfl ≫
        (S.X₁.sc (n+1)).moduleCatHomologyIso.hom
    LinearMap.range (quotientMap R S.g n).hom = LinearMap.ker q.hom ∧
    LinearMap.range q.hom = LinearMap.ker (quotientMap R S.f (n+1)).hom := by
  dsimp only
  let q : quotient R S.X₃ n ⟶ quotient R S.X₁ (n+1) :=
      (S.X₃.sc n).moduleCatHomologyIso.inv ≫ hS.δ n (n+1) rfl ≫
        (S.X₁.sc (n+1)).moduleCatHomologyIso.hom
  change LinearMap.range (quotientMap R S.g n).hom = LinearMap.ker q.hom ∧
    LinearMap.range q.hom = LinearMap.ker (quotientMap R S.f (n+1)).hom
  constructor
  · have hz : quotientMap R S.g n ≫ q = 0 := by
      simp only [quotientMap, q, Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc (HomologicalComplex.homologyMap S.g n), hS.comp_δ]
      simp
    let T := ShortComplex.mk (quotientMap R S.g n) q hz
    let U := ShortComplex.mk _ _ (hS.comp_δ n (n+1) rfl)
    have e : U ≅ T := ShortComplex.isoMk
      (S.X₂.sc n).moduleCatHomologyIso (S.X₃.sc n).moduleCatHomologyIso
      (S.X₁.sc (n+1)).moduleCatHomologyIso (by simp [T, U, quotientMap])
      (by simp [T, U, q])
    exact (ShortComplex.exact_of_iso e (hS.homology_exact₃ n (n+1) rfl)).moduleCat_range_eq_ker
  · have hz : q ≫ quotientMap R S.f (n+1) = 0 := by
      simp only [quotientMap, q, Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc (hS.δ n (n+1) rfl), hS.δ_comp]
      simp
    let T := ShortComplex.mk q (quotientMap R S.f (n+1)) hz
    let U := ShortComplex.mk _ _ (hS.δ_comp n (n+1) rfl)
    have e : U ≅ T := ShortComplex.isoMk
      (S.X₃.sc n).moduleCatHomologyIso (S.X₁.sc (n+1)).moduleCatHomologyIso
      (S.X₂.sc (n+1)).moduleCatHomologyIso (by simp [T, U, q])
      (by simp [T, U, quotientMap])
    exact (ShortComplex.exact_of_iso e (hS.homology_exact₁ n (n+1) rfl)).moduleCat_range_eq_ker
end HolomorphicAnosov.SingularCochain

