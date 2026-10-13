import HolomorphicAnosov.Topology.Homology.SingularChainCoefficientsCompactSupport
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

noncomputable section
namespace HolomorphicAnosov
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
/-- Coefficient-parametric factorization of a finite singular chain through a subset.
The proof follows the Finsupp coproduct decomposition used in Hatcher's relative
chain argument; this sandbox theorem is being checked before any landing. -/
theorem singularChain_lift_of_imageSupport_subset
    (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (n : ℕ)
    (c : SingularChain X R n) (A : Set X)
    (hc : singularChainImageSupport X R n c ⊆ A) :
    ∃ b : SingularChain (TopCat.of A) R n,
      (SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)) R).f n b = c := by
  classical
  let i : TopCat.of A ⟶ X :=
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)
  let f : ((TopCat.toSSet.obj (TopCat.of A)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X n :=
    (SSet.chainComplexMap (TopCat.toSSet.map i) R).f n
  change c ∈ LinearMap.range f.hom
  let e : ((TopCat.toSSet.obj X).chainComplex R).X n ≅
      ((ModuleCat.finsuppCocone ℤ (R : Type u)
        ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))).pt) :=
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℤ (R : Type u)
      ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)))
  let coeff : ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) →₀ (R : Type u)) :=
    e.hom.hom' c
  have hgen (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) (r : R) :
      e.hom.hom' (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ).hom' r) =
        Finsupp.single σ r := by
    let hcat := (TopCat.toSSet.obj X).isColimitChainComplexXCofan R n
    have hfac := hcat.comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ (R : Type u)
        ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))) ⟨σ⟩
    have hfac' := congrArg (fun k ↦ (CategoryTheory.ConcreteCategory.hom k) r) hfac
    rw [ModuleCat.comp_apply] at hfac'
    dsimp [e, SSet.chainComplexXCofan, SSet.ιChainComplex, ModuleCat.finsuppCocone] at hfac'
    change e.hom.hom' (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ).hom' r) = Finsupp.single σ r at hfac'
    exact hfac'
  let τ : ∀ σ, σ ∈ coeff.support →
      (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋n⦌) := fun σ hσ ↦
    ((TopCat.of A).toSSetObjEquiv _).symm
      ⟨fun t ↦ ⟨(TopCat.toSSetObjEquiv X _ σ) t, by
          apply hc
          exact Set.mem_iUnion_of_mem σ (Set.mem_iUnion_of_mem hσ (Set.mem_range_self t))⟩,
        (TopCat.toSSetObjEquiv X _ σ).continuous.subtype_mk (fun t ↦ by
          apply hc
          exact Set.mem_iUnion_of_mem σ (Set.mem_iUnion_of_mem hσ (Set.mem_range_self t)))⟩
  let g : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) → (R : Type u) →ₗ[ℤ]
      ((TopCat.toSSet.obj (TopCat.of A)).chainComplex R).X n := fun (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) ↦ {
    toFun := fun r ↦
    if hσ : σ ∈ coeff.support then
      (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R) (τ σ hσ) |>.hom' r
    else 0
    map_add' := by
      intro x y
      by_cases hσ : σ ∈ coeff.support <;> simp [hσ, map_add]
    map_smul' := by
      intro z x
      by_cases hσ : σ ∈ coeff.support <;> simp [hσ] }
  let b : ((TopCat.toSSet.obj (TopCat.of A)).chainComplex R).X n :=
    coeff.sum (fun σ r ↦ g σ r)
  have hτ (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) (hσ : σ ∈ coeff.support) :
      (TopCat.toSSet.map i).app (Opposite.op ⦋n⦌) (τ σ hσ) = σ := by
    apply (TopCat.toSSetObjEquiv X _).injective
    ext t
    rfl
  refine ⟨b, ?_⟩
  have hgoal : e.hom.hom' (f.hom' b) = e.hom.hom' c := by
    change e.hom.hom' (f.hom' (coeff.sum (fun σ r ↦ g σ r))) = coeff
    have fmap := map_finsuppSum f.hom' coeff (fun σ r ↦ g σ r)
    rw [fmap]
    have emap := map_finsuppSum e.hom.hom' coeff
      (fun σ r ↦ f.hom' (g σ r))
    rw [emap]
    have hcoeff : coeff.sum (fun σ r ↦ Finsupp.single σ r) = coeff := by
      ext σ
      simp
    have hsum : coeff.sum (fun a b ↦ e.hom.hom' (f.hom' ((g a) b))) =
          coeff.sum (fun σ r ↦ Finsupp.single σ r) := by
      apply Finsupp.sum_congr
      intro σ hσ
      have hz : coeff σ ≠ 0 := Finsupp.mem_support_iff.mp hσ
      have hmap := congrArg (fun q ↦ q.hom' (coeff σ))
          (SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map i)
            (R := R) (x := τ σ hσ))
      have hmap' : f.hom'
            (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R)
              (τ σ hσ)).hom' (coeff σ)) =
            ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ).hom' (coeff σ) := by
          change f.hom' (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R)
              (τ σ hσ)).hom' (coeff σ)) = _ at hmap
          simpa [hτ σ hσ] using hmap
      change e.hom.hom' (f.hom' (g σ (coeff σ))) = Finsupp.single σ (coeff σ)
      have hg : g σ (coeff σ) =
            ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex (R := R)
              (τ σ hσ)).hom' (coeff σ) := by
        simp only [g]
        split <;> rename_i hp
        · rfl
        · exact (hp hσ).elim
      rw [hg]
      rw [hmap', hgen]
    rw [hsum, hcoeff]
  have hcancel := congrArg (fun z ↦ e.inv.hom' z) hgoal
  have hcancel' : (e.hom ≫ e.inv).hom' (f.hom' b) =
      (e.hom ≫ e.inv).hom' c := by
    change e.inv.hom' (e.hom.hom' (f.hom' b)) =
      e.inv.hom' (e.hom.hom' c)
    exact hcancel
  rw [e.hom_inv_id] at hcancel'
  change f.hom' b = c
  change (𝟙 ((TopCat.toSSet.obj X).chainComplex R).X n).hom' (f.hom' b) =
    (𝟙 ((TopCat.toSSet.obj X).chainComplex R).X n).hom' c at hcancel'
  change (ConcreteCategory.hom (𝟙 ((TopCat.toSSet.obj X).chainComplex R).X n))
      (f.hom' b) =
    (ConcreteCategory.hom (𝟙 ((TopCat.toSSet.obj X).chainComplex R).X n)) c at hcancel'
  have hfinal : f.hom' b = c := by
    change f.hom' b = c at hcancel'
    exact hcancel'
  exact hfinal

end HolomorphicAnosov
