import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.DirectSum.Module

/-!
# Direct-sum coordinates for a tensor-total degree

Bredon, *Topology and Geometry*, VI §1 pp.315–316 defines degree `n` of
the tensor complex as the direct sum of the tensor products in bidegrees
`(p,q)` with `p+q=n`. This identifies that concrete direct sum with Mathlib's
categorical tensor-total object, including its summand injections.
-/

open CategoryTheory MonoidalCategory
open scoped TensorProduct DirectSum

universe u
noncomputable section

namespace HolomorphicAnosov.TensorTotalDegreeDirectSum

/-- The degree of a tensor-total complex is the direct sum of its bidegrees.
The equivalence sends every direct-sum injection to the actual total injection.
Its inverse is the coproduct descent of the direct-sum injections; the two
universal properties prove the inverse identities.
-/
theorem tensor_total_degree_direct_sum {K : Type u} [Field K]
    (C D : ChainComplex (ModuleCat.{u} K) ℕ) (n : ℕ) :
    let I := {pq : ℕ × ℕ // pq.1 + pq.2 = n}
    let T := fun i : I ↦ C.X i.val.1 ⊗[K] D.X i.val.2
    ∃ e : (⨁ i, T i) ≃ₗ[K] (HomologicalComplex.tensorObj C D).X n,
      ∀ (i : I) (x : T i), e (DirectSum.lof K I T i x) =
        HomologicalComplex.ιTensorObj C D i.val.1 i.val.2 n i.property x := by
  classical
  dsimp only
  let I := {pq : ℕ × ℕ // pq.1 + pq.2 = n}
  let T := fun i : I ↦ C.X i.val.1 ⊗[K] D.X i.val.2
  let f : (⨁ i, T i) →ₗ[K] (HomologicalComplex.tensorObj C D).X n :=
    DirectSum.toModule K I _ (fun i ↦
      (HomologicalComplex.ιTensorObj C D i.val.1 i.val.2 n i.property).hom)
  let g : (HomologicalComplex.tensorObj C D).X n ⟶ ModuleCat.of K (⨁ i, T i) :=
    HomologicalComplex.mapBifunctorDesc (fun p q h ↦
      ModuleCat.ofHom (DirectSum.lof K I T ⟨(p, q), h⟩))
  have hg (p q : ℕ) (h : p + q = n) :
      HomologicalComplex.ιTensorObj C D p q n h ≫ g =
        ModuleCat.ofHom (DirectSum.lof K I T ⟨(p, q), h⟩) :=
    HomologicalComplex.ι_mapBifunctorDesc _ _ _ _
  have hgf : g.hom.comp f = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change g (f (DirectSum.lof K I T i x)) = _
    simp only [f, DirectSum.toModule_lof]
    exact congrArg (fun k ↦ k x) (hg i.val.1 i.val.2 i.property)
  have hfg : f.comp g.hom = LinearMap.id := by
    suffices h : g ≫ ModuleCat.ofHom f = 𝟙 _ by
      exact congrArg ModuleCat.Hom.hom h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [← Category.assoc, hg]
    ext x
    change f (DirectSum.lof K I T ⟨(p, q), h⟩ x) = _
    simp only [f, DirectSum.toModule_lof]
    rfl
  refine ⟨LinearEquiv.ofLinearMap f g.hom hfg hgf, ?_⟩
  intro i x
  exact DirectSum.toModule_lof K _ _


end HolomorphicAnosov.TensorTotalDegreeDirectSum
