import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov
universe u
theorem singularSubspace_mem_iff (X : TopCat.{u}) (A : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (singularSubspace X A).obj n ↔
      ∀ t, X.toSSetObjEquiv n σ t ∈ A := by
  rw [singularSubspace, Subfunctor.range_obj]
  constructor
  · rintro ⟨τ, hτ⟩
    intro t
    have heq := congrArg (fun s => X.toSSetObjEquiv n s t) hτ
    rw [← heq]
    change (↑(((TopCat.of A).toSSetObjEquiv n τ).toFun t) : X) ∈ A
    exact (((TopCat.of A).toSSetObjEquiv n τ).toFun t).property
  · intro h
    let f : C(Convexity.StdSimplex ℝ (Fin ((unop n).len + 1)), A) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv n σ t, h t⟩, by
        exact (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of A).toSSetObjEquiv n).symm f, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext t
    
    rfl
end HolomorphicAnosov
