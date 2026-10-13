import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Trivialization

/-! The tangent quotient fibre topology is induced by inclusion into its total space (Demailly, V
§1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- At a point in the local coordinate domain, inclusion of the quotient fibre into its total space
induces the fibre topology (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem QuotientLocalData.fibre_inducing
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) (x : X) (hx : x ∈ D.V) :
    Topology.IsInducing (TotalSpace.mk x : HolomorphicQuotientTangentLine P x →
      TotalSpace ℂ (HolomorphicQuotientTangentLine P)) := by
  let e := D.trivialization
  have hm : ∀ v : HolomorphicQuotientTangentLine P x,
      (⟨x, v⟩ : TotalSpace ℂ (HolomorphicQuotientTangentLine P)) ∈ e.source := fun _ ↦ hx
  have hi : Topology.IsInducing (e.source.domRestrict e ∘
      Set.codRestrict (TotalSpace.mk x) e.source hm) := by
    have h : Topology.IsInducing (fun v ↦ (x, D.L x hx v)) :=
      (isInducing_prodMkRight x).comp (D.L x hx).toHomeomorph.isInducing
    have heq : e.source.domRestrict e ∘ Set.codRestrict (TotalSpace.mk x) e.source hm =
        (fun v ↦ (x, D.L x hx v)) := by
      funext v
      change (x, if h : x ∈ D.V then D.L x h v else 0) = (x, D.L x hx v)
      rw [dite_eq_left hx]
    rw [heq]
    exact h
  have hi' := e.toOpenPartialHomeomorph.isEmbedding_restrict.isInducing.of_comp_iff.mp hi
  exact Topology.IsInducing.of_codRestrict hm hi'


end HolomorphicAnosov
