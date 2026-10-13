import HolomorphicAnosov.Topology.GallierXuSurfacePresentation

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- The barycentric carrier of a finite abstract simplicial complex is compact.

This is the compact source-side guard used by the quotient comparison.  It is
proved directly from compactness of the standard simplex and the finite closed
support union; it makes no Hausdorff or surface assumption on the disk quotient.
-/
def triangleCarrierSupport (s : Finset (Fin N)) : Set (Fin N → ℝ) :=
  {x | ∀ v ∉ s, x v = 0}

lemma triangleCarrierSupport_closed {N : ℕ} (s : Finset (Fin N)) :
    IsClosed (triangleCarrierSupport s) := by
  unfold triangleCarrierSupport
  rw [show {x : Fin N → ℝ | ∀ v ∉ s, x v = 0} =
      ⋂ v ∈ (s : Set (Fin N))ᶜ, {x | x v = 0} by
    ext x
    simp]
  apply isClosed_biInter
  intro v _
  exact isClosed_eq (continuous_apply v) continuous_const

theorem triangle_carrier_compact {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) : IsCompact (carrier K) := by
  let F : Set (Finset (Fin N)) := K.faces
  have hF : F.Finite := Set.Finite.subset Set.finite_univ
    (by intro s _; exact Set.mem_univ s)
  have hU : IsClosed (⋃ s ∈ F, triangleCarrierSupport s) :=
    hF.isClosed_biUnion (fun s _ ↦ triangleCarrierSupport_closed s)
  let S : Set (Fin N → ℝ) := {x | (∀ v, 0 ≤ x v) ∧ ∑ v, x v = 1}
  have hS : IsCompact S := by
    have hcompact := isCompact_range (continuous_pi fun v ↦
      Convexity.StdSimplex.continuous_weights_apply (R := ℝ) v
        : Continuous (fun t : Convexity.StdSimplex ℝ (Fin N) ↦ fun v ↦ t.weights v))
    have heq : Set.range (fun t : Convexity.StdSimplex ℝ (Fin N) ↦
        fun v ↦ t.weights v) = S := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext x
      simp [S]
    rwa [heq] at hcompact
  have hsub : carrier K = S ∩
      (⋃ s ∈ F, triangleCarrierSupport s) := by
    ext x
    change (x ∈ S ∧ ∃ s ∈ K.faces, ∀ v ∉ s, x v = 0) ↔ _
    simp [triangleCarrierSupport, F]
  rw [hsub]
  exact hS.inter_right hU

end HolomorphicAnosov.Topology.GallierXu
