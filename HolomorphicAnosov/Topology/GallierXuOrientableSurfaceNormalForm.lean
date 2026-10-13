import HolomorphicAnosov.Topology.GallierXuPresentationRelabeling
import HolomorphicAnosov.Topology.GallierXuTriangleQuotientComparison
import HolomorphicAnosov.Topology.GallierXuPolygonReduction

noncomputable section
open Set Topology _root_.Topology
open scoped BigOperators Classical
namespace HolomorphicAnosov.Topology.GallierXu

/-- Finite orientable triangulated surfaces with nonempty boundary have the exact
canonical single-disk word through realized elementary operations.

Source: Gallier–Xu, Lemma 6.1, pp.92–95 and Theorem 6.1, p.96; the initial
parameterized quotient comparison follows Lee Proposition 6.14, p.173, and
Gallier–Xu Proposition 3.2, p.31, Note F.4, p.167. Obtain the original triangle
quotient homeomorphism, perform the finite polygon reduction up to relabeling,
and append the parameter-preserving realized renaming. Its edge-image formula
carries the prescribed original boundary cycles to the final canonical loops.
The finite reduction supplies the integer Euler-characteristic equality.

The triangle comparison and the reduction are explicit named proof obligations;
the final relabeling and this assembly have no independent admissions.
-/
theorem orientable_triangulated_surface_normal_form
    {N b : ℕ} (K : AbstractSimplicialComplex (Fin N)) (hb : 1 ≤ b)
    (hpure : PureTwo K) (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K) (B : Fin b → List (Fin N)) (hboundary : BoundaryCycles K B)
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o)) :
    ∃ g : ℕ, ∃ sequence : RealizedSequence (trianglePresentation K o) [normalWord g b],
      ∃ H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o),
        OriginalParameters K o H₀ ∧
        (∃ σ : Fin b ≃ Fin b, ∀ j : Fin b,
          (H₀.trans sequence.homeomorph) '' cycleCarrier (K := K) (B j) =
            edgeImage [normalWord g b] (2 * g + 2 * (σ j).val + 1)) ∧
        ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
          ((simplices K 2).card : ℤ) =
          (2 : ℤ) - 2 * (g : ℤ) - (b : ℤ) := by
  classical
  obtain ⟨H₀, hH₀⟩ := triangle_presentation_homeomorph K hpure hlinks o
  obtain ⟨g, Q, e, flip, f, hf, sequence, ⟨σ, hσ⟩, hEuler⟩ :=
    orientable_triangle_presentation_reduction K hb hpure hconnected hincidence hlinks
      B hboundary o horiented H₀ hH₀
  obtain ⟨H, hH, hEdge⟩ := labelRenaming_realized e flip f hf
  let move : Elementary Q [normalWord g b] :=
    .rename e flip f (fun k ↦ (hf k) ▸ List.IsRotated.refl _)
  let last : RealizedSequence Q [normalWord g b] := .cons move H hH (.nil _)
  refine ⟨g, sequence.trans last, H₀, hH₀, ⟨σ, ?_⟩, hEuler⟩
  intro j
  have hmap : H₀.trans (sequence.trans last).homeomorph =
      (H₀.trans sequence.homeomorph).trans H := by
    ext x
    simp only [Homeomorph.trans_apply, RealizedSequence.trans_homeomorph_apply]
    rfl
  rw [hmap]
  change (fun x ↦ H ((H₀.trans sequence.homeomorph) x)) '' _ = _
  rw [← Set.image_image, hσ j, hEdge]
  simp only [e.apply_symm_apply]

end HolomorphicAnosov.Topology.GallierXu

