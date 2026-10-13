import Mathlib.Analysis.InnerProductSpace.PiL2
import HolomorphicAnosov.Topology.AffineSimplexCombinationEquiv
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace HolomorphicAnosov

open Set Topology _root_.Topology

/-- An ordered finite affinely independent face identifies the affine-coordinate hyperplane with the face's affine span by a homeomorphism. It is given by the barycentric combination map. (Hatcher) -/
theorem exists_geometric_face_affine_span_homeomorph
    (N d : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : s ∈ P.faces)
    (hcard : s.card = d + 1) :
    ∃ e : fintypeAffineCoords (Fin (d + 1)) ℝ ≃ₜ
      affineSpan ℝ (Set.range (fun i : Fin (d + 1) =>
        ((Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hcard)).symm i).val)),
      ∀ w, (e w).val = Finset.univ.affineCombination ℝ
        (fun i : Fin (d + 1) =>
          ((Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hcard)).symm i).val) w := by
  classical
  let efin : Fin (d + 1) ≃ s :=
    (Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hcard)).symm
  let pts : Fin (d + 1) → EuclideanSpace ℝ (Fin N) := fun i => (efin i).val
  have hind : AffineIndependent ℝ pts := by
    exact (P.indep hs).comp_embedding efin.toEmbedding
  let q : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin N)) d := ⟨pts, hind⟩
  let E := fintypeAffineCoords (Fin (d + 1)) ℝ
  let F := affineSpan ℝ (Set.range q.points)
  let : Nonempty E := ⟨⟨Pi.single 0 1, by
    rw [mem_fintypeAffineCoords_iff_sum]
    simp⟩⟩
  let : Nonempty F := ⟨⟨q.points 0, mem_affineSpan ℝ (Set.mem_range_self _)⟩⟩
  obtain ⟨e0, he0⟩ := exists_affineSimplexCombinationEquiv q
  let a : (Fin (d + 1) → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin N) :=
    Finset.univ.affineCombination ℝ q.points
  have hm : AffineSubspace.map a E ≤ F := by
    rw [AffineSubspace.map_le_iff_le_comap]
    intro w hw
    exact affineCombination_mem_affineSpan_of_nonempty
      (mem_fintypeAffineCoords_iff_sum.mp hw) q.points
  let ar : E →ᵃ[ℝ] F := a.restrict hm
  have har : Function.Bijective ar := by
    have ha : (ar : E → F) = e0 := by
      funext w
      apply Subtype.ext
      exact (he0 w).symm
    rw [ha]
    exact e0.bijective
  let ae : E ≃ᵃ[ℝ] F := AffineEquiv.ofBijective har
  let ce := ae.toContinuousAffineEquiv (𝕜 := ℝ) (PE := E) (PF := F)
  exact ⟨ce.toHomeomorph, by
    intro w
    exact rfl⟩

end HolomorphicAnosov
