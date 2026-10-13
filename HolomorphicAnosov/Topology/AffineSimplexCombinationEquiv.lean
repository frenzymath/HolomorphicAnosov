import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

namespace HolomorphicAnosov
open Set Function Affine

/-- Affine barycentric coordinates identify the affine span of a finite simplex with the
coefficient hyperplane of functions summing to one. This is the affine-coordinate step
in Hatcher, Algebraic Topology, §2.1 pp.103--104. -/
theorem exists_affineSimplexCombinationEquiv {P : Type*}
    [AddCommGroup P] [Module ℝ P] {n : ℕ} (s : Affine.Simplex ℝ P n) :
    let E := fintypeAffineCoords (Fin (n + 1)) ℝ
    let F := affineSpan ℝ (Set.range s.points)
    letI : Nonempty E := ⟨⟨Pi.single 0 1, by
      rw [mem_fintypeAffineCoords_iff_sum]
      simp⟩⟩
    letI : Nonempty F := ⟨⟨s.points 0, mem_affineSpan ℝ (Set.mem_range_self _)⟩⟩
    ∃ e : E ≃ F, ∀ w : E,
      (e w).val = Finset.univ.affineCombination ℝ s.points w := by
  dsimp only
  let E : AffineSubspace ℝ (Fin (n + 1) → ℝ) := fintypeAffineCoords (Fin (n + 1)) ℝ
  let F : AffineSubspace ℝ P := affineSpan ℝ (Set.range s.points)
  let : Nonempty E := ⟨⟨Pi.single 0 1, by
    rw [mem_fintypeAffineCoords_iff_sum]
    simp⟩⟩
  let : Nonempty F := ⟨⟨s.points 0, mem_affineSpan ℝ (Set.mem_range_self _)⟩⟩
  let a : (Fin (n + 1) → ℝ) →ᵃ[ℝ] P := Finset.univ.affineCombination ℝ s.points
  have hmap : AffineSubspace.map a E ≤ F := by
    rw [AffineSubspace.map_le_iff_le_comap]
    intro w hw
    rw [AffineSubspace.mem_comap]
    exact affineCombination_mem_affineSpan_of_nonempty (by simpa using (mem_fintypeAffineCoords_iff_sum.mp hw)) s.points
  let ar : E →ᵃ[ℝ] F := a.restrict hmap
  have har : Function.Bijective ar := by
    refine ⟨?_, ?_⟩
    · intro w₁ w₂ h
      have h' := congrArg Subtype.val h
      change a (w₁ : Fin (n + 1) → ℝ) = a (w₂ : Fin (n + 1) → ℝ) at h'
      exact Subtype.ext (s.independent.injOn_affineCombination_fintypeAffineCoords w₁.property w₂.property h')
    · intro q
      obtain ⟨w, hw, hq⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype q.property
      refine ⟨⟨w, mem_fintypeAffineCoords_iff_sum.mpr hw⟩, ?_⟩
      apply Subtype.ext
      exact hq.symm
  refine ⟨Equiv.ofBijective ar har, ?_⟩
  intro w
  exact rfl

end HolomorphicAnosov
