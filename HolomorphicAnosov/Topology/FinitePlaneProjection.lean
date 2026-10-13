import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
namespace HolomorphicAnosov

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A finite set of points in the Euclidean plane admits a real linear projection
that separates all points. This is the generic-direction choice for Cairns strip
subdivision. -/
theorem exists_injective_plane_projection_of_finite {S : Set Plane} (hS : S.Finite) :
    ∃ t : ℝ, Function.Injective (fun z : S => z.1 0 + t * z.1 1) := by
  let P : Set (Plane × Plane) := S ×ˢ S
  let g : Plane × Plane → ℝ := fun p => (p.2 0 - p.1 0) / (p.1 1 - p.2 1)
  have hP : P.Finite := hS.prod hS
  have hg : (g '' P).Finite := hP.image g
  obtain ⟨t, ht⟩ := hg.exists_notMem
  refine ⟨t, ?_⟩
  intro z w hzw
  by_contra hne
  have hpair : (z.1, w.1) ∈ P := ⟨z.2, w.2⟩
  have him : z.1 1 ≠ w.1 1 := by
    intro him
    have hre : z.1 0 = w.1 0 := by
      have := hzw
      simp [him] at this
      exact this
    apply hne
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hre
    · exact him
  have hroot : t = g (z.1, w.1) := by
    dsimp [g]
    apply (eq_div_iff (sub_ne_zero.mpr him)).2
    linarith [hzw]
  apply ht
  exact ⟨(z.1, w.1), hpair, hroot.symm⟩

end HolomorphicAnosov
