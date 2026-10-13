import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The two complementary regions of the unit circle

Cairns (1951), §1 and §2(A), p.860; Mathlib's sphere/ball connectedness,
connected-component maximality, and norm-ball frontier/closure formulas.
DAG node: `topo.circle_complement_regions_g6`.
-/

noncomputable section
open Set Metric

namespace HolomorphicAnosov

/-- The inside and outside of the unit circle are its two complementary regions.
Source: Cairns (1951), §1 and §2(A), p.860, the standard circle model; Hirsch,
Differential Topology, p.155, radial coordinates. The inside is convex. The outside
is the continuous radial image of the product of the connected unit sphere and
the connected interval of radii greater than one. Their disjoint open union is
the circle complement. A connected component meeting either set stays in that set,
and each of the two connected sets fills the component through any of its points.
The frontier and closure assertions are the usual norm-ball formulas.
-/
theorem circle_complement_regions :
    let Q := ball (0 : ℂ) 1
    let E := (closedBall (0 : ℂ) 1)ᶜ
    IsConnected Q ∧ IsConnected E ∧ IsOpen Q ∧ IsOpen E ∧
    Q ∪ E = (sphere (0 : ℂ) 1)ᶜ ∧ Disjoint Q E ∧
    (fun z : ℂ ↦ connectedComponentIn (sphere (0 : ℂ) 1)ᶜ z) ''
      (sphere (0 : ℂ) 1)ᶜ = {Q, E} ∧
    frontier Q = sphere (0 : ℂ) 1 ∧ frontier E = sphere (0 : ℂ) 1 ∧
    closure Q = closedBall (0 : ℂ) 1 := by
  intro Q E
  have hQ : IsConnected Q := isConnected_ball (by norm_num)
  have hs : IsConnected (sphere (0 : ℂ) 1) :=
    isConnected_sphere (by simp [Complex.rank_real_complex]) 0
      (by norm_num)
  have heq : (fun p : ℂ × ℝ ↦ p.2 • p.1) ''
      (sphere (0 : ℂ) 1 ×ˢ Ioi (1 : ℝ)) = E := by
    ext z
    constructor
    · rintro ⟨⟨w, r⟩, ⟨hw, hr⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hw
      change ¬dist (r • w) 0 ≤ 1
      simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, hw, mul_one]
      exact not_le.mpr (hr.trans_le (le_abs_self _))
    · intro hz
      have hz' : 1 < ‖z‖ := by simpa [E, mem_closedBall, dist_zero_right] using hz
      have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz')
      refine ⟨(‖z‖⁻¹ • z, ‖z‖), ⟨?_, hz'⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm]
        simp [hn]
      · exact smul_inv_smul₀ hn z
  have hE : IsConnected E := by
    rw [← heq]
    exact (hs.prod isConnected_Ioi).image _ (continuous_snd.smul continuous_fst).continuousOn
  have hoQ : IsOpen Q := isOpen_ball
  have hoE : IsOpen E := isClosed_closedBall.isOpen_compl
  have hu : Q ∪ E = (sphere (0 : ℂ) 1)ᶜ := by
    ext z
    simp only [Q, E, mem_union, mem_ball, mem_compl_iff, mem_closedBall, mem_sphere,
      dist_zero_right, not_le]
    exact ne_iff_lt_or_gt.symm
  have hd : Disjoint Q E := by
    rw [disjoint_left]
    intro z hz hz'
    exact hz' (ball_subset_closedBall hz)
  have hcomp (A B : Set ℂ) (hA : IsConnected A) (hoA : IsOpen A) (hoB : IsOpen B)
      (hdis : Disjoint A B) (hun : A ∪ B = (sphere (0 : ℂ) 1)ᶜ)
      {z : ℂ} (hz : z ∈ A) : connectedComponentIn (sphere (0 : ℂ) 1)ᶜ z = A := by
    have hsub : A ⊆ (sphere (0 : ℂ) 1)ᶜ := by rw [← hun]; exact subset_union_left
    apply subset_antisymm
    · apply IsPreconnected.subset_left_of_subset_union hoA hoB hdis
        (by rw [hun]; exact connectedComponentIn_subset _ _)
        ⟨z, mem_connectedComponentIn (hsub hz), hz⟩ isPreconnected_connectedComponentIn
    · exact hA.isPreconnected.subset_connectedComponentIn hz hsub
  refine ⟨hQ, hE, hoQ, hoE, hu, hd, ?_, frontier_ball _ one_ne_zero,
    ?_, closure_ball _ one_ne_zero⟩
  · ext A
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hu] at hz
      rcases hz with hz | hz
      · simp [hcomp Q E hQ hoQ hoE hd hu hz]
      · simp [hcomp E Q hE hoE hoQ hd.symm (by rwa [union_comm]) hz]
    · intro hA
      rcases hA with hA | hA
      · subst A
        obtain ⟨z, hz⟩ := hQ.nonempty
        exact ⟨z, by rw [← hu]; exact Or.inl hz, hcomp Q E hQ hoQ hoE hd hu hz⟩
      · have hA' : A = E := hA
        subst A
        obtain ⟨z, hz⟩ := hE.nonempty
        exact ⟨z, by rw [← hu]; exact Or.inr hz,
          hcomp E Q hE hoE hoQ hd.symm (by rwa [union_comm]) hz⟩
  · exact (frontier_compl _).trans (frontier_closedBall _ one_ne_zero)

end HolomorphicAnosov
