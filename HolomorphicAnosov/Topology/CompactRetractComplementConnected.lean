import HolomorphicAnosov.Topology.BoundedOpenDomainBoundaryFixedImage
import HolomorphicAnosov.Topology.OnePointClosedBallComplementConnected
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn

namespace HolomorphicAnosov

open Set Metric
open scoped OnePoint

/-- A compact retract of the complex plane has preconnected sphere complement.

Agent-written proof from bounded fixed-point existence and the standard exterior
component argument (Conway II, Chapter 13, pp.1–3). Enclose K in a closed disk.
If a complementary component missed the exterior of this disk, it would be a
nonempty bounded open set. Its frontier lies in K, so the retraction fixes that
frontier and sends the component into the disjoint set K. The preceding bounded
fixed-point argument rules this out. Every component therefore meets the connected
sphere exterior, which contains infinity. The union of each component with that
exterior connects each point of the complement to infinity. -/
theorem compact_retract_sphere_complement_preconnected
    (K : Set ℂ) (hK : IsCompact K) (R : C(ℂ, ℂ))
    (hRK : range R ⊆ K) (hfix : ∀ z ∈ K, R z = z) :
    IsPreconnected (OnePoint.some '' K)ᶜ := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let E : Set (OnePoint ℂ) := (OnePoint.some '' closedBall (0 : ℂ) r)ᶜ
  have hE : IsPreconnected E := (onePoint_closedBall_complement_connected hr.le).isPreconnected
  have hEK : E ⊆ (OnePoint.some '' K)ᶜ := compl_subset_compl.mpr (image_mono hKr)
  apply isPreconnected_of_forall (∞ : OnePoint ℂ)
  intro y hy
  cases y using OnePoint.rec with
  | infty => exact ⟨E, hEK, by simp [E], by simp [E], hE⟩
  | coe z =>
    have hz : z ∈ Kᶜ := by simpa using hy
    let A := connectedComponentIn Kᶜ z
    have hAo : IsOpen A := hK.isClosed.isOpen_compl.connectedComponentIn
    have hAz : z ∈ A := mem_connectedComponentIn hz
    have hAK : A ⊆ Kᶜ := connectedComponentIn_subset Kᶜ z
    have htouch : ∃ w ∈ A, r < ‖w‖ := by
      by_contra hn
      have hAb : Bornology.IsBounded A := (isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset (by
        intro w hw
        simp only [mem_closedBall, dist_zero_right]
        exact le_of_not_gt (fun h ↦ hn ⟨w, hw, h⟩))
      have hfront : frontier A ⊆ K := by
        simpa using frontier_connectedComponentIn_subset_compl hK.isClosed.isOpen_compl z
      obtain ⟨w, hwA, hwR⟩ := bounded_open_domain_image_meets A hAo hAb ⟨z, hAz⟩ R
        (hK.isBounded.subset hRK) (fun w hw ↦ hfix w (hfront hw))
      exact hAK hwA (hRK hwR)
    obtain ⟨w, hwA, hwr⟩ := htouch
    have hwE : (w : OnePoint ℂ) ∈ E := by
      simpa [E, mem_closedBall, dist_zero_right] using hwr
    refine ⟨(OnePoint.some '' A) ∪ E, union_subset ?_ hEK,
      Or.inr (by simp [E]), Or.inl ⟨z, hAz, rfl⟩, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      simpa using hAK ha
    · exact IsPreconnected.union' ⟨(w : OnePoint ℂ), ⟨w, hwA, rfl⟩, hwE⟩
        (isPreconnected_connectedComponentIn.image _ OnePoint.continuous_coe.continuousOn) hE

end HolomorphicAnosov
