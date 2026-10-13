import HolomorphicAnosov.Geometry.IdealDiskTriangle
import HolomorphicAnosov.Geometry.IdealTriangleReflectionTiling
import HolomorphicAnosov.Geometry.IdealTriangleReflectionDiskPreservationG2

/-! The file proves disk preservation for finite Lyubich reflection itineraries. (Lyubich, §2.4.13) -/

namespace HolomorphicAnosov

open scoped ComplexConjugate

/-- Every finite side-reflection itinerary of a marked ideal disk triangle preserves the open unit disk. (Lyubich, §2.4.13) -/
theorem lyubich_itinerary_map_disk_preserving
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) :
    Set.MapsTo (T.itineraryMap w) {z : ℂ | ‖z‖ < 1} {z : ℂ | ‖z‖ < 1} := by
  let disk : Set ℂ := {z : ℂ | ‖z‖ < 1}
  have hstep : ∀ i : Fin 3, Set.MapsTo
      (idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))) disk disk := by
    intro i z hz
    apply IdealDiskTriangle.idealDiskSideReflection_mem_disk_g2
      (T.norm_vertex i) (T.norm_vertex (i + 1))
    apply T.distinct.ne
    intro h
    have hv : (i : Nat) = ((i + 1 : Fin 3) : Nat) := congrArg Fin.val h
    omega
    exact hz
  have hfold : ∀ (w : List (Fin 3)) (g : ℂ → ℂ),
      Set.MapsTo g disk disk →
        Set.MapsTo (w.foldl (fun g i ↦ g ∘
          idealDiskSideReflection (T.vertex i) (T.vertex (i + 1))) g) disk disk := by
    intro ws
    induction ws with
    | nil =>
        intro g hg
        simpa using hg
    | cons i ws ih =>
        intro g hg
        apply ih
        exact hg.comp (hstep i)
  have h := hfold w id (by intro z hz; exact hz)
  simpa [MarkedIdealDiskTriangle.itineraryMap, disk] using h

end HolomorphicAnosov
