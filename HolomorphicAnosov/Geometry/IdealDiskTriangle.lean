import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment

/-! ideal triangles and reflections in the disk. (Lyubich, §2.4.4) -/

namespace HolomorphicAnosov

open scoped ComplexConjugate

/-- Three marked distinct unit-circle points in positive cyclic order. (Lyubich, §2.4.4) -/
structure MarkedIdealDiskTriangle where
  vertex : Fin 3 → ℂ
  norm_vertex : ∀ i, ‖vertex i‖ = 1
  distinct : Function.Injective vertex
  positive_order : ∃ θ₀ θ₁ θ₂ : ℝ,
    θ₀ < θ₁ ∧ θ₁ < θ₂ ∧ θ₂ < θ₀ + 2 * Real.pi ∧
    vertex 0 = Complex.exp (θ₀ * Complex.I) ∧
    vertex 1 = Complex.exp (θ₁ * Complex.I) ∧
    vertex 2 = Complex.exp (θ₂ * Complex.I)

/-- The radial disk-to-Klein coordinate formula. (Lyubich, §2.4.4) -/
noncomputable def idealDiskKlein (z : ℂ) : ℂ :=
  2 * z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)

/-- The actual open ideal-triangle interior determined by its three vertices. (Lyubich, §2.4.4) -/
noncomputable def MarkedIdealDiskTriangle.interiorSet (T : MarkedIdealDiskTriangle) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ idealDiskKlein z ∈ interior (convexHull ℝ (Set.range T.vertex))}

/-- The filled closed ideal triangle, including its three boundary vertices. (Lyubich, §2.4.4) -/
noncomputable def MarkedIdealDiskTriangle.closedSet (T : MarkedIdealDiskTriangle) : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ idealDiskKlein z ∈ convexHull ℝ (Set.range T.vertex)}

/-- The open geodesic side between two marked vertices, with endpoints excluded. (Lyubich, §2.4.4) -/
noncomputable def MarkedIdealDiskTriangle.openSide
    (T : MarkedIdealDiskTriangle) (i j : Fin 3) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ idealDiskKlein z ∈ openSegment ℝ (T.vertex i) (T.vertex j)}

/-- Reflection in the geodesic joining distinct unit-circle points `a` and `b`. (Lyubich, §2.4.4) -/
noncomputable def idealDiskSideReflection (a b z : ℂ) : ℂ :=
  ((a + b) - 2 * a * b * conj z) / (2 - (a + b) * conj z)

/-- The source map of a finite reflection itinerary in the initial three sides. (Lyubich, §2.4.4) -/
noncomputable def MarkedIdealDiskTriangle.itineraryMap
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) : ℂ → ℂ :=
  w.foldl (fun g i ↦ g ∘ idealDiskSideReflection (T.vertex i)
    (T.vertex (i + 1))) id

/-- The open triangle reached by a finite reflection itinerary. (Lyubich, §2.4.4) -/
noncomputable def MarkedIdealDiskTriangle.itineraryInteriorSet
    (T : MarkedIdealDiskTriangle) (w : List (Fin 3)) : Set ℂ :=
  T.itineraryMap w '' T.interiorSet

end HolomorphicAnosov
