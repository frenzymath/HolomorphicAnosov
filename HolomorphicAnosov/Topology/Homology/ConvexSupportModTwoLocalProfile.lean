import HolomorphicAnosov.Topology.Homology.SupportHomeomorphismCoefficients
import HolomorphicAnosov.Topology.Homology.SupportNeighborhoodExcisionCoefficients
import HolomorphicAnosov.Topology.Homology.ConvexModTwoRestrictionIso
import HolomorphicAnosov.Topology.Homology.SphereReducedHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftDegree
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftBoundary
import HolomorphicAnosov.Topology.Homology.ModTwoULiftPointRelativeProfile
import HolomorphicAnosov.Topology.Homology.ModTwoULiftRadialRelativeProfile
import HolomorphicAnosov.Topology.Homology.ModTwoSupportPairProfileDescent
import HolomorphicAnosov.Topology.Homology.ModTwoSupportProfileHomeomorphTransport
import HolomorphicAnosov.Topology.Homology.ModTwoChartPointProfileExcision
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

/-!
Point-group profile for convex compact chart supports.
-/

universe u
noncomputable section
namespace HolomorphicAnosov.Topology.Homology

open Set CategoryTheory

/-- Every point of a nonempty compact convex chart support has the mod-two local profile concentrated in the manifold dimension. (Hatcher) -/
theorem hatcher_convex_support_mod2_local_point_profile
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (U : Set M) (hU : IsOpen U) (e : U ≃ₜ EuclideanSpace ℝ (Fin n))
    (A : Set M) (_hA : A.Nonempty) (hAcompact : IsCompact A) (hAU : A ⊆ U)
    (_hconvex : Convex ℝ (e '' {z : U | z.val ∈ A})) :
    ∀ x : A,
      Nonempty (modTwoSupportHomology M {x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        (∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology M {x.val} k)) := by
  let e' : U ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin n)) :=
    e.trans Homeomorph.ulift.symm
  have hpointU : ∀ x : A,
      Nonempty (modTwoSupportHomology U {z : U | z.val = x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        (∀ k : ℕ, k ≠ n →
          Subsingleton (modTwoSupportHomology U {z : U | z.val = x.val} k)) := by
    intro x
    have htarget :=
      (modTwo_ulift_euclidean_point_radial_profile n
        (e' ⟨x.val, hAU x.property⟩)).choose_spec.2
    have htransport := modTwo_support_profile_homeomorph_transport n e'
      ⟨x.val, hAU x.property⟩ htarget
    have hs : ({(⟨x.val, hAU x.property⟩ : U)} : Set U) =
        {z : U | z.val = x.val} := by
      ext z
      constructor
      · intro hz
        exact congrArg Subtype.val (Set.mem_singleton_iff.mp hz)
      · intro hz
        exact Subtype.ext hz
    rw [hs] at htransport
    exact htransport
  exact modTwo_chart_point_profile_excision n M U hU e A hAcompact hAU hpointU

end HolomorphicAnosov.Topology.Homology
