import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Convex.Contractible

/-!
# Punctured Euclidean one-point compactifications

Source: Hatcher, *Algebraic Topology*, Proposition 2B.1 proof, p.169, the
punctured-sphere base case; the maps here are Mathlib's native compactification and
stereographic homeomorphisms.
-/

noncomputable section
open Set
namespace HolomorphicAnosov

/-- Removing any point from the one-point compactification of Euclidean n-space
gives Euclidean n-space, including n=0.

Source: Hatcher Proposition 2B.1 proof, p.169. Identify the compactification with the unit sphere
in dimension n+1. Restrict that homeomorphism to the complements of the point
and its image. Stereographic projection centered at that image identifies its
complement with Euclidean n-space; its target is the whole Euclidean space.
-/
def euclideanPuncturedCompactificationHomeomorph (n : ℕ)
    (p : OnePoint (EuclideanSpace ℝ (Fin n))) :
    ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let e : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let s := stereographic' n (e p)
  have he : ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) ≃ₜ
      ({e p}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    e.subtype (by intro x; simp)
  exact he.trans ((Homeomorph.setCongr (stereographic'_source (n := n) (e p)).symm).trans
    (s.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) (e p))).trans
        (Homeomorph.Set.univ _))))

/-- The complement of a point in the Euclidean compactification is contractible.

Source: Hatcher Proposition 2B.1 proof, p.169. The stereographic homeomorphism identifies the
complement with a real vector space, whose linear contraction to zero is continuous.
-/
theorem euclideanPuncturedCompactification_contractible (n : ℕ)
    (p : OnePoint (EuclideanSpace ℝ (Fin n))) :
    ContractibleSpace ({p}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) :=
  (euclideanPuncturedCompactificationHomeomorph n p).contractibleSpace

end HolomorphicAnosov
