import HolomorphicAnosov.Topology.DiskDegreePairHomotopy
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Relative homology under point-avoiding homotopies

Source: Hatcher, *Algebraic Topology*, Proposition 2.19, p.118, and the local
relative degree maps in §2.2, p.136. Translation of the avoided value to zero
identifies the target pair with the punctured group pair used to define degree.
-/

open CategoryTheory Set

namespace HolomorphicAnosov.Topology

/-- A homotopy avoiding a point on a specified subset gives equal relative homology
maps after translating that point to zero, in every degree.

Source and proof: Hatcher, Proposition 2.19, p.118, applied to the punctured target
pair in the local degree construction, p.136. Subtract the fixed value `w` at each
time of the homotopy. Continuity of subtraction gives a continuous homotopy with
endpoints `f - w` and `g - w`. Point avoidance on `A` says that this homotopy maps
`A` into the complement of zero at every time. Restrict it to `A` to obtain a
homotopy of topological pairs. The relative prism therefore gives equality on
homology. No closedness, compactness, or good-pair condition is used.
-/
theorem singularSubspacePairMap_homology_eq_of_avoiding_homotopy
    {X Y : Type} [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y]
    (A : Set X) (f g : C(X, Y)) (w : Y)
    (hf : ∀ x ∈ A, f x ≠ w) (hg : ∀ x ∈ A, g x ≠ w)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ≠ w) (n : ℕ) :
    SSetPair.homologyMap
        (singularSubspacePairMap
          (TopCat.ofHom ⟨fun x ↦ f x - w, f.continuous.sub continuous_const⟩)
          A ({0}ᶜ : Set Y) (fun x hx ↦ sub_ne_zero.mpr (hf x hx)))
        (ModuleCat.of ℤ ℤ) n =
      SSetPair.homologyMap
        (singularSubspacePairMap
          (TopCat.ofHom ⟨fun x ↦ g x - w, g.continuous.sub continuous_const⟩)
          A ({0}ᶜ : Set Y) (fun x hx ↦ sub_ne_zero.mpr (hg x hx)))
        (ModuleCat.of ℤ ℤ) n := by
  let F : C(X, Y) := ⟨fun x ↦ f x - w, f.continuous.sub continuous_const⟩
  let G : C(X, Y) := ⟨fun x ↦ g x - w, g.continuous.sub continuous_const⟩
  let H' : ContinuousMap.Homotopy F G :=
    { toFun := fun p ↦ H p - w
      continuous_toFun := H.continuous.sub continuous_const
      map_zero_left := fun x ↦ congrArg (fun v ↦ v - w) (H.map_zero_left x)
      map_one_left := fun x ↦ congrArg (fun v ↦ v - w) (H.map_one_left x) }
  exact (relative_singular_homotopy_invariance (ModuleCat ℤ)
    (topPairHomotopy_of_continuousMapHomotopy A ({0}ᶜ : Set Y) F G
      (fun x hx ↦ sub_ne_zero.mpr (hf x hx))
      (fun x hx ↦ sub_ne_zero.mpr (hg x hx)) H'
      (fun t x hx ↦ sub_ne_zero.mpr (hH t x hx))) (ModuleCat.of ℤ ℤ)).2 n


end HolomorphicAnosov.Topology
