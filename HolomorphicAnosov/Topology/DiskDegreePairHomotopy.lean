import Mathlib.Topology.Category.TopPair
import Mathlib.Topology.Homotopy.Basic

namespace HolomorphicAnosov.Topology

universe u

open Set TopologicalSpace TopCat

/-- The continuous map on a subspace induced by a continuous map preserving a subset. -/
def topPairSubspaceMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun x ↦ ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- A continuous map preserving subsets, regarded as a map of topological pairs. -/
def topPairMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : MapsTo f A B) :
    TopPair.ofSubset (X := TopCat.of X) A ⟶ TopPair.ofSubset (X := TopCat.of Y) B :=
  TopPair.ofHom (X := TopPair.ofSubset (X := TopCat.of X) A)
    (Y := TopPair.ofSubset (X := TopCat.of Y) B)
    (TopCat.ofHom f) (TopCat.ofHom (topPairSubspaceMap A B f hf)) (by cat_disch)

/-- A continuous homotopy preserving subsets induces a homotopy of topological pairs. -/
noncomputable def topPairHomotopy_of_continuousMapHomotopy
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y)
    (f g : C(X, Y)) (hf : MapsTo f A B) (hg : MapsTo g A B)
    (H : ContinuousMap.Homotopy f g)
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ B) :
    TopPair.Homotopy (topPairMap A B f hf) (topPairMap A B g hg) := by
  have hpair : Continuous (fun p : unitInterval × A ↦ (p.1, (p.2 : X))) := by
    have hsub : Continuous (fun p : unitInterval × A ↦ (p.2 : X)) :=
      by
        change Continuous ((fun x : A ↦ (x : X)) ∘ (Prod.snd : unitInterval × A → A))
        exact (continuous_subtype_val : Continuous (fun x : A ↦ (x : X))).comp
          (continuous_snd : Continuous (Prod.snd : unitInterval × A → A))
    fun_prop
  have hcont : Continuous (fun p : unitInterval × A ↦ H (p.1, p.2)) :=
    H.continuous.comp hpair
  let Hsub : C(unitInterval × A, B) :=
    ⟨fun p ↦ ⟨H (p.1, p.2), hH p.1 p.2 p.2.property⟩,
      hcont.subtype_mk _⟩
  let Hsnd : ContinuousMap.Homotopy
      (topPairSubspaceMap A B f hf) (topPairSubspaceMap A B g hg) :=
    { toFun := Hsub
      map_zero_left := by
        intro x
        apply Subtype.ext
        exact H.map_zero_left x
      map_one_left := by
        intro x
        apply Subtype.ext
        exact H.map_one_left x }
  exact { fst := H, snd := Hsnd }

end HolomorphicAnosov.Topology
