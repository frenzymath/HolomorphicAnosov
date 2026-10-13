import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Analysis.Convex.PathConnected

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u v
variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,v} s t M)
/-- A stable path inside the displayed single box joining its two marked points. (Ghys) -/
def stableBoxPath
    (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk t) :
    letI := F.stableTopology (F.stableLabel b w)
    Path (⟨((F.box b).chart (z,w)).val, F.stable_label b z w⟩ :
        IntrinsicFoliationLeaf F.stablePartition (F.stableLabel b w))
      ⟨((F.box b).chart (z',w)).val, F.stable_label b z' w⟩ := by
  let := F.stableTopology (F.stableLabel b w)
  have : PathConnectedSpace (FoliationCoordinateDisk s) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_ball (0 : Fin s → ℝ) 1).isPathConnected ⟨0, by simp⟩)
  exact (PathConnectedSpace.somePath z z').map (F.stable_plaque b w).continuous

/-- The stable path above stays in its named original plaque for all times. -/
theorem stableBoxPath_in_plaque
    (b : F.boxIndex) (z z' : FoliationCoordinateDisk s) (w : FoliationCoordinateDisk t)
    (t : unitInterval) :
    letI := F.stableTopology (F.stableLabel b w)
    ∃ v : FoliationCoordinateDisk s,
      ((F.box b).chart (v,w)).val = (stableBoxPath F b z z' w t).val := by
  let := F.stableTopology (F.stableLabel b w)
  have : PathConnectedSpace (FoliationCoordinateDisk s) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_ball (0 : Fin s → ℝ) 1).isPathConnected ⟨0, by simp⟩)
  exact ⟨PathConnectedSpace.somePath z z' t, rfl⟩

/-- Relabeling equal marked endpoints preserves the chosen box and plaque. -/
def rebasePlaqueTransport {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x = x') (hy : y = y') :
    LocalPlaqueTransport F x' y' := by
  subst x'
  subst y'
  exact e

@[simp] theorem rebasePlaqueTransport_box {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x = x') (hy : y = y') :
    (rebasePlaqueTransport F e hx hy).box = e.box := by
  subst x'
  subst y'
  rfl

@[simp] theorem rebasePlaqueTransport_transverse {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x = x') (hy : y = y') :
    (rebasePlaqueTransport F e hx hy).transverse = e.transverse := by
  subst x'
  subst y'
  rfl

theorem rebasePlaqueTransport_segment {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x = x') (hy : y = y') (r : M) :
    (∃ v, ((F.box (rebasePlaqueTransport F e hx hy).box).chart
      (v, (rebasePlaqueTransport F e hx hy).transverse)).val = r) ↔
    (∃ v, ((F.box e.box).chart (v, e.transverse)).val = r) := by
  subst x'
  subst y'
  rfl


end HolomorphicAnosov.Ghys
