import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Analysis.Convex.PathConnected
/-! Realizing one-box plaque transports by intrinsic paths. -/
noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
universe u v

variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]

def LocalPlaqueTransport.castPoints
    {F : TransverseContinuousFoliations.{u,v} s t M} {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x' = x) (hy : y' = y) :
    LocalPlaqueTransport F x' y' := hx.symm ▸ hy.symm ▸ e

@[simp] theorem LocalPlaqueTransport.castPoints_box
    {F : TransverseContinuousFoliations.{u,v} s t M} {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x' = x) (hy : y' = y) :
    (e.castPoints hx hy).box = e.box := by subst x'; subst y'; rfl

@[simp] theorem LocalPlaqueTransport.castPoints_transverse
    {F : TransverseContinuousFoliations.{u,v} s t M} {x y x' y' : M}
    (e : LocalPlaqueTransport F x y) (hx : x' = x) (hy : y' = y) :
    (e.castPoints hx hy).transverse = e.transverse := by subst x'; subst y'; rfl

theorem LocalPlaqueTransport.castPoints_property
    {F : TransverseContinuousFoliations.{u,v} s t M} {x y x' y' : M}
    (H : ∀ x y : M, OpenPartialHomeomorph (F.ULeaf x) (F.ULeaf y) → Prop)
    (e : LocalPlaqueTransport F x y) (hx : x' = x) (hy : y' = y) :
    H x' y' (e.castPoints hx hy).map ↔ H x y e.map := by subst x'; subst y'; rfl

/-- A property of every represented stable-path holonomy holds for each one-box plaque transport. -/
theorem localPlaqueTransport_of_path_property
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (H : ∀ x y : M, OpenPartialHomeomorph (F.ULeaf x) (F.ULeaf y) → Prop)
    (hH : ∀ q : Quotient F.stablePartition,
      ∀ x y : IntrinsicFoliationLeaf F.stablePartition q,
      ∀ (γ : Path x y) (a b : unitInterval) (e : PathHolonomyRepresentative F γ a b),
      H (γ a).val (γ b).val e.map)
    (x y : M) (e : LocalPlaqueTransport F x y) : H x y e.map := by
  let q := F.stableLabel e.box e.transverse
  let φ : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun z ↦ ⟨((F.box e.box).chart (z,e.transverse)).val,
      F.stable_label e.box z e.transverse⟩
  have hφ : Continuous φ := (F.stable_plaque e.box e.transverse).continuous
  have hj := ((convex_ball (0 : Fin s → ℝ) 1).isPathConnected
    ⟨e.first.val, e.first.property⟩).joinedIn e.first.val e.first.property
      e.second.val e.second.property
  let δ : Path e.first e.second := hj.joined_subtype.somePath
  let γ := δ.map hφ
  have h0 : (γ 0).val = x := by simp only [Path.source]; exact e.first_point
  have h1 : (γ 1).val = y := by simp only [Path.target]; exact e.second_point
  let e' : LocalPlaqueTransport F (γ 0).val (γ 1).val := e.castPoints h0 h1
  have hseg : ∀ r : unitInterval, (0 : unitInterval) ≤ r → r ≤ 1 →
      ∃ z : FoliationCoordinateDisk s,
        ((F.box e'.box).chart (z,e'.transverse)).val = (γ r).val := by
    intro r _ _
    have hbox : e'.box = e.box := by simp [e']
    have htrans : e'.transverse = e.transverse := by simp [e']
    rw [hbox, htrans]
    exact ⟨δ r, rfl⟩
  let E : PathHolonomyRepresentative F γ 0 1 :=
    { e'.toPointedLeafHomeomorph with
      chain := PlaqueChainAlong.single 0 1 (by simp) e' hseg }
  have hh := hH q (φ e.first) (φ e.second) γ 0 1 E
  exact (e.castPoints_property H h0 h1).mp hh

end HolomorphicAnosov

