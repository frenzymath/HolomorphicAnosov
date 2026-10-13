import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- Two local inverse sheets of a covering agree near a common basepoint after a deck transformation
matching their values at that point. (Zhang, Lemma 4.2) -/
theorem inverse_sheets_differ_by_deck_locally
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (s t : X → Y) (D : Y → Y) (x : X)
    (hsc : ContinuousAt (fun z ↦ D (s z)) x) (htc : ContinuousAt t x)
    (hbase : D (s x) = t x) (W : Set Y) (hW : W ∈ 𝓝 (t x))
    (hinj : Set.InjOn p W) (hdeck : ∀ y, p (D y) = p y)
    (hs : ∀ᶠ z in 𝓝 x, p (s z) = z) (ht : ∀ᶠ z in 𝓝 x, p (t z) = z) :
    t =ᶠ[𝓝 x] fun z ↦ D (s z) := by
  have hWs : ∀ᶠ z in 𝓝 x, D (s z) ∈ W :=
    hsc (by simpa only [hbase] using hW)
  have hWt : ∀ᶠ z in 𝓝 x, t z ∈ W := htc hW
  filter_upwards [hWs, hWt, hs, ht] with z hzS hzT hzsp hztp
  apply hinj hzT hzS
  rw [hztp, hdeck, hzsp]


end HolomorphicAnosov.Paper.Zhang
