import Mathlib.Topology.Neighborhoods
import HolomorphicAnosov.Topology.OpenCoverPathSubdivision
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- A continuous map on a product admits a finite path subdivision whose compact path strips lie in assigned members of an open cover. -/
theorem exists_openCover_pathStripSubdivision
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x y : X} {ι : Type*} (γ : Path x y) (f : X × Y → Z) (hf : Continuous f)
    (w : Y) (V : ι → Set Z) (hV : ∀ i, IsOpen (V i))
    (hcover : ∀ t : unitInterval, ∃ i, f (γ t, w) ∈ V i) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → unitInterval,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∃ assigned : Fin n → ι, ∀ j : Fin n,
        let K := Set.range (γ.subpath (t j.castSucc) (t j.succ))
        IsCompact K ∧ IsConnected K ∧
          ∃ O : Set Y, IsOpen O ∧ w ∈ O ∧
            ∀ z ∈ K, ∀ v ∈ O, f (z, v) ∈ V (assigned j) := by
  let U : ι → Set X := fun i ↦ (fun z ↦ f (z, w)) ⁻¹' V i
  have hc : Continuous (fun z : X ↦ f (z, w)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  obtain ⟨n, hn, t, ht0, ht1, htmono, assigned, hsub⟩ :=
    exists_openCover_pathSubdivision γ U (fun i ↦ (hV i).preimage hc) hcover
  refine ⟨n, hn, t, ht0, ht1, htmono, assigned, ?_⟩
  intro j
  let δ := γ.subpath (t j.castSucc) (t j.succ)
  have hK : IsCompact (Set.range δ) := isCompact_range δ.continuous
  refine ⟨hK, isConnected_range δ.continuous, ?_⟩
  have htube : ∀ᶠ v in 𝓝 w, ∀ z ∈ Set.range δ, f (z, v) ∈ V (assigned j) := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hc' : Continuous (fun p : Y × X ↦ f (p.2, p.1)) :=
      hf.comp (continuous_snd.prodMk continuous_fst)
    exact hc'.continuousAt.eventually ((hV (assigned j)).mem_nhds (hsub j hz))
  obtain ⟨O, hOsub, hO, hw⟩ := mem_nhds_iff.mp htube
  exact ⟨O, hO, hw, fun z hz v hv ↦ hOsub hv z hz⟩


end HolomorphicAnosov
