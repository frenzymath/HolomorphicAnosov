import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import HolomorphicAnosov.Topology.UnitSphereSimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Normed.Module.Connected

/-! # Native disk fillings from trivial boundary loops

Source: Hatcher, Algebraic Topology, Proposition 1.33 pp.61–62 and
Proposition 1B.9 pp.90–91. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HolomorphicAnosov

/-- Path connectedness of the native sphere, by Mathlib sphere path connectedness. -/
theorem native_sphere_path_connected_for_filling (n : ℕ) (hn : 1 ≤ n) :
    PathConnectedSpace {v : Fin (n + 1) → ℝ // ‖v‖ = 1} := by
  have hr : 1 < Module.rank ℝ (Fin (n + 1) → ℝ) := by
    simp only [← Module.finrank_eq_rank, Module.finrank_pi, Fintype.card_fin]
    exact_mod_cast (show 1 < n + 1 by omega)
  have hs := (isPathConnected_sphere hr (0 : Fin (n + 1) → ℝ) (by norm_num : (0:ℝ) ≤ 1))
  have he : Metric.sphere (0 : Fin (n + 1) → ℝ) 1 = {v | ‖v‖ = 1} := by
    ext v
    simp
  rw [he] at hs
  exact isPathConnected_iff_pathConnectedSpace.mp hs


/-- A native sphere map with trivial images of every loop extends to its closed disk.
Source: Hatcher, Proposition 1.33 pp.61–62 and Proposition 1B.9 pp.90–91.
For d≥2 the boundary sphere is path connected and locally path connected.
Choose a boundary point and a point over its image. Trivial loop images put
the image fundamental group in the covering map image, so the lifting
criterion supplies a continuous sphere lift. Contract it in the contractible
cover and project the contraction. The resulting jointly continuous sphere
nullhomotopy extends over the native disk, with literal boundary equality,
by the sphere-to-disk extension theorem. -/
theorem native_sphere_filling_of_trivial_loops
    {Y E : Type*} [TopologicalSpace Y] [TopologicalSpace E] [ContractibleSpace E]
    (d : ℕ) (hd : 2 ≤ d) (p : E → Y) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (b : C({v : Fin d → ℝ // ‖v‖ = 1}, Y))
    (hloops : ∀ a (γ : Path a a), (γ.map b.continuous).Homotopic (Path.refl (b a))) :
    ∃ B : {v : Fin d → ℝ // ‖v‖ ≤ 1} → Y, Continuous B ∧
      ∀ s, B ⟨s.val, le_of_eq s.property⟩ = b s := by
  have he : d - 1 + 1 = d := by omega
  have : PathConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := by
    have h := native_sphere_path_connected_for_filling (d - 1) (by omega)
    rw [he] at h
    exact h
  have : LocallyPathConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := by
    have h := (unit_sphere_locally_path_connected (d - 1)).2
    rw [he] at h
    exact h
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let a : {v : Fin d → ℝ // ‖v‖ = 1} := ⟨fun _ ↦ 1, by simp⟩
  obtain ⟨e, he⟩ := hsurj (b a)
  have hr : (FundamentalGroup.map b a).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range := by
    rintro _ ⟨g, rfl⟩
    have hg : FundamentalGroup.map b a g = 1 := by
      induction g using Path.Homotopic.Quotient.ind with
      | mk γ => exact Path.Homotopic.Quotient.eq.mpr (hloops a γ)
    rw [hg]
    exact ⟨1, map_one _⟩
  obtain ⟨L, hL, _⟩ := hp.existsUnique_continuousMap_lifts_of_range_le he hr
  obtain ⟨estar, ⟨H⟩⟩ := id_nullhomotopic E
  apply nullhomotopic_sphere_disk_extension d (by omega) b b.continuous
  refine ⟨p estar, fun q ↦ p (H (q.1, L q.2)), ?_, ?_, ?_⟩
  · exact hp.continuous.comp (H.continuous.comp
      (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
  · intro z
    simpa only [H.apply_zero, ContinuousMap.id_apply, Function.comp_apply] using congrFun hL.2 z
  · intro z
    simp only [H.apply_one, ContinuousMap.const_apply]

end HolomorphicAnosov
