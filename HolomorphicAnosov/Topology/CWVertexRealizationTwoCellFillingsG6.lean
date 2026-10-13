import HolomorphicAnosov.Topology.MappedLoopNullOfFactoredPiOneG6
import HolomorphicAnosov.Topology.NativeSphereFillingOfTrivialLoopsG6
import HolomorphicAnosov.Topology.CWOneSkeletonPiOneSurjective
import HolomorphicAnosov.Topology.CWComplex.SuccessorMapGluingG6
import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HolomorphicAnosov
universe u v w
/-- Two-cell filling stage for the based CW realization. Source: Hatcher Proposition 1B.9 pp.90–91 and Chapter 0 pp.14–15.

Proof: for each original two-cell restrict its characteristic disk map to the
native boundary sphere. Every boundary loop is null in the characteristic
disk and hence in K. Choose a one-skeleton path from k₀ to its image
basepoint. Conjugation and the given induced-map equality show that its
image under f₁ is null as well. The covering lifting criterion therefore
lifts the boundary map into E; contraction of E and projection to Y give
a sphere nullhomotopy. Extend it over the native disk with exact boundary
values. Choose such a filling for every two-cell and apply successor-map
gluing. Whenever a characteristic point lies in the lower skeleton its
coordinate is on the boundary, so the disk filling agrees with f₁ there.
This proves compatibility even for nonregular attaching identifications.
The resulting f₂ restricts literally to f₁ on the original one-skeleton. -/
theorem cw_vertex_realization_two_cell_fillings_g6
    {K : Type u} {Y : Type v} {E : Type w} [TopologicalSpace K] [TopologicalSpace Y]
    [TopologicalSpace E] [T2Space K] [ConnectedSpace K]
    [Topology.CWComplex (Set.univ : Set K)] [PathConnectedSpace Y] [ContractibleSpace E]
    (k₀ : K) (hk₀ : k₀ ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀) (hφ : φ ≠ 1)
    (f₁ : C((Topology.CWComplex.skeleton (Set.univ : Set K) (1 : ℕ∞) : Set K), Y))
    (hf₁ : f₁ ⟨k₀, Topology.CWComplex.skeleton_mono (by norm_num) hk₀⟩ = y₀)
    (hπ : FundamentalGroup.mapOfEq f₁ hf₁ = φ.comp (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ _)) :
    ∃ f₂ : C((Topology.CWComplex.skeleton (Set.univ : Set K) (2 : ℕ∞) : Set K), Y),
      ∀ x : (Topology.CWComplex.skeleton (Set.univ : Set K) (1 : ℕ∞) : Set K),
        f₂ ⟨x.val, Topology.CWComplex.skeleton_mono (by norm_num) x.property⟩ = f₁ x := by
  classical
  let K₁ := (Topology.CWComplex.skeleton (Set.univ : Set K) (1 : ℕ∞) : Set K)
  let k₁ : K₁ := ⟨k₀, Topology.CWComplex.skeleton_mono (by norm_num) hk₀⟩
  let j : C(K₁, K) := ⟨Subtype.val, continuous_subtype_val⟩
  have : PathConnectedSpace K₁ := (cw_one_skeleton_pi1_surjective k₀ hk₀).1
  subst y₀
  have hπ' : FundamentalGroup.map f₁ k₁ = φ.comp (FundamentalGroup.map j k₁) := by
    ext g
    have h := DFunLike.congr_fun hπ g
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, FundamentalGroup.map_apply, k₁, j] using h
  let S := {v : Fin 2 → ℝ // ‖v‖ = 1}
  let D := {v : Fin 2 → ℝ // ‖v‖ ≤ 1}
  have : ContractibleSpace D := by
    have he : (Metric.closedBall (0 : Fin 2 → ℝ) 1) = {v | ‖v‖ ≤ 1} := by
      ext v
      simp
    have : ContractibleSpace (Metric.closedBall (0 : Fin 2 → ℝ) 1) :=
      Metric.contractibleSpace_closedBall (by norm_num)
    exact (Homeomorph.setCongr he).symm.contractibleSpace
  let inc : C(S, D) := ⟨fun s ↦ ⟨s.val, le_of_eq s.property⟩,
    by
          apply Continuous.subtype_mk
          exact continuous_subtype_val⟩
  have fill (i : Topology.RelCWComplex.cell (Set.univ : Set K) 2) :
      ∃ B : C(Metric.closedBall (0 : Fin 2 → ℝ) 1, Y),
      ∀ z (hx : Topology.RelCWComplex.map 2 i z.val ∈ K₁),
        B z = f₁ ⟨Topology.RelCWComplex.map 2 i z.val, hx⟩ := by
    let χ : C(D, K) := ⟨fun z ↦ Topology.RelCWComplex.map 2 i z.val,
      (Topology.RelCWComplex.continuousOn 2 i).comp_continuous continuous_subtype_val
        (by intro z; simpa [Metric.mem_closedBall, dist_zero_right] using z.property)⟩
    let χs : C(S, K₁) :=
      ⟨fun z ↦ ⟨Topology.RelCWComplex.map 2 i z.val,
        Topology.CWComplex.cellFrontier_subset_skeleton 1 i
          ⟨z.val, by simpa [Metric.mem_sphere, dist_zero_right] using z.property, rfl⟩⟩,
        by
          apply Continuous.subtype_mk
          exact (Topology.RelCWComplex.continuousOn 2 i).comp_continuous
            continuous_subtype_val (by
              intro z
              simpa [Metric.mem_closedBall, dist_zero_right] using le_of_eq z.property)⟩
    have hloops (a : S) (γ : Path a a) :
        (γ.map (f₁.comp χs).continuous).Homotopic (Path.refl ((f₁.comp χs) a)) := by
      have hc := (SimplyConnectedSpace.paths_homotopic (γ.map inc.continuous)
        (Path.refl (inc a))).map χ
      have hj : ((γ.map χs.continuous).map j.continuous).Homotopic
          (Path.refl (j (χs a))) := by
        convert hc using 1 <;> ext t <;> rfl
      have hh := mapped_loop_null_of_factored_pi1 k₁ f₁ j φ hπ' (χs a)
        (γ.map χs.continuous) hj
      exact hh
    obtain ⟨B, hB, hBs⟩ := native_sphere_filling_of_trivial_loops 2 (by norm_num)
      p hp hsurj (f₁.comp χs) hloops
    let toD : C(Metric.closedBall (0 : Fin 2 → ℝ) 1, D) :=
      ⟨fun z ↦ ⟨z.val, by
        have h := z.property
        change dist z.val 0 ≤ 1 at h
        rwa [dist_zero_right] at h⟩,
        by
          apply Continuous.subtype_mk
          exact continuous_subtype_val⟩
    refine ⟨⟨B ∘ toD, hB.comp toD.continuous⟩, ?_⟩
    intro z hx
    exact hBs ⟨z.val, cw_successor_coordinate_boundary_of_lower 1 i z hx⟩
  choose B hB using fill
  exact cw_successor_map_gluing_g6 1 f₁ B hB
end HolomorphicAnosov
