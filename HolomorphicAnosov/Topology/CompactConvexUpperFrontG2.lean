import Mathlib.Analysis.Convex.Continuous

open Set Filter Topology

namespace HolomorphicAnosov

/-- The top boundary of a compact convex planar set over a closed interval is a
continuous concave graph.

Source: Rockafellar, Convex Analysis, §10 Theorem 10.2, pp.84–85; this elementary
one-dimensional version is used in Cairns' perspective coordinates. Every nonempty
compact vertical fiber has a greatest height. Convex combinations of maximizing
points prove concavity of the height. Concavity gives continuity in the open interval.
At either endpoint, compactness gives cluster points in the original set, whose
heights are at most the endpoint maximum. The affine chord between the two endpoint
maxima lies below the graph, so cluster heights are also at least that maximum.
Uniqueness of cluster points gives continuity at both endpoints. -/
theorem compact_convex_upper_front_g2 (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hproj : Prod.fst '' K = Icc (0 : ℝ) 1) :
    ∃ H : ℝ → ℝ, ContinuousOn H (Icc 0 1) ∧ ConcaveOn ℝ (Icc 0 1) H ∧
      ∀ s ∈ Icc (0 : ℝ) 1, (s, H s) ∈ K ∧ ∀ y, (s, y) ∈ K → y ≤ H s := by
  classical
  have hfiber (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ∃ y : ℝ, (s,y) ∈ K ∧ ∀ z, (s,z) ∈ K → z ≤ y := by
    have hne : (K ∩ {p | p.1 = s}).Nonempty := by
      obtain ⟨p, hp, hps⟩ := (show s ∈ Prod.fst '' K by rwa [hproj])
      exact ⟨p, hp, hps⟩
    obtain ⟨p, hp, hmax⟩ :=
      (hK.inter_right (isClosed_eq continuous_fst continuous_const)).exists_isMaxOn hne
        continuous_snd.continuousOn
    refine ⟨p.2, ?_, fun z hz ↦ hmax ⟨hz, rfl⟩⟩
    have he : p.1 = s := hp.2
    simpa only [← he, Prod.mk.eta] using hp.1
  let H : ℝ → ℝ := fun s ↦ if hs : s ∈ Icc (0 : ℝ) 1 then (hfiber s hs).choose else 0
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (s,H s) ∈ K ∧ ∀ z, (s,z) ∈ K → z ≤ H s := by
    simpa only [H, dite_eq_left hs] using (hfiber s hs).choose_spec
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) H := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hmem := hconv (hH x hx).1 (hH y hy).1 ha hb hab
    exact (hH _ ((convex_Icc 0 1) hx hy ha hb hab)).2 _ hmem
  let L : ℝ → ℝ := fun s ↦ (1-s)*H 0+s*H 1
  have hlow (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : L s ≤ H s := by
    have h := hconc.2 (show (0:ℝ) ∈ Icc 0 1 by norm_num)
      (show (1:ℝ) ∈ Icc 0 1 by norm_num) (sub_nonneg.mpr hs.2) hs.1
      (show 1-s+s=1 by ring)
    simpa [L] using h
  have hLc : Continuous L := by dsimp [L]; fun_prop
  have hend (s : ℝ) (hs : s = 0 ∨ s = 1) : ContinuousWithinAt H (Icc 0 1) s := by
    have hsI : s ∈ Icc (0 : ℝ) 1 := by rcases hs with rfl | rfl <;> norm_num
    have hLs : L s = H s := by rcases hs with rfl | rfl <;> simp [L]
    have hpair : Tendsto (fun t ↦ (t,H t)) (𝓝[Icc (0:ℝ) 1] s) (𝓝 (s,H s)) := by
      apply hK.tendsto_nhds_of_unique_mapClusterPt
        (eventually_of_mem self_mem_nhdsWithin fun t ht ↦ (hH t ht).1)
      intro p hp hc
      have hfst : p.1 = s := by
        have hc' : ClusterPt p.1 (𝓝[Icc (0:ℝ) 1] s) := by
          simpa only [Function.comp_def, MapClusterPt, map_id'] using
            hc.continuousAt_comp continuous_fst.continuousAt
        exact eq_of_nhds_neBot (hc'.mono nhdsWithin_le_nhds)
      have hle : L p.1 ≤ p.2 :=
        (isClosed_le (hLc.comp continuous_fst) continuous_snd).mem_of_mapClusterPt hc
          (eventually_of_mem self_mem_nhdsWithin hlow)
      apply Prod.ext hfst
      apply le_antisymm
      · exact (hH s hsI).2 p.2 (by simpa only [← hfst, Prod.mk.eta] using hp)
      · simpa [hfst, hLs] using hle
    exact continuous_snd.continuousAt.tendsto.comp hpair
  refine ⟨H, ?_, hconc, hH⟩
  intro s hs
  by_cases h0 : s = 0
  · exact hend s (Or.inl h0)
  by_cases h1 : s = 1
  · exact hend s (Or.inr h1)
  have hi : s ∈ interior (Icc (0:ℝ) 1) := by
    rw [interior_Icc]
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm h0), lt_of_le_of_ne hs.2 h1⟩
  exact (hconc.continuousOn_interior s hi).continuousAt
    (isOpen_interior.mem_nhds hi) |>.continuousWithinAt

end HolomorphicAnosov

