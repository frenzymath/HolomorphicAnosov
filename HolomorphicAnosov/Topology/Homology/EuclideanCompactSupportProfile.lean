import HolomorphicAnosov.Topology.Homology.EuclideanFiniteBallUnionDetectionGap
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLift
import HolomorphicAnosov.Topology.Homology.IntegralSupportRestrictionNormalization

noncomputable section
namespace HolomorphicAnosov
open Set CategoryTheory HolomorphicAnosov.Topology _root_.Topology

/-- Compact Euclidean supports satisfy integral point detection and vanishing above ambient dimension. (Hatcher, Lemma 3.27) -/
theorem euclidean_compact_support_profile (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    (∀ a : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) K
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of _)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q : ℕ, n < q → Subsingleton (supportSingularHomology (TopCat.of _)
      K (ModuleCat.of ℤ (ULift.{0} ℤ)) q : Type 0)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let X := TopCat.of E
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  have lift (q : ℕ) (a : supportSingularHomology X K R q) :=
    compact_support_ball_homology_lift K hK q a
  constructor
  · intro a ha
    obtain ⟨r, hr, centers, hKL, _, _, b, hb⟩ := lift n a
    let L : Set E := ⋃ c ∈ centers, Metric.closedBall (c : E) r
    have hLi : L = ⋃ c ∈ centers.image (fun z : K ↦ (z : E)), Metric.closedBall c r := by
      ext x
      simp [L]
    have hprofile := euclidean_finite_ball_union_detection_gap n r hr
      (centers.image (fun z : K ↦ (z : E)))
    rw [← hLi] at hprofile
    have hb' : supportSingularHomologyRestrict X R hKL n b = a := by
      rw [integral_support_restrict_native_apply]
      exact hb
    have hzero : b = 0 := by
      apply hprofile.1 b
      intro x hx
      obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hc, hxc⟩ := Set.mem_iUnion.mp hxc
      have hball : Metric.closedBall (c : E) r ⊆ L :=
        fun y hy ↦ Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, hy⟩⟩
      have hcenter : (c : E) ∈ Metric.closedBall (c : E) r :=
        Metric.mem_closedBall_self hr.le
      have hbball : supportSingularHomologyRestrict X R hball n b = 0 := by
        apply ball_restriction_injective n (Metric.closedBall (c : E) r)
          (convex_closedBall _ _) (isCompact_closedBall _ _) c hcenter
        rw [map_zero, support_restrict_comp_local X R hball]
        have hh := support_restrict_comp_local X R hKL
          (Set.singleton_subset_iff.mpr c.property) n b
        rw [hb'] at hh
        exact hh.symm.trans (ha c c.property)
      have hh := support_restrict_comp_local X R hball
        (Set.singleton_subset_iff.mpr hxc) n b
      rw [hbball, map_zero] at hh
      exact hh.symm
    rw [hzero, map_zero] at hb'
    exact hb'.symm
  · intro q hq
    have hz (a : supportSingularHomology X K R q) : a = 0 := by
      obtain ⟨r, hr, centers, hKL, _, _, b, hb⟩ := lift q a
      let L : Set E := ⋃ c ∈ centers, Metric.closedBall (c : E) r
      have hLi : L = ⋃ c ∈ centers.image (fun z : K ↦ (z : E)), Metric.closedBall c r := by
        ext x
        simp [L]
      have hprofile := euclidean_finite_ball_union_detection_gap n r hr
        (centers.image (fun z : K ↦ (z : E)))
      rw [← hLi] at hprofile
      have hzero : b = 0 := (hprofile.2 q hq).elim _ _
      rw [hzero, map_zero] at hb
      exact hb.symm
    exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end HolomorphicAnosov
