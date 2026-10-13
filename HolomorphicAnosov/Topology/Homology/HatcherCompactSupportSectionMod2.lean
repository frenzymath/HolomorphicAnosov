import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.ConvexSupportModTwoLocalHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomologyEmpty
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.Homology.ModTwoLocalHomologyCompatibleFamily
import HolomorphicAnosov.Topology.Homology.CompactSupportClassOfLocalCompatibility
import HolomorphicAnosov.Topology.Homology.ModTwoSupportRestrictionComparison
import HolomorphicAnosov.Topology.Homology.HatcherCompactSupportDetectionMod2

/-!
Compact-support classes realizing compatible mod-two local homology families. (Hatcher, Lemma 3.27)
-/

noncomputable section

namespace HolomorphicAnosov.HatcherCompactSupport

universe u

open Set
open CategoryTheory
open CategoryTheory.Limits

/-- Every locally compatible mod-two local homology family has a unique compact-supported class realizing it; point restrictions detect zero and homology above the dimension vanishes. (Hatcher) -/
theorem hatcher_compact_support_section_mod2
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set M) (hA : IsCompact A)
    (s : ∀ x : M, SupportHomology ({x} : Set M) n) (hs : LocallyCompatible n s) :
    (∃! a : SupportHomology A n,
      ∀ x : A, supportToPoint A n x a = s x.val) ∧
    (∀ a : SupportHomology A n, (∀ x : A, supportToPoint A n x a = 0) → a = 0) ∧
    (∀ i : ℕ, n < i → Subsingleton (SupportHomology A i)) := by
  classical
  have hDV : ∀ K : Set M, IsCompact K →
      (∀ a : SupportHomology K n, (∀ x : K, supportToPoint K n x a = 0) → a = 0) ∧
      (∀ i : ℕ, n < i → Subsingleton (SupportHomology K i)) := by
    intro K hK
    by_cases hKn : K.Nonempty
    · exact hatcher_compact_support_section_mod2_nonempty_data n M K hK hKn
    · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKn
      subst K
      exact ⟨by intro a ha; exact (HolomorphicAnosov.Topology.Homology.modTwoSupportHomology_empty_subsingleton M n).elim _ _,
        by intro i hi; exact HolomorphicAnosov.Topology.Homology.modTwoSupportHomology_empty_subsingleton M i⟩
  let f := Int.castRingHom (ZMod 2)
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let W := (ModuleCat.restrictScalars.{u} f).obj V
  let X := TopCat.of M
  let e (K : Set M) : SupportHomology K n ≃+
      HolomorphicAnosov.Topology.supportSingularHomology X K W n :=
    (HolomorphicAnosov.Topology.Homology.ssetPairRestrictScalarsHomologyIso f
      (HolomorphicAnosov.Topology.supportSingularPair X K) V n).toLinearEquiv.toAddEquiv
  have hres {K L : Set M} (h : L ⊆ K) (a : SupportHomology K n) :
      e L (supportRestriction h n a) =
        HolomorphicAnosov.Topology.supportSingularHomologyRestrict X W h n (e K a) :=
    modTwoSupportRestriction_comparison M K L h n a
  have hdetect (K : Set M) (hKA : K ⊆ A) (hK : IsCompact K)
      (a : HolomorphicAnosov.Topology.supportSingularHomology X K W n)
      (ha : ∀ (x : M) (hx : x ∈ K),
        HolomorphicAnosov.Topology.supportSingularHomologyRestrict X W
          (Set.singleton_subset_iff.mpr hx) n a = 0) : a = 0 := by
    have hz : (e K).symm a = 0 := by
      apply (hDV K hK).1
      intro x
      apply (e {x.val}).injective
      change e {x.val} (supportRestriction (Set.singleton_subset_iff.mpr x.property) n
        ((e K).symm a)) = e {x.val} 0
      rw [hres, (e K).apply_symm_apply, map_zero]
      exact ha x.val x.property
    simpa using congrArg (e K) hz
  have hlocal (x : M) (_hx : x ∈ A) :
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
        ∃ aO : HolomorphicAnosov.Topology.supportSingularHomology X O W n,
          ∀ (y : M) (hy : y ∈ O),
            HolomorphicAnosov.Topology.supportSingularHomologyRestrict X W
              (Set.singleton_subset_iff.mpr hy) n aO = e {y} (s y) := by
    obtain ⟨c, r, hxc, hr, hrt, b, hb⟩ := hs x
    let O := chartBall c (c x) r
    refine ⟨O, c.isOpen_inter_preimage Metric.isOpen_ball,
      ⟨hxc, by simpa using hr⟩, e O b, ?_⟩
    intro y hy
    rw [← hres]
    exact congrArg (e {y}) (hb ⟨y, hy⟩)
  obtain ⟨a, ha, huniq⟩ := HolomorphicAnosov.compact_support_class_of_local_compatibility
    X W n A hA hdetect (fun x ↦ e {x} (s x)) hlocal
  refine ⟨⟨(e A).symm a, ?_, ?_⟩, (hDV A hA).1, (hDV A hA).2⟩
  · intro x
    apply (e {x.val}).injective
    change e {x.val} (supportRestriction (Set.singleton_subset_iff.mpr x.property) n
      ((e A).symm a)) = _
    rw [hres, (e A).apply_symm_apply]
    exact ha x.val x.property
  · intro b hb
    apply (e A).injective
    rw [(e A).apply_symm_apply]
    apply huniq
    intro x hx
    rw [← hres]
    exact congrArg (e {x}) (hb ⟨x, hx⟩)

end HolomorphicAnosov.HatcherCompactSupport
