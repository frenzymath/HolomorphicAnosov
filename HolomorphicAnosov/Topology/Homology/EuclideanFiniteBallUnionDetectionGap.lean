import HolomorphicAnosov.Topology.Homology.EuclideanCompactConvexHomologyProfile
import HolomorphicAnosov.Topology.Homology.ConvexSupportRestrictionIso
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.FiniteCompactConvexUnionInduction
import HolomorphicAnosov.Topology.Homology.BallRestrictionInjective
import HolomorphicAnosov.Topology.Homology.EmptySupportSubsingleton

set_option maxHeartbeats 4000000 in
noncomputable section
namespace HolomorphicAnosov
open Set CategoryTheory CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology
universe u

theorem support_restrict_comp_local
    (X : TopCat.{0}) (R : ModuleCat.{0} ℤ) {K L A : Set X}
    (hLK : L ⊆ K) (hAL : A ⊆ L) (q : ℕ)
    (a : supportSingularHomology X K R q) :
    supportSingularHomologyRestrict X R hAL q
        (supportSingularHomologyRestrict X R hLK q a) =
      supportSingularHomologyRestrict X R (hAL.trans hLK) q a := by
  have hcomp : supportSingularPairMap K L (𝟙 X)
      (fun _ hx hL ↦ hx (hLK hL)) ≫
      supportSingularPairMap L A (𝟙 X)
        (fun _ hx hA ↦ hx (hAL hA)) =
      supportSingularPairMap K A (𝟙 X)
        (fun _ hx hA ↦ hx (hLK (hAL hA))) := by
    ext <;> rfl
  have hnorm {B C : Set X} (h : C ⊆ B) :
      supportSingularHomologyRestrict X R h q =
        (SSetPair.homologyMap
          (supportSingularPairMap B C (𝟙 X)
            (fun _ hx hC ↦ hx (h hC))) R q).hom.toAddMonoidHom := by
    simp [supportSingularHomologyRestrict, supportSingularHomologyMap]
  rw [hnorm, hnorm, hnorm]
  change (SSetPair.homologyMap _ R q ≫ SSetPair.homologyMap _ R q) a = _
  rw [← SSetPair.homologyMap_comp, hcomp]
  rfl

private theorem union_restriction_injective_local (D : CompactSupportMVData.{0}) (q : ℕ)
    (hnext : Subsingleton (supportSingularHomology D.space (D.left ∩ D.right)
      D.coefficients (q + 1) : Type 0)) :
    Function.Injective (supportMayerVietorisPhi D.space D.coefficients D.left D.right q) := by
  obtain ⟨δ, hδ, _⟩ := hatcher_compact_support_mayer_vietoris
  have he := (hδ D).1 q |>.1
  have hz : δ D q = 0 := by
    ext x
    have hx : x = 0 := hnext.elim x 0; rw [hx]; simp
  rw [hz] at he
  intro x y hxy
  have hker : supportMayerVietorisPhi D.space D.coefficients D.left D.right q (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z,hz⟩ := he (x-y) |>.mp hker
  exact sub_eq_zero.mp (by simpa using hz.symm)

private theorem union_zero_local (D : CompactSupportMVData.{0}) (q : ℕ)
    (hnext : Subsingleton (supportSingularHomology D.space (D.left ∩ D.right)
      D.coefficients (q + 1) : Type 0))
    (c : supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q)
    (hl : supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_left q c = 0)
    (hr : supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_right q c = 0) : c = 0 := by
  apply union_restriction_injective_local D q hnext
  change (_, -_) = _
  rw [hl, hr]
  simp

private theorem base_ball_profile (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : Convex ℝ K) (hcK : IsCompact K) :
    ((∀ a : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) K
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of _)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
      (∀ q : ℕ, n < q → Subsingleton (supportSingularHomology (TopCat.of _)
        K (ModuleCat.of ℤ (ULift.{0} ℤ)) q : Type 0))) := by
  by_cases hne : K.Nonempty
  · have hne' := hne
    obtain ⟨x,hx⟩ := hne
    have hix := convex_compact_support_restriction_isIso K hK hcK x hx n
    have hzero : ∀ a : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) K
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
        (∀ y (hy : y ∈ K), supportSingularHomologyRestrict (TopCat.of _)
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hy) n a = 0) → a = 0 := by
      intro a ha
      have hi : Function.Injective (supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n) := by
        exact ball_restriction_injective n K hK hcK x hx
      apply hi
      simpa using ha x hx
    constructor
    · exact hzero
    · intro q hq
      obtain ⟨hp,_⟩ := euclidean_compact_convex_homology_profile n K hK hcK hne'
      exact ModuleCat.subsingleton_of_isZero (hp q hq)
  · have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst K
    constructor
    · intro a ha
      exact (support_empty_subsingleton_public (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) n).elim _ _
    · intro q hq
      exact support_empty_subsingleton_public (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) q

private theorem point_restriction_union_left_local (n : ℕ)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (c : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) (A ∪ B)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n)
    (hc : ∀ x (hx : x ∈ A ∪ B),
      supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n c = 0) :
    ∀ x (hx : x ∈ A),
      supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n
        (supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) Set.subset_union_left n c) = 0 := by
  intro x hx
  rw [support_restrict_comp_local (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) Set.subset_union_left
    (Set.singleton_subset_iff.mpr hx) n c]
  exact hc x (Or.inl hx)

private theorem point_restriction_union_right_local (n : ℕ)
    (A B : Set (EuclideanSpace ℝ (Fin n)))
    (c : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) (A ∪ B)
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n)
    (hc : ∀ x (hx : x ∈ A ∪ B),
      supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n c = 0) :
    ∀ x (hx : x ∈ B),
      supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n
        (supportSingularHomologyRestrict (TopCat.of (EuclideanSpace ℝ (Fin n)))
          (ModuleCat.of ℤ (ULift.{0} ℤ)) Set.subset_union_right n c) = 0 := by
  intro x hx
  rw [support_restrict_comp_local (TopCat.of (EuclideanSpace ℝ (Fin n)))
    (ModuleCat.of ℤ (ULift.{0} ℤ)) Set.subset_union_right
    (Set.singleton_subset_iff.mpr hx) n c]
  exact hc x (Or.inr hx)

private theorem union_homology_subsingleton_local (D : CompactSupportMVData.{0}) (q : ℕ)
    (hleft : Subsingleton (supportSingularHomology D.space D.left D.coefficients q : Type 0))
    (hright : Subsingleton (supportSingularHomology D.space D.right D.coefficients q : Type 0))
    (hnext : Subsingleton (supportSingularHomology D.space (D.left ∩ D.right)
      D.coefficients (q + 1) : Type 0)) :
    Subsingleton (supportSingularHomology D.space (D.left ∪ D.right)
      D.coefficients q : Type 0) := by
  refine ⟨fun x y ↦ ?_⟩
  apply union_restriction_injective_local D q hnext
  apply Prod.ext
  · exact hleft.elim _ _
  · exact congrArg Neg.neg (hright.elim _ _)

/-- Finite unions of positive-radius closed Euclidean balls satisfy integral top-degree point detection and above-dimension vanishing. (Hatcher, Lemma 3.27) -/
theorem euclidean_finite_ball_union_detection_gap (n : ℕ) (r : ℝ) (_hr : 0 < r)
    (centers : Finset (EuclideanSpace ℝ (Fin n))) :
    let L : Set (EuclideanSpace ℝ (Fin n)) := ⋃ x ∈ centers, Metric.closedBall x r
    (∀ a : supportSingularHomology (TopCat.of (EuclideanSpace ℝ (Fin n))) L
      (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
      (∀ x (hx : x ∈ L), supportSingularHomologyRestrict (TopCat.of _)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q : ℕ, n < q → Subsingleton (supportSingularHomology (TopCat.of _)
      L (ModuleCat.of ℤ (ULift.{0} ℤ)) q : Type 0)) := by
  dsimp only
  let P : Set (EuclideanSpace ℝ (Fin n)) → Prop := fun K ↦
    (∀ a : supportSingularHomology (TopCat.of _) K (ModuleCat.of ℤ (ULift.{0} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of _)
        (ModuleCat.of ℤ (ULift.{0} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q : ℕ, n < q → Subsingleton (supportSingularHomology (TopCat.of _) K
      (ModuleCat.of ℤ (ULift.{0} ℤ)) q : Type 0))
  have hconv : ∀ K, IsCompact K → Convex ℝ K → P K := by
    intro K hc hv
    exact base_ball_profile n K hv hc
  have hunion : ∀ A B, IsCompact A → IsCompact B → P A → P B → P (A ∩ B) → P (A ∪ B) := by
    intro A B hA hB hPA hPB hPAB
    let D : CompactSupportMVData.{0} := ⟨TopCat.of (EuclideanSpace ℝ (Fin n)), inferInstance, A, B, hA, hB, ModuleCat.of ℤ (ULift.{0} ℤ)⟩
    have hnext := hPAB.2 (n+1) (Nat.lt_succ_self n)
    constructor
    · intro c hc
      apply union_zero_local D n hnext c
      · apply hPA.1
        exact point_restriction_union_left_local n A B c hc
      · apply hPB.1
        exact point_restriction_union_right_local n A B c hc
    · intro q hq
      apply union_homology_subsingleton_local D q (hPA.2 q hq) (hPB.2 q hq) (hPAB.2 (q+1) (lt_trans hq (Nat.lt_succ_self q)))
  exact finite_compact_convex_union_induction P hconv hunion centers
    (fun x ↦ Metric.closedBall x r)
    (fun _ _ ↦ isCompact_closedBall _ _) (fun _ _ ↦ convex_closedBall _ _)

end HolomorphicAnosov
