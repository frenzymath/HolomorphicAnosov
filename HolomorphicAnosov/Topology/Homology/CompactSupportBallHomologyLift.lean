import HolomorphicAnosov.Topology.Homology.RelativeCycleRepresentative
import HolomorphicAnosov.Topology.Homology.SingularChainSupportFactorization
import HolomorphicAnosov.Topology.Homology.RelativeCycleLift
import HolomorphicAnosov.Topology.Homology.CompactSupportBallEnlargement
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport

/-!
# Compact support classes lift to finite centered ball unions

Source: Hatcher, Algebraic Topology, Lemma 3.27 step (4), pp.237–238.
This is the finite relative-cycle enlargement, with the actual restriction map.
-/

open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
namespace HolomorphicAnosov
universe u

/-- Every integral relative singular homology class supported on a compact K
in a proper metric space lifts to a compact finite union of positive-radius
closed balls centered at points of K, containing K in its interior.
The lift restricts to the original class by the actual identity-induced map.
Source: Hatcher, Lemma 3.27 step (4), pp.237–238.

Proof: choose a native relative-cycle representative and an ambient lift z.
Its boundary is the image of an actual chain b in the complement of K. The
ambient image C of the finite simplex-image support of b is compact and avoids
K. Choose a finite centered closed-ball enlargement L of K disjoint from C.
The support factorization theorem lifts b through the subspace of K-complement
lying outside L; mapping this chain into the complement of L preserves its
ambient image. Therefore z has boundary in the complement of L. The native
relative-cycle lifting theorem now yields a class supported on L, and quotient
naturality makes its restriction equal to the original class. The proof covers
empty K, zero chains, and degree zero; no orientability, convexity, vector-space
structure, or positive dimension is assumed. Properness ensures the ball union
is compact and is satisfied by the Euclidean chart model used in the parent. -/
theorem compact_support_ball_homology_lift
    {E : Type u} [MetricSpace E] [ProperSpace E]
    (K : Set E) (hK : IsCompact K) (i : ℕ)
    (a : ((supportSingularPair (TopCat.of E) K).homology (ModuleCat.of ℤ (ULift.{u} ℤ)) i :
      ModuleCat.{u} ℤ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ centers : Finset K,
      let L : Set E := ⋃ x ∈ centers, Metric.closedBall (x : E) r
      ∃ hKL : K ⊆ L,
        K ⊆ interior L ∧ IsCompact L ∧
        ∃ aL : ((supportSingularPair (TopCat.of E) L).homology (ModuleCat.of ℤ (ULift.{u} ℤ)) i :
          ModuleCat.{u} ℤ),
          SSetPair.homologyMap (supportSingularPairMap (X := TopCat.of E) (Y := TopCat.of E) L K
            (𝟙 _) (fun _ hv hK ↦ hv (hKL hK)))
            (ModuleCat.of ℤ (ULift.{u} ℤ)) i aL = a := by
  let X := TopCat.of E
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  let P := supportSingularPair X K
  obtain ⟨c, z, hc, hz, hb⟩ := relative_cycle_ambient_representative P R i a
  let j := (ComplexShape.down ℕ).next i
  obtain ⟨b, hb⟩ := hb j
  let C : Set E := Subtype.val '' integralSingularChainImageSupport (TopCat.of ↥(Kᶜ)) j b
  have hC : IsCompact C := (integralSingularChainImageSupport_isCompact _ _ b).image
    continuous_subtype_val
  have hKC : Disjoint K C := by
    rw [Set.disjoint_left]
    rintro x hx ⟨z, _, rfl⟩
    exact z.property hx
  obtain ⟨r, hr, _, centers, hcover, hcompact, hdisjoint⟩ :=
    compact_support_ball_enlargement K C hK hC.isClosed hKC 1 zero_lt_one
  let L : Set E := ⋃ x ∈ centers, Metric.closedBall (x : E) r
  have hKL : K ⊆ L := hcover.trans interior_subset
  have hbs : integralSingularChainImageSupport (TopCat.of ↥(Kᶜ)) j b ⊆
      Subtype.val ⁻¹' Lᶜ := by
    intro v hv hL
    exact Set.disjoint_left.mp hdisjoint hL ⟨v, hv, rfl⟩
  let A : Set ↥(Kᶜ) := Subtype.val ⁻¹' Lᶜ
  obtain ⟨d, hd⟩ := integralSingularChain_lift_of_imageSupport_subset (TopCat.of ↥(Kᶜ)) j b A hbs
  let f : TopCat.of A ⟶ TopCat.of ↥(Kᶜ) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let g : TopCat.of A ⟶ TopCat.of ↥(Lᶜ) := TopCat.ofHom
    ⟨fun v ↦ ⟨v.val.val, v.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let iK : TopCat.of ↥(Kᶜ) ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iL : TopCat.of ↥(Lᶜ) ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let bL := (SSet.chainComplexMap (TopCat.toSSet.map g) R).f j d
  have hsame : (SSet.chainComplexMap (TopCat.toSSet.map iL) R).f j bL =
      (SSet.chainComplexMap (TopCat.toSSet.map iK) R).f j b := by
    have he : SSet.chainComplexMap (TopCat.toSSet.map g) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map iL) R =
        SSet.chainComplexMap (TopCat.toSSet.map f) R ≫
          SSet.chainComplexMap (TopCat.toSSet.map iK) R := by
      dsimp only [SSet.chainComplexMap]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    have hej := congrArg (fun m ↦ m.f j d) he
    change (SSet.chainComplexMap (TopCat.toSSet.map iL) R).f j bL =
      (SSet.chainComplexMap (TopCat.toSSet.map iK) R).f j
        ((SSet.chainComplexMap (TopCat.toSSet.map f) R).f j d) at hej
    exact hej.trans (congrArg ((SSet.chainComplexMap (TopCat.toSSet.map iK) R).f j) hd)
  obtain ⟨aL, haL⟩ := relative_homology_lift_of_ambient_boundary
    (supportSingularPairMap (X := X) (Y := X) L K (𝟙 X) (fun _ hv hK ↦ hv (hKL hK)))
    R i c z
    ⟨bL, hsame.trans hb⟩ (by
      change (P.chainComplexπ R).f i
        ((SSet.chainComplexMap (TopCat.toSSet.map (𝟙 X)) R).f i z) = _
      rw [TopCat.toSSet.map_id]
      change (P.chainComplexπ R).f i ((SSet.chainComplexMap (𝟙 P.right) R).f i z) = _
      have hid : (SSet.chainComplexMap (𝟙 P.right) R).f i = 𝟙 _ := by
        exact congrArg (fun m ↦ m.f i)
          (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R).map_id P.right)
      rw [hid]
      exact hz)
  exact ⟨r, hr, centers, hKL, hcover, hcompact, aL, haL.trans hc⟩


end HolomorphicAnosov
