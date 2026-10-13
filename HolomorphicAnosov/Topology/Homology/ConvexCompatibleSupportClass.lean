import HolomorphicAnosov.Topology.Homology.ConvexSupportRestrictionIso
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Convex.PathConnected

/-!
Compatible point classes on a compact convex support. (Hatcher, Lemma 3.27)
-/

open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
namespace HolomorphicAnosov
universe u

/-- A locally compatible family of integral point-supported classes has a unique class on every nonempty compact convex support, in every degree. (Hatcher, Lemma 3.27) -/
theorem convex_compact_support_compatible_class {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ)
    (K : Set E) (hK : Convex ℝ K) (hcK : IsCompact K) (hnK : K.Nonempty)
    (α : ∀ x : E, supportSingularHomology (TopCat.of E) {x}
      reducedSingularIntegralCoefficients.{u} q)
    (hα : ∀ x : E, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧
      ∃ aW : supportSingularHomology (TopCat.of E) W
        reducedSingularIntegralCoefficients.{u} q,
      ∀ (y : E) (hy : y ∈ W), supportSingularHomologyRestrict (TopCat.of E)
        reducedSingularIntegralCoefficients.{u} (Set.singleton_subset_iff.mpr hy) q aW = α y) :
    ∃! aK : supportSingularHomology (TopCat.of E) K
      reducedSingularIntegralCoefficients.{u} q,
      ∀ (x : E) (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of E)
        reducedSingularIntegralCoefficients.{u} (Set.singleton_subset_iff.mpr hx) q aK = α x := by
  classical
  have hbij (A : Set E) (hA : Convex ℝ A) (hcA : IsCompact A)
      (x : E) (hx : x ∈ A) := convex_compact_support_restriction_bijective A hA hcA x hx q
  let R := reducedSingularIntegralCoefficients.{u}
  let H (A : Set E) := supportSingularHomology (TopCat.of E) A R q
  let res (A B : Set E) (h : B ⊆ A) : H A →+ H B :=
    supportSingularHomologyRestrict (TopCat.of E) R h q
  have comp {B C D : Set E} (hCB : C ⊆ B) (hDC : D ⊆ C) (a : H B) :
      res C D hDC (res B C hCB a) = res B D (hDC.trans hCB) a := by
    have hpair : supportSingularPairMap B C (𝟙 (TopCat.of E))
        (fun _ hx hC ↦ hx (hCB hC)) ≫
        supportSingularPairMap C D (𝟙 (TopCat.of E)) (fun _ hx hD ↦ hx (hDC hD)) =
        supportSingularPairMap B D (𝟙 (TopCat.of E))
          (fun _ hx hD ↦ hx (hCB (hDC hD))) := by
      ext <;> rfl
    have norm {B C : Set E} (h : C ⊆ B) : res B C h =
        (SSetPair.homologyMap
          (supportSingularPairMap B C (𝟙 (TopCat.of E)) (fun _ hx hC ↦ hx (h hC))) R q
          ).hom.toAddMonoidHom := by
      simp [res, supportSingularHomologyRestrict, supportSingularHomologyMap]
    rw [norm, norm, norm]
    change (SSetPair.homologyMap _ R q ≫ SSetPair.homologyMap _ R q) a = _
    rw [← SSetPair.homologyMap_comp, hpair]
    rfl
  obtain ⟨x₀, hx₀⟩ := hnK
  obtain ⟨a, ha⟩ := (hbij K hK hcK x₀ hx₀).surjective (α x₀)
  let good : K → Prop := fun x ↦ res K {x.val} (Set.singleton_subset_iff.mpr x.property) a = α x
  have hgood : IsLocallyConstant good := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨W, hW, hyW, aW, haW⟩ := hα y
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW y hyW
    let r := δ / 2
    have hr : 0 < r := half_pos hδ
    let A := K ∩ Metric.closedBall (y : E) r
    have hAK : A ⊆ K := Set.inter_subset_left
    have hAW : A ⊆ W := fun _ hz ↦ hball
      (Metric.closedBall_subset_ball (half_lt_self hδ) hz.2)
    have hAc : IsCompact A := hcK.inter_right Metric.isClosed_closedBall
    have hAv : Convex ℝ A := hK.inter (convex_closedBall (y : E) r)
    have hyA : (y : E) ∈ A := ⟨y.property, Metric.mem_closedBall_self hr.le⟩
    let b : H A := res K A hAK a
    let c : H A := res W A hAW aW
    have iff_good (z : K) (hzA : (z : E) ∈ A) : good z ↔ b = c := by
      let hpoint : {z.val} ⊆ A := Set.singleton_subset_iff.mpr hzA
      have hb : res A {z.val} hpoint b =
          res K {z.val} (Set.singleton_subset_iff.mpr z.property) a := comp hAK hpoint a
      have hc : res A {z.val} hpoint c = α z := by
        rw [show res A {z.val} hpoint c = res W {z.val} (hpoint.trans hAW) aW from
          comp hAW hpoint aW]
        exact haW z (hAW hzA)
      constructor
      · intro hz
        apply (hbij A hAv hAc z hzA).injective
        change res A {z.val} hpoint b = res A {z.val} hpoint c
        rw [hb, hc]
        exact hz
      · intro hbc
        change res K {z.val} (Set.singleton_subset_iff.mpr z.property) a = α z
        rw [← hb, hbc, hc]
    refine ⟨Subtype.val ⁻¹' Metric.ball (y : E) r,
      Metric.isOpen_ball.preimage continuous_subtype_val, Metric.mem_ball_self hr, ?_⟩
    intro z hz
    exact propext ((iff_good z ⟨z.property, Metric.ball_subset_closedBall hz⟩).trans
      (iff_good y hyA).symm)
  have : PreconnectedSpace K := Subtype.preconnectedSpace hK.isPreconnected
  have hall (x : E) (hx : x ∈ K) :
      res K {x} (Set.singleton_subset_iff.mpr hx) a = α x := by
    have heq := hgood.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x₀, hx₀⟩
    exact heq.mpr ha
  refine ⟨a, hall, ?_⟩
  intro a' ha'
  apply (hbij K hK hcK x₀ hx₀).injective
  exact (ha' x₀ hx₀).trans ha.symm

end HolomorphicAnosov

