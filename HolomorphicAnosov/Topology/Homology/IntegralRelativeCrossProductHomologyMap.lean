import HolomorphicAnosov.Topology.Homology.IntegralRelativeProductData
import HolomorphicAnosov.Topology.Homology.IntegralRelativeChainProduct
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import HolomorphicAnosov.Topology.Homology.IntegralRelativeCrossProductLeftBoundaryAnnihilation
import HolomorphicAnosov.Topology.Homology.IntegralRelativeCrossProductRightBoundaryAnnihilation

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The native target cycle obtained from two source relative cycles. -/
theorem integral_relative_cross_product_target_cycle (X Y : TopCat.{u})
    (A : Set X) (B : Set Y) (p q : ℕ)
    (a : (RelativeComplex X A).cycles p)
    (b : (RelativeComplex Y B).cycles q) :
    ∃ cc : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).cycles (p + q),
      (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p + q) cc =
        integralRelativeChainProduct X Y A B p q
          ((RelativeComplex X A).iCycles p a)
          ((RelativeComplex Y B).iCycles q b) := by
  let T := RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)
  let S := T.sc (p + q)
  have h := integralRelativeChainProduct_cycles X Y A B p q a b
  let cc := S.cyclesMk
    (integralRelativeChainProduct X Y A B p q
      ((RelativeComplex X A).iCycles p a)
      ((RelativeComplex Y B).iCycles q b)) h
  refine ⟨cc, ?_⟩
  exact ShortComplex.i_cyclesMk S _ h

/-- The bilinear homology map and its native-cycle representative equation. -/
theorem integral_relative_cross_product_homology_map_boundary_descent :
    ∃ P : ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ),
        RelativeHomology X A p →ₗ[ℤ] RelativeHomology Y B q →ₗ[ℤ]
          RelativeHomology (TopCat.of (X × Y)) (ProductSubspace A B) (p + q),
      (∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
        (ca : (RelativeComplex X A).cycles p) (cb : (RelativeComplex Y B).cycles q),
        ∃ cc : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).cycles (p + q),
          (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p + q) cc =
            integralRelativeChainProduct X Y A B p q
              ((RelativeComplex X A).iCycles p ca)
              ((RelativeComplex Y B).iCycles q cb) ∧
          P X Y A B p q ((RelativeComplex X A).homologyπ p ca)
            ((RelativeComplex Y B).homologyπ q cb) =
              (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).homologyπ
                (p + q) cc) := by
  classical
  have hex (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ) :
      ∃ P : RelativeHomology X A p →ₗ[ℤ] RelativeHomology Y B q →ₗ[ℤ]
          RelativeHomology (TopCat.of (X × Y)) (ProductSubspace A B) (p + q),
        ∀ ca cb, ∃ cc,
          (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p + q) cc =
            integralRelativeChainProduct X Y A B p q
              ((RelativeComplex X A).iCycles p ca) ((RelativeComplex Y B).iCycles q cb) ∧
          P ((RelativeComplex X A).homologyπ p ca) ((RelativeComplex Y B).homologyπ q cb) =
            (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).homologyπ (p + q) cc := by
    let C := RelativeComplex X A
    let D := RelativeComplex Y B
    let T := RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)
    choose c hc using integral_relative_cross_product_target_cycle X Y A B p q
    change ∀ a b, T.iCycles (p + q) (c a b) =
      integralRelativeChainProduct X Y A B p q (C.iCycles p a) (D.iCycles q b) at hc
    have hinj := (ModuleCat.mono_iff_injective (T.iCycles (p + q))).mp inferInstance
    have cadd₁ (a a' : C.cycles p) (b : D.cycles q) : c (a + a') b = c a b + c a' b := by
      apply hinj
      simp only [map_add, hc, LinearMap.add_apply]
    have cadd₂ (a : C.cycles p) (b b' : D.cycles q) : c a (b + b') = c a b + c a b' := by
      apply hinj
      simp only [map_add, hc]
    have czero₁ (b : D.cycles q) : c 0 b = 0 := by
      apply hinj
      simp only [map_zero, hc, LinearMap.zero_apply]
    have czero₂ (a : C.cycles p) : c a 0 = 0 := by
      apply hinj
      simp only [map_zero, hc]
    let F : C.cycles p →ₗ[ℤ] D.cycles q →ₗ[ℤ] T.homology (p + q) :=
      integralLinear _ (ModuleCat.of ℤ (D.cycles q →ₗ[ℤ] T.homology (p + q)))
        { toFun := fun a ↦ integralLinear _ _
            { toFun := fun b ↦ T.homologyπ (p + q) (c a b)
              map_zero' := by rw [czero₂]; exact map_zero _
              map_add' := by intro b b'; rw [cadd₂]; exact map_add _ _ _ }
          map_zero' := by ext b; change T.homologyπ (p + q) (c 0 b) = 0; rw [czero₁]; exact map_zero _
          map_add' := by
            intro a a'; ext b
            change T.homologyπ (p + q) (c (a + a') b) = _
            rw [cadd₁]; exact map_add _ _ _ }
    have hboundary (a : C.cycles p) (b : D.cycles q)
        (hz : ∃ z : T.X (p + q + 1), T.d (p + q + 1) (p + q) z =
          integralRelativeChainProduct X Y A B p q (C.iCycles p a) (D.iCycles q b)) :
        F a b = 0 := by
      obtain ⟨z, hz⟩ := hz
      have he : c a b = T.toCycles (p + q + 1) (p + q) z := by
        apply hinj
        rw [hc]
        exact hz.symm.trans (congrArg (fun f ↦ f z) (T.toCycles_i (p + q + 1) (p + q))).symm
      change T.homologyπ (p + q) (c a b) = 0
      rw [he]
      exact congrArg (fun f ↦ f z) (T.toCycles_comp_homologyπ (p + q + 1) (p + q))
    have hleft : C.toCycles (p + 1) p ≫ ModuleCat.ofHom F = 0 := by
      ext x b
      apply hboundary
      apply integral_relative_cross_product_left_boundary_annihilation
      exact ⟨x, congrArg (fun f ↦ f x) (C.toCycles_i (p + 1) p)⟩
    let L := (CokernelCofork.IsColimit.desc' (C.homologyIsCokernel (p + 1) p (by simp))
      (ModuleCat.ofHom F) hleft).val.hom
    have hL (a : C.cycles p) (b : D.cycles q) : L (C.homologyπ p a) b = F a b := by
      exact congrArg (fun f ↦ f.hom a b)
        (CokernelCofork.IsColimit.desc' (C.homologyIsCokernel (p + 1) p (by simp))
          (ModuleCat.ofHom F) hleft).property
    have hright : D.toCycles (q + 1) q ≫ ModuleCat.ofHom (integralFlip _ _ _ L) = 0 := by
      ext y a
      obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ p)).mp inferInstance a
      change L (C.homologyπ p a) (D.toCycles (q + 1) q y) = 0
      rw [hL]
      apply hboundary
      apply integral_relative_cross_product_right_boundary_annihilation
      exact ⟨y, congrArg (fun f ↦ f y) (D.toCycles_i (q + 1) q)⟩
    let R := (CokernelCofork.IsColimit.desc' (D.homologyIsCokernel (q + 1) q (by simp))
      (ModuleCat.ofHom (integralFlip _ _ _ L)) hright).val.hom
    refine ⟨integralFlip _ _ _ R, ?_⟩
    intro a b
    refine ⟨c a b, hc a b, ?_⟩
    have hR := congrArg (fun f ↦ f.hom b (C.homologyπ p a))
      (CokernelCofork.IsColimit.desc' (D.homologyIsCokernel (q + 1) q (by simp))
        (ModuleCat.ofHom (integralFlip _ _ _ L)) hright).property
    exact hR.trans (hL a b)
  choose P hP using hex
  exact ⟨P, hP⟩

theorem integral_relative_cross_product_homology_map_provider :
    ∃ P : ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ),
        RelativeHomology X A p →ₗ[ℤ] RelativeHomology Y B q →ₗ[ℤ]
          RelativeHomology (TopCat.of (X × Y)) (ProductSubspace A B) (p + q),
      (∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
        (ca : (RelativeComplex X A).cycles p) (cb : (RelativeComplex Y B).cycles q),
        ∃ cc : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).cycles (p + q),
          (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p + q) cc =
            integralRelativeChainProduct X Y A B p q
              ((RelativeComplex X A).iCycles p ca)
              ((RelativeComplex Y B).iCycles q cb) ∧
          P X Y A B p q ((RelativeComplex X A).homologyπ p ca)
            ((RelativeComplex Y B).homologyπ q cb) =
              (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).homologyπ
                (p + q) cc) :=
  integral_relative_cross_product_homology_map_boundary_descent

end HolomorphicAnosov.Topology

