import HolomorphicAnosov.Topology.Homology.IntegralRelativeChainProduct
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

theorem integral_relative_cross_product_cast_differential
    {X : TopCat.{u}} {A : Set X} {m n : ℕ}
    (h : m = n) (h' : m - 1 = n - 1)
    (a : (RelativeComplex X A).X m) :
    ((RelativeComplex X A).d n (n - 1)).hom
        (integralRelativeChainProduct_castRelativeChain h a) =
      integralRelativeChainProduct_castRelativeChain h'
        (((RelativeComplex X A).d m (m - 1)).hom a) := by
  subst n
  rfl

theorem integral_relative_cross_product_cast_chain_comp
    {X : TopCat.{u}} {A : Set X} {m n k : ℕ}
    (h : m = n) (h' : n = k) (a : (RelativeComplex X A).X m) :
    integralRelativeChainProduct_castRelativeChain h'
        (integralRelativeChainProduct_castRelativeChain h a) =
      integralRelativeChainProduct_castRelativeChain (h.trans h') a := by
  subst n
  subst k
  rfl

theorem integral_relative_cross_product_cast_differential_target
    {X : TopCat.{u}} {A : Set X} {m n k : ℕ}
    (h : m = n) (h' : m - 1 = k)
    (a : (RelativeComplex X A).X m) :
    ((RelativeComplex X A).d n k).hom
        (integralRelativeChainProduct_castRelativeChain h a) =
      integralRelativeChainProduct_castRelativeChain h'
        (((RelativeComplex X A).d m (m - 1)).hom a) := by
  subst n
  subst k
  rfl

theorem integral_relative_cross_product_cast_relative_proof_irrel
    {X : TopCat.{u}} {A : Set X} {m n : ℕ} (h h' : m = n)
    (a : (RelativeComplex X A).X m) :
    integralRelativeChainProduct_castRelativeChain h a =
      integralRelativeChainProduct_castRelativeChain h' a := by
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

/-- Positive-degree source boundary transport for the left boundary-annihilation interface.  -/
theorem integral_relative_cross_product_left_positive_boundary_source
    (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
    (ca : (RelativeComplex X A).cycles p)
    (cb : (RelativeComplex Y B).cycles (q + 1))
    (x : (RelativeComplex X A).X (p + 1))
    (hx : (RelativeComplex X A).iCycles p ca = (RelativeComplex X A).d (p + 1) p x)
    (c : Chain X (p + 1))
    (hc : relativeProjection X A (p + 1) c = x)
    (d : Chain Y (q + 1))
    (hd : relativeProjection Y B (q + 1) d = (RelativeComplex Y B).iCycles (q + 1) cb)
    (ud : Chain (TopCat.of B) q)
    (hud :
      (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B))
        singularIntegralCoefficients).f q ud =
        ((TopCat.toSSet.obj Y).chainComplex singularIntegralCoefficients).d
          (q + 1) q d)
    (hm : p + (q + 1) = (p + 1) + (q + 1) - 1) :
    ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).d
      ((p + 1) + (q + 1)) (((p + 1) + (q + 1)) - 1)).hom
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d)) =
      integralRelativeChainProduct_castRelativeChain hm
        (integralRelativeChainProduct X Y A B p (q + 1)
          ((RelativeComplex X A).iCycles p ca)
          ((RelativeComplex Y B).iCycles (q + 1) cb)) := by
  rw [integral_relative_projection_differential_comm]
  have hdx : relativeProjection X A p
      (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) =
      (RelativeComplex X A).iCycles p ca := by
    have h := congrArg (fun f => f.hom c)
      (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).comm
        (p + 1) p)
    change (RelativeComplex X A).d (p + 1) p
        (relativeProjection X A (p + 1) c) = _ at h
    rw [hc, ← hx] at h
    exact h.symm
  have hp := congrArg
    (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)).hom
    (integral_cross_product_positive_boundary X Y p q c d)
  let P := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + q + 1)
  erw [P.hom.map_add, P.hom.toAddMonoidHom.map_zsmul] at hp
  dsimp only [P, LinearMap.toAddMonoidHom_coe] at hp
  erw [integralRelativeChainProduct_relativeProjection_cast,
    integralRelativeChainProduct_relativeProjection_cast,
    integralRelativeChainProduct_relativeProjection_cast] at hp
  erw [← hud, signedCrossProduct_right_subspace_vanishes A B (p + 1) q c ud,
    integralRelativeChainProduct_castRelativeChain_zero, zsmul_zero, add_zero] at hp
  erw [← integralRelativeChainProduct_projection, hdx, hd] at hp
  have hinj {m n : ℕ} (h : m = n) : Function.Injective
      (integralRelativeChainProduct_castRelativeChain
        (X := TopCat.of (X × Y)) (A := ProductSubspace A B) h) := by
    subst n
    exact Function.injective_id
  apply hinj (show ((p + 1) + (q + 1)) - 1 = p + q + 1 by omega)
  rw [integral_relative_cross_product_cast_chain_comp]
  exact hp

/-- Boundary annihilation in the left variable for the relative signed chain product. -/
theorem integral_relative_cross_product_left_boundary_annihilation :
    ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
      (ca : (RelativeComplex X A).cycles p)
      (cb : (RelativeComplex Y B).cycles q),
      (∃ x : (RelativeComplex X A).X (p + 1),
        (RelativeComplex X A).iCycles p ca =
          (RelativeComplex X A).d (p + 1) p x) →
      ∃ z : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).X (p + q + 1),
        (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).d (p + q + 1) (p + q) z =
          integralRelativeChainProduct X Y A B p q
            ((RelativeComplex X A).iCycles p ca)
            ((RelativeComplex Y B).iCycles q cb) := by
  intro X Y A B p q ca cb hca
  cases q with
  | zero =>
      obtain ⟨x, hx⟩ := hca
      obtain ⟨(c : Chain X (p + 1)), hc⟩ := (ModuleCat.epi_iff_surjective (relativeProjection X A (p + 1))).mp
        (Cofork.IsColimit.epi
          ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX
            singularIntegralCoefficients (p + 1))) x
      obtain ⟨d, hd, ud, hud⟩ := integral_relative_cycle_ambient_boundary_lift Y B 0 cb
      let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
      let z := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) (p + 1)
        (signedSingularCrossProduct X Y (p + 1) 0 c d)
      refine ⟨z, ?_⟩
      change (T.d (p + 1) p).hom z = _
      have hcomm := congrArg (fun f => f.hom
          (signedSingularCrossProduct X Y (p + 1) 0 c d))
        (((singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)).chainComplexπ
          singularIntegralCoefficients).comm (p + 1) p)
      change (T.d (p + 1) p).hom z =
        relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) p
          (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
            (p + 1) p (signedSingularCrossProduct X Y (p + 1) 0 c d)) at hcomm
      rw [hcomm]
      have hbd := integralRelativeChainProduct_zero_right_boundary X Y p c d
      have hbd' :
          relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) p
              (((TopCat.toSSet.obj (TopCat.of (X × Y))).chainComplex singularIntegralCoefficients).d
                (p + 1) p (signedSingularCrossProduct X Y (p + 1) 0 c d)) =
            relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) p
              (signedSingularCrossProduct X Y p 0
                (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) d) := by
        simpa only [Nat.add_zero] using congrArg
          (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) p).hom hbd
      rw [hbd']
      have hdx :
          relativeProjection X A p
              (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) =
            (RelativeComplex X A).iCycles p ca := by
        have hcommX := congrArg (fun f => f.hom c)
          (((singularSubspacePair X A).chainComplexπ singularIntegralCoefficients).comm
            (p + 1) p)
        change (RelativeComplex X A).d (p + 1) p
            (relativeProjection X A (p + 1) c) =
          relativeProjection X A p
            (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) at hcommX
        rw [hc, ← hx] at hcommX
        exact hcommX.symm
      have hprod := integralRelativeChainProduct_projection X Y A B p 0
        (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) d
      have hprod' :
          relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B) p
              (signedSingularCrossProduct X Y p 0
                (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c) d) =
            integralRelativeChainProduct X Y A B p 0
              (relativeProjection X A p
                (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (p + 1) p c))
              (relativeProjection Y B 0 d) := by
        simpa only [Nat.add_zero] using hprod.symm
      rw [hprod', hdx, hd]
  | succ q =>
      obtain ⟨x, hx⟩ := hca
      obtain ⟨(c : Chain X (p + 1)), hc⟩ :=
        (ModuleCat.epi_iff_surjective (relativeProjection X A (p + 1))).mp
          (Cofork.IsColimit.epi
            ((singularSubspacePair X A).isColimitCokernelCoforkChainComplexX
              singularIntegralCoefficients (p + 1))) x
      obtain ⟨d, hd, ud, hud⟩ := integral_relative_cycle_ambient_boundary_lift Y B (q + 1) cb
      let T := (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B))
      let he : (p + 1) + (q + 1) = p + q + 2 := by omega
      let z0 := integralRelativeChainProduct_castRelativeChain he
        (relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d))
      have hz0 :
          (T.d (p + q + 2) (p + q + 1)).hom z0 =
            integralRelativeChainProduct X Y A B p (q + 1)
              ((RelativeComplex X A).iCycles p ca)
              ((RelativeComplex Y B).iCycles (q + 1) cb) := by
        let zsrc := relativeProjection (TopCat.of (X × Y)) (ProductSubspace A B)
          ((p + 1) + (q + 1))
          (signedSingularCrossProduct X Y (p + 1) (q + 1) c d)
        have hcast := integral_relative_cross_product_cast_differential_target
          (X := TopCat.of (X × Y)) (A := ProductSubspace A B)
          he (by omega : (p + 1) + (q + 1) - 1 = p + q + 1) zsrc
        change (T.d (p + q + 2) (p + q + 1)).hom
            (integralRelativeChainProduct_castRelativeChain he zsrc) = _
        rw [hcast]
        let hm : p + (q + 1) = (p + 1) + (q + 1) - 1 := by omega
        have hsource :
            (T.d ((p + 1) + (q + 1)) (((p + 1) + (q + 1)) - 1)).hom zsrc =
              integralRelativeChainProduct_castRelativeChain hm
                (integralRelativeChainProduct X Y A B p (q + 1)
                  ((RelativeComplex X A).iCycles p ca)
                  ((RelativeComplex Y B).iCycles (q + 1) cb)) := by
          exact integral_relative_cross_product_left_positive_boundary_source
            X Y A B p q ca cb x hx c hc d hd ud hud hm
        rw [hsource]
        rw [integral_relative_cross_product_cast_chain_comp]
        let hdeg : p + (q + 1) = p + q + 1 := by omega
        change integralRelativeChainProduct_castRelativeChain _
            (integralRelativeChainProduct X Y A B p (q + 1)
              ((RelativeComplex X A).iCycles p ca)
              ((RelativeComplex Y B).iCycles (q + 1) cb)) =
          integralRelativeChainProduct_castRelativeChain hdeg
            (integralRelativeChainProduct X Y A B p (q + 1)
              ((RelativeComplex X A).iCycles p ca)
              ((RelativeComplex Y B).iCycles (q + 1) cb))
        exact integral_relative_cross_product_cast_relative_proof_irrel _ _ _
      refine ⟨z0, ?_⟩
      exact hz0
end HolomorphicAnosov.Topology

