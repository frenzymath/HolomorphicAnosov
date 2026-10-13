import HolomorphicAnosov.Paper.Ghys.OrderedProjectiveProductDevelopment
import HolomorphicAnosov.Geometry.ProjectiveFixedInfinityAffine
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteNeInfinity

open Set IsManifold
open scoped ContDiff Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov
/-- Normalizes the two omitted projective values to infinity by projective transformations. (Ghys, p.600) -/
theorem punctured_product_normalizing_maps
    (poleS poleU : ComplexProjectiveLine) :
    ∃ ms mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
      ms • poleS = complexProjectiveLineInfinity ∧
        mu • poleU = complexProjectiveLineInfinity := by
  obtain ⟨ms, hms⟩ := MulAction.exists_smul_eq
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) poleS
      complexProjectiveLineInfinity
  obtain ⟨mu, hmu⟩ := MulAction.exists_smul_eq
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) poleU
      complexProjectiveLineInfinity
  exact ⟨ms, mu, hms, hmu⟩

end HolomorphicAnosov
namespace HolomorphicAnosov.Ghys

/-- An injective punctured-product development becomes a biholomorphism onto `ComplexModel 2` after normalizing its omitted values. (Ghys, Theorem A, p.600) -/
theorem normalized_product_biholomorph_provider_g12
    {U : Type*} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U]
    (D : U → ComplexProjectiveLine × ComplexProjectiveLine)
    (hD : Function.Injective D)
    (hlocal : IsLocalDiffeomorph (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞ D)
    {poleS poleU : ComplexProjectiveLine}
    (hrange : Set.range D = ({poleS}ᶜ ×ˢ {poleU}ᶜ)) :
    ∃ (ms mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
      (D0 : Biholomorph 2 2 U (ComplexModel 2)),
      ms • poleS = complexProjectiveLineInfinity ∧
      mu • poleU = complexProjectiveLineInfinity ∧
      (∀ u, D0 u 0 = complexProjectiveLineChartFun 1 (ms • (D u).1) 0 ∧
        D0 u 1 = complexProjectiveLineChartFun 1 (mu • (D u).2) 0) := by
  classical
  obtain ⟨ms, mu, hms, hmu⟩ := punctured_product_normalizing_maps poleS poleU
  let G1 (m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
      Diffeomorph (complexModel 1) (complexModel 1)
        ComplexProjectiveLine ComplexProjectiveLine ∞ :=
    { toEquiv := MulAction.toPerm m
      contMDiff_toFun := projective_special_linear_action_contMDiff m
      contMDiff_invFun := projective_special_linear_action_contMDiff m⁻¹ }
  let G := (G1 ms).prodCongr (G1 mu)
  let c := (complexProjectiveLineChart 1).prod (complexProjectiveLineChart 1)
  have hc : complexProjectiveLineChart 1 ∈
      maximalAtlas (complexModel 1) ∞ ComplexProjectiveLine :=
    IsManifold.subset_maximalAtlas ⟨1, rfl⟩
  let C : PartialDiffeomorph ((complexModel 1).prod (complexModel 1))
      ((complexModel 1).prod (complexModel 1))
      (ComplexProjectiveLine × ComplexProjectiveLine) (ComplexModel 1 × ComplexModel 1) ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := (contMDiffOn_of_mem_maximalAtlas hc).prodMap
        (contMDiffOn_of_mem_maximalAtlas hc)
      contMDiffOn_invFun := (contMDiffOn_symm_of_mem_maximalAtlas hc).prodMap
        (contMDiffOn_symm_of_mem_maximalAtlas hc) }
  let L : (ComplexModel 1 × ComplexModel 1) ≃L[ℂ] ComplexModel 2 :=
    ((ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).prodCongr
      (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))).trans
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
  let Ld : Diffeomorph ((complexModel 1).prod (complexModel 1)) (complexModel 2)
      (ComplexModel 1 × ComplexModel 1) (ComplexModel 2) ∞ :=
    { toEquiv := L.toEquiv
      contMDiff_toFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact L.contDiff.contMDiff
      contMDiff_invFun := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact L.symm.contDiff.contMDiff }
  let Q := G.toPartialDiffeomorph.trans (C.trans Ld.toPartialDiffeomorph)
  have hsrc (p : ComplexProjectiveLine × ComplexProjectiveLine) :
      p ∈ Q.source ↔ p ∈ ({poleS}ᶜ ×ˢ {poleU}ᶜ) := by
    have hs (m : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
        (a p : ComplexProjectiveLine) (hm : m • a = complexProjectiveLineInfinity) :
        m • p ∈ complexProjectiveLineChartSource 1 ↔ p ≠ a := by
      constructor
      · intro hp hpa
        subst p
        rw [hm] at hp
        have he := projective_left_inv 1 complexProjectiveLineInfinity hp
        exact developing_finite_ne_infinity
          (complexProjectiveLineChartFun 1 complexProjectiveLineInfinity 0) he
      · intro hp
        by_contra hn
        have he := developing_eq_infinity_of_not_finite_source (m • p) hn
        exact hp (MulAction.injective m (he.trans hm.symm))
    change (p ∈ Set.univ ∧
      ((ms • p.1 ∈ complexProjectiveLineChartSource 1 ∧
        mu • p.2 ∈ complexProjectiveLineChartSource 1) ∧ True)) ↔ _
    simp only [mem_univ, true_and, and_true, mem_prod, mem_compl_iff, mem_singleton_iff]
    exact and_congr (hs ms poleS p.1 hms) (hs mu poleU p.2 hmu)
  have htgt : Q.target = Set.univ := by
    ext z
    simp [Q, C, c, G, G1, Diffeomorph.toPartialDiffeomorph,
      PartialDiffeomorph.trans, complexProjectiveLineChart]
  have hDsrc (u : U) : D u ∈ Q.source :=
    (hsrc _).mpr (hrange ▸ Set.mem_range_self u)
  let Dn : U → ComplexModel 2 := fun u ↦ Q (D u)
  have hlocaln : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ Dn :=
    fun u ↦ (hlocal u).comp (complexModel 2) (ComplexModel 2) (Q.isLocalDiffeomorphAt _ _ _ (hDsrc u))
  have hbij : Function.Bijective Dn := by
    constructor
    · intro u v huv
      exact hD (Q.toPartialEquiv.injOn (hDsrc u) (hDsrc v) huv)
    · intro z
      have hz : z ∈ Q.target := htgt.symm ▸ Set.mem_univ z
      have hp : Q.symm z ∈ Set.range D := by
        rw [hrange]
        exact (hsrc _).mp (Q.toPartialEquiv.map_target hz)
      obtain ⟨u, hu⟩ := hp
      refine ⟨u, ?_⟩
      change Q (D u) = z
      rw [hu]
      exact Q.toPartialEquiv.right_inv hz
  refine ⟨ms, mu, hlocaln.diffeomorphOfBijective hbij, hms, hmu, ?_⟩
  intro u
  change (L (c (G (D u)))) 0 = _ ∧ (L (c (G (D u)))) 1 = _
  exact ⟨rfl, rfl⟩

end HolomorphicAnosov.Ghys

