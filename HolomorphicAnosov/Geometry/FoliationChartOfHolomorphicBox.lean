import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! A codimension-one holomorphic product box yields a foliation chart with the transverse
coordinate first. (Zhang, §2.1, Eqs. (3)–(4), p.4) -/

open Set Filter
open scoped ContDiff Manifold

namespace HolomorphicAnosov.SingleBundleHolomorphicBox

noncomputable section

/-- A complex-linear block permutation identifying the product model with `ComplexModel (r + 1)` and
placing the transverse factor first. -/
def transverseFirst (r : ℕ) :
    (ComplexModel r × ComplexModel 1) ≃L[ℂ] ComplexModel (r + 1) :=
  ((ContinuousLinearEquiv.prodComm ℂ (ComplexModel r) (ComplexModel 1)).trans
    ((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).prodCongr
      (ContinuousLinearEquiv.refl ℂ (ComplexModel r)))).trans
    (Fin.consEquivL ℂ (fun _ : Fin (r + 1) ↦ ℂ))

/-- The zeroth coordinate of `transverseFirst r z` is the transverse scalar `z.2 0`. -/
theorem transverseFirst_zero (r : ℕ) (z : ComplexModel r × ComplexModel 1) :
    transverseFirst r z 0 = z.2 0 := rfl

/-- A biholomorphic product box flattening a codimension-one subbundle yields a maximal-atlas chart
on the same source whose zeroth-coordinate derivative has that subbundle as kernel. (Zhang, Eqs.
(3)–(4), p.4) -/
theorem foliation_chart_of_box {r : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (r + 1)) X]
    [IsManifold (complexModel (r + 1)) ∞ X]
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel (r + 1)) x))
    (b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel 1))
    (hb : ContMDiffOn (complexModel (r + 1)) 𝓘(ℂ, ComplexModel r × ComplexModel 1)
      ∞ b b.source)
    (hbi : ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel 1) (complexModel (r + 1))
      ∞ b.symm b.target)
    (hflat : ∀ y ∈ b.source, (P y).map
      (mfderiv (complexModel (r + 1)) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b y).toLinearMap =
        LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel 1)).toLinearMap) :
    ∃ c : OpenPartialHomeomorph X (ComplexModel (r + 1)),
      c.source = b.source ∧ c ∈ IsManifold.maximalAtlas (complexModel (r + 1)) ∞ X ∧
      ∀ x ∈ c.source, P x = LinearMap.ker
        (((ContinuousLinearMap.proj (0 : Fin (r + 1))).comp
          ((tangentSpaceCastModel (complexModel (r + 1)) (c x)).toContinuousLinearMap.comp
            (mfderiv (complexModel (r + 1)) (complexModel (r + 1)) c x))).toLinearMap) := by
  let e := transverseFirst r
  let c := b.trans e.toHomeomorph.toOpenPartialHomeomorph
  have hcsource : c.source = b.source := by
    ext x
    simp [c]
  have hc : ContMDiffOn (complexModel (r + 1)) (complexModel (r + 1)) ∞ c c.source := by
    rw [hcsource]
    exact e.toContinuousLinearMap.contMDiff.comp_contMDiffOn hb
  have hci : ContMDiffOn (complexModel (r + 1)) (complexModel (r + 1)) ∞
      c.symm c.target := by
    apply hbi.comp e.symm.toContinuousLinearMap.contMDiff.contMDiffOn
    intro z hz
    exact hz.2
  refine ⟨c, hcsource, c.mem_maximalAtlas_of_contMDiffOn hc hci, ?_⟩
  intro x hx
  have hxb : x ∈ b.source := hcsource ▸ hx
  have hbd := (hb.mdifferentiableOn (by simp) x hxb).mdifferentiableAt
    (b.open_source.mem_nhds hxb)
  have hD : (mfderiv (complexModel (r + 1)) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b x).IsInvertible :=
    ⟨(show b.MDifferentiable (complexModel (r + 1)) 𝓘(ℂ, ComplexModel r × ComplexModel 1) from
      ⟨hb.mdifferentiableOn (by simp), hbi.mdifferentiableOn (by simp)⟩).mfderiv hxb, rfl⟩
  let D := mfderiv (complexModel (r + 1)) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b x
  have hder : mfderiv (complexModel (r + 1)) (complexModel (r + 1)) c x =
      e.toContinuousLinearMap.comp D := by
    change mfderiv (complexModel (r + 1)) (complexModel (r + 1)) (e ∘ b) x = _
    rw [mfderiv_comp x e.mdifferentiableAt hbd, mfderiv_eq_fderiv, e.fderiv]
    rfl
  ext v
  rw [LinearMap.mem_ker, hder]
  change v ∈ P x ↔ e (D v) 0 = 0
  rw [show e (D v) 0 = (D v).2 0 from transverseFirst_zero r (D v)]
  have hflat' := hflat x hxb
  change (P x).map D.toLinearMap = _ at hflat'
  constructor
  · intro hv
    have hm : D v ∈ (P x).map D.toLinearMap := ⟨v, hv, rfl⟩
    rw [hflat'] at hm
    obtain ⟨w, hw⟩ := hm
    rw [← hw]
    rfl
  · intro hv
    have hm : D v ∈ (P x).map D.toLinearMap := by
      rw [hflat']
      refine ⟨(D v).1, ?_⟩
      change ((D v).1, (0 : ComplexModel 1)) = D v
      apply Prod.ext
      · rfl
      · change (0 : ComplexModel 1) = (D v).2
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        exact hv.symm
    obtain ⟨w, hw, hwv⟩ := hm
    exact hD.bijective.injective hwv ▸ hw

end
end HolomorphicAnosov.SingleBundleHolomorphicBox

