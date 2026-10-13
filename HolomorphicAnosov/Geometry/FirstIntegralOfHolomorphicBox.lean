import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set Filter
open scoped ContDiff Manifold

namespace HolomorphicAnosov.SingleBundleHolomorphicBox

/-- The transverse component of a codimension-one holomorphic flattening chart is a holomorphic
submersion whose derivative kernel is the prescribed tangent subbundle. (Zhang, Eqs. (3)–(4),
p.4) -/
theorem first_integral_of_box {d r : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel 1))
    (hb : ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) ∞ b b.source)
    (hbi : ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel 1) (complexModel d) ∞ b.symm b.target)
    (hflat : ∀ y ∈ b.source, (P y).map
      (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b y).toLinearMap =
        LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel 1)).toLinearMap) :
    ∃ q : X → ℂ, ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ q b.source ∧
      ∀ y ∈ b.source, Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ) q y) ∧
        LinearMap.ker (mfderiv (complexModel d) 𝓘(ℂ) q y).toLinearMap = P y := by
  let L : (ComplexModel r × ComplexModel 1) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (0 : Fin 1)).comp
      (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel 1))
  let q : X → ℂ := L ∘ b
  refine ⟨q, L.contMDiff.comp_contMDiffOn hb, ?_⟩
  intro y hy
  have hbd := (hb.mdifferentiableOn (by simp) y hy).mdifferentiableAt
    (b.open_source.mem_nhds hy)
  have hD : (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b y).IsInvertible :=
    ⟨(show b.MDifferentiable (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) from
      ⟨hb.mdifferentiableOn (by simp), hbi.mdifferentiableOn (by simp)⟩).mfderiv hy, rfl⟩
  let D := mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b y
  have hq : mfderiv (complexModel d) 𝓘(ℂ) q y = L.comp D := by
    rw [show q = L ∘ b from rfl, mfderiv_comp y L.mdifferentiableAt hbd]
    congr 1
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  rw [hq]
  constructor
  · intro z
    obtain ⟨v, hv⟩ := hD.bijective.surjective (0, fun _ ↦ z)
    exact ⟨v, by change L (D v) = z; rw [hv]; rfl⟩
  · ext v
    change L (D v) = 0 ↔ v ∈ P y
    have hflat' : (P y).map D.toLinearMap =
        LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel 1)).toLinearMap :=
      hflat y hy
    constructor
    · intro hv
      have hDv : D v ∈ (P y).map D.toLinearMap := by
        rw [hflat']
        refine ⟨(D v).1, ?_⟩
        change ((D v).1, (0 : ComplexModel 1)) = D v
        apply Prod.ext
        · rfl
        · funext j
          have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          exact hv.symm
      obtain ⟨w, hw, hwv⟩ := hDv
      exact hD.bijective.injective hwv ▸ hw
    · intro hv
      have hm : D v ∈ (P y).map D.toLinearMap := ⟨v, hv, rfl⟩
      rw [hflat'] at hm
      obtain ⟨w, hw⟩ := hm
      rw [← hw]
      rfl

end HolomorphicAnosov.SingleBundleHolomorphicBox

