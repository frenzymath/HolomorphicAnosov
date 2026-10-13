import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientDifferentialContinuousEquivalence
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ExistsLocalData
import HolomorphicAnosov.Geometry.BiholomorphToReal

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

/-! This file proves holomorphicity of the scalar coefficient of the quotient differential of a
subbundle-preserving biholomorphism in local quotient frames. (Zhang, §2.1, (5), p.5; Demailly,
V §11, p.267 and §14.1, p.273) -/
omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
theorem quotient_frame_multiplier_smooth_coefficient_bridge_g12
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (hV : ∀ x, x ∈ V → f x ∈ W) :
    ∀ x ∈ V, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ (V : Set X) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
        (QuotientLineConnection.imageFrameCoefficient f hf e e') N := by
  intro x hx
  obtain ⟨D, hxD⟩ := exists_quotient_local_data P hP hline (f x)
  obtain ⟨A, v, hA, hxA, hAV, hv, hvs⟩ := e.holomorphic x hx
  have hxW : f x ∈ W := hV x hx
  obtain ⟨B, v', hB, hfxB, hBW, hv', hvs'⟩ := e'.holomorphic (f x) hxW
  let N : Opens X := ⟨A ∩ f ⁻¹' (D.V ∩ B),
    hA.inter ((D.V.isOpen.inter hB).preimage f.continuous)⟩
  have hxN : x ∈ N := ⟨hxA, ⟨hxD, hfxB⟩⟩
  have hNV : (N : Set X) ⊆ V := fun y hy ↦ hAV hy.1
  have hNW : MapsTo f N D.V := fun y hy ↦ hy.2.1
  have hNB : MapsTo f N B := fun y hy ↦ hy.2.2
  have htf : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨f y, mfderiv (complexModel d) (complexModel d) f y (v y)⟩ :
        TangentBundle (complexModel d) X)) (N : Set X) := by
    have hff : ContMDiffOn (complexModel d) (complexModel d) ∞ (f : X → X) N :=
      f.contMDiff.contMDiffOn
    have hfm := hff.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      N.isOpen.uniqueMDiffOn
    have hcomp := hfm.comp (hv.mono inter_subset_left) (fun y hy ↦ hy)
    apply hcomp.congr
    intro y hy
    dsimp [tangentMapWithin]
    rw [mfderivWithin_of_isOpen N.isOpen hy]
  have hnum : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y ↦ D.θ (f y) (mfderiv (complexModel d) (complexModel d) f y (v y))) (N : Set X) := by
    intro y hy
    have hq : ContMDiffAt (complexModel d) (complexModel d).tangent ∞
        (fun z ↦ (⟨f z, mfderiv (complexModel d) (complexModel d) f z (v z)⟩ :
          TangentBundle (complexModel d) X)) y :=
      (htf y hy).contMDiffAt (N.isOpen.mem_nhds hy)
    have hyf : f y ∈ (D.V : Set X) ∩ B := hy.2
    have hh := D.hscalar ⟨f y, mfderiv (complexModel d) (complexModel d) f y (v y)⟩ hyf.1
    exact (hh.comp y hq).contMDiffWithinAt
  have hTcomp : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨f y, v' (f y)⟩ : TangentBundle (complexModel d) X)) (N : Set X) :=
    hv'.comp f.contMDiff.contMDiffOn hNB
  have hden : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y ↦ D.θ (f y) (v' (f y))) (N : Set X) := by
    intro y hy
    have hq : ContMDiffAt (complexModel d) (complexModel d).tangent ∞
        (fun z ↦ (⟨f z, v' (f z)⟩ : TangentBundle (complexModel d) X)) y :=
      (hTcomp y hy).contMDiffAt (N.isOpen.mem_nhds hy)
    have hh := D.hscalar ⟨f y, v' (f y)⟩ hy.2.1
    exact (hh.comp y hq).contMDiffWithinAt
  have hden_nonzero : ∀ y ∈ (N : Set X),
      D.θ (f y) (v' (f y)) ≠ 0 := by
    intro y hy hz
    have hyf : f y ∈ (D.V : Set X) ∩ B := hy.2
    have hp0 : QuotientLineConnection.projection P (f y) (v' (f y)) = 0 := by
      apply (D.L (f y) hyf.1).injective
      rw [D.apply_mk]
      simpa using hz
    have hs0 : e'.sectionValue (f y) = 0 := by
      rw [← hvs' (f y) hy.2.2]
      exact hp0
    have hone := e'.normalized (f y) (hV y (hNV hy))
    rw [hs0, map_zero] at hone
    exact zero_ne_one hone
  refine ⟨N, N.isOpen, hxN, hNV, ?_⟩
  intro y hy
  have hid : ∀ z ∈ (N : Set X),
      QuotientLineConnection.imageFrameCoefficient f hf e e' z =
        (D.θ (f z) (mfderiv (complexModel d) (complexModel d) f z (v z))) /
          D.θ (f z) (v' (f z)) := by
    intro z hz
    have hzf : f z ∈ (D.V : Set X) ∩ B := hz.2
    have hq : QuotientLineConnection.quotientDerivative f hf z (e.sectionValue z) =
        QuotientLineConnection.projection P (f z)
          (mfderiv (complexModel d) (complexModel d) f z (v z)) := by
      rw [← hvs z hz.1]
      rfl
    have hspan : QuotientLineConnection.quotientDerivative f hf z (e.sectionValue z) =
        (QuotientLineConnection.imageFrameCoefficient f hf e e' z) •
          e'.sectionValue (f z) := by
      apply (e'.coordinate (f z) (hV z (hNV hz))).injective
      simp [QuotientLineConnection.imageFrameCoefficient, hV z (hNV hz),
        e'.normalized (f z) (hV z (hNV hz))]
    have hnum_eq : D.θ (f z)
        (mfderiv (complexModel d) (complexModel d) f z (v z)) =
        (QuotientLineConnection.imageFrameCoefficient f hf e e' z) *
          D.θ (f z) (v' (f z)) := by
      have hL := congrArg (D.L (f z) hzf.1) hspan
      rw [map_smul, smul_eq_mul] at hL
      calc
        D.θ (f z) (mfderiv (complexModel d) (complexModel d) f z (v z)) =
            (D.L (f z) hzf.1)
              (QuotientLineConnection.projection P (f z)
                (mfderiv (complexModel d) (complexModel d) f z (v z))) :=
          (D.apply_mk (f z) hzf.1 _).symm
        _ = (D.L (f z) hzf.1)
            (QuotientLineConnection.quotientDerivative f hf z (e.sectionValue z)) := by rw [hq]
        _ = (QuotientLineConnection.imageFrameCoefficient f hf e e' z) *
            (D.L (f z) hzf.1) (e'.sectionValue (f z)) := hL
        _ = (QuotientLineConnection.imageFrameCoefficient f hf e e' z) *
            (D.L (f z) hzf.1)
              (QuotientLineConnection.projection P (f z) (v' (f z))) := by
          rw [← hvs' (f z) hzf.2]
        _ = (QuotientLineConnection.imageFrameCoefficient f hf e e' z) *
            D.θ (f z) (v' (f z)) := by rw [D.apply_mk]
    change QuotientLineConnection.imageFrameCoefficient f hf e e' z =
      (D.θ (f z) (mfderiv (complexModel d) (complexModel d) f z (v z))) /
        D.θ (f z) (v' (f z))
    exact (eq_div_iff (hden_nonzero z hz)).mpr hnum_eq.symm
  have hratio := (hnum y hy).div₀ (hden y hy) (hden_nonzero y hy)
  apply hratio.congr
  · exact hid
  · exact hid y hy

end HolomorphicAnosov.ConnectionCalculus

