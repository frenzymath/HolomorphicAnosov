import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The normalized local stable coordinate is continuous in the original tangent total space.
(Zhang, Eq. (14) and Lemma 2.5, pp. 7–8) -/

namespace HolomorphicAnosov

open Set Bundle _root_.Topology
open scoped Manifold ContDiff

noncomputable section

universe u

/-- The normalized local stable coordinate is jointly continuous in its base point and argument in
the ambient tangent total space. -/
theorem normalized_local_coordinate_continuous
    {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (S : ContinuousComplexTangentSubbundle (complexModel d) X)
    (t : X → ℂ) (V : Set X) (hV : IsOpen V)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (hderiv : ∀ x ∈ V,
      (localStableCoordinateDerivative S.toDistribution t x).IsInvertible) :
    ContinuousOn
      (fun q : X × X =>
        (⟨q.1,
          (normalizedLocalStableCoordinate S.toDistribution t q.1 q.2).val⟩ :
          TangentBundle (complexModel d) X))
      (V ×ˢ V) := by
  classical
  intro xp hxp
  obtain ⟨r, hr⟩ := S.locally_trivial xp.1
  let : TopologicalSpace (TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) X)) inferInstance
  obtain ⟨e, hxe, he⟩ := hr
  let := he
  let B := fun x ↦ localStableCoordinateDerivative S.toDistribution t x
  obtain ⟨A, hA⟩ := hderiv xp.1 hxp.1
  let w0 : Fin r → ℂ := e.linearEquivAt ℂ xp.1 hxe (A.symm 1)
  have hw0 : w0 ≠ 0 := by
    intro h
    have ha : A.symm 1 = 0 := (e.linearEquivAt ℂ xp.1 hxe).map_eq_zero_iff.mp h
    have hz := congrArg A ha
    exact one_ne_zero (by simpa only [A.apply_symm_apply, map_zero] using hz)
  let O : Set X := e.baseSet ∩ V
  have hO : IsOpen O := e.open_baseSet.inter hV
  have hxo : xp.1 ∈ O := ⟨hxe, hxp.1⟩
  let w : ∀ x, S.toDistribution x := fun x ↦ e.symm x w0
  have hframe : Continuous (fun x : O ↦
      (⟨x.val, (w x.val).val⟩ : TangentBundle (complexModel d) X)) := by
    have hc : Continuous (fun x : O ↦
        (⟨x.val, w x.val⟩ : TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x)))) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun x ↦ ⟨x.property.1, mem_univ _⟩)
    exact continuous_induced_dom.comp hc
  have hw (x : O) : w x.val ≠ 0 := by
    change (e.linearEquivAt ℂ x.val x.property.1).symm w0 ≠ 0
    exact fun h ↦ hw0 ((e.linearEquivAt ℂ x.val x.property.1).symm.map_eq_zero_iff.mp h)
  have hBw (x : O) : B x.val (w x.val) ≠ 0 := by
    obtain ⟨C, hC⟩ := hderiv x.val x.property.2
    change localStableCoordinateDerivative S.toDistribution t x.val (w x.val) ≠ 0
    rw [← hC]
    exact fun h ↦ hw x (C.map_eq_zero_iff.mp h)
  have hscalar : Continuous (fun x : O ↦ B x.val (w x.val)) := by
    have hc := (ht.continuousOn_tangentMapWithin (by simp) hV.uniqueMDiffOn).comp_continuous
      hframe (fun x ↦ x.property.2)
    have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ) (n := ∞)).continuous.comp hc
    apply hs.congr
    intro x
    change mfderivWithin (complexModel d) 𝓘(ℂ) t V x.val (w x.val).val = _
    rw [mfderivWithin_of_isOpen hV x.property.2]
    rfl
  let Q : Set (X × X) := O ×ˢ V
  have hQ : IsOpen Q := hO.prod hV
  have hxpQ : xp ∈ Q := ⟨hxo, hxp.2⟩
  have hfirst : Continuous (fun z : Q ↦ (⟨z.val.1, z.property.1⟩ : O)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hdiff : Continuous (fun z : Q ↦ t z.val.2 - t z.val.1) :=
    (ht.continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun z ↦ z.property.2)).sub
      (ht.continuousOn.comp_continuous
        (continuous_fst.comp continuous_subtype_val) (fun z ↦ z.property.1.2))
  have hratio : Continuous (fun z : Q ↦ (t z.val.2 - t z.val.1) / B z.val.1 (w z.val.1)) :=
    hdiff.div (hscalar.comp hfirst) (fun z ↦ hBw ⟨z.val.1, z.property.1⟩)
  have hc : Continuous (fun z : Q ↦
      (⟨z.val.1, e.symm z.val.1 (((t z.val.2 - t z.val.1) /
        B z.val.1 (w z.val.1)) • w0)⟩ :
          TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x)))) :=
    e.continuousOn_symm.comp_continuous
      ((continuous_fst.comp continuous_subtype_val).prodMk (hratio.smul continuous_const))
      (fun z ↦ ⟨z.property.1.1, mem_univ _⟩)
  have hnorm (z : Q) : normalizedLocalStableCoordinate S.toDistribution t z.val.1 z.val.2 =
      e.symm z.val.1 (((t z.val.2 - t z.val.1) / B z.val.1 (w z.val.1)) • w0) := by
    change (B z.val.1).inverse _ = _
    apply (hderiv z.val.1 z.property.1.2).inverse_apply_eq.mpr
    rw [show e.symm z.val.1 = (e.linearEquivAt ℂ z.val.1 z.property.1.1).symm from rfl,
      map_smul, map_smul]
    change _ = _ * B z.val.1 (w z.val.1)
    exact (div_mul_cancel₀ _ (hBw ⟨z.val.1, z.property.1⟩)).symm
  have hcont : Continuous (fun z : Q ↦
      (⟨z.val.1, (normalizedLocalStableCoordinate S.toDistribution t z.val.1 z.val.2).val⟩ :
        TangentBundle (complexModel d) X)) := by
    apply (continuous_induced_dom.comp hc).congr
    intro z
    exact congrArg (fun v : S.toDistribution z.val.1 ↦
      (⟨z.val.1, v.val⟩ : TangentBundle (complexModel d) X)) (hnorm z).symm
  exact ((continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt
    (hQ.mem_nhds hxpQ)).continuousWithinAt

end
end HolomorphicAnosov
