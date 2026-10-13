import HolomorphicAnosov.Geometry.VectorDolbeaultDerivative
import HolomorphicAnosov.Analysis.InnerProductSpace.JacobianSingularValues
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.NormalizedHermitianJacobian

open scoped ContDiff Manifold Topology
open Bundle Filter
open Set
namespace HolomorphicAnosov
noncomputable section

/-- The intrinsic unit-ball supremum equals the operator norm of the restriction to the source
subspace. -/
theorem fibreNormOperator_eq_restricted_opNorm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (P : Submodule ℂ V) (L : V →L[ℂ] W) :
    fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) P L = ‖L.comp P.subtypeL‖ := by
  let := NormedSpace.restrictScalars ℝ ℂ V
  let := NormedSpace.restrictScalars ℝ ℂ W
  let p := normSeminorm ℝ V
  let q := normSeminorm ℝ W
  let A := L.comp P.subtypeL
  have hbound : ∀ v ∈ P, q (L v) ≤ ‖A‖ * p v := by
    intro v hv
    exact A.le_opNorm ⟨v, hv⟩
  have hb : BddAbove {a : ℝ | ∃ v : V, v ∈ P ∧ p v ≤ 1 ∧ a = q (L v)} := by
    refine ⟨‖A‖, ?_⟩
    rintro b ⟨v, hv, hpv, rfl⟩
    exact (hbound v hv).trans (mul_le_of_le_one_right (norm_nonneg A) hpv)
  have hnonneg : 0 ≤ fibreNormOperator p q P L := by
    apply le_csSup hb
    exact ⟨0, P.zero_mem, by simp [p], by simp [q]⟩
  apply le_antisymm
  · exact CompactHermitianBoundsScratch.operator_le_of_pointwise p q P
      (L.toLinearMap.restrictScalars ℝ) (norm_nonneg A) hbound
  · apply A.opNorm_le_bound hnonneg
    intro v
    exact CompactHermitianBoundsScratch.pointwise_le_operator p q P
      (L.toLinearMap.restrictScalars ℝ) (fun _ hv ↦ norm_pos_iff.mpr hv) hb v.property

/-- A linear isomorphism between positive-dimensional Hermitian subspaces with conorm at least one
has operator norm bounded by the modulus of its determinant in unitary bases. (Zhang, (29),
p.16) -/
theorem hermitian_restricted_operator_le_det
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (hV : InnerProductSpace.Core ℂ V) (hW : InnerProductSpace.Core ℂ W)
    (P : Submodule ℂ V) (Q : Submodule ℂ W) (L : V ≃ₗ[ℂ] W)
    (hmap : P.map L.toLinearMap = Q) (r : ℕ) (hr : 0 < r)
    (hPr : Module.finrank ℂ P = r) (hQr : Module.finrank ℂ Q = r)
    (hconorm : 1 ≤ fibreNormConorm (HermitianFibreAlgebra.coreLength hV)
      (HermitianFibreAlgebra.coreLength hW) P L.toLinearMap) :
    ∃ (bP : Module.Basis (Fin r) ℂ P) (bQ : Module.Basis (Fin r) ℂ Q),
      (∀ i j, hV.inner (bP j) (bP i) = if i = j then 1 else 0) ∧
      (∀ i j, hW.inner (bQ j) (bQ i) = if i = j then 1 else 0) ∧
      fibreNormOperator (HermitianFibreAlgebra.coreLength hV)
        (HermitianFibreAlgebra.coreLength hW) P L.toLinearMap ≤
          ‖(LinearMap.toMatrix bP bQ (L.ofSubmodules P Q hmap).toLinearMap).det‖ := by
  classical
  let Le : V ≃ₗ[ℂ] W := L
  let Ue : P ≃ₗ[ℂ] Q := Le.ofSubmodules P Q hmap
  let : Module ℂ V := inferInstance
  let : Module ℂ W := inferInstance
  let : InnerProductSpace.Core ℂ V := hV
  let : InnerProductSpace.Core ℂ W := hW
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup W := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  let : InnerProductSpace ℂ W := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ W)
  let L' : V ≃L[ℂ] W := Le.toContinuousLinearEquiv
  let U : P ≃L[ℂ] Q := Ue.toContinuousLinearEquiv
  let bP := (stdOrthonormalBasis ℂ P).reindex (finCongr hPr)
  let bQ := (stdOrthonormalBasis ℂ Q).reindex (finCongr hQr)
  refine ⟨bP.toBasis, bQ.toBasis, ?_, ?_, ?_⟩
  · intro i j
    exact bP.inner_eq_ite j i |>.trans (by simp only [eq_comm])
  · intro i j
    exact bQ.inner_eq_ite j i |>.trans (by simp only [eq_comm])
  · have hnorm : fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) P L' =
        ‖U.toContinuousLinearMap‖ := by
      calc
        _ = ‖L'.toContinuousLinearMap.comp P.subtypeL‖ :=
          fibreNormOperator_eq_restricted_opNorm P L'.toContinuousLinearMap
        _ = _ := by
          apply le_antisymm
          · exact (L'.toContinuousLinearMap.comp P.subtypeL).opNorm_le_bound
              (norm_nonneg U.toContinuousLinearMap) (fun v ↦ U.toContinuousLinearMap.le_opNorm v)
          · exact U.toContinuousLinearMap.opNorm_le_bound
              (norm_nonneg (L'.toContinuousLinearMap.comp P.subtypeL))
              (fun v ↦ (L'.toContinuousLinearMap.comp P.subtypeL).le_opNorm v)
    have hset : (fun v : P ↦ ‖U v‖) '' {v : P | ‖v‖ = 1} =
        {a : ℝ | ∃ v : V, v ∈ P ∧ ‖v‖ = 1 ∧ a = ‖L' v‖} := by
      ext a
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, v.property, hv, rfl⟩
      · rintro ⟨v, hv, hn, rfl⟩
        exact ⟨⟨v, hv⟩, hn, rfl⟩
    have hc : 1 ≤ sInf ((fun v : P ↦ ‖U v‖) '' {v : P | ‖v‖ = 1}) := by
      rw [hset]
      exact hconorm
    have hspec := jacobian_singular_values r hr hPr hQr U
    have hb := hspec.2.2.2.2.1 hc
    rw [hspec.2.2.2.2.2 bP bQ] at hb
    change fibreNormOperator (norm : V → ℝ) (norm : W → ℝ) P L' ≤ _
    rw [hnorm]
    exact hb

/-- Continuous preferred coordinates of an antilinear tensor give a continuous map on the native
tangent bundle. -/
theorem continuous_native_antilinear_tensor
    {d : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (B : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] TangentSpace (complexModel d) x)
    (hB : ∀ a, ContinuousOn (preferredAntilinearTensorCoefficients B a)
      (chartAt (ComplexModel d) a).target) :
    Continuous (fun z : TangentBundle (complexModel d) X ↦
      TotalSpace.mk' (ComplexModel d) z.proj (B z.proj z.snd)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let c := chartAt (ComplexModel d) z.proj
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) z.proj
  let A : Set (TangentBundle (complexModel d) X) := {w | w.proj ∈ c.source}
  have hA : IsOpen A := c.open_source.preimage (FiberBundle.continuous_proj _ _)
  have hzA : z ∈ A := mem_chart_source _ _
  have ht : Continuous (fun w : A ↦ t w.val) :=
    t.continuousOn.comp_continuous continuous_subtype_val (fun w ↦ w.property)
  have hbase : Continuous (fun w : A ↦ w.val.proj) :=
    (FiberBundle.continuous_proj _ _).comp continuous_subtype_val
  have hc : Continuous (fun w : A ↦ c w.val.proj) :=
    c.continuousOn.comp_continuous hbase (fun w ↦ w.property)
  have hcoeff := (hB z.proj).comp_continuous hc (fun w ↦ c.map_source w.property)
  have happ : Continuous (fun w : A ↦
      preferredAntilinearTensorCoefficients B z.proj (c w.val.proj) (t w.val).2) :=
    ((ContinuousLinearMap.apply' (ComplexModel d) (starRingEnd ℂ)).continuous.comp
      (continuous_snd.comp ht)).clm_apply hcoeff
  have hresult := t.continuousOn_symm.comp_continuous (hbase.prodMk happ)
    (fun w ↦ ⟨w.property, Set.mem_univ _⟩)
  have heq : (fun w : A ↦ TotalSpace.mk' (ComplexModel d) w.val.proj
      (t.symm w.val.proj (preferredAntilinearTensorCoefficients B z.proj (c w.val.proj) (t w.val).2))) =
      (fun w : A ↦ TotalSpace.mk' (ComplexModel d) w.val.proj (B w.val.proj w.val.snd)) := by
    funext w
    have hw : w.val.proj ∈ t.baseSet := w.property
    simp only [preferredAntilinearTensorCoefficients, ContinuousLinearMap.comp_apply]
    rw [c.left_inv w.property]
    rw [← t.continuousLinearMapAt_apply_of_mem ℂ hw,
      t.symmL_continuousLinearMapAt hw]
    congr 1
    rw [← t.symmL_apply (R := ℂ) hw]
    exact t.symmL_continuousLinearMapAt hw _
  change Continuous (fun w : A ↦ TotalSpace.mk' (ComplexModel d) w.val.proj
    (t.symm w.val.proj (preferredAntilinearTensorCoefficients B z.proj (c w.val.proj) (t w.val).2))) at hresult
  rw [heq] at hresult
  exact (continuousOn_iff_continuous_domRestrict.mpr hresult).continuousAt (hA.mem_nhds hzA)

/-- A continuous antilinear tangent tensor on a compact manifold has a uniform operator bound in a
smooth Hermitian metric. (Zhang, p.16) -/
theorem uniform_hermitian_antilinear_tensor_bound
    {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (B : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ] TangentSpace (complexModel d) x)
    (hB : ∀ a, ContinuousOn (preferredAntilinearTensorCoefficients B a)
      (chartAt (ComplexModel d) a).target)
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x v,
      hermitianBoundsNorm h x (B x v) ≤ C * hermitianBoundsNorm h x v := by
  let q := HermitianFibreAlgebra.hermitianBoundsRealSeminorm h
  let BR (x : X) : TangentSpace (complexModel d) x →ₗ[ℝ] TangentSpace (complexModel d) x :=
    { toFun := B x
      map_add' := (B x).map_add
      map_smul' := by
        intro r v
        change B x ((r : ℂ) • v) = (r : ℂ) • B x v
        rw [(B x).map_smulₛₗ]
        have hr : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
        change star (r : ℂ) • B x v = (r : ℂ) • B x v
        rw [hr] }
  let p := fun x ↦ (q x).comp (BR x)
  have hq : Continuous (fun z : TangentBundle (complexModel d) X ↦ q z.proj z.snd) :=
    Preparation.continuous_hermitian_tangent_norm h hh
  exact Preparation.uniform_tangent_seminorm_upper_bound p q
    (hq.comp (continuous_native_antilinear_tensor B hB)) hq
    (fun x _ hv ↦ HermitianFibreAlgebra.coreLength_pos (h x) hv)


end
end HolomorphicAnosov
