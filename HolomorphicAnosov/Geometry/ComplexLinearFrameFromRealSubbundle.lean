import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Geometry.ContinuousTangentLinearCombination
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Complex-linear local frame candidates are constructed from an original real subbundle. (Hatcher, §1.1, p. 8; Demailly, I §3.C, p. 23).
-/

noncomputable section
open Set Bundle Topology _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Vectors in a complex tangent subspace extend to a jointly continuous family of complex-linear maps with image in the corresponding subspaces. (Hatcher, §1.1, p. 8). -/
theorem complex_linear_frame_from_real_subbundle
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (S : ∀ y : M, Submodule ℂ (TangentSpace (complexModel d) y))
    (hS : ∀ y, ((S y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = P.toDistribution y)
    (x : M) {s : ℕ} (b : Fin s → S x) :
    ∃ (U : Set M) (L : ∀ y : M, (Fin s → ℂ) →ₗ[ℂ] TangentSpace (complexModel d) y),
      IsOpen U ∧ x ∈ U ∧
      L x = Fintype.linearCombination ℂ (fun i ↦ (b i).val) ∧
      (∀ y w, L y w ∈ S y) ∧
      ContinuousOn (fun z : M × (Fin s → ℂ) ↦
        (⟨z.1, L z.1 z.2⟩ : TangentBundle (complexModel d) M)) (U ×ˢ univ) := by
  classical
  obtain ⟨r, t, hx, ht⟩ := P.locally_trivial x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ P.toDistribution y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
  let := ht
  have hb (i : Fin s) : complexTangentToReal d x (b i) ∈ P.toDistribution x := by
    rw [← hS x]
    exact ⟨(b i).val, (b i).property, rfl⟩
  let c (i : Fin s) := t.linearEquivAt ℝ x hx ⟨complexTangentToReal d x (b i), hb i⟩
  let v (y : M) (i : Fin s) : TangentSpace (complexModel d) y :=
    (complexTangentToReal d y).symm (t.symm y (c i)).val
  have hv_mem (y : M) (i : Fin s) : v y i ∈ S y := by
    have hv : ((t.symm y (c i)).val : TangentSpace (realModel d) y) ∈
        ((S y).restrictScalars ℝ).map
          (complexTangentToReal d y).toLinearEquiv.toLinearMap := by
      simpa only [hS y] using (t.symm y (c i)).property
    exact (Submodule.mem_map_equiv _).mp hv
  have hvx (i : Fin s) : v x i = (b i).val := by
    have hc : t.symm x (c i) = ⟨complexTangentToReal d x (b i), hb i⟩ :=
      (t.linearEquivAt ℝ x hx).symm_apply_apply _
    dsimp only [v]
    rw [hc]
    exact (complexTangentToReal d x).symm_apply_apply _
  have hv_cont (i : Fin s) : ContinuousOn
      (fun y ↦ (⟨y, v y i⟩ : TangentBundle (complexModel d) M)) t.baseSet := by
    have hi : Continuous (fun z : TotalSpace (Fin r → ℝ) (fun y ↦ P.toDistribution y) ↦
        (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) := continuous_induced_dom
    exact (continuous_complexTangentToReal_symm.comp hi).comp_continuousOn
      (t.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy ↦ ⟨hy, mem_univ _⟩))
  let L (y : M) := Fintype.linearCombination ℂ (v y)
  refine ⟨t.baseSet, L, t.open_baseSet, hx, ?_, ?_, ?_⟩
  · exact congrArg (Fintype.linearCombination ℂ) (funext hvx)
  · intro y w
    change (∑ i, w i • v y i) ∈ S y
    exact (S y).sum_mem (fun i _ ↦ (S y).smul_mem (w i) (hv_mem y i))
  · exact continuousOn_tangent_linear_combination (complexModel d)
      (Prod.fst : M × (Fin s → ℂ) → M)
      (fun z i ↦ v z.1 i) (fun z i ↦ z.2 i)
      continuousOn_fst
      (fun i ↦ (hv_cont i).comp continuousOn_fst (fun _ hz ↦ hz.1))
      (fun i ↦ ((continuous_apply i).comp continuous_snd).continuousOn)

end HolomorphicAnosov
