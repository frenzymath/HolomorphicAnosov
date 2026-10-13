import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Topology.VectorBundle.Basic

/-! Real subbundle charts transfer to complex tangent subspaces under the canonical realification.
(Demailly, I §3.C, p.23) -/

noncomputable section
open Set Bundle Topology _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A real-linear chart on a real tangent subbundle transfers to complex tangent subspaces with the
same realification and their induced tangent topology. (Demailly, I §3.C, p.23; Hatcher, §1.1,
pp.5–6) -/
theorem realification_subbundle_chart
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (P : ∀ y : M, Submodule ℝ (TangentSpace (realModel d) y))
    (S : ∀ y : M, Submodule ℂ (TangentSpace (complexModel d) y))
    (hS : ∀ y, ((S y).restrictScalars ℝ).map
      (complexTangentToReal d y).toLinearEquiv.toLinearMap = P y)
    (r : ℕ) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ P y)) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ S y)) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∀ t : Trivialization (Fin r → ℝ)
        (TotalSpace.proj (F := Fin r → ℝ) (E := fun y ↦ P y)),
      t.IsLinear ℝ →
      ∃ e : Trivialization (Fin r → ℝ)
          (TotalSpace.proj (F := Fin r → ℝ) (E := fun y ↦ S y)),
        e.baseSet = t.baseSet ∧ e.IsLinear ℝ := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ P y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) inferInstance
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y ↦ S y)) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  intro t ht
  let := ht
  have hforward (y : M) (v : S y) : complexTangentToReal d y v ∈ P y := by
    rw [← hS y]
    exact ⟨v, v.property, rfl⟩
  have hbackward (y : M) (v : P y) : (complexTangentToReal d y).symm v ∈ S y := by
    have hv : (v : TangentSpace (realModel d) y) ∈ ((S y).restrictScalars ℝ).map
        (complexTangentToReal d y).toLinearEquiv.toLinearMap := by
      simpa only [hS y] using v.property
    exact (Submodule.mem_map_equiv _).mp hv
  let H : TotalSpace (Fin r → ℝ) (fun y ↦ S y) ≃ₜ
      TotalSpace (Fin r → ℝ) (fun y ↦ P y) := {
    toFun := fun z ↦ ⟨z.proj, ⟨complexTangentToReal d z.proj z.snd, hforward _ _⟩⟩
    invFun := fun z ↦ ⟨z.proj, ⟨(complexTangentToReal d z.proj).symm z.snd, hbackward _ _⟩⟩
    left_inv := by
      intro z
      apply TotalSpace.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      exact (complexTangentToReal d z.proj).symm_apply_apply z.snd
    right_inv := by
      intro z
      apply TotalSpace.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      exact (complexTangentToReal d z.proj).apply_symm_apply z.snd
    continuous_toFun := by
      apply continuous_induced_rng.mpr
      exact (continuous_complexTangentToReal (d := d) (X := M)).comp
        (show Continuous (fun z : TotalSpace (Fin r → ℝ) (fun y ↦ S y) ↦
          (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) from
          continuous_induced_dom)
    continuous_invFun := by
      apply continuous_induced_rng.mpr
      exact (continuous_complexTangentToReal_symm (d := d) (X := M)).comp
        (show Continuous (fun z : TotalSpace (Fin r → ℝ) (fun y ↦ P y) ↦
          (⟨z.proj, z.snd.val⟩ : TangentBundle (realModel d) M)) from
          continuous_induced_dom) }
  let e := t.compHomeomorph H
  refine ⟨e, rfl, ?_⟩
  constructor
  intro y hy
  change IsLinearMap ℝ (fun v : S y ↦
    (t ⟨y, ⟨complexTangentToReal d y v, hforward y v⟩⟩).2)
  constructor
  · intro v w
    change (t ⟨y, ⟨complexTangentToReal d y (v + w), _⟩⟩).2 = _
    have heq : (⟨complexTangentToReal d y (v + w), hforward y (v + w)⟩ : P y) =
        ⟨complexTangentToReal d y v, hforward y v⟩ +
          ⟨complexTangentToReal d y w, hforward y w⟩ := by
      apply Subtype.ext
      exact map_add (complexTangentToReal d y) _ _
    rw [heq]
    exact (t.linear ℝ hy).map_add _ _
  · intro c v
    have heq : (⟨complexTangentToReal d y ((c • v : S y) : TangentSpace (complexModel d) y), hforward y (c • v)⟩ : P y) =
        c • ⟨complexTangentToReal d y v, hforward y v⟩ := by
      apply Subtype.ext
      exact map_smul (complexTangentToReal d y) c (v : TangentSpace (complexModel d) y)
    rw [heq]
    exact (t.linear ℝ hy).map_smul _ _

end HolomorphicAnosov
