import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Topology.VectorBundleOfLinearTrivializations
import Mathlib.Topology.VectorBundle.Basic
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineNormalization
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineModelEquivs
import HolomorphicAnosov.Paper.Ghys.NativeComplexLineTransport

/-! This file equips continuous rank-one complex tangent subbundles with fibre and vector bundle
structures modeled on `ℂ`, using the topology induced by the tangent inclusion. (Ghys, Lemma
2.1, p. 589; Lemma 3.3, p. 592) -/

noncomputable section
namespace HolomorphicAnosov

open Bundle Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold

universe u
attribute [local instance] complex_isManifold_real

/-- A continuous rank-one complex tangent subbundle admits complex fibre bundle and vector bundle
structures modeled on `ℂ` in its induced total-space topology. -/
theorem exists_native_complex_line_vectorBundle
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (T : ContinuousComplexTangentSubbundle (complexModel d) M)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hTS : T.toDistribution = S)
    (hRank : ∀ x, Module.finrank ℂ (S x) = 1) :
    let E := fun x : M ↦ ↥(S x)
    letI : TopologicalSpace (TotalSpace ℂ E) := TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∃ fb : FiberBundle ℂ E,
      letI := fb
      VectorBundle ℂ ℂ E := by
  subst S
  dsimp only
  let : TopologicalSpace (TotalSpace ℂ (fun x : M ↦ ↥(T.toDistribution x))) :=
    TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  classical
  have hnormalized (x : M) : ∃ e' : Trivialization ℂ
      (TotalSpace.proj (F := ℂ)
        (E := fun y : M ↦ ↥(T.toDistribution y))),
      x ∈ e'.baseSet ∧ e'.IsLinear ℂ := by
    let r := (T.locally_trivial x).choose
    let : TopologicalSpace
        (TotalSpace (Fin r → ℂ) (fun y : M ↦ ↥(T.toDistribution y))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let e := (T.locally_trivial x).choose_spec.choose
    change Trivialization (Fin r → ℂ)
      (TotalSpace.proj (F := Fin r → ℂ)
        (E := fun y : M ↦ ↥(T.toDistribution y))) at e
    have he : x ∈ e.baseSet := (T.locally_trivial x).choose_spec.choose_spec.1
    have hlinear : e.IsLinear ℂ := (T.locally_trivial x).choose_spec.choose_spec.2
    have hEq : Module.finrank ℂ (T.toDistribution x) = r :=
      (e.linearEquivAt ℂ x he).finrank_eq.trans <| by
        simp [r]
    have hrank : Module.finrank ℂ (Fin r → ℂ) = 1 := by
      calc
        Module.finrank ℂ (Fin r → ℂ) = r := by
          simp
        _ = Module.finrank ℂ (T.toDistribution x) := hEq.symm
        _ = 1 := hRank x
    let hmodel := (exists_complex_line_equiv_of_finrank_one (Fin r → ℂ) hrank).some
    let hTotal : TotalSpace ℂ (fun y : M ↦ ↥(T.toDistribution y)) ≃ₜ
        TotalSpace (Fin r → ℂ) (fun y : M ↦ ↥(T.toDistribution y)) :=
      { toEquiv :=
          { toFun := fun z ↦ ⟨z.proj, z.snd⟩
            invFun := fun z ↦ ⟨z.proj, z.snd⟩
            left_inv := by intro z; rfl
            right_inv := by intro z; rfl }
        continuous_toFun := by
          apply continuous_induced_rng.mpr
          simpa [Function.comp_def] using
            (continuous_induced_dom : Continuous
              (fun z : TotalSpace ℂ (fun y : M ↦ ↥(T.toDistribution y)) ↦
                (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)))
        continuous_invFun := by
          apply continuous_induced_rng.mpr
          simpa [Function.comp_def] using
            (continuous_induced_dom : Continuous
              (fun z : TotalSpace (Fin r → ℂ) (fun y : M ↦ ↥(T.toDistribution y)) ↦
                (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M))) }
    have hproj : (π (Fin r → ℂ) (fun y : M ↦ ↥(T.toDistribution y))) ∘ hTotal =
        π ℂ (fun y : M ↦ ↥(T.toDistribution y)) := by
      funext z
      rfl
    let e0 : Trivialization (Fin r → ℂ)
        (TotalSpace.proj (F := ℂ)
          (E := fun y : M ↦ ↥(T.toDistribution y))) :=
      Bundle.Trivialization.compHomeomorphOver e hTotal
        (fun z ↦ congrFun hproj z)
    refine ⟨e0.transFiberHomeomorph (hmodel.toContinuousLinearEquiv.toHomeomorph), ?_, ?_⟩
    · change x ∈ e0.baseSet
      exact he
    · refine ⟨?_⟩
      intro b hb
      change b ∈ e0.baseSet at hb
      change IsLinearMap ℂ (fun y : (T.toDistribution b) ↦
        (hmodel.toContinuousLinearEquiv.toHomeomorph ((e0 ⟨b, y⟩).2)))
      refine { map_add := ?_, map_smul := ?_ }
      · intro y z
        change hmodel ((e0 ⟨b, y + z⟩).2) =
          hmodel ((e0 ⟨b, y⟩).2) + hmodel ((e0 ⟨b, z⟩).2)
        change hmodel ((e ⟨b, y + z⟩).2) =
          hmodel ((e ⟨b, y⟩).2) + hmodel ((e ⟨b, z⟩).2)
        rw [congrArg hmodel ((hlinear.linear b hb).map_add y z)]
        exact hmodel.map_add _ _
      · intro c y
        change hmodel ((e0 ⟨b, c • y⟩).2) = c • hmodel ((e0 ⟨b, y⟩).2)
        change hmodel ((e ⟨b, c • y⟩).2) = c • hmodel ((e ⟨b, y⟩).2)
        rw [congrArg hmodel ((hlinear.linear b hb).map_smul c y)]
        exact hmodel.map_smul _ _
  let e' : ∀ x : M, Trivialization ℂ
      (TotalSpace.proj (F := ℂ)
        (E := fun y : M ↦ ↥(T.toDistribution y))) := fun x ↦ (hnormalized x).choose
  have hcover : ∀ x, x ∈ (e' x).baseSet := fun x ↦ (hnormalized x).choose_spec.1
  have hlin' : ∀ x, (e' x).IsLinear ℂ := fun x ↦ (hnormalized x).choose_spec.2
  have hind : ∀ x, IsInducing (@TotalSpace.mk M ℂ
      (fun y : M ↦ ↥(T.toDistribution y)) x) := by
    intro x
    have hmk := FiberBundle.totalSpaceMk_isInducing (ComplexModel d)
      (TangentSpace (complexModel d) : M → Type) x
    have hcomp : IsInducing (fun y : T.toDistribution x ↦
        (⟨x, y.val⟩ : TangentBundle (complexModel d) M)) :=
      hmk.comp (Topology.IsInducing.subtypeVal)
    apply IsInducing.mk
    rw [induced_compose]
    exact hcomp.eq_induced
  rcases Topology.exists_vectorBundle_of_linear_trivializations e'
      (fun x ↦ ⟨x, hcover x⟩) hlin' hind with ⟨fb, _, hfb⟩
  exact ⟨fb, hfb⟩


end HolomorphicAnosov
