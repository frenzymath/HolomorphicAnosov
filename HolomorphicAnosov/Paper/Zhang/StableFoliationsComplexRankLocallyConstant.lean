import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.LocallyConstant.Basic

/-! Local constancy of the fibre dimension of continuous complex tangent subbundles. (Ghys, Lemma
2.1, p.589) -/

noncomputable section
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.StableFoliationsSupport

/-- The complex fibre dimension of a continuous complex tangent subbundle is locally constant.
(Ghys, Lemma 2.1, p.589) -/
theorem complex_subbundle_finrank_isLocallyConstant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (S : ContinuousComplexTangentSubbundle I M) :
    IsLocallyConstant (fun x : M ↦ Module.finrank ℂ (S.toDistribution x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨r, e, hx, he⟩ := S.locally_trivial x
  let : TopologicalSpace
      (Bundle.TotalSpace (Fin r → ℂ) (fun y : M ↦ ↥(S.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle I M)) inferInstance
  let := he
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact (e.linearEquivAt ℂ y hy).finrank_eq.trans
    (e.linearEquivAt ℂ x hx).finrank_eq.symm

end HolomorphicAnosov.StableFoliationsSupport
