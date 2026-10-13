import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov
namespace ParameterGraphHomAtlas
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
  (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))

/-- In matching Hom frames, inversion is fixed finite-model inversion. -/
def modelInverse (i : A) (x : FiniteFiberModel (rank e f i)) :
    FiniteFiberModel (rank f e i) :=
  modelEquiv f e i (ContinuousLinearMap.inverse ((modelEquiv e f i).symm x))

lemma inverse_coordinates (i p : A) (hp : p ∈ baseSet e f i)
    (Q : E p →L[ℝ] F p) :
    coordinates f e i p ⟨hp.2,hp.1⟩ Q.inverse =
      modelInverse e f i (coordinates e f i p hp Q) := by
  simp only [modelInverse,coordinates,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  apply congrArg (modelEquiv f e i)
  change (e.coordinates i p hp.1).toContinuousLinearMap.comp
    (Q.inverse.comp (f.coordinates i p hp.2).symm.toContinuousLinearMap) =
      ((f.coordinates i p hp.2).toContinuousLinearMap.comp
        (Q.comp (e.coordinates i p hp.1).symm.toContinuousLinearMap)).inverse
  rw [ContinuousLinearMap.inverse_equiv_comp,ContinuousLinearMap.inverse_comp_equiv]
  rfl

lemma coordinates_isInvertible (i p : A) (hp : p ∈ baseSet e f i)
    (Q : E p →L[ℝ] F p) :
    ((modelEquiv e f i).symm (coordinates e f i p hp Q)).IsInvertible ↔ Q.IsInvertible := by
  simp only [coordinates,ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  change ((f.coordinates i p hp.2).toContinuousLinearMap.comp
    (Q.comp (e.coordinates i p hp.1).symm.toContinuousLinearMap)).IsInvertible ↔ Q.IsInvertible
  rw [ContinuousLinearMap.isInvertible_equiv_comp,ContinuousLinearMap.isInvertible_comp_equiv]

lemma modelInverse_contDiffAt (i : A) (r : ℕ) (x : FiniteFiberModel (rank e f i))
    (hx : ((modelEquiv e f i).symm x).IsInvertible) :
    ContDiffAt ℝ (r : ℕ∞ω) (modelInverse e f i) x := by
  exact (modelEquiv f e i).contDiff.contDiffAt.comp x
    (hx.contDiffAt_map_inverse.comp x (modelEquiv e f i).symm.contDiff.contDiffAt)

lemma inverse_chart_expression (i p : A) (hp : p ∈ baseSet e f i) :
    let := topology e f
    let := topology f e
    fibreChartExpression (atlas e f) (atlas f e) id
      (fun p ↦ ContinuousLinearMap.inverse (M := E p) (M₂ := F p)) i i p = modelInverse e f i := by
  let := topology e f
  let := topology f e
  funext x
  change FiniteFiberModel (rank e f i) at x
  have hc : (chart e f i) (⟨p,(coordinates e f i p hp).symm x⟩ : Sigma (fun p ↦ E p →L[ℝ] F p)) = (p,x) := by
    rw [chart_apply e f i p hp]
    simp
  have hi : (chart e f i).toOpenPartialHomeomorph.symm (p,x) =
      (⟨p,(coordinates e f i p hp).symm x⟩ : Sigma (fun p ↦ E p →L[ℝ] F p)) := by
    rw [← hc]
    exact (chart e f i).toOpenPartialHomeomorph.left_inv hp
  change ((chart f e i) (⟨_,_⟩ : Sigma (fun p ↦ F p →L[ℝ] E p))).2 = _
  change ((chart f e i) (⟨((chart e f i).toOpenPartialHomeomorph.symm (p,x)).1,
    (((chart e f i).toOpenPartialHomeomorph.symm (p,x)).2).inverse⟩ : Sigma (fun p ↦ F p →L[ℝ] E p))).2 = _
  rw [hi,chart_apply f e i p ⟨hp.2,hp.1⟩,inverse_coordinates e f i p hp]
  simp

/-- The invertible locus is open in the genuine original Hom topology.
Near each point, the matching Hom chart turns invertibility into invertibility
of a fixed finite-model operator, an open condition. -/
theorem isOpen_invertible :
    letI := topology e f
    IsOpen {z : Sigma (fun p ↦ E p →L[ℝ] F p) | z.2.IsInvertible} := by
  let := topology e f
  rw [isOpen_iff_mem_nhds]
  intro z hz
  let i := z.1
  have hp : z.1 ∈ baseSet e f i := ⟨e.mem_baseSet i,f.mem_baseSet i⟩
  have hs : (chart e f i).source ∈ nhds z := (chart e f i).open_source.mem_nhds hp
  have hc : ContinuousAt (fun w : Sigma (fun p ↦ E p →L[ℝ] F p) ↦
      (modelEquiv e f i).symm ((chart e f i w).2)) z :=
    (modelEquiv e f i).symm.continuous.continuousAt.comp
      ((chart e f i).toOpenPartialHomeomorph.continuousAt hp).snd
  have hzi : ((modelEquiv e f i).symm ((chart e f i z).2)).IsInvertible := by
    rw [chart_apply e f i z.1 hp]
    exact (coordinates_isInvertible e f i z.1 hp z.2).mpr hz
  have ht := hc.preimage_mem_nhds (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hzi)
  filter_upwards [hs,ht] with w hw hwi
  change ((modelEquiv e f i).symm ((chart e f i w).2)).IsInvertible at hwi
  rw [chart_apply e f i w.1 hw] at hwi
  exact (coordinates_isInvertible e f i w.1 hw w.2).mp hwi

/-- HPS pp.32–36,62: inversion is jointly fibre C^r on the original
invertible Hom locus. Matching source and receiving Hom charts identify it
with one fixed finite-model inverse. Its continuous ordinary jets are carried
back by the receiving frame; the local jet criterion then handles every pair
of charts. Original fibre smoothness follows from finite dimensionality and
the usual smooth inversion theorem. -/
theorem joint_inverse (r : ℕ) :
    letI := topology e f
    letI := topology f e
    JointFiberContDiffOn (atlas e f) (atlas f e) id r
      {z : Sigma (fun p ↦ E p →L[ℝ] F p) | z.2.IsInvertible}
      (fun p ↦ ContinuousLinearMap.inverse (M := E p) (M₂ := F p)) := by
  let := topology e f
  let := topology f e
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    let : FiniteDimensional ℝ (E z.1) :=
      (e.coordinates z.1 z.1 (e.mem_baseSet z.1)).symm.toLinearEquiv.finiteDimensional
    exact hz.contDiffAt_map_inverse
  · intro i m hm
    change ContinuousOn
      (fun z : (baseSet e f i) ×
          (FiniteFiberModel (rank e f i) × (Fin m → FiniteFiberModel (rank e f i))) ↦
        (⟨z.1.val,iteratedFDeriv ℝ m ContinuousLinearMap.inverse
          ((coordinates e f i z.1.val z.1.property).symm z.2.1)
          (fun a ↦ (coordinates e f i z.1.val z.1.property).symm (z.2.2 a))⟩ :
          Sigma (fun p ↦ F p →L[ℝ] E p)))
      {z | ((coordinates e f i z.1.val z.1.property).symm z.2.1).IsInvertible}
    rw [continuousOn_iff_continuous_domRestrict]
    let S : Set ((baseSet e f i) ×
        (FiniteFiberModel (rank e f i) × (Fin m → FiniteFiberModel (rank e f i)))) :=
      {z | ((coordinates e f i z.1.val z.1.property).symm z.2.1).IsInvertible}
    have hinv (z : S) : ((modelEquiv e f i).symm z.1.2.1).IsInvertible := by
      have hh := (coordinates_isInvertible e f i z.1.1.val z.1.1.property
        ((coordinates e f i z.1.1.val z.1.1.property).symm z.1.2.1)).mpr z.2
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
    have hj : Continuous (fun z : S ↦ iteratedFDeriv ℝ m (modelInverse e f i) z.1.2.1) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact ((modelInverse_contDiffAt e f i r z.1.2.1 (hinv z)).continuousAt_iteratedFDeriv
        (by exact_mod_cast hm)).comp (f := fun z : S ↦ z.1.2.1)
          continuous_subtype_val.snd.fst.continuousAt
    have hv : Continuous (fun z : S ↦ z.1.2.2) := continuous_subtype_val.snd.snd
    have heval := continuous_eval.comp (hj.prodMk hv)
    have hb : Continuous (fun z : S ↦ (⟨z.1.1.val,⟨z.1.1.property.2,z.1.1.property.1⟩⟩ :
        (atlas f e).chart i |>.baseSet)) :=
      (continuous_subtype_val.comp continuous_subtype_val.fst).subtype_mk _
    have hout := (atlas_frame_continuous (atlas f e) i).comp (hb.prodMk heval)
    apply hout.congr
    intro z
    change (⟨z.1.1.val,(coordinates f e i z.1.1.val ⟨z.1.1.property.2,z.1.1.property.1⟩).symm
      (iteratedFDeriv ℝ m (modelInverse e f i) z.1.2.1 z.1.2.2)⟩ :
      Sigma (fun p ↦ F p →L[ℝ] E p)) = _
    congr 1
    have hjet := parameter_graph_atlas_iterated_derivative_of_equiv (atlas e f) (atlas f e)
      id (fun p ↦ ContinuousLinearMap.inverse (M := E p) (M₂ := F p)) i i z.1.1.val
      z.1.1.property ⟨z.1.1.property.2,z.1.1.property.1⟩ m z.1.2.1 z.1.2.2
    rw [inverse_chart_expression e f i z.1.1.val z.1.1.property] at hjet
    exact (coordinates f e i z.1.1.val ⟨z.1.1.property.2,z.1.1.property.1⟩).symm_apply_eq.mpr hjet

end ParameterGraphHomAtlas
end HolomorphicAnosov
