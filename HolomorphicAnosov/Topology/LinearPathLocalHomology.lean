import HolomorphicAnosov.Topology.DiskDegreePairHomotopy
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local homology along paths of nonsingular linear maps

Source: Hatcher, Algebraic Topology, Proposition 2.19, p.118; Vector Bundles
and K-Theory, pp.23–24. Paths of nonsingular linear maps preserve the punctured
space. Their induced local homology maps and their determinant signs are constant.
-/

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov

/-- A continuous path of injective real linear endomorphisms induces the same map
on the homology of the punctured pair at both endpoints, in every degree.

Source: Hatcher, Algebraic Topology, Proposition 2.19, p.118, applied to the
linear paths of Vector Bundles and K-Theory, pp.23–24. Evaluation gives a jointly
continuous homotopy. Injectivity and preservation of zero ensure it preserves
the punctured subspace at every time. Restricting to that subspace gives a pair
homotopy, and the relative singular prism gives equality of the induced maps.
No positive dimension or choice of orientation generator is required.
Node: `topo.linear_path_local_homology_g6`.
-/
theorem linear_path_local_homology
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : unitInterval → E →L[ℝ] E) (hD : Continuous D)
    (hI : ∀ t, Function.Injective (D t)) (q : ℕ) :
    SSetPair.homologyMap
        (singularSubspacePairMap (TopCat.ofHom (toContinuousMap (D 0)))
          {x | x ≠ 0} {x | x ≠ 0}
          (fun _x hx hz ↦ hx (hI 0 (hz.trans (D 0).map_zero.symm))))
        singularIntegralCoefficients q =
      SSetPair.homologyMap
        (singularSubspacePairMap (TopCat.ofHom (toContinuousMap (D 1)))
          {x | x ≠ 0} {x | x ≠ 0}
          (fun _x hx hz ↦ hx (hI 1 (hz.trans (D 1).map_zero.symm))))
        singularIntegralCoefficients q := by
  let H : ContinuousMap.Homotopy (toContinuousMap (D 0)) (toContinuousMap (D 1)) :=
    { toFun := fun p ↦ D p.1 p.2
      continuous_toFun := (hD.comp continuous_fst).clm_apply continuous_snd
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact (relative_singular_homotopy_invariance (ModuleCat ℤ)
    (Topology.topPairHomotopy_of_continuousMapHomotopy {x : E | x ≠ 0} {x : E | x ≠ 0}
      (toContinuousMap (D 0)) (toContinuousMap (D 1))
      (fun _x hx hz ↦ hx (hI 0 (hz.trans (D 0).map_zero.symm)))
      (fun _x hx hz ↦ hx (hI 1 (hz.trans (D 1).map_zero.symm))) H
      (fun t x hx hz ↦ hx (hI t (hz.trans (D t).map_zero.symm))))
    singularIntegralCoefficients).2 q

/-- The determinant sign is constant along a continuous path of injective
endomorphisms of a finite-dimensional real space.

Source: Hatcher, Vector Bundles and K-Theory, p.24. The determinant is continuous
and never zero along the path, so its sign is a continuous map from the connected
interval to the discrete sign type. Such a map is constant. This also includes
the zero-dimensional space, whose determinant is the empty determinant one.
Node: `topo.linear_path_local_homology_g6`.
-/
theorem linear_path_det_sign
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : unitInterval → E →L[ℝ] E) (hD : Continuous D)
    (hI : ∀ t, Function.Injective (D t)) :
    SignType.sign (D 0).det = SignType.sign (D 1).det := by
  have hn (t : unitInterval) : (D t).det ≠ 0 := by
    change LinearMap.det (D t).toLinearMap ≠ 0
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]
    exact LinearMap.ker_eq_bot.mpr (hI t)
  have hc : Continuous (fun t ↦ SignType.sign (D t).det) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_sign_of_ne_zero (hn t)).comp
      (f := fun t : unitInterval ↦ (D t).det)
      ((ContinuousLinearMap.continuous_det.comp hD).continuousAt)
  exact ((IsLocallyConstant.iff_continuous _).mpr hc).apply_eq_of_preconnectedSpace 0 1

end HolomorphicAnosov

