import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
HPS (1977), first proof of (5.5), printed pp.61–62: the fixed local-frame
calculation for joint fibre jets under continuous linear source/receiving changes.
The parameter has only a topology. Whole fibres are used, as in the cutoff
supplier's HasContinuousVerticalJets and the graph supplier's JointFiberContDiff.
This file does not assert that the native adapted atlas has yet been bound to
these fixed-model source/receiving changes.
-/

open Set
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.HPS.VerticalJetTransport

variable {P U V W Z : Type*} [TopologicalSpace P]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Exact ordinary vertical-jet formula, with the source linear map inserted
in each argument and the receiving linear map applied to the result. This
includes order zero and uses only the stated finite fibre regularity. -/
theorem jet_linear_transport (r m : ℕ) (hm : m ≤ r)
    (g : V → W) (hg : ContDiff ℝ r g) (L : U →L[ℝ] V) (R : W →L[ℝ] Z) (x : U) :
    iteratedFDeriv ℝ m (fun u ↦ R (g (L u))) x =
      R.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m g (L x)).compContinuousLinearMap (fun _ ↦ L)) := by
  change iteratedFDeriv ℝ m (R ∘ (g ∘ L)) x = _
  rw [R.iteratedFDeriv_comp_left ((hg.comp L.contDiff).contDiffAt) (by exact_mod_cast hm),
    L.iteratedFDeriv_comp_right hg x (by exact_mod_cast hm)]

/-- On the actual common base carrier S and whole source fibres, joint
continuity of the mth input jet is preserved by continuous source/receiving
linear coordinate changes. No smoothness of any parameter map is assumed.
Source: the parameter construction of HPS (5.5), printed p.62, expressed by
Mathlib's native linear pre/postcomposition formula. -/
theorem continuousOn_jet_linear_transport (S : Set P) (r m : ℕ) (hm : m ≤ r)
    (g : P → V → W) (hg : ∀ p ∈ S, ContDiff ℝ r (g p))
    (L : P → U →L[ℝ] V) (R : P → W →L[ℝ] Z)
    (hL : ContinuousOn L S) (hR : ContinuousOn R S)
    (hjet : ContinuousOn (fun z : P × V ↦ iteratedFDeriv ℝ m (g z.1) z.2)
      (S ×ˢ univ)) :
    ContinuousOn (fun z : P × U ↦
      iteratedFDeriv ℝ m (fun u ↦ R z.1 (g z.1 (L z.1 u))) z.2) (S ×ˢ univ) := by
  have hLs : ContinuousOn (fun z : P × U ↦ L z.1) (S ×ˢ univ) :=
    hL.comp continuous_fst.continuousOn (fun _ hz ↦ hz.1)
  have hRs : ContinuousOn (fun z : P × U ↦ R z.1) (S ×ˢ univ) :=
    hR.comp continuous_fst.continuousOn (fun _ hz ↦ hz.1)
  have hpoint : ContinuousOn (fun z : P × U ↦ (z.1, L z.1 z.2)) (S ×ˢ univ) :=
    continuous_fst.continuousOn.prodMk (hLs.clm_apply continuous_snd.continuousOn)
  have hJ := hjet.comp hpoint (fun z hz ↦ And.intro hz.1 (mem_univ _))
  have hpre : ContinuousOn (fun z : P × U ↦
      (iteratedFDeriv ℝ m (g z.1) (L z.1 z.2)).compContinuousLinearMap
        (fun _ ↦ L z.1)) (S ×ˢ univ) :=
    ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin m ↦ U) (fun _ : Fin m ↦ V) W).cont.comp_continuousOn
        (continuousOn_pi.mpr (fun _ ↦ hLs))).clm_apply hJ
  have hpost : ContinuousOn (fun z : P × U ↦
      (R z.1).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m (g z.1) (L z.1 z.2)).compContinuousLinearMap
          (fun _ ↦ L z.1))) (S ×ˢ univ) :=
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin m ↦ U) W Z).continuous.comp_continuousOn hRs).clm_apply hpre
  apply hpost.congr
  intro z hz
  exact jet_linear_transport r m hm (g z.1) (hg z.1 hz.1) (L z.1) (R z.1) z.2

/-- The full finite-order fixed-frame payload required by JointFiberContDiff,
on one common frame overlap S. The same cutoff and same coordinate changes
are retained at every order m ≤ r, and in particular at m = 0. -/
theorem fibreCr_and_jets_linear_transport (S : Set P) (r : ℕ)
    (g : P → V → W) (hg : ∀ p ∈ S, FibreCr r (g p))
    (L : P → U →L[ℝ] V) (R : P → W →L[ℝ] Z)
    (hL : ContinuousOn L S) (hR : ContinuousOn R S)
    (hjets : ∀ m ≤ r,
      ContinuousOn (fun z : P × V ↦ FibreJet m (g z.1) z.2) (S ×ˢ univ)) :
    (∀ p ∈ S, FibreCr r (fun u ↦ R p (g p (L p u)))) ∧
      ∀ m ≤ r, ContinuousOn
        (fun z : P × U ↦ FibreJet m (fun u ↦ R z.1 (g z.1 (L z.1 u))) z.2)
        (S ×ˢ univ) := by
  constructor
  · intro p hp
    exact (R p).contDiff.comp ((hg p hp).comp (L p).contDiff)
  · intro m hm
    exact continuousOn_jet_linear_transport S r m hm g hg L R hL hR (hjets m hm)

end HolomorphicAnosov.HPS.VerticalJetTransport

