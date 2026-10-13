import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

/-- Joint continuity of the first two scalar derivatives of genuine leaf-flowbox overlaps. (Ghys, §3) -/
theorem native_flowbox_overlap_derivatives_continuous {M ι J T : Type*} [TopologicalSpace M] [TopologicalSpace T]
    (L : ι → Type*) [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
    [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (inclusion : ∀ i, L i → M) (hcover : ∀ p, ∃ i x, inclusion i x = p)
    (c : J → OpenPartialHomeomorph M (ℂ × T))
    (hchart : ∀ k i (x : L i), inclusion i x ∈ (c k).source →
      ∃ q : LeafChart (L i), x ∈ q.val.source ∧
        ∀ v ∈ q.val.source, inclusion i v ∈ (c k).source ∧
          c k (inclusion i v) = (q.val v, (c k (inclusion i x)).2)) :
    ∀ k l,
      ContinuousOn (fun p : ℂ × T ↦ deriv (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
        ((c k).symm.trans (c l)).source ∧
      ContinuousOn (fun p : ℂ × T ↦ iteratedDeriv 2 (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
        ((c k).symm.trans (c l)).source := by
  intro k l
  let W := ((c k).symm.trans (c l)).source
  let H := fun p : ℂ × T ↦ ((c l) ((c k).symm p)).1
  have hW : IsOpen W := ((c k).symm.trans (c l)).open_source
  have hH : ContinuousOn H W := ((c k).symm.trans (c l)).continuousOn.fst
  have hhol : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ W} := by
    intro t z hz
    obtain ⟨i, x, hx⟩ := hcover ((c k).symm (z, t))
    have hzt : (z, t) ∈ (c k).target := hz.1
    have hk : inclusion i x ∈ (c k).source := hx ▸ (c k).map_target hzt
    have hl : inclusion i x ∈ (c l).source := hx ▸ hz.2
    have hp : c k (inclusion i x) = (z, t) := by rw [hx, (c k).right_inv hzt]
    obtain ⟨q, hq, hqc⟩ := hchart k i x hk
    obtain ⟨r, hr, hrc⟩ := hchart l i x hl
    have hzx : z = q.val x := by
      have hh := congrArg Prod.fst (hqc x hq).2
      rw [hp] at hh
      exact hh
    have hnear : (fun w ↦ H (w, t)) =ᶠ[𝓝 (q.val x)] (r.val ∘ q.val.symm) := by
      have hpre : ∀ᶠ w in 𝓝 (q.val x), q.val.symm w ∈ r.val.source := by
        have hc := q.val.continuousAt_symm (q.val.map_source hq)
        have hr' : q.val.symm (q.val x) ∈ r.val.source := by rwa [q.val.left_inv hq]
        exact hc.eventually (r.val.open_source.mem_nhds hr')
      filter_upwards [q.val.open_target.mem_nhds (q.val.map_source hq), hpre] with w hw hwr
      have hqw := hqc (q.val.symm w) (q.val.map_target hw)
      have he : c k (inclusion i (q.val.symm w)) = (w, t) := by
        simpa only [q.val.right_inv hw, hp] using hqw.2
      have hinv : (c k).symm (w, t) = inclusion i (q.val.symm w) := by
        rw [← he, (c k).left_inv hqw.1]
      change ((c l) ((c k).symm (w, t))).1 = r.val (q.val.symm w)
      rw [hinv]
      exact congrArg Prod.fst (hrc (q.val.symm w) hwr).2
    have hqs := contMDiffAt_symm_of_mem_maximalAtlas q.property (q.val.map_source hq)
    have hrs := contMDiffAt_of_mem_maximalAtlas r.property hr
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (r.val ∘ q.val.symm) (q.val x) := by
      apply ContMDiffAt.comp _ _ hqs
      simpa only [q.val.left_inv hq] using hrs
    rw [hzx]
    exact ((hcomp.contDiffAt.differentiableAt (by simp)).congr_of_eventuallyEq hnear).differentiableWithinAt
  have hfirst := SliceDerivativePreparation.joint_deriv_continuousOn_open W hW H hH hhol
  have hsecond := SliceDerivativePreparation.joint_deriv_continuousOn_open W hW
    (fun p ↦ deriv (fun z ↦ H (z, p.2)) p.1) hfirst
    (fun t ↦ (hhol t).deriv (hW.preimage (continuous_id.prodMk continuous_const)))
  refine ⟨hfirst, ?_⟩
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hsecond

end HolomorphicAnosov.Ghys

