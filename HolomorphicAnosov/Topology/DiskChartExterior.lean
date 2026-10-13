import HolomorphicAnosov.Topology.DiskChartOpenInteriorBoundary
import HolomorphicAnosov.Topology.OnePointCompactComplement

open Set Metric
namespace HolomorphicAnosov

/-- The exterior of a planar disk chart is connected and has the same frontier
as the chart interior. Source: Hatcher, Proposition 2B.1(a), pp.169–170, and
Theorem 2B.3, p.172. The inverse chart embeds a compact disk, so its spherical
complement is preconnected; compact-complement comparison removes infinity.
If a boundary point were interior to the closed cell, the chart restricted to
that plane neighborhood would have open image contained in the closed disk
and containing a circle point, contrary to the ball being the disk interior.
Thus the original open cell is regular open and its exterior has its frontier. -/
theorem disk_chart_exterior
    (U : Set ℂ) (hU : IsOpen U)
    (F : closure U ≃ₜ closedBall (0 : ℂ) 1)
    (hF : ∀ z : closure U, (z : ℂ) ∈ U ↔ (F z : ℂ) ∈ ball (0 : ℂ) 1) :
    IsConnected (closure U)ᶜ ∧ ¬Bornology.IsBounded (closure U)ᶜ ∧
      frontier (closure U)ᶜ = frontier U := by
  let f : closedBall (0 : ℂ) 1 → ℂ := fun z ↦ (F.symm z : ℂ)
  have hf : Continuous f := continuous_subtype_val.comp F.symm.continuous
  have hfi : Function.Injective f := fun x y h ↦ F.symm.injective (Subtype.ext h)
  have hr : range f = closure U := by
    ext z
    exact ⟨fun ⟨w, hw⟩ ↦ hw ▸ (F.symm w).property,
      fun hz ↦ ⟨F ⟨z, hz⟩, congrArg Subtype.val (F.symm_apply_apply _)⟩⟩
  have hcompact : IsCompact (closure U) := hr ▸ isCompact_range hf
  have hunbounded : ¬Bornology.IsBounded (closure U)ᶜ := by
    intro h
    apply NormedSpace.unbounded_univ ℝ ℂ
    simpa using hcompact.isBounded.union h
  have hne : ((closure U)ᶜ).Nonempty := by
    by_contra h
    exact hunbounded (by rw [not_nonempty_iff_eq_empty.mp h]; exact Bornology.isBounded_empty)
  let e := Complex.orthonormalBasisOneI.repr.symm
  let T : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
    e.toHomeomorph.subtype (fun x ↦ by simp)
  let g : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℂ := f ∘ T
  have hg : Continuous g := hf.comp T.continuous
  have hgr : range g = closure U := by
    rw [range_comp, T.surjective.range_eq, image_univ, hr]
  have hS : IsPreconnected (OnePoint.some '' closure U)ᶜ := by
    rw [← hgr]
    exact (Topology.hatcher_planar_disk_spherical_separation 0 1 (by norm_num)
      g hg (hfi.comp T.injective)).1
  have hpre : IsPreconnected (closure U)ᶜ := by
    apply isPreconnected_of_forall_pair
    intro x hx y hy
    have hxy : OnePoint.some y ∈ connectedComponentIn
        (OnePoint.some '' closure U)ᶜ (OnePoint.some x) :=
      hS.subset_connectedComponentIn (by simpa using hx) subset_rfl (by simpa using hy)
    exact ⟨connectedComponentIn (closure U)ᶜ x, connectedComponentIn_subset _ _,
      mem_connectedComponentIn hx,
      Topology.onePoint_complex_complement_component hcompact hx hy hxy,
      isPreconnected_connectedComponentIn⟩
  have hreg : interior (closure U) = U := by
    apply Subset.antisymm _ hU.subset_interior_closure
    intro z hz
    let k : interior (closure U) → ℂ :=
      fun w ↦ (F ⟨w, interior_subset w.property⟩ : ℂ)
    have hk : Continuous k := by fun_prop
    have hki : Function.Injective k := by
      intro x y h
      exact Subtype.ext (congrArg (fun w : closure U ↦ (w : ℂ))
        (F.injective (Subtype.ext h)))
    have hopen : IsOpen (range k) := complex_planar_open_range _ isOpen_interior k hk hki
    have hsub : range k ⊆ closedBall (0 : ℂ) 1 := by
      rintro w ⟨x, rfl⟩
      exact (F ⟨x, interior_subset x.property⟩).property
    have hball : range k ⊆ ball (0 : ℂ) 1 := by
      rw [← interior_closedBall (0 : ℂ) one_ne_zero]
      exact interior_maximal hsub hopen
    exact (hF ⟨z, interior_subset hz⟩).mpr (hball (mem_range_self (f := k) ⟨z, hz⟩))
  refine ⟨⟨hne, hpre⟩, hunbounded, ?_⟩
  rw [frontier_compl, frontier, closure_closure, hreg, ← hU.frontier_eq]

end HolomorphicAnosov
