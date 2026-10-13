import HolomorphicAnosov.Topology.GeometricFaceAffineSpanHomeomorph
import HolomorphicAnosov.Topology.GeometricFaceDeltaStdHomeomorph
import HolomorphicAnosov.Topology.GeometricFaceIntrinsicInteriorBridge
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology

namespace HolomorphicAnosov
open Set Topology _root_.Topology Metric
open scoped BigOperators
noncomputable section
variable {N d : ℕ}
def stdToCoordY (w : Convexity.StdSimplex ℝ (Fin (d+1))) : fintypeAffineCoords (Fin (d+1)) ℝ :=
  ⟨Finsupp.equivFunOnFinite w.weights, by rw [mem_fintypeAffineCoords_iff_sum]; simp⟩
lemma cont_stdToCoordY : Continuous (@stdToCoordY d) := by
  apply Continuous.subtype_mk
  · apply continuous_pi; intro i; exact Convexity.StdSimplex.continuous_weights_apply ℝ i

/-- The standard simplex parameterizes the hull by its barycentric combination. (Hatcher) -/
theorem geometric_face_std_barycentric_homeomorph
    (N d : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : s ∈ P.faces) (hcard : s.card = d + 1) :
    ∃ betaStd : Convexity.StdSimplex ℝ (Fin (d + 1)) ≃ₜ
      {x : EuclideanSpace ℝ (Fin N) // x ∈ convexHull ℝ (s : Set _)},
      ∀ w, (betaStd w).val = Finset.univ.affineCombination ℝ
        (fun i : Fin (d + 1) ↦
          ((Fintype.equivFinOfCardEq
            (show Fintype.card s = d + 1 by simpa using hcard)).symm i).val)
        (fun i ↦ w.weights i) := by
  classical
  classical
  let efin : Fin (d+1) ≃ s := (Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hcard)).symm
  let pts : Fin (d+1) → EuclideanSpace ℝ (Fin N) := fun i => (efin i).val
  let hull : Set (EuclideanSpace ℝ (Fin N)) :=
    convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))
  have hrange : Set.range pts =
      (s : Set (EuclideanSpace ℝ (Fin N))) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact (efin i).property
    · intro hx; exact ⟨efin.symm ⟨x, hx⟩, by simp [pts]⟩
  obtain ⟨e, he⟩ := exists_geometric_face_affine_span_homeomorph N d P s hs hcard
  let F : Convexity.StdSimplex ℝ (Fin (d+1)) → EuclideanSpace ℝ (Fin N) :=
    fun w => (e (stdToCoordY w)).val
  have hF_cont : Continuous F := by
    exact continuous_subtype_val.comp (e.continuous.comp cont_stdToCoordY)
  have hF_image : Set.range F = hull := by
    apply Set.Subset.antisymm
    · rintro x ⟨w, rfl⟩
      change (e (stdToCoordY w)).val ∈ hull
      rw [he (stdToCoordY w)]
      change ((Finset.affineCombination ℝ Finset.univ pts) (fun i => w.weights i)) ∈
        convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))
      rw [← hrange]
      exact affineCombination_mem_convexHull (R := ℝ)
        (E := EuclideanSpace ℝ (Fin N)) (s := Finset.univ) (v := pts)
        (w := fun i => w.weights i) (fun i _ => w.weights_nonneg i)
        (by simp)
    · intro x hx
      rw [Finset.mem_convexHull'] at hx
      rcases hx with ⟨W, hWnonneg, hWsum, hWvec⟩
      let wf : Fin (d+1) → ℝ := fun i => W ((efin i).val)
      have hw_nonneg : ∀ i, 0 ≤ wf i := fun i => hWnonneg _ (efin i).property
      have hw_sum : ∑ i, wf i = 1 := by
        change (∑ i, W ((efin i).val)) = 1
        have hs' := Fintype.sum_equiv efin (fun i => W (efin i).val)
          (fun y : s => W y.val) (fun i => rfl)
        calc
          (∑ i, W ((efin i).val)) = ∑ y : s, W y.val := hs'
          _ = ∑ y ∈ s, W y := Finset.sum_coe_sort s W
          _ = 1 := hWsum
      let w : Convexity.StdSimplex ℝ (Fin (d+1)) :=
        ⟨Finsupp.equivFunOnFinite.symm wf, hw_nonneg,
          by simpa [Finsupp.sum_fintype] using hw_sum⟩
      refine ⟨w, ?_⟩
      change (e (stdToCoordY w)).val = x
      rw [he (stdToCoordY w)]
      change (Finset.affineCombination ℝ Finset.univ pts) wf = x
      have hv : (∑ i, wf i • pts i) = ∑ y ∈ s, W y • y := by
        change (∑ i, W ((efin i).val) • pts i) = _
        calc
          (∑ i, W ((efin i).val) • pts i) = ∑ y : s, W y.val • y.val :=
            Fintype.sum_equiv efin (fun i => W (efin i).val • pts i)
              (fun y : s => W y.val • y.val) (fun i => rfl)
          _ = ∑ y ∈ s, W y • y := Finset.sum_coe_sort s (fun y => W y • y)
      have hWvec' : (∑ y ∈ s, W y • y) = x := by
        simpa only [Finset.sum_attach] using hWvec
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum]
      rw [hv]
      exact hWvec'
  have hF_inj : Function.Injective F := by
    intro w₁ w₂ h
    have heq : e (stdToCoordY w₁) = e (stdToCoordY w₂) := Subtype.ext h
    have hcoord : stdToCoordY w₁ = stdToCoordY w₂ := e.injective heq
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    simpa [stdToCoordY] using congrArg (fun z => z i) (congrArg Subtype.val hcoord)
  let f : Convexity.StdSimplex ℝ (Fin (d+1)) →
      {x : EuclideanSpace ℝ (Fin N) // x ∈ hull} := fun w => ⟨F w, by
    rw [← hF_image]
    exact Set.mem_range_self w⟩
  have hf_cont : Continuous f := by
    exact Continuous.subtype_mk hF_cont (fun w => by
      rw [← hF_image]
      exact Set.mem_range_self w)
  have hf_bij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro w₁ w₂ h
      exact hF_inj (by simpa [f] using congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range F := by
        rw [hF_image]
        exact x.property
      rcases hx with ⟨w, hw⟩
      exact ⟨w, Subtype.ext hw⟩
  let : CompactSpace (Convexity.StdSimplex ℝ (Fin (d+1))) := inferInstance
  let hKcompact : IsCompact
      (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))) :=
    s.finite_toSet.isCompact_convexHull ℝ
  let : CompactSpace {x : EuclideanSpace ℝ (Fin N) // x ∈ hull} :=
    isCompact_iff_compactSpace.mp (by simpa [hull] using hKcompact)
  let betaStd : Convexity.StdSimplex ℝ (Fin (d+1)) ≃ₜ
      {x : EuclideanSpace ℝ (Fin N) // x ∈ hull} :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij) hf_cont
  have hbeta : ∀ w, (betaStd w).val =
      Finset.univ.affineCombination ℝ pts (fun i => w.weights i) := by
    intro w
    change (e (stdToCoordY w)).val = _
    rw [he (stdToCoordY w)]
    rfl
  exact ⟨betaStd, hbeta⟩

theorem geometric_face_barycentric_homeomorph
    (N d : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : s ∈ P.faces)
    (hcard : s.card = d + 1) :
    let V := Fin d → ℝ
    let Delta : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    let I : Set V := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
    ∃ beta : {u : V // u ∈ Delta} ≃ₜ
        {x : EuclideanSpace ℝ (Fin N) // x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))},
      beta '' {u : {u : V // u ∈ Delta} | (u : V) ∈ I} =
        {x : {x : EuclideanSpace ℝ (Fin N) //
          x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))} |
          x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))))} := by
  obtain ⟨betaStd, hbeta⟩ := geometric_face_std_barycentric_homeomorph N d P s hs hcard
  refine ⟨(face_delta_std_homeomorph d).trans betaStd, ?_⟩
  exact geometric_face_intrinsicInterior_strict_bridge N d P s hs hcard betaStd hbeta
end
end HolomorphicAnosov
