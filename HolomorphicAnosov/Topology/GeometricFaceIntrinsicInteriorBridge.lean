import HolomorphicAnosov.Topology.GeometricFaceDeltaStdHomeomorph
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import HolomorphicAnosov.Topology.StandardCoordinateSimplexInteriorFrontier

namespace HolomorphicAnosov

private def wholeCoord (d : ℕ) : (Fin d → ℝ) ≃ₜ fintypeAffineCoords (Fin (d+1)) ℝ where
  toFun u := ⟨faceBaryExt d u, (mem_fintypeAffineCoords_iff_sum).mpr (faceBaryExt_sum d u)⟩
  invFun w := fun (i : Fin d) => w.val i.succ
  left_inv u := rfl
  right_inv w := by
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun i => rfl) j
    have hsum := mem_fintypeAffineCoords_iff_sum.mp w.property
    rw [Fin.sum_univ_succ] at hsum
    change 1 - ∑ i : Fin d, w.val i.succ = w.val 0
    linarith
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · change Continuous (fun u : Fin d → ℝ => 1 - ∑ i, u i)
      fun_prop
    · change Continuous (fun u : Fin d → ℝ => u i)
      fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact (continuous_apply i.succ).comp continuous_subtype_val

open Set Topology _root_.Topology Metric
open scoped BigOperators
noncomputable section

/-- The strict positive-weight locus of the standard simplex maps to the intrinsic interior of the geometric convex hull under the affine barycentric map. (Hatcher) -/
theorem geometric_face_stdSimplex_intrinsicInterior_bridge
    (N d : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : s ∈ P.faces)
    (hcard : s.card = d + 1)
    (betaStd : Convexity.StdSimplex ℝ (Fin (d + 1)) ≃ₜ
      {x : EuclideanSpace ℝ (Fin N) //
        x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))})
    (hbeta : ∀ w, (betaStd w).val =
      Finset.univ.affineCombination ℝ
        (fun i : Fin (d + 1) =>
          ((Fintype.equivFinOfCardEq
            (show Fintype.card s = d + 1 by simpa using hcard)).symm i).val)
        (fun i => w.weights i)) :
    betaStd '' {w : Convexity.StdSimplex ℝ (Fin (d + 1)) |
      ∀ j, 0 < w.weights j} =
      {x : {x : EuclideanSpace ℝ (Fin N) //
          x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))} |
        x.val ∈ intrinsicInterior ℝ
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))))} := by
  classical
  let E0 := EuclideanSpace ℝ (Fin N)
  let efin : Fin (d+1) ≃ s := (Fintype.equivFinOfCardEq (show Fintype.card s = d + 1 by simpa using hcard)).symm
  let pts : Fin (d+1) → E0 := fun i => (efin i).val
  have hrange : Set.range pts = (s : Set E0) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact (efin i).property
    · intro hy
      refine ⟨efin.symm ⟨y, hy⟩, ?_⟩
      simp [pts]
  obtain ⟨e, he⟩ := exists_geometric_face_affine_span_homeomorph N d P s hs hcard
  let C : Set (fintypeAffineCoords (Fin (d+1)) ℝ) := {w | ∀ i, 0 ≤ (w : Fin (d+1) → ℝ) i}
  let E := fintypeAffineCoords (Fin (d+1)) ℝ
  let A := affineSpan ℝ (Set.range pts)
  have hC_image : e '' C = {x : A | x.val ∈ convexHull ℝ (s : Set E0)} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hew := he w
      change (e w).val ∈ convexHull ℝ (s : Set E0)
      rw [hew]
      change (Finset.affineCombination ℝ Finset.univ pts)
          (fun i => (w : Fin (d+1) → ℝ) i) ∈ convexHull ℝ (s : Set E0)
      rw [← hrange]
      exact affineCombination_mem_convexHull (R := ℝ) (E := E0) (s := Finset.univ) (v := pts)
        (w := fun i => (w : Fin (d+1) → ℝ) i)
        (fun i _ => hw i) (mem_fintypeAffineCoords_iff_sum.mp w.property)
    · intro hx
      change x.val ∈ convexHull ℝ (s : Set E0) at hx
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
      let w : E := ⟨Finsupp.equivFunOnFinite.symm wf, by
        rw [mem_fintypeAffineCoords_iff_sum]
        simpa [Finsupp.sum_fintype] using hw_sum⟩
      have hwC : w ∈ C := by intro i; exact hw_nonneg i
      refine ⟨w, hwC, ?_⟩
      apply Subtype.ext
      rw [he]
      change Finset.univ.affineCombination ℝ pts wf = x.val
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum]
      have hv : (∑ i, wf i • pts i) = ∑ y ∈ s, W y • y := by
        change (∑ i, W ((efin i).val) • pts i) = _
        calc
          (∑ i, W ((efin i).val) • pts i) = ∑ y : s, W y.val • y.val :=
            Fintype.sum_equiv efin (fun i => W (efin i).val • pts i)
              (fun y : s => W y.val • y.val) (fun i => rfl)
          _ = ∑ y ∈ s, W y • y := Finset.sum_coe_sort s (fun y => W y • y)
      rw [hv]
      simpa only [Finset.sum_attach] using hWvec
  let Delta : Set (Fin d → ℝ) := faceCoordDelta d
  let I : Set (Fin d → ℝ) := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
  have hwhole_delta : wholeCoord d '' Delta = C := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · dsimp [wholeCoord, faceBaryExt]
        change 0 ≤ 1 - ∑ j, u j
        linarith [hu.2]
      · exact hu.1 j
    · intro hw
      refine ⟨(wholeCoord d).symm w, ?_, ?_⟩
      · exact ⟨fun i => hw i.succ, by
          have hsum := mem_fintypeAffineCoords_iff_sum.mp w.property
          rw [Fin.sum_univ_succ] at hsum
          have h0 := hw 0
          change (∑ i : Fin d, w.val i.succ) ≤ 1
          linarith⟩
      · exact (wholeCoord d).apply_symm_apply w
  have hwhole_strict : wholeCoord d '' I = interior C := by
    have hinter : interior Delta = I := by
      exact (standard_coordinate_simplex_interior d).2
    calc
      wholeCoord d '' I = wholeCoord d '' interior Delta := by rw [hinter]
      _ = interior (wholeCoord d '' Delta) := (wholeCoord d).image_interior Delta
      _ = interior C := by rw [hwhole_delta]
  have hstrictA : e '' interior C =
      interior {x : A | x.val ∈ convexHull ℝ (s : Set E0)} := by
    rw [e.image_interior, hC_image]
  have hAeq : A = affineSpan ℝ (convexHull ℝ (s : Set E0)) := by
    dsimp [A]
    rw [hrange, affineSpan_convexHull]
  let H : AffineSubspace ℝ E0 := affineSpan ℝ (convexHull ℝ (s : Set E0))
  let : Nonempty A := by
    refine ⟨⟨pts 0, ?_⟩⟩
    exact subset_affineSpan ℝ (Set.range pts) ⟨0, rfl⟩
  let : Nonempty H := by
    refine ⟨⟨pts 0, ?_⟩⟩
    exact subset_affineSpan ℝ (convexHull ℝ (s : Set E0))
      (subset_convexHull ℝ (s : Set E0) (show pts 0 ∈ (s : Set E0) from (efin 0).property))
  let q : A ≃ₜ H := AffineSubspace.ofEq hAeq
  have hcarrier : q '' {x : A | x.val ∈ convexHull ℝ (s : Set E0)} =
      {x : H | x.val ∈ convexHull ℝ (s : Set E0)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(q.symm x), ?_, ?_⟩
      · exact hx
      · apply Subtype.ext
        rfl
  have hcarrier_interior : q '' interior {x : A | x.val ∈ convexHull ℝ (s : Set E0)} =
      interior {x : H | x.val ∈ convexHull ℝ (s : Set E0)} := by
    rw [q.image_interior, hcarrier]
  have htarget : e '' interior C =
      {x : A | x.val ∈ intrinsicInterior ℝ
        (convexHull ℝ (s : Set E0))} := by
    rw [hstrictA]
    ext x
    constructor
    · intro hx
      have hqx : q x ∈ interior {y : H | y.val ∈ convexHull ℝ (s : Set E0)} := by
        rw [← hcarrier_interior]
        exact ⟨x, hx, rfl⟩
      have hi : (q x).val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E0)) :=
        mem_intrinsicInterior.mpr ⟨q x, hqx, rfl⟩
      exact hi
    · intro hx
      rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, hyeq⟩
      have hxy : q.symm y = x := Subtype.ext (by
        exact hyeq)
      rw [← hxy]
      have hsy : q.symm y ∈ interior {z : A | z.val ∈ convexHull ℝ (s : Set E0)} := by
        have hmem : y ∈ q '' interior {z : A | z.val ∈ convexHull ℝ (s : Set E0)} := by
          rw [hcarrier_interior]
          exact hy
        rcases hmem with ⟨z, hz, hzy⟩
        have hzq : z = q.symm y := by
          apply q.injective
          simp [hzy]
        simpa [hzq] using hz
      exact hsy
  let W : Set (Convexity.StdSimplex ℝ (Fin (d + 1))) := {w | ∀ j, 0 < w.weights j}
  let stdToCoordY' (w : Convexity.StdSimplex ℝ (Fin (d+1))) : E :=
    ⟨Finsupp.equivFunOnFinite w.weights, by
      rw [mem_fintypeAffineCoords_iff_sum]
      simp⟩
  have hstd_image : stdToCoordY' '' W = interior C := by
    rw [← hwhole_strict]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨faceBaryDrop d w.weights, ?_, ?_⟩
      · constructor
        · intro i; exact hw i.succ
        · have ht := w.total_of_fintype
          rw [Fin.sum_univ_succ] at ht
          linarith [hw 0]
      · apply Subtype.ext
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · change 1 - ∑ i : Fin d, w.weights i.succ = w.weights 0
          rw [← w.total_of_fintype]
          rw [Fin.sum_univ_succ]
          ring
        · rfl
    · rintro ⟨u, hu, rfl⟩
      let w : Convexity.StdSimplex ℝ (Fin (d + 1)) :=
        ⟨Finsupp.equivFunOnFinite.symm (wholeCoord d u),
          by
            intro j
            exact faceBaryExt_nonneg d ⟨(fun i => le_of_lt (hu.1 i)), hu.2.le⟩ j,
          by
            simpa [Finsupp.sum_fintype] using (mem_fintypeAffineCoords_iff_sum.mp (wholeCoord d u).property)⟩
      refine ⟨w, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · change 0 < 1 - ∑ i, u i
          linarith [hu.2]
        · exact hu.1 i
      · apply Subtype.ext
        rfl
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwC : stdToCoordY' w ∈ interior C := by
      rw [← hstd_image]
      exact ⟨w, hw, rfl⟩
    have hzA : e (stdToCoordY' w) ∈ interior {z : A | z.val ∈ convexHull ℝ (s : Set E0)} := by
      rw [← hstrictA]
      exact ⟨stdToCoordY' w, hwC, rfl⟩
    have hq : q (e (stdToCoordY' w)) ∈ interior {z : H | z.val ∈ convexHull ℝ (s : Set E0)} := by
      rw [← hcarrier_interior]
      exact ⟨e (stdToCoordY' w), hzA, rfl⟩
    have hi : (q (e (stdToCoordY' w))).val ∈ intrinsicInterior ℝ
        (convexHull ℝ (s : Set E0)) :=
      mem_intrinsicInterior.mpr ⟨q (e (stdToCoordY' w)), hq, rfl⟩
    change (betaStd w).val ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E0))
    have hbe : (betaStd w).val = (e (stdToCoordY' w)).val := by
      rw [hbeta, he]
      rfl
    rw [hbe]
    exact hi
  · intro hx
    rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, hyeq⟩
    have hy' : y ∈ interior {z : H | z.val ∈ convexHull ℝ (s : Set E0)} := hy
    have hyA : y ∈ q '' interior {z : A | z.val ∈ convexHull ℝ (s : Set E0)} := by
      rw [hcarrier_interior]
      exact hy'
    rcases hyA with ⟨z, hz, hzy⟩
    have hzE : z ∈ e '' interior C := by
      rw [hstrictA]
      exact hz
    rcases hzE with ⟨u, hu, huz⟩
    have huW : u ∈ interior C := hu
    rw [← hstd_image] at huW
    rcases huW with ⟨w, hw, hwu⟩
    refine ⟨w, hw, ?_⟩
    apply Subtype.ext
    calc
      (betaStd w).val = (e (stdToCoordY' w)).val := by
        rw [hbeta, he]
        rfl
      _ = (e u).val := by rw [hwu]
      _ = z.val := congrArg Subtype.val huz
      _ = x.val := by
        calc
          z.val = (q z).val := rfl
          _ = y.val := congrArg Subtype.val hzy
          _ = x.val := hyeq
end


/-- Intrinsic-interior transport for the ordered barycentric simplex. (Hatcher) -/
theorem geometric_face_intrinsicInterior_strict_bridge
    (N d : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (s : Finset (EuclideanSpace ℝ (Fin N)))
    (hs : s ∈ P.faces)
    (hcard : s.card = d + 1)
    (betaStd : Convexity.StdSimplex ℝ (Fin (d + 1)) ≃ₜ
      {x : EuclideanSpace ℝ (Fin N) //
        x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))})
    (hbeta : ∀ w, (betaStd w).val =
      Finset.univ.affineCombination ℝ
        (fun i : Fin (d + 1) =>
          ((Fintype.equivFinOfCardEq
            (show Fintype.card s = d + 1 by simpa using hcard)).symm i).val)
        (fun i => w.weights i)) :
    ((face_delta_std_homeomorph d).trans betaStd) ''
        {u : {u : faceCoordV d // u ∈ faceCoordDelta d} |
          (u : faceCoordV d) ∈
            {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}} =
      {x : {x : EuclideanSpace ℝ (Fin N) //
          x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))} |
        x.val ∈ intrinsicInterior ℝ
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))))} := by
  let W : Set (Convexity.StdSimplex ℝ (Fin (d + 1))) := {w | ∀ j, 0 < w.weights j}
  have hstrict :
      ((face_delta_std_homeomorph d).trans betaStd) ''
          {u : {u : faceCoordV d // u ∈ faceCoordDelta d} |
            (u : faceCoordV d) ∈
              {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}} =
        betaStd '' W := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨face_delta_std_homeomorph d u, ?_, rfl⟩
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · have hsum : ∑ i, (u : faceCoordV d) i < 1 := hu.2
        have hw0 : (face_delta_std_homeomorph d u).weights 0 =
            1 - ∑ i, (u : faceCoordV d) i := by
          rfl
        rw [hw0]
        linarith
      · have hwi : (face_delta_std_homeomorph d u).weights i.succ =
            (u : faceCoordV d) i := by
          rfl
        rw [hwi]
        exact hu.1 i
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(face_delta_std_homeomorph d).symm w, ?_, ?_⟩
      · constructor
        · intro i
          have hi := hw i.succ
          have hui : ((face_delta_std_homeomorph d).symm w : faceCoordV d) i =
              w.weights i.succ := by
            rfl
          rw [hui]
          exact hi
        · have h0 := hw 0
          have hsum : ∑ i, ((face_delta_std_homeomorph d).symm w : faceCoordV d) i < 1 := by
            have hsum' : (∑ i : Fin d, w.weights i.succ) = 1 - w.weights 0 := by
              have htotal := w.total_of_fintype
              rw [Fin.sum_univ_succ] at htotal
              linarith
            have hu_sum : (∑ i, ((face_delta_std_homeomorph d).symm w : faceCoordV d) i) =
                (∑ i : Fin d, w.weights i.succ) := by
              apply Finset.sum_congr rfl
              intro (i : Fin d) hi
              rfl
            rw [hu_sum, hsum']
            linarith
          exact hsum
      · rw [Homeomorph.trans_apply]
        exact congrArg betaStd ((face_delta_std_homeomorph d).apply_symm_apply w)
  rw [hstrict]
  exact geometric_face_stdSimplex_intrinsicInterior_bridge N d P s hs hcard betaStd hbeta


end HolomorphicAnosov
