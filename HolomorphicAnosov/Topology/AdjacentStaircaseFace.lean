import HolomorphicAnosov.Topology.Homology.SignedShuffleStaircaseRecursion

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The two paths obtained by prefixing a common staircase by H,V and V,H
share the same diagonal face. This is the finite adjacent-square face
identification expanding the calculation omitted in Hatcher §3.B, pp.277--278.

Proof: In the continuous-map representation, compose both affine coordinate
maps with the vertex-deletion map. Vertex zero stays zero in both. Each other
surviving vertex lies after the two new steps; both coordinates are those of the
same tail vertex, increased by one. Functoriality of the affine simplex map then
gives equality. The assertion holds for arbitrary grid-vertex tails and hence
also for every staircase, including a zero-dimensional tail. -/
theorem adjacent_prefix_middle_face_agree {p q : ℕ} {X Y : TopCat.{u}}
    (w : GridPath p q) (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ
      (1 : Fin ((p + 1) + (q + 1) + 1))
      (productSimplex (p := p + 1) (q := q + 1) X Y
        (@prependHorizontal p (q + 1) (prependVertical w)) σ τ) =
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ
      (1 : Fin ((p + 1) + (q + 1) + 1))
      (productSimplex (p := p + 1) (q := q + 1) X Y
        (@prependVertical (p + 1) q (prependHorizontal w)) σ τ) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y))
    (Opposite.op ⦋(p + 1) + (q + 1) - 1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
      (Convexity.StdSimplex.map
        (fun k ↦ (@prependHorizontal p (q + 1) (prependVertical w) k).1)
        (Convexity.StdSimplex.map
          (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q + 1⦌) τ)
      (Convexity.StdSimplex.map
        (fun k ↦ (@prependHorizontal p (q + 1) (prependVertical w) k).2)
        (Convexity.StdSimplex.map
          (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove z))) = _
  change _ =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
      (Convexity.StdSimplex.map
        (fun k ↦ (@prependVertical (p + 1) q (prependHorizontal w) k).1)
        (Convexity.StdSimplex.map
          (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q + 1⦌) τ)
      (Convexity.StdSimplex.map
        (fun k ↦ (@prependVertical (p + 1) q (prependHorizontal w) k).2)
        (Convexity.StdSimplex.map
          (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove z)))
  simp only [← Convexity.StdSimplex.map_comp]
  congr 3 <;> funext i
  · by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      rfl
    · have hsucc : (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i = i.succ := by
        apply Fin.succAbove_of_le_castSucc
        have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
        change 1 ≤ i.val
        exact hige
      change (@prependHorizontal p (q + 1) (prependVertical w)
        ((1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i)).1 =
        (@prependVertical (p + 1) q (prependHorizontal w)
          ((1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i)).1
      rw [hsucc]
      simp [prependHorizontal, prependVertical, hi]
  · by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      rfl
    · have hsucc : (1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i = i.succ := by
        apply Fin.succAbove_of_le_castSucc
        have hige : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr hi
        change 1 ≤ i.val
        exact hige
      change (@prependHorizontal p (q + 1) (prependVertical w)
        ((1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i)).2 =
        (@prependVertical (p + 1) q (prependHorizontal w)
          ((1 : Fin ((p + 1) + (q + 1) + 1)).succAbove i)).2
      rw [hsucc]
      simp [prependHorizontal, prependVertical, hi]

/-- The two adjacent-square prefixes have opposite staircase orientations.
Source: Eilenberg--Mac Lane (1953), §5 equation (5.7), p.65, applied twice;
this is the local sign check in Hatcher §3.B, p.278.

Proof: A horizontal prefix creates no inversion. A vertical prefix creates one
inversion per horizontal step. Thus the two prefix orders add respectively p
and p+1 inversions to the tail count, giving opposite powers of minus one. -/
theorem adjacent_prefix_orientation_neg {p q : ℕ} {w : GridPath p q}
    (hw : w ∈ staircases p q) :
    orientation (prependHorizontal (prependVertical w)) =
      - orientation (prependVertical (prependHorizontal w)) := by
  have hwH : prependHorizontal w ∈ staircases (p + 1) q :=
    prependHorizontal_mem w hw
  have h0 : w 0 = (0, 0) := (Finset.mem_filter.mp hw).2.1
  have hV : (prependVertical w) 0 = (0, 0) := by simp [prependVertical]
  rw [orientation_prependHorizontal (prependVertical w) hV,
    orientation_prependVertical w hw,
    orientation_prependVertical (prependHorizontal w) hwH,
    orientation_prependHorizontal w h0]
  rw [pow_succ]
  ring

end HolomorphicAnosov.SignedSingularCrossProduct
