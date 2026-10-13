import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import HolomorphicAnosov.Topology.Cubical.FiniteBoxUnionDeformation

/-! Open strong deformation neighborhoods of cubical skeleta.
Source: Hatcher, Algebraic Topology, Appendix A.5 p.523, with the explicit finite
coordinate-box construction in `FiniteBoxUnionDeformation`. -/

namespace HolomorphicAnosov.Cubical

/-- The skeleton and each contained subcomplex have nested open strong deformation
neighborhoods in their original Euclidean ambient space. Both carriers are finite
unions of their literal closed coordinate cells. First apply the finite-box
neighborhood construction to the skeleton inside the entire ambient space, obtaining
U. Then apply it to the subcomplex inside the open set U intersect V, obtaining W.
The two strong deformation retractions fix the carriers throughout and remain in
their respective neighborhoods. The empty subcomplex gives W empty.
Source: Hatcher, Appendix A.5 p.523. -/
theorem cubical_skeleton_deformation_neighborhoods
    (N : ℕ) (_hN : 1 ≤ N) (K : FiniteRectilinearSubdivision N)
    (q : ℕ) (_hq : q ≤ N) (D : CubicalSubcomplex K)
    (hD : D.carrier ⊆ K.skeleton q) :
    let S := K.skeleton q
    let retracts := fun (A U : Set (Fin N → ℝ)) ↦
      ∃ hAU : A ⊆ U, ∃ r : C(U, A),
        (∀ a : A, r ⟨a.val, hAU a.property⟩ = a) ∧
          Nonempty ((ContinuousMap.id U).HomotopyRel
            ((ContinuousMap.inclusion hAU).comp r) {x : U | x.val ∈ A})
    ∀ V : Set (Fin N → ℝ), IsOpen V → D.carrier ⊆ V →
      ∃ U W : Set (Fin N → ℝ), IsOpen U ∧ IsOpen W ∧
        S ⊆ U ∧ D.carrier ⊆ W ∧ W ⊆ U ∩ V ∧ retracts S U ∧ retracts D.carrier W ∧
        (D.carrier = ∅ → W = ∅) := by
  classical
  clear _hN _hq
  dsimp only
  intro V hV hDV
  let BS : Finset (ClosedCoordinateCell N) :=
    (K.finite_cells.subset (show {c | c ∈ K.cells ∧ c.dimension ≤ q} ⊆ K.cells from fun _ h ↦ h.1)).toFinset
  let BD : Finset (ClosedCoordinateCell N) := (K.finite_cells.subset D.subset_cells).toFinset
  have hS : (⋃ c ∈ BS, c.carrier) = K.skeleton q := by
    ext x
    simp only [BS,Set.Finite.mem_toFinset,Set.mem_ofPred_eq,
      FiniteRectilinearSubdivision.skeleton,Set.mem_iUnion]
    aesop
  have hDC : (⋃ c ∈ BD, c.carrier) = D.carrier := by
    simp only [BD,Set.Finite.mem_toFinset,CubicalSubcomplex.carrier]
  have hs := finiteBoxUnion_deformationNeighborhood BS Set.univ isOpen_univ (Set.subset_univ _)
  dsimp only at hs
  rw [hS] at hs
  obtain ⟨U,hU,hUuniv,hSU,rS,hrS,hHS,hUS⟩ := hs
  have hDint : (⋃ c ∈ BD, c.carrier) ⊆ U ∩ V := by
    rw [hDC]
    exact fun x hx ↦ ⟨hSU (hD hx),hDV hx⟩
  have hd := finiteBoxUnion_deformationNeighborhood BD (U ∩ V) (hU.inter hV) hDint
  dsimp only at hd
  rw [hDC] at hd
  obtain ⟨W,hW,hWUV,hDW,rD,hrD,hHD,hWD⟩ := hd
  exact ⟨U,W,hU,hW,hSU,hDW,hWUV,⟨hSU,rS,hrS,hHS⟩,⟨hDW,rD,hrD,hHD⟩,hWD⟩

end HolomorphicAnosov.Cubical
