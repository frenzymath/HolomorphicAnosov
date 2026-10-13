import HolomorphicAnosov.Topology.Homology.CanonicalNonzeroLocalFamilyCompatible
import HolomorphicAnosov.Topology.Homology.HatcherCompactSupportSectionMod2

/-!
# Mod-two top homology of a closed connected smooth manifold

Source: Hatcher, *Algebraic Topology*, Theorem 3.26 and Lemma 3.27,
printed pp.236–238, with the canonical mod-two orientation on pp.234–235.
The DAG node is `topo.closed_manifold_mod2_top_homology`.
-/

noncomputable section

namespace HolomorphicAnosov

universe u

open scoped ContDiff
open Set CategoryTheory

open HatcherCompactSupport
open scoped Simplicial

/--
A nonempty connected closed smooth real `n`-manifold has nontrivial singular
homology with coefficients `ZMod 2` in degree `n`, and has subsingleton
singular homology in every degree strictly above `n`.

The original topology and full Euclidean atlas are fixed. Compactness,
Hausdorffness, second countability, connectedness and nonemptiness are explicit;
`IsManifold` of order infinity on the whole Euclidean model expresses a smooth
manifold without boundary. No orientation, positive dimension or finite
triangulation hypothesis is added.

The homology object is Mathlib's unnormalized singular simplicial homology:
`TopCat.toSSet` has continuous maps from the standard topological simplices,
and `SSet.chainComplex` is their coproduct with the alternating face boundary.
The coefficient object is the regular `ZMod 2` module, universe-lifted only
so that it and the simplex-indexed coproducts lie in the universe of `M`.
`ULift.moduleEquiv` identifies these coefficients with literal `ZMod 2`.
The conclusion concerns the actual carrier of the resulting `ModuleCat`
homology object, not a proxy invariant or a normalized-chain substitute.

Natural-language proof (Hatcher Theorem 3.26 and Lemma 3.27, pp.236–238):
Forget smoothness and use the original boundaryless topological manifold.
The local calculation identifies `H_n(M,M\{x};ZMod 2)` with `ZMod 2` at
every point `x`. Its unique nonzero element is the local class `mu_x`.
In a coordinate neighborhood, choose a closed coordinate ball `D` with open
interior `W`. The unique nonzero class supported on `D` restricts first to
`H_n(M,M\W;ZMod 2)` and then to `mu_y` for every `y` in `W`.
Thus the family of local classes is locally compatible. This is the canonical
mod-two orientation; it is obtained from the local calculation, not assumed.

Apply the compact-support section part of Lemma 3.27 to the compact support
`A=M`. It gives a class `mu_M` in `H_n(M,M\M;ZMod 2)=H_n(M;ZMod 2)`
restricting to `mu_x` at every point. Nonemptiness supplies a point `x`.
If `mu_M` were zero, its restriction would be zero, contradicting the chosen
nonzero local class. Zero and `mu_M` are therefore distinct, which proves
nontriviality of the top homology carrier. The higher-degree vanishing part
of the same lemma at `A=M` gives a zero homology object for every `q>n`.
Its underlying module is subsingleton, since every element equals zero.

If `n=0`, the full zero-dimensional charts are singletons, hence the manifold
is discrete. Connectedness and nonemptiness give one point. Its degree-zero
homology is `ZMod 2` and its positive-degree homology vanishes, consistent
with the same local and compact-support calculation. No exceptional positive
rank condition is used. Connectedness is retained exactly as in the node,
even though the nontriviality and vanishing argument works componentwise.

Stage2 only: the named theorem proof is intentionally admitted; its local
homology and compact-support prerequisites retain their own lower obligations.
-/
theorem closed_manifold_mod2_top_homology
    (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [Nonempty M] [ConnectedSpace M] :
    let X := TopCat.toSSet.obj (TopCat.of M)
    let R : ModuleCat.{u} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
    Nontrivial (X.homology (C := ModuleCat.{u} (ZMod 2)) R n : Type u) ∧
      ∀ q : ℕ, n < q → Subsingleton (X.homology (C := ModuleCat.{u} (ZMod 2)) R q : Type u) := by
  let X := TopCat.toSSet.obj (TopCat.of M)
  let R : ModuleCat.{u} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let P := Topology.Homology.singularSubspacePair M (Set.univ : Set M)ᶜ
  have hleft : ¬ P.left.Nonempty := by
    dsimp [P, Topology.Homology.singularSubspacePair]
    intro h
    change Nonempty ((TopCat.toSSet.obj
      (TopCat.of {x : M // x ∈ (Set.univ : Set M)ᶜ})) _⦋0⦌) at h
    obtain ⟨z⟩ := h
    exact (TopCat.toSSetObj₀Equiv z).property (by simp)
  let : P.left.HasDimensionLT 0 := by
    rw [← SSet.notNonempty_iff_hasDimensionLT_zero]
    exact hleft
  have hsec := HatcherCompactSupport.hatcher_compact_support_section_mod2 n M
    Set.univ isCompact_univ (canonicalNonzeroLocalFamily (n := n))
    canonicalNonzeroLocalFamily_locallyCompatible
  obtain ⟨a, ha, _⟩ := hsec.1
  have ha0 : a ≠ 0 := by
    intro hzero
    let x : M := Classical.choice inferInstance
    have h := ha ⟨x, Set.mem_univ x⟩
    rw [hzero, map_zero] at h
    exact canonicalNonzeroLocalFamily_ne_zero x h.symm
  have hrel : Nontrivial (P.homology (C := ModuleCat (ZMod 2)) R n : Type u) :=
    ⟨⟨a, 0, ha0⟩⟩
  refine ⟨?_, ?_⟩
  · have : IsIso (P.homologyπ R n) := inferInstance
    let E := Iso.toLinearEquiv (asIso (P.homologyπ R n))
    exact E.toEquiv.surjective.nontrivial
  · intro q hq
    let : Subsingleton (P.homology (C := ModuleCat (ZMod 2)) R q : Type u) :=
      hsec.2.2 q hq
    have : IsIso (P.homologyπ R q) := inferInstance
    exact (Iso.toLinearEquiv (asIso (P.homologyπ R q))).injective.subsingleton

end HolomorphicAnosov

