import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition

/-! Hatcher, Algebraic Topology, naturality of pair pullbacks p.201 and the
characteristic-map excision square of Proposition 3.17 p.217. -/

open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- The canonical relative pullback commutes with restriction to matching
subspaces. Source: Hatcher p.201 and the excision square p.217.
Both composites are the kernel map of the same ambient restriction square.
Cancel the kernel inclusion and use singular-cochain functor composition.
Applying homology, the intermediate quotient identifications cancel, giving
the equality for the literal relative kernel/image cohomology quotients. -/
theorem relativeCohomologyPullback_restriction_square
    (R : Type u) [CommRing R] {X Y : TopCat.{u}}
    (A U : Set X) (B V : Set Y) (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hUV : Set.MapsTo f U V) (n : ℕ) :
    relativeCohomologyPullback R f hf n ≫
        relativeCohomologyPullback R (X := TopCat.of U) (Y := X)
          (A := {x | x.1 ∈ A}) (B := A) (subspaceInclusion X U)
          (fun _ hx ↦ hx) n =
      relativeCohomologyPullback R (X := TopCat.of V) (Y := Y)
          (A := {y | y.1 ∈ B}) (B := B) (subspaceInclusion Y V)
          (fun _ hy ↦ hy) n ≫
        relativeCohomologyPullback R (X := TopCat.of U) (Y := TopCat.of V)
          (A := {x | x.1 ∈ A}) (B := {y | y.1 ∈ B})
          (pairSubspaceMap f hUV) (fun _ hx ↦ hf hx) n := by
  have hs : relativePullback R f hf ≫
        relativePullback R (X := TopCat.of U) (Y := X)
          (A := {x | x.1 ∈ A}) (B := A) (subspaceInclusion X U)
          (fun _ hx ↦ hx) =
      relativePullback R (X := TopCat.of V) (Y := Y)
          (A := {y | y.1 ∈ B}) (B := B) (subspaceInclusion Y V)
          (fun _ hy ↦ hy) ≫
        relativePullback R (X := TopCat.of U) (Y := TopCat.of V)
          (A := {x | x.1 ∈ A}) (B := {y | y.1 ∈ B})
          (pairSubspaceMap f hUV) (fun _ hx ↦ hf hx) := by
    apply (cancel_mono (kernel.ι (pullback R
      (subspaceInclusion (TopCat.of U) {x | x.1 ∈ A})))).mp
    dsimp only [relativePullback, kernel.map]
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    change kernel.ι (pullback R (subspaceInclusion Y B)) ≫
        (cochainFunctor R).map f.op ≫ (cochainFunctor R).map (subspaceInclusion X U).op =
      kernel.ι (pullback R (subspaceInclusion Y B)) ≫
        (cochainFunctor R).map (subspaceInclusion Y V).op ≫
          (cochainFunctor R).map (pairSubspaceMap f hUV).op
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hh := congrArg (fun t ↦ quotientMap R t n) hs
  simpa only [relativeCohomologyPullback, quotientMap, HomologicalComplex.homologyMap_comp,
    Category.assoc, Iso.hom_inv_id_assoc] using hh

end HolomorphicAnosov.SingularCochain
