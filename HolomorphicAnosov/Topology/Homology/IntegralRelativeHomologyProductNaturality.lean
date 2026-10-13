import HolomorphicAnosov.Topology.Homology.IntegralRelativeChainProductNaturality

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Every integral relative homology product represented by the prescribed chain product is natural in maps of pairs. -/
theorem integralRelativeHomologyProduct_naturality_of_representatives
    (P : ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ),
      RelativeHomology X A p →ₗ[ℤ] RelativeHomology Y B q →ₗ[ℤ]
        RelativeHomology (TopCat.of (X × Y)) (ProductSubspace A B) (p+q))
    (hP : ∀ (X Y : TopCat.{u}) (A : Set X) (B : Set Y) (p q : ℕ)
      (ca : (RelativeComplex X A).cycles p) (cb : (RelativeComplex Y B).cycles q),
      ∃ cc : (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).cycles (p+q),
        (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p+q) cc =
          integralRelativeChainProduct X Y A B p q
            ((RelativeComplex X A).iCycles p ca) ((RelativeComplex Y B).iCycles q cb) ∧
        P X Y A B p q ((RelativeComplex X A).homologyπ p ca) ((RelativeComplex Y B).homologyπ q cb) =
          (RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).homologyπ (p+q) cc)
    (X Y X' Y' : TopCat.{u}) (f : X ⟶ X') (g : Y ⟶ Y')
    (A : Set X) (B : Set Y) (A' : Set X') (B' : Set Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') (p q : ℕ)
    (a : RelativeHomology X A p) (b : RelativeHomology Y B q) :
    relativeMap (productMap f g) (ProductSubspace A B) (ProductSubspace A' B')
      (relativeProductSubspace_map f g A B A' B' hf hg) (p+q)
      (P X Y A B p q a b) =
    P X' Y' A' B' p q (relativeMap f A A' hf p a) (relativeMap g B B' hg q b) := by
  obtain ⟨ca, rfl⟩ := (ModuleCat.epi_iff_surjective ((RelativeComplex X A).homologyπ p)).mp inferInstance a
  obtain ⟨cb, rfl⟩ := (ModuleCat.epi_iff_surjective ((RelativeComplex Y B).homologyπ q)).mp inferInstance b
  let F := SSetPair.chainComplexMap (singularSubspacePairMap f A A' hf) singularIntegralCoefficients
  let G := SSetPair.chainComplexMap (singularSubspacePairMap g B B' hg) singularIntegralCoefficients
  let H := SSetPair.chainComplexMap (singularSubspacePairMap (productMap f g)
    (ProductSubspace A B) (ProductSubspace A' B')
    (relativeProductSubspace_map f g A B A' B' hf hg)) singularIntegralCoefficients
  have hfclass := congrArg (fun k => k ca) (HomologicalComplex.homologyπ_naturality F p)
  have hgclass := congrArg (fun k => k cb) (HomologicalComplex.homologyπ_naturality G q)
  change relativeMap f A A' hf p ((RelativeComplex X A).homologyπ p ca) = (RelativeComplex X' A').homologyπ p (HomologicalComplex.cyclesMap F p ca) at hfclass
  change relativeMap g B B' hg q ((RelativeComplex Y B).homologyπ q cb) = (RelativeComplex Y' B').homologyπ q (HomologicalComplex.cyclesMap G q cb) at hgclass
  rw [hfclass, hgclass]
  obtain ⟨cc, hcc, hcclass⟩ := hP X Y A B p q ca cb
  obtain ⟨cc', hcc', hcclass'⟩ := hP X' Y' A' B' p q
    (HomologicalComplex.cyclesMap F p ca) (HomologicalComplex.cyclesMap G q cb)
  have hcycle : HomologicalComplex.cyclesMap H (p+q) cc = cc' := by
    apply (ModuleCat.mono_iff_injective
      ((RelativeComplex (TopCat.of (X' × Y')) (ProductSubspace A' B')).iCycles (p+q))).mp inferInstance
    have hh := congrArg (fun k => k cc) (HomologicalComplex.cyclesMap_i H (p+q))
    change (RelativeComplex (TopCat.of (X' × Y')) (ProductSubspace A' B')).iCycles (p+q)
      (HomologicalComplex.cyclesMap H (p+q) cc) =
      H.f (p+q) ((RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)).iCycles (p+q) cc) at hh
    rw [hh, hcc, hcc']
    have hfa := congrArg (fun k => k ca) (HomologicalComplex.cyclesMap_i F p)
    have hgb := congrArg (fun k => k cb) (HomologicalComplex.cyclesMap_i G q)
    change (RelativeComplex X' A').iCycles p (HomologicalComplex.cyclesMap F p ca) =
      F.f p ((RelativeComplex X A).iCycles p ca) at hfa
    change (RelativeComplex Y' B').iCycles q (HomologicalComplex.cyclesMap G q cb) =
      G.f q ((RelativeComplex Y B).iCycles q cb) at hgb
    rw [hfa, hgb]
    exact integralRelativeChainProduct_naturality X Y X' Y' f g A B A' B' hf hg p q
      ((RelativeComplex X A).iCycles p ca) ((RelativeComplex Y B).iCycles q cb)
  rw [hcclass, hcclass']
  exact (congrArg (fun k => k cc) (HomologicalComplex.homologyπ_naturality H (p+q))).trans
    (congrArg ((RelativeComplex (TopCat.of (X' × Y')) (ProductSubspace A' B')).homologyπ (p+q)) hcycle)

end HolomorphicAnosov.Topology
