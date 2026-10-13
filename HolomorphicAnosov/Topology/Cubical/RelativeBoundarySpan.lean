import HolomorphicAnosov.Topology.Cubical.SkeletonStepHomology
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Homology.Additive

open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov.Cubical

/-- A finite chain decomposition into maps from cell pairs generates relative homology. -/
theorem relative_homology_span_of_chain_decomposition
    {ι : Type} [Fintype ι] (P : SSetPair) (C : ι → SSetPair)
    (f : ∀ i, C i ⟶ P) (R : ModuleCat ℚ) (n : ℕ)
    (p : ∀ i, P.chainComplex R ⟶ (C i).chainComplex R)
    (h : ∑ i, p i ≫ SSetPair.chainComplexMap (f i) R = 𝟙 _) :
    Submodule.span ℚ (⋃ i, Set.range (SSetPair.homologyMap (f i) R n)) = ⊤ := by
  classical
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have he : ∑ i, F.map (p i) ≫ SSetPair.homologyMap (f i) R n = 𝟙 _ := by
    have he := congrArg F.map h
    simp only [Functor.map_sum, Functor.map_comp, F.map_id] at he
    exact he
  apply top_unique
  intro x _
  have hx := congrArg (fun g ↦ g x) he
  change (∑ i, F.map (p i) ≫ SSetPair.homologyMap (f i) R n).hom x = x at hx
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  rw [← hx]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, _, rfl⟩)

/-- Surjective relative homology maps carry spanning cell families to spanning families. -/
theorem relative_homology_span_map
    {ι : Type} (P Q : SSetPair) (C : ι → SSetPair)
    (f : ∀ i, C i ⟶ P) (g : P ⟶ Q) (R : ModuleCat ℚ) (n : ℕ)
    [Epi (SSetPair.homologyMap g R n)]
    (hspan : Submodule.span ℚ (⋃ i, Set.range (SSetPair.homologyMap (f i) R n)) = ⊤) :
    Submodule.span ℚ (⋃ i, Set.range (SSetPair.homologyMap (f i ≫ g) R n)) = ⊤ := by
  let W : Submodule ℚ ↥(Q.homology R n) :=
    Submodule.span ℚ (⋃ i, Set.range (SSetPair.homologyMap (f i ≫ g) R n))
  have hle : Submodule.span ℚ (⋃ i, Set.range (SSetPair.homologyMap (f i) R n)) ≤
      W.comap (SSetPair.homologyMap g R n).hom := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
    change SSetPair.homologyMap g R n (SSetPair.homologyMap (f i) R n y) ∈ W
    have he := congrArg (fun h ↦ h y) (SSetPair.homologyMap_comp (f i) g R n)
    change SSetPair.homologyMap (f i ≫ g) R n y =
      SSetPair.homologyMap g R n (SSetPair.homologyMap (f i) R n y) at he
    rw [← he]
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, y, rfl⟩)
  rw [hspan] at hle
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (SSetPair.homologyMap g R n)).mp inferInstance x
  exact hle Submodule.mem_top

/-- Hatcher, Algebraic Topology, Theorem 2.16 pp.116–118 and the cellular
boundary formula pp.140–141. If relative homology is spanned by classes from
cell pairs and the ambient absolute homology vanishes, the included homology
of the cell boundaries spans the homology of the subspace. Exactness makes the
connecting map onto. For each cell-pair class, naturality identifies its image
under this connecting map with the inclusion of its own boundary class.
Linearity extends this containment from the spanning family to every relative
class, and surjectivity supplies every class of the subspace. -/
theorem relative_boundary_span_of_relative_generators
    {ι : Type} (P : SSetPair) (C : ι → SSetPair)
    (f : ∀ i, C i ⟶ P) (R : ModuleCat ℚ) (q : ℕ)
    (hz : IsZero (P.right.homology R q))
    (hspan : Submodule.span ℚ
      (⋃ i, Set.range (SSetPair.homologyMap (f i) R (q + 1))) = ⊤) :
    Submodule.span ℚ (⋃ i, Set.range (SSet.homologyMap (f i).left R q)) = ⊤ := by
  classical
  let W : Submodule ℚ ↥(P.left.homology R q) :=
    Submodule.span ℚ (⋃ i, Set.range (SSet.homologyMap (f i).left R q))
  have hnat (i : ι) :
      (C i).homologyδ R (q + 1) q ≫ SSet.homologyMap (f i).left R q =
      SSetPair.homologyMap (f i) R (q + 1) ≫ P.homologyδ R (q + 1) q := by
    let φ : (C i).chainComplexShortComplex R ⟶ P.chainComplexShortComplex R := {
      τ₁ := ((SSetPair.chainComplexFunctorLeft (ModuleCat ℚ)).obj R).map (f i)
      τ₂ := ((SSetPair.chainComplexFunctorRight (ModuleCat ℚ)).obj R).map (f i)
      τ₃ := SSetPair.chainComplexMap (f i) R
      comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight (ModuleCat ℚ)).app R).naturality (f i)
      comm₂₃ := ((SSetPair.chainComplexFunctorπ (ModuleCat ℚ)).app R).naturality (f i) }
    exact HomologicalComplex.HomologySequence.δ_naturality φ
      ((C i).shortExact_chainComplexShortComplex R)
      (P.shortExact_chainComplexShortComplex R) (q + 1) q rfl
  have hmem : ∀ x : ↥(P.homology R (q + 1)), P.homologyδ R (q + 1) q rfl x ∈ W := by
    have hle : Submodule.span ℚ
        (⋃ i, Set.range (SSetPair.homologyMap (f i) R (q + 1))) ≤
        W.comap (P.homologyδ R (q + 1) q).hom := by
      apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
      change P.homologyδ R (q + 1) q rfl (SSetPair.homologyMap (f i) R (q + 1) y) ∈ W
      have he := congrArg (fun g ↦ g y) (hnat i)
      change SSet.homologyMap (f i).left R q ((C i).homologyδ R (q + 1) q rfl y) =
        P.homologyδ R (q + 1) q rfl (SSetPair.homologyMap (f i) R (q + 1) y) at he
      rw [← he]
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, _, rfl⟩)
    rw [hspan] at hle
    intro x
    exact hle (Submodule.mem_top)
  have hepi : Epi (P.homologyδ R (q + 1) q) :=
    (P.homology_exact₁ R (q + 1) q).epi_f (hz.eq_of_tgt _ _)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp hepi x
  exact hmem y

end HolomorphicAnosov.Cubical
open Set CategoryTheory CategoryTheory.Limits _root_.Topology
namespace HolomorphicAnosov.CharacteristicCellComparison
open HolomorphicAnosov.Cubical

/-- Characteristic boundary maps generate the lower-skeleton homology whenever
the next skeleton has zero homology. -/
theorem characteristic_boundary_homology_span
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m q : ℕ) (hm : m = q + 1)
    (hz : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (Skeleton X m)))) :
    Submodule.span ℚ (⋃ i : RelCWComplex.cell (univ : Set X) m,
      Set.range (SSet.homologyMap
        (singularSubspacePairMap (TopCat.ofHom (characteristicCell X m i))
          (cellBoundary m) (lowerSkeleton X m) (characteristicCell_mapsTo X m i)).left
        (ModuleCat.of ℚ ℚ) q)) = ⊤ := by
  subst m
  let R := ModuleCat.of ℚ ℚ
  let I := RelCWComplex.cell (univ : Set X) (q + 1)
  let Y := TopCat.of (CellDisk.{0} (q + 1))
  let A : Set Y := cellBoundary (q + 1)
  let : Finite I := RelCWComplex.FiniteType.finite_cell (q + 1)
  let := Fintype.ofFinite I
  let Φ : TopCat.of (Σ _i : I, Y) ⟶ TopCat.of (Skeleton X (q + 1)) := TopCat.ofHom
    ⟨fun z ↦ characteristicCell X (q + 1) z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell X (q + 1) i).continuous⟩
  let P := singularSubspacePair (TopCat.of (Skeleton X (q + 1))) (lowerSkeleton X (q + 1))
  let f := singularSubspacePairMap Φ {z | z.2 ∈ A} (lowerSkeleton X (q + 1))
    (fun z hz ↦ characteristicCell_mapsTo X (q + 1) z.1 hz)
  let e := sigmaSubspacePairIso (ι := I) Y A
  let g := e.hom ≫ f
  have : IsIso (SSetPair.homologyMap f R (q + 1)) :=
    characteristic_relative_homology_isIso X (q + 1) R (q + 1)
  have : IsIso (SSetPair.homologyMap g R (q + 1)) := by
    dsimp only [g]
    rw [SSetPair.homologyMap_comp]
    infer_instance
  have hs := relative_homology_span_of_chain_decomposition
    (sigmaSubspacePair (ι := I) Y A) (fun _ : I ↦ singularSubspacePair Y A)
    (sigmaPairInclusion Y A) R (q + 1) (sigmaRelativeProjection Y A R)
    (sigmaRelativeProjection_sum Y A R)
  have hsg := relative_homology_span_map _ P (fun _ : I ↦ singularSubspacePair Y A)
    (sigmaPairInclusion Y A) g R (q + 1) hs
  have hb := relative_boundary_span_of_relative_generators P
    (fun _ : I ↦ singularSubspacePair Y A) (fun i ↦ sigmaPairInclusion Y A i ≫ g)
    R q hz hsg
  have he (i : I) : sigmaPairInclusion Y A i ≫ g =
      singularSubspacePairMap (TopCat.ofHom (characteristicCell X (q + 1) i))
        (cellBoundary (q + 1)) (lowerSkeleton X (q + 1))
        (characteristicCell_mapsTo X (q + 1) i) := by
    ext n z <;> rfl
  simp_rw [he] at hb
  exact hb

end HolomorphicAnosov.CharacteristicCellComparison
