import HolomorphicAnosov.Topology.ZeroAugmentHomologyIso
import HolomorphicAnosov.Topology.ShortComplexHomologyMapMiddle

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `algebra.zero_augment_homology_iso_naturality`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- The augmentation grading comparison commutes with chain maps whose
successor components are the original chain components. The homology maps
are induced by short-complex maps with identical middle components.

Source: Hatcher p.118, naturality of the augmented pair sequence. Express each
comparison as the homology map of the short-complex comparison conjugated by
the canonical reindexing isomorphisms. Homology-map functoriality expresses each
side as one composite short-complex map. Their middle components are F.f(n+1)
and f.f(n), respectively, with identity factors. The hypothesis identifies
them, and middle-component congruence identifies their homology maps. -/
theorem zeroAugmentHomologyIso_naturality
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L)
    (F : ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp) ⟶
      ChainComplex.augment L (0 : L.X 0 ⟶ 0) (by simp)) (n : ℕ)
    (hF : F.f (n + 1) = f.f n) :
    HomologicalComplex.homologyMap F (n + 1) ≫ (zeroAugmentHomologyIso L n).hom =
      (zeroAugmentHomologyIso K n).hom ≫ HomologicalComplex.homologyMap f n := by
  let KA := ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)
  let LA := ChainComplex.augment L (0 : L.X 0 ⟶ 0) (by simp)
  let φK : KA.sc (n + 1) ⟶ K.sc n :=
    (KA.isoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom ≫
      zeroAugmentShortComplexMap K n ≫
      (K.isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).inv
  let φL : LA.sc (n + 1) ⟶ L.sc n :=
    (LA.isoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom ≫
      zeroAugmentShortComplexMap L n ≫
      (L.isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).inv
  have hK : (zeroAugmentHomologyIso K n).hom = ShortComplex.homologyMap φK := by
    simp only [φK, ShortComplex.homologyMap_comp]
    rfl
  have hL : (zeroAugmentHomologyIso L n).hom = ShortComplex.homologyMap φL := by
    simp only [φL, ShortComplex.homologyMap_comp]
    rfl
  rw [hK, hL]
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map F) ≫
      ShortComplex.homologyMap φL =
    ShortComplex.homologyMap φK ≫ ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  have hmiddle :
      (((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map F) ≫ φL).τ₂ =
        (φK ≫ ((HomologicalComplex.shortComplexFunctor _ _ n).map f)).τ₂ := by
    cases n with
    | zero =>
      change F.f 1 ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) = (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ f.f 0
      simpa only [Category.id_comp, Category.comp_id] using hF
    | succ n =>
      change F.f (n + 2) ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ f.f (n + 1)
      simpa only [Category.id_comp, Category.comp_id] using hF
  exact HolomorphicAnosov.shortComplex_homologyMap_eq_of_middle_eq _ _ hmiddle

end HolomorphicAnosov.GoodPair

