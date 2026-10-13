import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupNaturality

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher, Algebraic Topology, Proposition 3.10 p210 gives binary cup-product naturality. The induction on a reindexed dependent list, including length and pullback transports, is agent-written to supply the iterated pullback step omitted from the coordinate-basis proof.

DAG node: `topo.torus_public_monomial_pullback_g17`. -/
theorem monomial_pullback
    {ι κ : Type} {X Y : TopCat} (f : X ⟶ Y)
    (cupX : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (cupY : ∀ p q : ℕ, SingularCochain.cohomology ℚ Y p →ₗ[ℚ]
      SingularCochain.cohomology ℚ Y q →ₗ[ℚ]
        SingularCochain.cohomology ℚ Y (p + q))
    (hrepX : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cupX p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hrepY : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) q),
      ∃ hc : SingularCochain.cupCochain ℚ Y b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ Y) (p + q),
        cupY p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ Y) (p + q)
            ⟨SingularCochain.cupCochain ℚ Y b.val c.val, hc⟩)
    (oneX : SingularCochain.cohomology ℚ X 0)
    (oneY : SingularCochain.cohomology ℚ Y 0)
    (alphaX : κ → SingularCochain.cohomology ℚ X 1)
    (alphaY : ι → SingularCochain.cohomology ℚ Y 1) (u : ι → κ)
    (hunit : (SingularCochain.cohomologyPullback ℚ f 0).hom oneY = oneX)
    (hgen : ∀ i, (SingularCochain.cohomologyPullback ℚ f 1).hom (alphaY i) =
      alphaX (u i)) :
    let mY : ∀ l : List ι, SingularCochain.cohomology ℚ Y l.length :=
      fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ Y l.length)
        oneY (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ Y d : Type))
          (Nat.add_comm 1 l.length)) (cupY 1 l.length (alphaY i) v)) l
    let mX : ∀ l : List κ, SingularCochain.cohomology ℚ X l.length :=
      fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length)
        oneX (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          (Nat.add_comm 1 l.length)) (cupX 1 l.length (alphaX i) v)) l
    ∀ l : List ι,
      HEq ((SingularCochain.cohomologyPullback ℚ f l.length).hom (mY l))
        (mX (l.map u)) := by
  let mY : ∀ l : List ι, SingularCochain.cohomology ℚ Y l.length :=
    fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ Y l.length)
      oneY (fun i l v ↦ cast (congrArg
        (fun d ↦ (SingularCochain.cohomology ℚ Y d : Type))
        (Nat.add_comm 1 l.length)) (cupY 1 l.length (alphaY i) v)) l
  let mX : ∀ l : List κ, SingularCochain.cohomology ℚ X l.length :=
    fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length)
      oneX (fun i l v ↦ cast (congrArg
        (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
        (Nat.add_comm 1 l.length)) (cupX 1 l.length (alphaX i) v)) l
  change ∀ l : List ι,
    HEq ((SingularCochain.cohomologyPullback ℚ f l.length).hom (mY l))
      (mX (l.map u))
  intro l
  induction l with
  | nil => exact heq_of_eq hunit
  | cons i l ihl =>
    change HEq
      ((SingularCochain.cohomologyPullback ℚ f (l.length + 1)).hom
        (cast (congrArg (fun d ↦ (SingularCochain.cohomology ℚ Y d : Type))
          (Nat.add_comm 1 l.length)) (cupY 1 l.length (alphaY i) (mY l))))
      (cast (congrArg (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
        (Nat.add_comm 1 (l.map u).length))
        (cupX 1 (l.map u).length (alphaX (u i))
          (mX (l.map u))))
    refine (((by
      intro A B f p q h a
      cases h
      rfl) : ∀ {A B : TopCat} (f : A ⟶ B) {p q : ℕ} (h : p = q)
        (a : SingularCochain.cohomology ℚ B p),
        HEq ((SingularCochain.cohomologyPullback ℚ f q).hom
          (cast (congrArg (fun d ↦
            (SingularCochain.cohomology ℚ B d : Type)) h) a))
          (cast (congrArg (fun d ↦
            (SingularCochain.cohomology ℚ A d : Type)) h)
            ((SingularCochain.cohomologyPullback ℚ f p).hom a))) f
        (Nat.add_comm 1 l.length) _).trans ((cast_heq _ _).trans ?_)
    have hg := hgen i
    have hnat := specified_cup_naturality f cupX cupY hrepX hrepY
      1 l.length (alphaY i) (mY l)
    rw [hg] at hnat
    refine (heq_of_eq hnat).trans ?_
    let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
    let F : Sigma H → Sigma H := fun p ↦
      ⟨1 + p.1, cupX 1 p.1 (alphaX (u i)) p.2⟩
    have hs : (⟨l.length,
        (SingularCochain.cohomologyPullback ℚ f l.length).hom (mY l)⟩ : Sigma H) =
        ⟨(l.map u).length, mX (l.map u)⟩ :=
      Sigma.mk.inj_iff.mpr ⟨(List.length_map _).symm, ihl⟩
    exact (Sigma.mk.inj_iff.mp (congrArg F hs)).2.trans (cast_heq _ _).symm


end HolomorphicAnosov.TorusRationalCupBasisKronecker
