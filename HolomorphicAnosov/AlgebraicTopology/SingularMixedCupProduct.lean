import HolomorphicAnosov.AlgebraicTopology.SingularMixedCupCochain
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductCocycles
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductLeibniz
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCochainDegreeKernel
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductAssociativity
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductUnit
import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.Topology.SingularConstantOneCocycleG10
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Mixed singular cup products on cohomology

Source: Hatcher, Algebraic Topology, Lemma 3.6 and quotient argument pp.206–207,
ordinary/relative products p.209, naturality Proposition 3.10 p.210.
DAG node: `topo.singular_mixed_cup_product_g5`.

The cochain product is the existing bilinear relative lift. Differential commutation
and injectivity of the inclusion transfer Leibniz to it. Products with a boundary
are boundaries (including zero input degree), so the two quotient universal
properties give the bilinear product. Representative reduction transfers
associativity, the constant-one unit, and pullback naturality to the quotient.
The elementary kernel/image, equality-transport, and quotient adapters below
keep the native ModuleCat cohomology representation explicit.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain.MixedCup
variable (R : Type u) [CommRing R]

/-- The bilinear mixed cochain formula supplied by Hatcher p.209. -/
def tagged_cochain_cup (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :=
  Classical.choose (mixed_cup_cochain R X A i j p q)

theorem tagged_cochain_cup_inclusion (X : TopCat.{u}) (A : Set X)
    (i j : Bool) (p q : ℕ)
    (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q) :
    (cupInclusion R X A (i || j)).f (p+q) (tagged_cochain_cup R X A i j p q a b) =
      cupCochain R X ((cupInclusion R X A i).f p a) ((cupInclusion R X A j).f q b) :=
  Classical.choose_spec (mixed_cup_cochain R X A i j p q) a b

set_option backward.isDefEq.respectTransparency false in
theorem mem_cycles_iff_d_eq_zero (Q : CochainComplex (ModuleCat.{u} R) ℕ)
 (n : ℕ) (a : Q.X n) : a ∈ cycles R Q n ↔ Q.d n (n+1) a = 0 := by
 change Q.dFrom n a = 0 ↔ _
 rw [Q.dFrom_eq (j := n+1) (by simp [ComplexShape.up, ComplexShape.up'])]
 change (Q.xNextIso _).inv (Q.d n (n+1) a) = 0 ↔ _
 exact (ModuleCat.mono_iff_injective (Q.xNextIso _).inv).mp inferInstance |>.eq_iff' (map_zero _)

set_option backward.isDefEq.respectTransparency false in
theorem map_cocycle {Q Q' : CochainComplex (ModuleCat.{u} R) ℕ} (f : Q ⟶ Q')
 (n : ℕ) (a : cycles R Q n) : f.f n a.val ∈ cycles R Q' n := by
 rw [mem_cycles_iff_d_eq_zero]
 have h := congrArg (fun g => g a.val) (f.comm n (n+1))
 change Q'.d n (n+1) (f.f n a.val) = f.f (n+1) (Q.d n (n+1) a.val) at h
 rw [h, (mem_cycles_iff_d_eq_zero R _ _ _).mp a.property]
 exact map_zero _

set_option backward.isDefEq.respectTransparency false in
theorem inclusion_degree_injective (X : TopCat.{u}) (A : Set X) (i : Bool) (n : ℕ) :
 Function.Injective ((cupInclusion R X A i).f n) := by
 cases i
 · change Function.Injective (𝟙 ((complex R X).X n))
   exact Function.injective_id
 · apply (ModuleCat.mono_iff_injective _).mp
   change Mono ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n).map
     (kernel.ι (pullback R (subspaceInclusion X A))))
   infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem tagged_cup_is_cocycle (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
 (a : cycles R (cupComplex R X A i) p) (b : cycles R (cupComplex R X A j) q) :
 tagged_cochain_cup R X A i j p q a.val b.val ∈ cycles R (cupComplex R X A (i || j)) (p+q) := by
 rw [mem_cycles_iff_d_eq_zero]
 apply inclusion_degree_injective R X A (i || j) (p+q+1)
 have hc := cupCochain_mem_cycles R X
   ⟨(cupInclusion R X A i).f p a.val, map_cocycle R _ p a⟩
   ⟨(cupInclusion R X A j).f q b.val, map_cocycle R _ q b⟩
 have hcomm := congrArg (fun g => g (tagged_cochain_cup R X A i j p q a.val b.val))
   ((cupInclusion R X A (i || j)).comm (p+q) (p+q+1))
 change (complex R X).d (p+q) (p+q+1)
     ((cupInclusion R X A (i || j)).f (p+q) (tagged_cochain_cup R X A i j p q a.val b.val)) =
   (cupInclusion R X A (i || j)).f (p+q+1)
     ((cupComplex R X A (i || j)).d (p+q) (p+q+1) (tagged_cochain_cup R X A i j p q a.val b.val)) at hcomm
 rw [← hcomm, tagged_cochain_cup_inclusion, (mem_cycles_iff_d_eq_zero R _ _ _).mp hc]
 exact (map_zero _).symm

set_option backward.isDefEq.respectTransparency false in
theorem boundary_successor_iff (Q : CochainComplex (ModuleCat.{u} R) ℕ)
 (n : ℕ) (a : cycles R Q (n+1)) :
 a ∈ boundaries R Q (n+1) ↔ ∃ b : Q.X n, Q.d n (n+1) b = a.val := by
 constructor
 · rintro ⟨b,hb⟩
   refine ⟨(Q.xPrevIso (show (ComplexShape.up ℕ).Rel n (n+1) by simp [ComplexShape.up,ComplexShape.up'])).hom b, ?_⟩
   have h := congrArg Subtype.val hb
   change Q.dTo (n+1) b = a.val at h
   rw [Q.dTo_eq (i := n) (by simp [ComplexShape.up,ComplexShape.up'])] at h
   exact h
 · rintro ⟨b,hb⟩
   refine ⟨(Q.xPrevIso (show (ComplexShape.up ℕ).Rel n (n+1) by simp [ComplexShape.up,ComplexShape.up'])).inv b, ?_⟩
   apply Subtype.ext
   change Q.dTo (n+1) _ = a.val
   rw [Q.dTo_eq (i := n) (by simp [ComplexShape.up,ComplexShape.up'])]
   change Q.d n (n+1) ((Q.xPrevIso _).hom ((Q.xPrevIso _).inv b)) = a.val
   rw [Iso.inv_hom_id_apply]
   exact hb

set_option backward.isDefEq.respectTransparency false in
theorem boundary_zero_iff (Q : CochainComplex (ModuleCat.{u} R) ℕ)
 (a : cycles R Q 0) : a ∈ boundaries R Q 0 ↔ a = 0 := by
 constructor
 · rintro ⟨b,hb⟩
   apply Subtype.ext
   have h := congrArg Subtype.val hb
   change Q.dTo 0 b = a.val at h
   rw [Q.dTo_eq_zero (by simp [ComplexShape.up,ComplexShape.up',ComplexShape.prev])] at h
   exact h.symm
 · intro h
   subst a
   exact Submodule.zero_mem _

set_option backward.isDefEq.respectTransparency false in
/-- The relative lift satisfies Leibniz. Hatcher Lemma 3.6 pp.206–207 and p.209: apply the injective inclusion and the ordinary identity. -/
theorem tagged_cochain_leibniz (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
 (a : (cupComplex R X A i).X p) (b : (cupComplex R X A j).X q) :
 (cupComplex R X A (i || j)).d (p+q) (p+q+1) (tagged_cochain_cup R X A i j p q a b) =
 ((cupComplex R X A (i || j)).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
   (tagged_cochain_cup R X A i j (p+1) q ((cupComplex R X A i).d p (p+1) a) b) +
 (-1:R)^p • tagged_cochain_cup R X A i j p (q+1) a ((cupComplex R X A j).d q (q+1) b) := by
 apply inclusion_degree_injective R X A (i || j) (p+q+1)
 rw [map_add, map_smul]
 have hcomm := congrArg (fun g => g (tagged_cochain_cup R X A i j p q a b))
   ((cupInclusion R X A (i || j)).comm (p+q) (p+q+1))
 change (complex R X).d (p+q) (p+q+1) ((cupInclusion R X A (i || j)).f (p+q)
   (tagged_cochain_cup R X A i j p q a b)) =
   (cupInclusion R X A (i || j)).f (p+q+1) ((cupComplex R X A (i || j)).d (p+q) (p+q+1)
   (tagged_cochain_cup R X A i j p q a b)) at hcomm
 rw [← hcomm, tagged_cochain_cup_inclusion]
 have hcast := congrArg (fun g => g (tagged_cochain_cup R X A i j (p+1) q
   ((cupComplex R X A i).d p (p+1) a) b))
   (HomologicalComplex.XIsoOfEq_hom_naturality (cupInclusion R X A (i || j))
     (show (p+1)+q=p+q+1 by omega))
 change ((complex R X).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
   ((cupInclusion R X A (i || j)).f ((p+1)+q)
     (tagged_cochain_cup R X A i j (p+1) q ((cupComplex R X A i).d p (p+1) a) b)) =
   (cupInclusion R X A (i || j)).f (p+q+1)
   (((cupComplex R X A (i || j)).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
     (tagged_cochain_cup R X A i j (p+1) q ((cupComplex R X A i).d p (p+1) a) b)) at hcast
 erw [← hcast, tagged_cochain_cup_inclusion R X A i j (p+1) q,
   tagged_cochain_cup_inclusion R X A i j p (q+1) a
     ((cupComplex R X A j).d q (q+1) b)]
 have hi := congrArg (fun g => g a) ((cupInclusion R X A i).comm p (p+1))
 have hj := congrArg (fun g => g b) ((cupInclusion R X A j).comm q (q+1))
 change (complex R X).d p (p+1) ((cupInclusion R X A i).f p a) =
    (cupInclusion R X A i).f (p+1) ((cupComplex R X A i).d p (p+1) a) at hi
 change (complex R X).d q (q+1) ((cupInclusion R X A j).f q b) =
    (cupInclusion R X A j).f (q+1) ((cupComplex R X A j).d q (q+1) b) at hj
 rw [← hi, ← hj]
 exact cochain_cup_leibniz R X _ _

set_option backward.isDefEq.respectTransparency false in
def tagged_cup_linear (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
    cycles R (cupComplex R X A i) p →ₗ[R] cycles R (cupComplex R X A j) q →ₗ[R]
      cycles R (cupComplex R X A (i || j)) (p+q) where
  toFun a :=
    { toFun := fun b ↦ ⟨tagged_cochain_cup R X A i j p q a.val b.val,
        tagged_cup_is_cocycle R X A i j p q a b⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  map_add' := by intros; ext b; exact DFunLike.congr_fun (map_add _ _ _) b.val
  map_smul' := by intros; ext b; exact DFunLike.congr_fun (map_smul _ _ _) b.val

set_option backward.isDefEq.respectTransparency false in
theorem boundary_rel_iff (Q : CochainComplex (ModuleCat.{u} R) ℕ)
 (n m : ℕ) (hn : n+1=m) (a : cycles R Q m) :
 a ∈ boundaries R Q m ↔ ∃ b : Q.X n, Q.d n m b = a.val := by
 subst m
 exact boundary_successor_iff R Q n a

set_option backward.isDefEq.respectTransparency false in
/-- A boundary in the first factor gives a boundary. Hatcher p.207: use the cup of a primitive with the second cocycle; zero-degree boundaries vanish. -/
theorem tagged_cup_boundary_left (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
 (a : cycles R (cupComplex R X A i) p) (b : cycles R (cupComplex R X A j) q)
 (ha : a ∈ boundaries R (cupComplex R X A i) p) :
 tagged_cup_linear R X A i j p q a b ∈ boundaries R (cupComplex R X A (i || j)) (p+q) := by
 cases p with
 | zero =>
   have ha0 := (boundary_zero_iff R _ a).mp ha
   subst a
   simp
 | succ p =>
   obtain ⟨a',ha'⟩ := (boundary_successor_iff R _ p a).mp ha
   rw [boundary_rel_iff R _ (p+q) ((p+1)+q) (by omega)]
   refine ⟨tagged_cochain_cup R X A i j p q a' b.val, ?_⟩
   apply (ModuleCat.mono_iff_injective
     ((cupComplex R X A (i || j)).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom).mp inferInstance
   have hd := congrArg (fun g => g (tagged_cochain_cup R X A i j p q a' b.val))
     ((cupComplex R X A (i || j)).d_comp_XIsoOfEq_hom
       (show (p+1)+q=p+q+1 by omega) (p+q))
   change ((cupComplex R X A (i || j)).XIsoOfEq (show (p+1)+q=p+q+1 by omega)).hom
     ((cupComplex R X A (i || j)).d (p+q) ((p+1)+q)
       (tagged_cochain_cup R X A i j p q a' b.val)) =
     (cupComplex R X A (i || j)).d (p+q) (p+q+1)
       (tagged_cochain_cup R X A i j p q a' b.val) at hd
   rw [hd, tagged_cochain_leibniz, ha',
     (mem_cycles_iff_d_eq_zero R _ _ _).mp b.property]
   have hz : tagged_cochain_cup R X A i j p (q+1) a' 0 = 0 := by
     apply inclusion_degree_injective R X A (i || j) (p+(q+1))
     simp [tagged_cochain_cup]
   rw [hz, smul_zero, add_zero]
   rfl

set_option backward.isDefEq.respectTransparency false in
/-- A boundary in the second factor gives a boundary. Hatcher p.207: use (-1)^p times the cup with a primitive; zero-degree boundaries vanish. -/
theorem tagged_cup_boundary_right (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
 (a : cycles R (cupComplex R X A i) p) (b : cycles R (cupComplex R X A j) q)
 (hb : b ∈ boundaries R (cupComplex R X A j) q) :
 tagged_cup_linear R X A i j p q a b ∈ boundaries R (cupComplex R X A (i || j)) (p+q) := by
 cases q with
 | zero =>
   have hb0 := (boundary_zero_iff R _ b).mp hb
   subst b
   rw [map_zero]
   exact Submodule.zero_mem _
 | succ q =>
   obtain ⟨b',hb'⟩ := (boundary_successor_iff R _ q b).mp hb
   rw [boundary_rel_iff R _ (p+q) (p+(q+1)) (by omega)]
   refine ⟨(-1:R)^p • tagged_cochain_cup R X A i j p q a.val b', ?_⟩
   erw [map_smul, tagged_cochain_leibniz,
     (mem_cycles_iff_d_eq_zero R _ _ _).mp a.property, hb']
   have hz : tagged_cochain_cup R X A i j (p+1) q 0 b' = 0 := by
     apply inclusion_degree_injective R X A (i || j) ((p+1)+q)
     simp [tagged_cochain_cup]
   rw [hz, map_zero, zero_add, smul_smul]
   have hsign : (-1:R)^p * (-1:R)^p = 1 := by rw [← mul_pow]; simp
   rw [hsign, one_smul]
   rfl

set_option backward.isDefEq.respectTransparency false in
def tagged_cup_class_linear (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
 cycles R (cupComplex R X A i) p →ₗ[R] cycles R (cupComplex R X A j) q →ₗ[R]
   cupCohomology R X A (i || j) (p+q) :=
 (tagged_cup_linear R X A i j p q).compr₂
   (cocycleClass R (cupComplex R X A (i || j)) (p+q))

set_option backward.isDefEq.respectTransparency false in
theorem tagged_cup_class_boundary_left (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
 boundaries R (cupComplex R X A i) p ≤ (tagged_cup_class_linear R X A i j p q).ker := by
 intro a ha
 apply LinearMap.ext
 intro b
 change cocycleClass R _ _ (tagged_cup_linear R X A i j p q a b) = 0
 exact (Submodule.Quotient.mk_eq_zero _).mpr (tagged_cup_boundary_left R X A i j p q a b ha)

set_option backward.isDefEq.respectTransparency false in
theorem tagged_cup_class_boundary_right (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
 boundaries R (cupComplex R X A j) q ≤ (tagged_cup_class_linear R X A i j p q).flip.ker := by
 intro b hb
 apply LinearMap.ext
 intro a
 change cocycleClass R _ _ (tagged_cup_linear R X A i j p q a b) = 0
 exact (Submodule.Quotient.mk_eq_zero _).mpr (tagged_cup_boundary_right R X A i j p q a b hb)

set_option backward.isDefEq.respectTransparency false in
/-- The bilinear cup product on ordinary and relative cohomology. Hatcher pp.207,209: the cochain formula kills either boundary submodule, hence descends through both quotient maps. -/
def descended_cup (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ) :
 cupCohomology R X A i p →ₗ[R] cupCohomology R X A j q →ₗ[R]
   cupCohomology R X A (i || j) (p+q) :=
 (tagged_cup_class_linear R X A i j p q).liftQ₂
   (boundaries R (cupComplex R X A i) p) (boundaries R (cupComplex R X A j) q)
   (tagged_cup_class_boundary_left R X A i j p q)
   (tagged_cup_class_boundary_right R X A i j p q)

set_option backward.isDefEq.respectTransparency false in
/-- The quotient cup product has the prescribed representative formula. Hatcher pp.207,209 and the defining equation of the bilinear quotient lift. -/
theorem descended_cup_representatives (X : TopCat.{u}) (A : Set X) (i j : Bool) (p q : ℕ)
 (a : cycles R (cupComplex R X A i) p) (b : cycles R (cupComplex R X A j) q) :
 descended_cup R X A i j p q (cocycleClass R _ p a) (cocycleClass R _ q b) =
   cocycleClass R _ (p+q) (tagged_cup_linear R X A i j p q a b) := rfl

set_option backward.isDefEq.respectTransparency false in
def cycle_map {Q Q' : CochainComplex (ModuleCat.{u} R) ℕ} (f : Q ⟶ Q') (n : ℕ) :
 cycles R Q n →ₗ[R] cycles R Q' n :=
 ((f.f n).hom.comp (cycles R Q n).subtype).codRestrict _ (fun a ↦ map_cocycle R f n a)

set_option backward.isDefEq.respectTransparency false in
theorem cycle_map_via_iso {Q Q' : CochainComplex (ModuleCat.{u} R) ℕ}
 (f : Q ⟶ Q') (n : ℕ) :
 (Q.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap f n ≫
   (Q'.sc n).moduleCatCyclesIso.hom = ModuleCat.ofHom (cycle_map R f n) := by
 apply (cancel_mono (Q'.sc n).moduleCatLeftHomologyData.i).mp
 simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
 change (Q.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap f n ≫ Q'.iCycles n =
   ModuleCat.ofHom (cycle_map R f n) ≫ (Q'.sc n).moduleCatLeftHomologyData.i
 rw [HomologicalComplex.cyclesMap_i, ← Category.assoc]
 change (Q.sc n).moduleCatCyclesIso.inv ≫ (Q.sc n).iCycles ≫ f.f n = _
 rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
 rfl

set_option backward.isDefEq.respectTransparency false in
theorem quotientMap_cocycleClass {Q Q' : CochainComplex (ModuleCat.{u} R) ℕ}
 (f : Q ⟶ Q') (n : ℕ) (a : cycles R Q n) :
 quotientMap R f n (cocycleClass R Q n a) =
   cocycleClass R Q' n (cycle_map R f n a) := by
 have h : (Q.sc n).moduleCatLeftHomologyData.π ≫ quotientMap R f n =
     ModuleCat.ofHom (cycle_map R f n) ≫ (Q'.sc n).moduleCatLeftHomologyData.π := by
   dsimp [quotientMap]
   rw [← Category.assoc, ← ShortComplex.moduleCatCyclesIso_inv_π]
   change (Q.sc n).moduleCatCyclesIso.inv ≫ Q.homologyπ n ≫
     HomologicalComplex.homologyMap f n ≫ (Q'.sc n).moduleCatHomologyIso.hom = _
   rw [HomologicalComplex.homologyπ_naturality_assoc]
   change (Q.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap f n ≫
     (Q'.sc n).homologyπ ≫ (Q'.sc n).moduleCatHomologyIso.hom = _
   rw [ShortComplex.π_moduleCatCyclesIso_hom]
   have hm := cycle_map_via_iso R f n =≫ (Q'.sc n).moduleCatLeftHomologyData.π
   simpa only [Category.assoc] using hm
 exact congrArg (fun g => g a) h

set_option backward.isDefEq.respectTransparency false in
theorem cocycleClass_surjective (Q : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
 Function.Surjective (cocycleClass R Q n) :=
 Submodule.mkQ_surjective _

set_option backward.isDefEq.respectTransparency false in
def tagged_pullback {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
    (hf : Set.MapsTo f A B) (i : Bool) : cupComplex R Y B i ⟶ cupComplex R X A i :=
  match i with
  | false => pullback R f
  | true => relativePullback R f hf

set_option backward.isDefEq.respectTransparency false in
theorem tagged_pullback_square {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) (i : Bool) :
    tagged_pullback R f A B hf i ≫ cupInclusion R X A i =
      cupInclusion R Y B i ≫ pullback R f := by
  cases i
  · change pullback R f ≫ 𝟙 _ = 𝟙 _ ≫ pullback R f
    simp
  · dsimp [tagged_pullback, cupInclusion, relativePullback]
    exact kernel.lift_ι _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem tagged_cup_pullback {X Y : TopCat.{u}} (f : X ⟶ Y) (A : Set X) (B : Set Y)
 (hf : Set.MapsTo f A B) (i j : Bool) (p q : ℕ)
 (a : cycles R (cupComplex R Y B i) p) (b : cycles R (cupComplex R Y B j) q) :
 cycle_map R (tagged_pullback R f A B hf (i || j)) (p+q)
   (tagged_cup_linear R Y B i j p q a b) =
 tagged_cup_linear R X A i j p q
   (cycle_map R (tagged_pullback R f A B hf i) p a)
   (cycle_map R (tagged_pullback R f A B hf j) q b) := by
 apply Subtype.ext
 apply inclusion_degree_injective R X A (i || j) (p+q)
 have hout := congrArg (fun g => g.f (p+q) (tagged_cochain_cup R Y B i j p q a.val b.val))
   (tagged_pullback_square R f A B hf (i || j))
 change (cupInclusion R X A (i || j)).f (p+q)
   ((tagged_pullback R f A B hf (i || j)).f (p+q) (tagged_cochain_cup R Y B i j p q a.val b.val)) =
   (pullback R f).f (p+q) ((cupInclusion R Y B (i || j)).f (p+q)
     (tagged_cochain_cup R Y B i j p q a.val b.val)) at hout
 change (cupInclusion R X A (i || j)).f (p+q)
   ((tagged_pullback R f A B hf (i || j)).f (p+q) (tagged_cochain_cup R Y B i j p q a.val b.val)) =
   (cupInclusion R X A (i || j)).f (p+q) (tagged_cochain_cup R X A i j p q
     ((tagged_pullback R f A B hf i).f p a.val) ((tagged_pullback R f A B hf j).f q b.val))
 rw [hout, tagged_cochain_cup_inclusion, tagged_cochain_cup_inclusion, pullback_cupCochain]
 have hi := congrArg (fun g => g.f p a.val) (tagged_pullback_square R f A B hf i)
 have hj := congrArg (fun g => g.f q b.val) (tagged_pullback_square R f A B hf j)
 change (cupInclusion R X A i).f p ((tagged_pullback R f A B hf i).f p a.val) =
   (pullback R f).f p ((cupInclusion R Y B i).f p a.val) at hi
 change (cupInclusion R X A j).f q ((tagged_pullback R f A B hf j).f q b.val) =
   (pullback R f).f q ((cupInclusion R Y B j).f q b.val) at hj
 rw [hi,hj]

set_option backward.isDefEq.respectTransparency false in
/-- Pullbacks of pairs preserve the quotient cup products. Hatcher Proposition 3.10 p.210: reduce to representatives and use the cochain pullback square. -/
theorem descended_cup_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
 (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) (i j : Bool) (p q : ℕ)
 (a : cupCohomology R Y B i p) (b : cupCohomology R Y B j q) :
 quotientMap R (tagged_pullback R f A B hf (i || j)) (p+q)
   (descended_cup R Y B i j p q a b) =
 descended_cup R X A i j p q
   (quotientMap R (tagged_pullback R f A B hf i) p a)
   (quotientMap R (tagged_pullback R f A B hf j) q b) := by
 obtain ⟨a, rfl⟩ := cocycleClass_surjective R _ p a
 obtain ⟨b, rfl⟩ := cocycleClass_surjective R _ q b
 rw [descended_cup_representatives, quotientMap_cocycleClass, quotientMap_cocycleClass,
   quotientMap_cocycleClass, descended_cup_representatives, tagged_cup_pullback]

set_option backward.isDefEq.respectTransparency false in
theorem class_heq_of_degree_cast (Q : CochainComplex (ModuleCat.{u} R) ℕ)
 {m n : ℕ} (h : m=n) (a : cycles R Q m) (b : cycles R Q n)
 (hab : (Q.XIsoOfEq h).hom a.val = b.val) :
 HEq (cocycleClass R Q m a) (cocycleClass R Q n b) := by
 subst n
 apply heq_of_eq
 congr 1
 apply Subtype.ext
 simpa [HomologicalComplex.XIsoOfEq] using hab

set_option backward.isDefEq.respectTransparency false in
def unit_cocycle (X : TopCat.{u}) : cycles R (complex R X) 0 :=
 ⟨oneCochain R X, by
   obtain ⟨c,hc,_⟩ := exists_constantOne_cocycle R X
   rw [← hc]
   exact c.property⟩

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary constant-one class is a right unit. Hatcher p.207: the cochain unit identity transfers through inclusion and the quotient projection. -/
theorem tagged_cup_unit_right (X : TopCat.{u}) (A : Set X) (i : Bool) (p : ℕ)
 (a : cycles R (cupComplex R X A i) p) :
 HEq (descended_cup R X A i false p 0 (cocycleClass R _ p a)
    (cocycleClass R _ 0 (unit_cocycle R X))) (cocycleClass R _ p a) := by
 cases i
 · rw [descended_cup_representatives]
   apply heq_of_eq
   apply congrArg (cocycleClass R (cupComplex R X A false) p)
   apply Subtype.ext
   apply inclusion_degree_injective R X A false p
   change (cupInclusion R X A false).f p
     (tagged_cochain_cup R X A false false p 0 a.val (oneCochain R X)) =
     (cupInclusion R X A false).f p a.val
   erw [tagged_cochain_cup_inclusion R X A false false p 0 a.val (oneCochain R X)]
   change cupCochain R X ((cupInclusion R X A false).f p a.val) (oneCochain R X) = _
   exact (cupCochain_unit R X _).1
 · rw [descended_cup_representatives]
   apply heq_of_eq
   apply congrArg (cocycleClass R (cupComplex R X A true) p)
   apply Subtype.ext
   apply inclusion_degree_injective R X A true p
   change (cupInclusion R X A true).f p
     (tagged_cochain_cup R X A true false p 0 a.val (oneCochain R X)) =
     (cupInclusion R X A true).f p a.val
   erw [tagged_cochain_cup_inclusion R X A true false p 0 a.val (oneCochain R X)]
   change cupCochain R X ((cupInclusion R X A true).f p a.val) (oneCochain R X) = _
   exact (cupCochain_unit R X _).1

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary constant-one class is a left unit. Hatcher p.207: the cochain unit identity transfers through inclusion and the quotient projection. -/
theorem tagged_cup_unit_left (X : TopCat.{u}) (A : Set X) (i : Bool) (p : ℕ)
 (a : cycles R (cupComplex R X A i) p) :
 HEq (descended_cup R X A false i 0 p (cocycleClass R _ 0 (unit_cocycle R X))
    (cocycleClass R _ p a)) (cocycleClass R _ p a) := by
 cases i
 · rw [descended_cup_representatives]
   apply class_heq_of_degree_cast R (cupComplex R X A false) (Nat.zero_add p)
   apply inclusion_degree_injective R X A false p
   have hcast := congrArg (fun g => g (tagged_cochain_cup R X A false false 0 p
     (oneCochain R X) a.val))
     (HomologicalComplex.XIsoOfEq_hom_naturality (cupInclusion R X A false) (Nat.zero_add p))
   change ((complex R X).XIsoOfEq (Nat.zero_add p)).hom ((cupInclusion R X A false).f (0+p)
     (tagged_cochain_cup R X A false false 0 p (oneCochain R X) a.val)) =
     (cupInclusion R X A false).f p (((cupComplex R X A false).XIsoOfEq (Nat.zero_add p)).hom
     (tagged_cochain_cup R X A false false 0 p (oneCochain R X) a.val)) at hcast
   change (cupInclusion R X A false).f p (((cupComplex R X A false).XIsoOfEq (Nat.zero_add p)).hom
     (tagged_cochain_cup R X A false false 0 p (oneCochain R X) a.val)) =
     (cupInclusion R X A false).f p a.val
   erw [← hcast, tagged_cochain_cup_inclusion R X A false false 0 p (oneCochain R X) a.val]
   change ((complex R X).XIsoOfEq (Nat.zero_add p)).hom
     (cupCochain R X (oneCochain R X) ((cupInclusion R X A false).f p a.val)) = _
   exact (cupCochain_unit R X _).2
 · rw [descended_cup_representatives]
   apply class_heq_of_degree_cast R (cupComplex R X A true) (Nat.zero_add p)
   apply inclusion_degree_injective R X A true p
   have hcast := congrArg (fun g => g (tagged_cochain_cup R X A false true 0 p
     (oneCochain R X) a.val))
     (HomologicalComplex.XIsoOfEq_hom_naturality (cupInclusion R X A true) (Nat.zero_add p))
   change ((complex R X).XIsoOfEq (Nat.zero_add p)).hom ((cupInclusion R X A true).f (0+p)
     (tagged_cochain_cup R X A false true 0 p (oneCochain R X) a.val)) =
     (cupInclusion R X A true).f p (((cupComplex R X A true).XIsoOfEq (Nat.zero_add p)).hom
     (tagged_cochain_cup R X A false true 0 p (oneCochain R X) a.val)) at hcast
   change (cupInclusion R X A true).f p (((cupComplex R X A true).XIsoOfEq (Nat.zero_add p)).hom
     (tagged_cochain_cup R X A false true 0 p (oneCochain R X) a.val)) =
     (cupInclusion R X A true).f p a.val
   erw [← hcast, tagged_cochain_cup_inclusion R X A false true 0 p (oneCochain R X) a.val]
   change ((complex R X).XIsoOfEq (Nat.zero_add p)).hom
     (cupCochain R X (oneCochain R X) ((cupInclusion R X A true).f p a.val)) = _
   exact (cupCochain_unit R X _).2

set_option backward.isDefEq.respectTransparency false in
theorem class_heq_of_inclusion_cast (X : TopCat.{u}) (A : Set X)
 {i j : Bool} (hij : i=j) {m n : ℕ} (hmn : m=n)
 (a : cycles R (cupComplex R X A i) m) (b : cycles R (cupComplex R X A j) n)
 (hab : ((complex R X).XIsoOfEq hmn).hom ((cupInclusion R X A i).f m a.val) =
   (cupInclusion R X A j).f n b.val) :
 HEq (cocycleClass R (cupComplex R X A i) m a)
   (cocycleClass R (cupComplex R X A j) n b) := by
 subst j
 subst n
 apply heq_of_eq
 apply congrArg (cocycleClass R (cupComplex R X A i) m)
 apply Subtype.ext
 apply inclusion_degree_injective R X A i m
 simpa [HomologicalComplex.XIsoOfEq] using hab

set_option backward.isDefEq.respectTransparency false in
/-- The mixed quotient cup product is associative. Hatcher p.207: choose representatives, identify the two total degrees, and apply cochain associativity under the injective inclusion. -/
theorem descended_cup_assoc (X : TopCat.{u}) (A : Set X) (i j k : Bool) (p q r : ℕ)
 (a : cupCohomology R X A i p) (b : cupCohomology R X A j q) (c : cupCohomology R X A k r) :
 HEq (descended_cup R X A (i || j) k (p+q) r (descended_cup R X A i j p q a b) c)
   (descended_cup R X A i (j || k) p (q+r) a (descended_cup R X A j k q r b c)) := by
 obtain ⟨a,rfl⟩ := cocycleClass_surjective R _ p a
 obtain ⟨b,rfl⟩ := cocycleClass_surjective R _ q b
 obtain ⟨c,rfl⟩ := cocycleClass_surjective R _ r c
 rw [descended_cup_representatives, descended_cup_representatives,
   descended_cup_representatives, descended_cup_representatives]
 apply class_heq_of_inclusion_cast R X A (Bool.or_assoc i j k) (Nat.add_assoc p q r)
 change ((complex R X).XIsoOfEq (Nat.add_assoc p q r)).hom
   ((cupInclusion R X A ((i || j) || k)).f ((p+q)+r)
     (tagged_cochain_cup R X A (i || j) k (p+q) r
       (tagged_cochain_cup R X A i j p q a.val b.val) c.val)) =
   (cupInclusion R X A (i || (j || k))).f (p+(q+r))
     (tagged_cochain_cup R X A i (j || k) p (q+r) a.val
       (tagged_cochain_cup R X A j k q r b.val c.val))
 erw [tagged_cochain_cup_inclusion R X A (i || j) k (p+q) r,
   tagged_cochain_cup_inclusion R X A i j p q,
   tagged_cochain_cup_inclusion R X A i (j || k) p (q+r),
   tagged_cochain_cup_inclusion R X A j k q r]
 exact cupCochain_assoc R X _ _ _

open Convexity


end HolomorphicAnosov.SingularCochain.MixedCup
