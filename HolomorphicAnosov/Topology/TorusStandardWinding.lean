import HolomorphicAnosov.Topology.TorusStandardWindingIntegerKernelMapBijective
import HolomorphicAnosov.Topology.TorusStandardWindingIntegralToralMapZero
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_continuous
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Topology.TorusCoordinateCover
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Coordinate winding of the real torus

Source: Hatcher, *Algebraic Topology*, Theorem 1.7 and proof, pp.29–31;
Proposition 1.12, Example 1.13 and Induced Homomorphisms, p.34.
The torus is the actual product `UnitAddTorus (Fin n)` at its zero basepoint.

The normalized loop with winding vector z is specified by its pointwise formula
`t ↦ (j ↦ [t*z_j])`, so the unit vector gives the positively oriented standard loop.
The integral toral map is the published finite integer row action. Its continuous
representative and basedness proof are exhibited in the conclusion, rather than
postulated as premises. Mathlib's `FundamentalGroup.mapOfEq` is then the actual
induced based map. The coordinate formula uses `Matrix.mulVec`, without transpose.
-/

/-!
Implementation route note. The original source plan below is retained verbatim, but the
kernel proof takes the shorter whole-coordinate Mathlib monodromy route. In
`Topology/Homotopy/Lifting.lean` (monodromy and its composition laws, and the endpoint
homomorphism with injectivity/surjectivity, lines390–445 and560–686), path and homotopy
lifting identify the fundamental group with the translation deck group. The
`MulEquiv.ofBijective` construction used here is definitionally the same generic
construction as `fundamentalGroupEquiv`; it is not a formalization of Hatcher's separate
coordinate-product homotopy proof or an avoidance of that generic equivalence. The
contractibility of the actual real coordinate space supplies simply connectedness.
The explicit integer-kernel equivalence, commutative removal of the opposite convention,
straight-loop endpoints, and row-matrix naturality are proved here and fix all signs.
Hatcher pp.29–34 remains the mathematical source; the implementation APIs just listed
supply the alternative proved lifting mechanism, without additional hypotheses.
-/

namespace HolomorphicAnosov

open _root_.HolomorphicAnosov.Topology

noncomputable section
open Filter Function
open scoped _root_.Topology


/-- The concrete additive deck-coordinate equivalence, constructed from the preceding bijection. -/
private def integerKernelEquiv (n : ℕ) : (Fin n → ℤ) ≃+ (coordinateProjection n).ker :=
  AddEquiv.ofBijective (integerKernelMap n) (integerKernelMap_bijective n)

/-- The genuine straight integral lift in the native real-coordinate space. -/
private def straightIntegralPath (n : ℕ) (z : Fin n → ℤ) :
    Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)) where
  toFun t i := (t : ℝ) * (z i : ℝ)
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

/-- Projection of the actual straight integral path, with its quotient-zero endpoint casts. -/
private def integralLoop (n : ℕ) (z : Fin n → ℤ) : Path (0 : UnitAddTorus (Fin n)) 0 :=
  ((straightIntegralPath n z).map (coordinateProjection_cover n).continuous).cast
    (by ext; simp [coordinateProjection]) (by
      ext i
      exact ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩).symm)

/-- The projected straight path has the literal positive quotient-circle formula by reduction. -/
private theorem integralLoop_formula (n : ℕ) (z : Fin n → ℤ) (t : unitInterval)
    (i : Fin n) : integralLoop n z t i = (((t : ℝ) * (z i : ℝ) : ℝ) : UnitAddCircle) := rfl


/-- The original zero point as an element of the actual quotient projection fibre. -/
private def zeroFiber (n : ℕ) :
    (coordinateProjection n) ⁻¹' {0} := ⟨0, by simp⟩

/-- Endpoint coordinates remove the harmless opposite convention by commutativity. -/
private def deckCoordinateEquiv (n : ℕ) :
    (Multiplicative (coordinateProjection n).ker)ᵐᵒᵖ ≃*
      Multiplicative (Fin n → ℤ) where
  toFun g := Multiplicative.ofAdd ((integerKernelEquiv n).symm g.unop.toAdd)
  invFun z := MulOpposite.op (Multiplicative.ofAdd (integerKernelEquiv n z.toAdd))
  left_inv g := by simp
  right_inv z := by simp
  map_mul' g h := by
    change Multiplicative.ofAdd ((integerKernelEquiv n).symm (h.unop.toAdd + g.unop.toAdd)) = _
    simp [map_add, add_comm]

/-- The actual lifted endpoint homomorphism, with its path/homotopy lifting bijectivity. -/
private def windingEquiv (n : ℕ) :
    FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ) :=
  (MulEquiv.ofBijective
    ((coordinateProjection_cover n).fundamentalGroupToMulOpposite (zeroFiber n))
    ⟨(coordinateProjection_cover n).fundamentalGroupToMulOpposite_injective _,
      (coordinateProjection_cover n).fundamentalGroupToMulOpposite_surjective _⟩).trans
    (deckCoordinateEquiv n)

/-- Mathlib `IsCoveringMap.monodromy_eq_of_map_eq` applied to the straight integral lift. -/
private theorem integralLoop_monodromy (n : ℕ) (z : Fin n → ℤ) :
    (coordinateProjection_cover n).isCoveringMap.monodromy
      ⟦integralLoop n z⟧ (zeroFiber n) =
      ⟨(integerKernelMap n z).val, (integerKernelMap n z).property⟩ := by
  apply (coordinateProjection_cover n).isCoveringMap.monodromy_eq_of_map_eq
    (⟦straightIntegralPath n z⟧)
  rfl

/-- The endpoint-homomorphism characterization and the preceding monodromy equation fix the positive winding value. -/
private theorem winding_integralLoop (n : ℕ) (z : Fin n → ℤ) :
    windingEquiv n (FundamentalGroup.fromPath ⟦integralLoop n z⟧) =
      Multiplicative.ofAdd z := by
  have h := (coordinateProjection_cover n).fundamentalGroupToMulOpposite_apply_eq_Iff
    (e := zeroFiber n) (γ := FundamentalGroup.fromPath ⟦integralLoop n z⟧)
    (g := MulOpposite.op (Multiplicative.ofAdd (integerKernelMap n z)))
  have hh : (coordinateProjection_cover n).fundamentalGroupToMulOpposite
      (zeroFiber n) (FundamentalGroup.fromPath ⟦integralLoop n z⟧) =
      MulOpposite.op (Multiplicative.ofAdd (integerKernelMap n z)) := by
    apply h.mpr
    rw [integralLoop_monodromy]
    change (integerKernelMap n z).val + 0 = (integerKernelMap n z).val
    simp
  change deckCoordinateEquiv n ((coordinateProjection_cover n).fundamentalGroupToMulOpposite
    (zeroFiber n) (FundamentalGroup.fromPath ⟦integralLoop n z⟧)) = _
  rw [hh]
  change Multiplicative.ofAdd ((integerKernelEquiv n).symm (integerKernelEquiv n z)) = _
  simp


/-- The literal finite row calculation: projection commutes with integer multiplication and sums; distributivity gives `B.mulVec z`. -/
private theorem integralToralMap_integralLoop {n : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin n) ℤ) (z : Fin n → ℤ) (t : unitInterval) :
    integralToralMap B (integralLoop n z t) =
      integralLoop n (Matrix.mulVec (B : Matrix (Fin n) (Fin n) ℤ) z) t := by
  ext i
  change (∑ j, B i j • (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) =
    (((t : ℝ) * ((∑ j, B i j * z j : ℤ) : ℝ) : ℝ) : UnitAddCircle)
  rw [show ((∑ j, B i j * z j : ℤ) : ℝ) = ∑ j, (B i j : ℝ) * (z j : ℝ) by simp]
  rw [Finset.mul_sum]
  change (∑ j, B i j • (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (∑ j, (t : ℝ) * ((B i j : ℝ) * (z j : ℝ)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

/-- Mathlib `FundamentalGroup.mapOfEq_apply` and the preceding pointwise row calculation identify the actual mapped path class. -/
private theorem mapped_integralLoop {n : ℕ}
    (B : Matrix.GeneralLinearGroup (Fin n) ℤ) (z : Fin n → ℤ) :
    FundamentalGroup.mapOfEq
      ⟨integralToralMap B, Dynamics.integralToralMap_continuous B⟩ (integralToralMap_zero B)
      (FundamentalGroup.fromPath ⟦integralLoop n z⟧) =
      FundamentalGroup.fromPath ⟦integralLoop n (Matrix.mulVec (B : Matrix (Fin n) (Fin n) ℤ) z)⟧ := by
  rw [FundamentalGroup.mapOfEq_apply]
  change ⟦((integralLoop n z).map (Dynamics.integralToralMap_continuous B)).cast _ _⟧ = _
  congr 1
  ext t i
  exact congrFun (integralToralMap_integralLoop B z t) i


/-- Coordinate winding gives the normalized fundamental-group isomorphism of the real torus,
natural for integral toral automorphisms.

Source: Hatcher, *Algebraic Topology*, Theorem 1.7 and complete proof, pp.29–31;
Proposition 1.12, Example 1.13 and Induced Homomorphisms, p.34. The positive quotient
circle loop corresponds to the source's exp(2πit). The matrix clause follows by the
explicit finite-sum coordinate calculation for the published `integralToralMap`.

Complete natural-language proof, relative to the named DAG providers:

C1. Let E=Fin n -> R, T=UnitAddTorus(Fin n), D=Fin n -> AddSubgroup.zmultiples(1:R), and p:E->T be
the actual coordinatewise quotient additive homomorphism. The integer subgroup of R is discrete. The
period-one circle projection is therefore an additive quotient covering. Its quotient-map fields
give continuity and surjectivity, and the quotient-cover-to-cover and cover-openness theorems give
openness. Thus each coordinate projection is an open quotient map.
Providers: topo.def_real_torus, mathlib.zmultiples_discrete_order_topology_g8, mathlib.addcircle_quotient_cover_g8, mathlib.add_quotient_cover_is_covering_g8, mathlib.covering_map_open_g8.

C2. The coordinatewise product p is an open quotient map by the product theorem. If p(x)=p(y), each
coordinate equality supplies g_i in zmultiples(1:R) with g_i+y_i=x_i; choosing these coordinates
gives one g in D with g+y=x. Conversely every such translation preserves each quotient coordinate. A
fixed g acts continuously, since each coordinate action is continuous and product continuity is
coordinatewise.
Providers: topo.def_real_torus, mathlib.addcircle_quotient_cover_g8, mathlib.open_quotient_map_pi_g8.

C3. For x in E, choose from each circle quotient covering a neighborhood U_i of x_i such that
(g_i+U_i) intersect U_i nonempty forces g_i=0. Since Fin n is finite, U=product_i U_i is a
neighborhood of x. If (g+U) intersects U, an intersection point in every coordinate invokes the
chosen condition and forces g_i=0 for every i, hence g=0. This is exactly the additive quotient-
cover disjointness field. Together with the previous quotient-map, orbit and continuity fields it
constructs the additive quotient-cover witness for p, hence an actual continuous, surjective, open
covering projection. These cover data are retained because the Franks covering consumers use this
real-coordinate cover as well as the stated winding equivalence.
Providers: topo.def_real_torus, mathlib.addcircle_quotient_cover_g8, mathlib.add_quotient_cover_is_covering_g8, mathlib.covering_map_open_g8, mathlib.finite_pi_neighborhood_g8.

C4. Define iota:Z^(Fin n)->D by iota(z)_i=(z_i:R). Integer casts preserve addition, so iota is an
additive homomorphism. If iota(z)=iota(w), coordinate equality and injectivity of the integer cast
imply z_i=w_i for all i. If g is in D, subgroup membership gives integers z_i with z_i times 1=g_i;
choosing them gives iota(z)=g. Thus iota is bijective and its inverse is the additive deck-
coordinate equivalence. This is the actual translation subgroup, not an independently chosen
lattice.
Providers: topo.def_real_torus, mathlib.zmultiples_membership_g8, mathlib.int_cast_injective_g8.

C5. The real vector space E=Fin n→R is contractible and therefore simply connected by the two named
Mathlib leaves. Together with C1–C4 this verifies that p:E→UnitAddTorus(Fin n) is the pointed simply
connected translation cover, with p(0)=0 and integer deck translation iota(z). This is auxiliary
cover data for existing consumers. The winding isomorphism below is proved by Hatcher’s circle and
finite-product argument, without applying the general quotient-cover fundamental-group equivalence.
Providers: mathlib.real_vector_space_contractible_g8, mathlib.contractible_space_simply_connected_g8, topo.def_real_torus.

W1. Match the concrete circle to the circle in Hatcher Theorem1.7. For period1, the exact
homeomorphism AddCircle.homeomorphCircle identifies UnitAddCircle with the complex unit circle,
sends0 to1, and sends the coset of a real r to exp(2πir). Thus the path t↦[kt] corresponds to
Hatcher’s ω_k(t)=(cos(2πkt),sin(2πkt)), with ω_1 the positive generator. Its real lift t↦kt starts
at0 and ends at k. The coordinate quotient covering from C1 transports to precisely Hatcher’s
p:R→S¹; the zero-fibre theorem says that its fibre over the basepoint is Z, not an oppositely
oriented identification.
Providers: topo.def_real_torus, mathlib.addcircle_homeomorph_circle_g7, mathlib.addcircle_toCircle_coe_exp_g2, mathlib.addcircle_zero_fiber_g8, mathlib.addcircle_quotient_cover_g8, mathlib.add_quotient_cover_is_covering_g8.

W2. Follow the written proof of Theorem1.7, pp.30–31, for a based circle loop a. The path-lift
theorem gives its continuous real lift ã starting at0, and covering uniqueness fixes that lift. The
endpoint lies in the base fibre Z; write ã(1)=k. Hatcher’s explicit homotopy (s,t)↦(1−s)ã(t)+skt is
continuous, starts at0 and ends at k for every s. Projecting it through the continuous circle
quotient gives an endpoint-fixed homotopy a~(t↦[kt]). This proves existence of the normalized
representative. The named path/homotopy lift primitives implement Hatcher’s written
properties(a),(b),(c): he constructs lifts on finitely many interval pieces in evenly covered
neighborhoods by inverse sheets, shrinks the parameter neighborhood at each join, proves uniqueness
successively on the connected pieces, and glues the local lifts. No abstract quotient-cover group
equivalence replaces this argument.
Providers: mathlib.covering_exists_path_lifts, mathlib.isCoveringMap_eqOn_of_comp_eqOn, mathlib.path_homotopic_map_g8, topo.path_homotopy_quotient_eq_g8.

W3. For uniqueness, take an endpoint-fixed homotopy from t↦[kt] to t↦[lt]. Lift the entire homotopy
through the circle cover with initial real path t↦kt. Along each boundary t=0 or t=1 its image is a
constant downstairs basepoint, so its continuous lifted boundary takes values in the discrete
integer fibre and is constant on the connected homotopy interval. Thus all lifted paths start at0
and all end at k. Uniqueness of the real lift identifies the last lifted path with t↦lt, and
evaluating at1 gives k=l. Consequently the integer endpoint is independent of the representative
loop and each circle loop class has exactly one integer k. For concatenation a then b, lift a from0
and then the integer translate k+ b̃ of the lift of b from0; the joined continuous real path ends at
k+l. Uniqueness identifies it with the lift of the concatenation. Hence winding adds under
chronological path composition; the constant loop has integer0 and reversal has integer−k. Mathlib’s
FundamentalGroup multiplication reverses chronological composition (a*b=b.trans a), but l+k=k+l, so
the same endpoint function is a group homomorphism to Multiplicative Z with no sign change.
Providers: mathlib.covering_homotopy_lift_g8, mathlib.isCoveringMap_eqOn_of_comp_eqOn, mathlib.zmultiples_discrete_order_topology_g8, mathlib.fundamental_group_path_quotient_g8, mathlib.path_homotopy_quotient_operations_g8, topo.path_homotopy_quotient_eq_g8.

W4. Apply the actual finite-product proof of Hatcher Proposition1.12 and Example1.13, p.34, directly
to T=Fin n→UnitAddCircle. A based loop a in T gives the n based coordinate loops a_j, because
evaluation is continuous. Conversely a finite family of based coordinate loops gives the based loop
t↦(j↦a_j(t)), continuous by the product topology. An endpoint-fixed homotopy in T gives such a
homotopy in every coordinate; conversely coordinate homotopies combine as (s,t)↦(j↦H_j(s,t)), again
jointly continuous by the product topology with both endpoints fixed. Therefore two torus loops have
equal classes exactly when all coordinate classes agree. Projection commutes with constant paths,
reversal and the actual chronological composition, so this bijection of classes respects the
FundamentalGroup operations including their reversed multiplication convention. Composing with W2–W3
in each coordinate gives the group equivalence w:FundamentalGroup(T,0)≃*Multiplicative(Fin n→Z). An
explicit inverse sends z to the class of integralLoop z, the path t↦(j↦[t(z_j:R)]). The quotient
representative and equality primitives make both directions apply to every actual fundamental-group
element, rather than only to a selected class. This is precisely the finite-product argument written
in the source; Hatcher explicitly states its extension to every n by induction.
Providers: topo.def_real_torus, mathlib.fundamental_group_path_quotient_g8, mathlib.path_homotopy_quotient_operations_g8, mathlib.path_homotopy_quotient_mk_surjective_g8, topo.path_homotopy_quotient_eq_g8, mathlib.addcircle_zero_fiber_g8.

W5. The j-th coordinate of integralLoop z is the circle path t↦[t z_j], whose real lift ends at z_j,
so w([integralLoop z])=ofAdd(z). In particular standardLoop j=integralLoop(Pi.single j 1) has
coordinate[t] at j and0 elsewhere, and w sends its class to the positive unit vector e_j. This also
identifies the normalized witness referred to as windingEquiv n in consumers: every loop is
homotopic to integralLoop of its winding vector by W4, so two group equivalences with these
coordinate-winding values agree on every element. No archived implementation or independently chosen
lattice equivalence is a premise.
Providers: topo.def_real_torus, mathlib.fundamental_group_path_quotient_g8, topo.path_homotopy_quotient_eq_g8.

W6. Retain the actual cover/monodromy compatibility needed by Franks consumers. For any torus loop a
at0, let ã be its real-coordinate lift starting at0 using the product covering p from C1–C5. Each
coordinate ã_j is the unique real lift of a_j from0; W2–W4 therefore give ã(1)_j=(w([a]).toAdd)_j.
Thus the actual lift endpoint is the real integer vector iota(w([a]).toAdd). The monodromy-of-
projected-path leaf identifies this endpoint with monodromy([a],0), including the fixed endpoint
casts. For integralLoop z the actual straight lift t↦tz makes this equation monodromy([integralLoop
z],zeroFiber)=integerFiber z. Translating a real lift by an integer vector gives the analogous
endpoint displacement at any integer fibre point. This preserves the pointed cover and positive
endpoint data used by topo.franks_compact_cw_cover_lifts, topo.franks1969_global_product and
original-map fixed-lift consumers without using fundamentalGroupEquiv or an opposite-group
equivalence.
Providers: mathlib.covering_exists_path_lifts, mathlib.isCoveringMap_eqOn_of_comp_eqOn, mathlib.covering_monodromy_of_projected_path_g8, mathlib.addcircle_zero_fiber_g8.

N1. For the defined map integralToralMap B(x)_i=∑j B_ij•x_j on UnitAddTorus(Fin n), coordinate
evaluation x↦x_j is continuous in the product topology. For each fixed integer B_ij, integer
multiplication on UnitAddCircle is continuous; compose these maps and take their finite sum. Every
output coordinate is therefore continuous, and the product-topology criterion gives continuity of
integralToralMap B. Apply the same calculation to B⁻¹ when needed. When n=0 the product is a
singleton and the empty-coordinate criterion still applies. This uses the existing finite-sum
definition and topology unchanged, without any spectral or conjugacy assertion. The finite-sum
formula gives integralToralMap B 0=0. With this equality, use the named FundamentalGroup.mapOfEq and
mapOfEq_apply provider to identify the induced loop class with the composed loop, retaining the
endpoint casts.
Providers: zhang.def_real_torus_model, mathlib.fundamental_group_map_of_eq_apply_g8.

N2. At coordinate i and parameter t, applying integralToralMap B to integralLoop z gives sum_j B_ij
times [t*z_j]. Projection commutes with integer scalar multiplication and finite sums, so this
equals [sum_j (B_ij:R)*(t*(z_j:R))]. Integer casts preserve finite sums and products, and
distributivity gives [t*((sum_j B_ij*z_j):R)]. The exact mulVec coordinate theorem identifies the
sum with (B.mulVec z)_i, so the mapped paths, hence their actual homotopy classes, equal
integralLoop(B.mulVec z). Thus e_j is sent to column j of B, with no transpose; negative entries
obey the same integer action.
Providers: topo.def_real_torus, zhang.def_real_torus_model, mathlib.addcircle_projection_zsmul_g8, mathlib.additive_hom_finset_sum_g8, mathlib.matrix_mulvec_column_sum_g8.

N3. Given any γ in the actual FundamentalGroup(T,0), put z=(w γ).toAdd. By W4–W5 and injectivity, γ
is the class of integralLoop z. Hatcher’s induced-map formula and N1–N2 give toralPi1Map B
γ=[integralLoop(B.mulVec z)]. Applying W5 yields (w(toralPi1Map B γ)).toAdd=B.mulVec((w γ).toAdd).
The j-th generator therefore goes to column j of B. This is the full stated naturality formula for
every integral matrix unit, with no transpose. The finite-sum calculation in fact uses no
invertibility, though no stronger matrix hypothesis or conclusion is added to the statement.
Providers: mathlib.fundamental_group_map_of_eq_apply_g8, zhang.def_real_torus_model, mathlib.matrix_mulvec_column_sum_g8.

E0. For n=0 the torus and real-coordinate cover are singletons and Fin0→Z is the trivial group.
Every path and homotopy is the unique constant one; W4 is the empty product bijection, so w is the
unique group equivalence. There is no standard-loop index, and the matrix formula is empty-
coordinate equality for the unique0×0 matrix. The retained quotient-cover construction and
contractibility are valid for this singleton. For n=1, t↦[t] has endpoint+1 and t↦[−t] has
endpoint−1, explicitly fixing the generator orientation. All torus coordinate formulae and negative
matrix entries use integer scalar multiplication in the given quotient circle.
Providers: topo.def_real_torus, mathlib.fundamental_group_path_quotient_g8.

The first normalization clause constructs every integral loop with the actual quotient
formula and its winding value. Specializing z to `Pi.single j 1` gives exactly the j-th
standard loop and positive unit vector. The following standard-loop clause makes this
normalization explicit for every path with that formula. Such paths exist by the first
clause, and their formulas determine them uniquely. The continuous map F is constrained
pointwise to the published `integralToralMap B`; its basedness witness is used only for
the endpoint transport in Mathlib's induced homomorphism. Thus no map or continuity
hypothesis replaces part of the conclusion. For n=0 all products are singletons and the
standard-loop clause is vacuous; negative matrix entries retain the integer action.
-/
theorem torus_pi1_standard_winding (n : ℕ) :
    ∃ e : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃*
        Multiplicative (Fin n → ℤ),
      (∀ z : Fin n → ℤ,
        ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
          (∀ (t : unitInterval) (j : Fin n),
            p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
          e (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z) ∧
      (∀ (j : Fin n) (p : Path (0 : UnitAddTorus (Fin n)) 0),
        (∀ (t : unitInterval) (i : Fin n),
          p t i = (((t : ℝ) * (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) : ℝ) :
            UnitAddCircle)) →
        e (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd (Pi.single j 1)) ∧
      (∀ B : Matrix.GeneralLinearGroup (Fin n) ℤ,
        ∃ F : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)),
          (∀ x, F x = integralToralMap B x) ∧
          ∃ h0 : F 0 = 0,
            ∀ γ : FundamentalGroup (UnitAddTorus (Fin n)) 0,
              (e (FundamentalGroup.mapOfEq F h0 γ)).toAdd =
                Matrix.mulVec (B : Matrix (Fin n) (Fin n) ℤ) (e γ).toAdd) := by
  refine ⟨windingEquiv n, ?_, ?_, ?_⟩
  · intro z
    exact ⟨integralLoop n z, integralLoop_formula n z, winding_integralLoop n z⟩
  · intro j p hp
    have hpath : p = integralLoop n (Pi.single j 1) := by
      ext t i
      exact hp t i
    rw [hpath]
    exact winding_integralLoop n _
  · intro B
    refine ⟨⟨integralToralMap B, Dynamics.integralToralMap_continuous B⟩, fun _ ↦ rfl,
      integralToralMap_zero B, ?_⟩
    intro γ
    let z := (windingEquiv n γ).toAdd
    have hγ : γ = FundamentalGroup.fromPath ⟦integralLoop n z⟧ := by
      apply (windingEquiv n).injective
      rw [winding_integralLoop]
      rfl
    rw [hγ, mapped_integralLoop, winding_integralLoop, winding_integralLoop]
    rfl

end
end HolomorphicAnosov
