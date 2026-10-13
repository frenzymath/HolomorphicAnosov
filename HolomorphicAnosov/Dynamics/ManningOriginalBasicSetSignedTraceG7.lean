import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FibreEdgeTargetUnique
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingUniqueOfFibre
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.LabelCardLeOverlapMultiplicity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerEquivalencePath
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedLabelsCode
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedBlocksCommonImage
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTime
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeSucc
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimePeriod
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingTargetsEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordEqOfZero
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockAssignment
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockAssignmentMem
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SupportedAlphabetCardBound
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordFibreCardBound
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CodingLocalSignedCount
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceOfPhysicalFibreCounts
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordFibreBoundOfCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordPhysicalImageExists
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CodingFibreCardLeOverlapMultiplicity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordMatchingUnique
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompactProductOriginalBracket
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricContractingBracket
import HolomorphicAnosov.Dynamics.Bowen.OriginalFactOneGivesCompactProductData
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricSplicingPartition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PositiveComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Compositions
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompositionList
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OverlapMultiplicity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Blocks
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CommonPoint
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetCondition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Alphabet
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetList
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetUnionCard
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetTotalLeOverlapMultiplicity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatching
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TupleMatching
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.Transition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneComposition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabel
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelBlock
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SingletonSymbol
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelSingletonSymbol
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SymbolLabelBijective
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NextTime
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SignedTraceSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingSingleton
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OneCompositionTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OverlapMultiplicityPos
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PartitionBoundary
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.DistinctRectanglesFrontier
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MemPartitionBoundaryOfDistinctLabels
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.AlphabetHasDistinctLabels
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPointsSubsetBoundary
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPointsSubsingleton
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdges
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdgesCons
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.EdgeMatrix
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatrixPowerPathSum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SnocTailNext
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PathEdgesCycle
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TraceEqCardCycles
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordCardEqTrace
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CappedMetric
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExistsCompatibleMetricPreservingFiniteEdist
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExistsComponentwiseLengthMetric
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExpansiveFiniteWindow
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueUniformTail
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueSmallStartAllSmall
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleBothPlaquesOnSmallPairs
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RectangleCoverExpansive
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ContinuousBracketDiagonalBuffer
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FactBracketOriginalMetricMembership
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalPlaqueIntersectionUnique
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SplicingOriginalRectangle
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StableSpliceImageEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.UnstableSpliceImageEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ProperRectanglesInteriorLabel
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SplicingOriginalMarkov
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SpliceAt
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RelatedCodesSameImage
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.NoCrossTransition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RestrictedIterateVal
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RestrictedZpowVal
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowNegCoe
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueHomeomorphPow
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.UnstablePlaqueHomeomorphPow
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.ExtendClosedPairBracket
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalRectanglesToPublicPartition
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RelativeToFactOneDatum
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalMetricProviderPremise
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantComplementSignPair
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FinitePeriodicPointsOfExpansive
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricExpansivity
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricMesh
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FiniteEdistConnectedComponent
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompactFiniteEdistBound
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.RelativeHyperbolicBasicSetG7
import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Manning's signed periodic trace formula for the original basic set

Source: Manning, Axiom A diffeomorphisms have rational zeta functions (1971),
Lemma 1 p.216, Lemma 2 p.217, ordered alphabets and matrices pp.217–218,
and cancellation theorem pp.218–219. Common-image-first periodic construction:
de Jong, ETDS46 (2026), §3.2 pp.2464–2465. Joint ordinary coding:
Bowen, Markov partitions and minimal sets for Axiom A diffeomorphisms (1970),
Proposition 10/Corollary 11 p.913 and Proposition 12 p.914, for one retained
source-constructed partition. No arbitrary-given-partition guard is a premise.
DAG node: `dynamics.manning_original_basic_set_signed_trace_g7`.
-/

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set
open scoped BigOperators ContDiff Manifold Bundle Classical

noncomputable section

/-- Arbitrarily fine proper Markov partitions of an original hyperbolic basic set
admit the exact signed periodic trace formula, with singleton matrix identification,
periodic common-image and unique-matching assertions, boundary correction support,
and uniform periodic fibre bound.

Sources: Manning1971 Lemmas1–2 pp.216–217, §3 pp.217–218 and §4 pp.218–219;
de Jong2026 §3.2 pp.2464–2465 common-image-first construction; Bowen1970,
Markov partitions and minimal sets, Proposition10/Corollary11 p.913 and
Proposition12 p.914. Partition existence uses Bowen1970, Markov partitions
for Axiom A diffeomorphisms, pp.725–747, through the named joint coding provider.

The only dynamical input is the actual `RelativeHyperbolicBasicSet` on the original
smooth map and metric. The proper partition, expansive bound and every finite matrix
are outputs. The ordered compositions and alphabets are actual Mathlib finite data;
empty alphabets have zero trace, and positive periods include smaller least periods.
The integer exponent in the sign is the number of ordered blocks plus one.
`periodicPhysicalPoints` is a relation, never a global tuple coding function. Its
singleton and matching uniqueness are conclusions only for positive cyclic words.
Singleton alphabet identification is the bijection `symbolLabel`, and the displayed
entry equality says its reindexing gives exactly the same `originalTransition P`.
The boundary assertion concerns only compositions different from `(1)`; the uniform
bound concerns every composition. No connected-rectangle or mixing assumption is added.

Complete source-following natural-language proof:
Step 1. Choose the proper fine partition and define all finite matrices
First apply the named compact hyperbolic Fact1 theorem to the original f and Λ, using its locally maximal hypothesis. It provides a compatible adapted metric d*, a positive closed-plaque radius γ, and the unique bracket intersection Wγ^s(x)∩Wγ^u(y) whenever d*(x,y)≤ε0. In particular [x,x]=x, since x belongs to both plaques. If d*(f^j x,f^j y)≤γ for every integer j, then y lies in both Wγ^s(x) and Wγ^u(x), so y=x. Thus γ is an expansive bound in d*. The identity from (Λ,d) to (Λ,d*) is continuous because both metrics induce the given compact topology. Apply the named compact uniform-continuity theorem and its metric modulus leaf to obtain δ>0 such that d(x,y)<δ implies d*(x,y)<γ. Put e=δ/2>0. If all integer orbit distances in d are ≤e, they are <δ, so the preceding d* expansivity gives x=y; hence e is an expansive bound for the original d. This is the same source plaque-uniqueness expansivity argument used in Bowen’s coding proof, with the compatible-metric transfer expanded explicitly. In the executable proof, an initial arbitrary coding family supplies the same adapted expansivity consequence from diagonal rectangle uniqueness. Its rectangles are then discarded. Restrict the continuous contracting Fact1 bracket to a positive original close-pair radius at plaque radius e/4, using compact metric comparison; original expansivity proves its uniqueness. Only after these scales are fixed, request a final coding family with mesh smaller than η, e/2 and the bracket close radius, and with splice errors small enough to transfer to original closed e/4 plaques. The public splice transfer proves original-metric rectangle and Markov laws. The public carrier constructor supplies the proper original-metric partition with this bracket and these final rectangles. Retain this final single existential tuple (N,D,R_1,…,R_N,T,π) for all counting: T is its B transition matrix, mesh<η and mesh<e/2. For these exact R,T,π the provider gives onto coding, covariance, fibre bound D, every-label equality at every integer coordinate, periodicity of codes over periodic points and single-coordinate rigidity over such a point. No partition or coding map is selected after this final tuple. The finite covering index set is nonempty, so q≥1; q is a maximum because there are finitely many label subsets. Define the finite ordered-disjoint alphabets and matching matrices literally as in the statement. A_ι may be empty, giving trace0. For (1) the alphabet consists of singleton label sets and its matrix is exactly T.

Step 2. Related codes and the no-cross-transition lemma at a periodic fibre
Codes a^1,…,a^r whose rectangles at each integer time have a common point have equal images: each pair of physical iterates is at distance less than e because the two mesh<e/2 rectangles meet, so original-distance e-expansivity forces equality. Indeed a point in the two rectangles gives the triangle bound d(f^jπ(a),f^jπ(b))≤diam(R_(a_j))+diam(R_(b_j))<e at every j. In a periodic fibre of this retained π, distinct codes have distinct coordinate labels at every time by its joint single-coordinate rigidity conclusion. Each code is periodic by that same provider, so finitely many codes have a common positive period ℓ. If a T-edge joined a_j^h to a_(j+1)^t for h≠t, splice the past of a^h to the future of a^t at j+sℓ for every integer s. Each splice is legal, has the common physical image by the related-rectangle argument, and the splices are distinct because the two original codes disagree at every coordinate. This contradicts the uniform finite fibre bound. Therefore the only edges between the current and next labels of a periodic fibre are those following its own codes. This is Manning Lemma2. The exact prerequisite locators are Bowen, Markov partitions and minimal sets for Axiom A diffeomorphisms, Proposition 10 and Corollary 11 p. 913 and Proposition 12 p. 914. Proposition 12 is stated over Φ(a,b), the set on which both geometric rank tuples are constant along every iterate; periodic physical orbits lie in such a set because the rank monotonicity of Proposition 8 returns to its initial value around the period. Thus its use here is restricted to an already identified periodic fibre. Every uniform fibre bound and rigidity invocation in this step concerns the tuple retained in step1; the open arbitrary-partition variant is not used.

Step 3. Construct the periodic tuple image before proving unique matching, following de Jong
Use the written common-image-first construction in de Jong §3.2, printed pp.2464–2465 (PDF13–14), with the ordinary coding and joint finite-fibre conclusions of the single witness retained in step1. Fix a period-m B_ι word S(n)=(S_1(n),…,S_k(n)), n∈Z, and put r=|ι| and U(n)=⋃_j S_j(n). These are vertices of de Jong’s unordered r-set graph G_r: every union has r distinct labels with a common rectangle point. Every tuple edge has a union perfect T-matching, by taking the union of its disjoint block bijections; thus U(n)→U(n+1) is an edge of G_r. Choose any such block matchings at every integer time. They need not repeat with period m, and uniqueness is not assumed. Following the chosen bijections forwards and their inverses backwards from the r labels of U(0) gives r ordinary admissible codes a^1,…,a^r. At each n their coordinate labels are exactly U(n), so they are mutually separated and related. This is the explicit elementary following-bijections expansion of de Jong’s p2464 correspondence to ordinary codes. Manning Lemma1, with its mesh/expansivity calculation already given above, proves that all r codes have one physical image z. This establishes the image before applying any periodic no-cross assertion. The same comparison handles every alternative matching system: each code from either choice has its coordinate-n label in U(n); hence its rectangle intersects every rectangle occurring in the other choice at that time. Manning Lemma1’s pairwise distance/expansivity proof therefore gives the same z for both choices. This comparison of arbitrary choices is an elementary consequence of the published related-code calculation; de Jong does not separately spell it out. Finally U(n+m)=U(n), so each shifted code σ^m a^h is related at every coordinate to the original codes. The same calculation and the ordinary coding relation πσ^m=f^mπ give f^m z=z. This is the periodic specialization of de Jong’s displayed factor relation at the top of p2465; it uses no finite-order permutation or cyclic-word expansion. Only now use the retained joint coding provider’s periodic-fibre conclusion: every a^h over the periodic physical z is periodic, and the r codes are distinct. The preceding written Manning Lemma2 argument thus applies with all its hypotheses established. It forbids each off-diagonal T-edge from a^h_n to a^t_(n+1), h≠t, leaving exactly the r chosen edges between U(n) and U(n+1). Consequently every permitted union matching, and hence every permitted block matching, equals the chosen matching at that time. Following these forced edges fixes the ordinary code belonging to each initial label, independently of all matching choices. This supplies precisely the cycle-only conclusion of de Jong Remark3.9 p2465 via the already written Manning Lemma2 proof p217; the remark’s compressed assertion that an ambiguous edge on a cycle contradicts Proposition3.8(B) is not a replacement proof of the lower no-diamonds property. The block division is retained by restriction of the unique union matching, since the original block matchings exist. Therefore the counted period-m ordered-disjoint-block words have a well-defined periodic image and choice-independent matchings. No global single-valued tuple coding theorem, or global uniqueness for transient edges, is asserted.
Source location: de Jong, On sets of periodic orbit lengths in finitely presented dynamical systems, ETDS46(2026),2452–2484, §3.1 Proposition3.8(A),(B) p2463; §3.2 unordered-set graph and related-code image construction p2464, factor relation and Remark3.9 p2465. Manning1971 Lemma1p216 and full written Lemma2 proof p217.

Step 4. Count exactly one net contribution from every period-m physical point
Let f^m z=z and let its finite full fibre have r codes. It is nonempty, and the retained provider makes coordinate evaluation a bijection to Set(f^j z)={i:f^j z∈R_i} at every integer j. These labels have the common point f^j z, so r≤q. The permutation σ^m of this fibre need not be identity. A period-m tuple word over z is exactly an ordered family of pairwise disjoint subsets of the fibre, of sizes i_1,…,i_k, each invariant under that permutation; its symbols at timej are their coordinate-j rectangle-label sets. For completeness, in the forward direction each tuple block is followed by its forced T-matching to a set of ordinary codes over z; the block-size condition holds because their labels differ at every coordinate. Periodicity of the word says exactly that its zero-coordinate code subset is invariant under σ^m, since coordinate evaluation is injective and the forced edges identify its continuations. Conversely any ordered disjoint family of σ^m-invariant subsets yields the displayed label blocks at every integer j. These symbols are admissible: all labels contain f^j z, and each code contributes its legal next edge, furnishing the required block bijections. They repeat after m by invariance. Thus these two constructions are inverse, using only the no-cross lemma and the retained coordinate bijections, not equality of code period and physical period. For |ι|<r append the nonempty complement of the union as a last block. It is invariant under σ^m, giving a word of composition (i_1,…,i_k,r−|ι|) with total size r and at least two blocks. Deleting the last block is the inverse operation. Their signs are opposite, so all such contributions cancel. The remaining total-size-r one-block composition(r) has exactly the full fibre as its block and contributes+1. Compositions |ι|>r contribute0. The number for any fixed composition is at most (k+1)^r≤(q+1)^q, by assigning each of r fibre codes either to one of k blocks or to the unused complement.

Step 5. Finiteness, matrix traces and boundary support
Each z fixed by f^m yields its full-fibre one-block word, so there are finitely many such z because there are finitely many m-periodic words in the finitely many finite alphabets, and equal full-fibre words have the same common image by step3. There are finitely many positive compositions of total size≤q, so the number of alphabets is finite. Expand matrix multiplication inductively: (B^m)_(v,v) is the sum over length-m paths from v back to v of the product of edge entries. For a zero-one matrix each nonzero product is1, so summing the diagonal counts exactly the m-periodic labeled words, including words whose least period divides m. The exact Matrix.trace leaf is this diagonal sum. Sum the previous cancellation identity over these finitely many physical points to obtain the signed trace formula. For ι≠(1), |ι|≥2, so its common physical image has at least two distinct rectangle labels at time0. Because the partition is proper with disjoint relative interiors, their intersection lies in their relative frontiers. Explicitly, a point of R_i∩R_j in int_ΛR_i would, by R_j=closure(int_ΛR_j), have every sufficiently small neighborhood inside int_ΛR_i meet int_ΛR_j, contradicting disjoint interiors. Both rectangles are closed, so failure to belong to their interiors is precisely frontier membership. This proves correction support in ∂R; it does not imply boundary measure zero or a strict growth-rate gap.
-/
theorem manning_original_basic_set_signed_trace
    {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (f : Diffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Λ : Set M) (hΛ : RelativeHyperbolicBasicSet f Λ)
    (η : ℝ) (hη : 0 < η) :
    ∃ (P : ProperRelativeMarkovPartition f.toHomeomorph Λ) (e : ℝ),
      0 < e ∧
      (∀ x y : Λ,
        (∀ j : ℤ, dist ((P.onSet.toEquiv ^ j) x) ((P.onSet.toEquiv ^ j) y) ≤ e) →
        x = y) ∧
      (∀ i, Metric.diam (P.rectangles i) < η ∧ Metric.diam (P.rectangles i) < e / 2) ∧
      1 ≤ overlapMultiplicity P.rectangles ∧
      Function.Bijective (symbolLabel P.rectangles) ∧
      (∀ s t : Alphabet P.rectangles oneComposition,
        transition P.rectangles (originalTransition P) oneComposition s t =
          originalTransition P (symbolLabel P.rectangles s) (symbolLabel P.rectangles t)) ∧
      (∀ (m : ℕ) (hm : 0 < m),
        Set.Finite {x : Λ | ((P.onSet : Λ → Λ)^[m]) x = x} ∧
        (Nat.card {x : Λ // ((P.onSet : Λ → Λ)^[m]) x = x} : ℤ) =
          signedTraceSum P.rectangles (originalTransition P)
            (overlapMultiplicity P.rectangles) m ∧
        ∀ c : PositiveComposition (overlapMultiplicity P.rectangles),
          (Nat.card (PeriodicWord P.rectangles (originalTransition P) c.2 hm) : ℤ) =
            Matrix.trace (transition P.rectangles (originalTransition P) c.2 ^ m) ∧
          (∀ w : PeriodicWord P.rectangles (originalTransition P) c.2 hm,
            ∃! x : Λ, x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
              c.2 P.onSet hm w) ∧
          (∀ (w : PeriodicWord P.rectangles (originalTransition P) c.2 hm)
            (t : Fin m) (k : Fin c.2.length),
            ∃! a : ↥((w.val t).val k) ≃ ↥((w.val (nextTime hm t)).val k),
              ∀ i, originalTransition P i.val (a i).val = 1) ∧
          (c.2.blocks ≠ [1] →
            ∀ (w : PeriodicWord P.rectangles (originalTransition P) c.2 hm) (x : Λ),
              x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
                c.2 P.onSet hm w → x ∈ partitionBoundary P) ∧
          (∀ x : Λ,
            Nat.card {w : PeriodicWord P.rectangles (originalTransition P) c.2 hm //
              x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
                c.2 P.onSet hm w} ≤
              (overlapMultiplicity P.rectangles + 1) ^ overlapMultiplicity P.rectangles)) := by
  -- The residual source argument constructs one joint Bowen partition/coding,
  -- then applies de Jong's periodic image and Manning's fibre cancellation.
  suffices hcore :
      ∃ (P : ProperRelativeMarkovPartition f.toHomeomorph Λ) (e : ℝ),
        0 < e ∧
        (∀ x y : Λ,
          (∀ j : ℤ, dist ((P.onSet.toEquiv ^ j) x) ((P.onSet.toEquiv ^ j) y) ≤ e) →
          x = y) ∧
        (∀ i, Metric.diam (P.rectangles i) < η ∧
          Metric.diam (P.rectangles i) < e / 2) ∧
        ∀ (m : ℕ) (hm : 0 < m),
          (Nat.card {x : Λ // ((P.onSet : Λ → Λ)^[m]) x = x} : ℤ) =
            signedTraceSum P.rectangles (originalTransition P)
              (overlapMultiplicity P.rectangles) m ∧
          ∀ c : PositiveComposition (overlapMultiplicity P.rectangles),
            (∀ w : PeriodicWord P.rectangles (originalTransition P) c.2 hm,
              ∃ x : Λ, x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
                c.2 P.onSet hm w) ∧
            (∀ (w : PeriodicWord P.rectangles (originalTransition P) c.2 hm)
              (t : Fin m) (k : Fin c.2.length),
              ∃! a : ↥((w.val t).val k) ≃ ↥((w.val (nextTime hm t)).val k),
                ∀ i, originalTransition P i.val (a i).val = 1) ∧
            (∀ x : Λ,
              Nat.card {w : PeriodicWord P.rectangles (originalTransition P) c.2 hm //
                x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
                  c.2 P.onSet hm w} ≤
                (overlapMultiplicity P.rectangles + 1) ^ overlapMultiplicity P.rectangles) by
    obtain ⟨P, e, he, hexp, hsmall, hperiod⟩ := hcore
    let : CompactSpace Λ := isCompact_iff_compactSpace.mp P.compact
    refine ⟨P, e, he, hexp, hsmall,
      overlapMultiplicity_pos P.rectangles P.nonempty.to_subtype P.cover,
      symbolLabel_bijective P.rectangles P.rectangles_nonempty,
      oneComposition_transition P, ?_⟩
    intro m hm
    obtain ⟨hcount, hwords⟩ := hperiod m hm
    refine ⟨finite_periodicPoints_of_expansive P.onSet he hexp hm, hcount, ?_⟩
    intro c
    obtain ⟨himage, hmatching, hbound⟩ := hwords c
    refine ⟨periodicWord_card_eq_trace P.rectangles (originalTransition P) c.2 hm,
      ?_, hmatching, ?_, hbound⟩
    · intro w
      obtain ⟨x, hx⟩ := himage w
      refine ⟨x, hx, ?_⟩
      intro y hy
      exact periodicPhysicalPoints_subsingleton P e hexp
        (fun i ↦ (hsmall i).2.trans (half_lt_self he)) c.2 hm w hy hx
    · intro hc w x hx
      exact periodicPhysicalPoints_subset_boundary P c.2 hc hm w hx
  let : Bundle.RiemannianBundle
    (fun x : M => TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
    ⟨hΛ.metric.toRiemannianMetric⟩
  obtain ⟨Hdatum, hdatumMetric⟩ := relative_to_factOneDatum f Λ hΛ
  have hinv : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ := fun x ↦ (hΛ.invariant x).symm
  have htransOriginal := hΛ.transitive
  let originalMetricM : MetricSpace M := inferInstance
  let originalMetricΛ : MetricSpace Λ := inferInstance
  have originalCompactΛ : CompactSpace Λ := isCompact_iff_compactSpace.mp Hdatum.compact
  let tMBowen : TopologicalSpace M := inferInstance
  obtain ⟨dBowen, htopBowen, hmetric⟩ :=
    original_metric_provider_premise (tM := tMBowen) hΛ.metric
  let bowenMetricM : MetricSpace M :=
    @MetricSpace.replaceTopology M tMBowen dBowen htopBowen.symm
  let stable : ∀ x : M, Submodule ℝ (TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) := fun x ↦
    if hx : x ∈ Λ then Hdatum.stable.fibre ⟨x, hx⟩ else ⊥
  let unstable : ∀ x : M, Submodule ℝ (TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) := fun x ↦
    if hx : x ∈ Λ then Hdatum.unstable.fibre ⟨x, hx⟩ else ⊥
  have hstable_eq : (fun x : Λ ↦ stable x.val) = Hdatum.stable.fibre := by
    funext x
    simp only [stable, dite_eq_left x.property]
  have hunstable_eq : (fun x : Λ ↦ unstable x.val) = Hdatum.unstable.fibre := by
    funext x
    simp only [unstable, dite_eq_left x.property]
  have hstablec : BowenBasicSetCoding.IsContinuousDistributionOn Λ stable := by
    unfold BowenBasicSetCoding.IsContinuousDistributionOn
    have hh := Hdatum.stable.locally_trivial
    rw [← hstable_eq] at hh
    exact hh
  have hunstablec : BowenBasicSetCoding.IsContinuousDistributionOn Λ unstable := by
    unfold BowenBasicSetCoding.IsContinuousDistributionOn
    have hh := Hdatum.unstable.locally_trivial
    rw [← hunstable_eq] at hh
    exact hh
  have hcompl : ∀ x ∈ Λ, IsCompl (stable x) (unstable x) := by
    intro x hx
    simpa only [stable, unstable, dite_eq_left hx] using Hdatum.complementary ⟨x, hx⟩
  have hstableinv : ∀ x ∈ Λ,
      (stable x).map (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) f x).toLinearMap = stable (f x) := by
    intro x hx
    simpa only [stable, dite_eq_left hx, dite_eq_left (Hdatum.forward_mem hx)] using
      Hdatum.stable_invariant ⟨x, hx⟩
  have hunstableinv : ∀ x ∈ Λ,
      (unstable x).map (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) f x).toLinearMap = unstable (f x) := by
    intro x hx
    simpa only [unstable, dite_eq_left hx, dite_eq_left (Hdatum.forward_mem hx)] using
      Hdatum.unstable_invariant ⟨x, hx⟩
  have hnorm : ∀ {x : M} (v : TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x),
      hyperbolicRiemannianNorm Hdatum.originalMetric v = ‖v‖ := by
    intro x v
    rw [hdatumMetric]
    exact (norm_eq_sqrt_real_inner v).symm
  have hstablebound : ∀ (k : ℕ) (x : M), x ∈ Λ → ∀ v ∈ stable x,
      ‖mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((f : M → M)^[k]) x v‖ ≤
        Hdatum.C * Hdatum.rate ^ k * ‖v‖ := by
    intro k x hx v hv
    have hh := Hdatum.stable_estimate k ⟨x, hx⟩ v
      (by simpa only [stable, dite_eq_left hx] using hv)
    simpa only [hnorm] using hh
  have hunstablebound : ∀ (k : ℕ) (x : M), x ∈ Λ → ∀ v ∈ unstable x,
      ‖mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((f.symm : M → M)^[k]) x v‖ ≤
        Hdatum.C * Hdatum.rate ^ k * ‖v‖ := by
    intro k x hx v hv
    have hh := Hdatum.unstable_estimate k ⟨x, hx⟩ v
      (by simpa only [unstable, dite_eq_left hx] using hv)
    simpa only [hnorm] using hh
  have hlocal : ∃ U : Set M, IsOpen U ∧ Λ ⊆ U ∧
      Λ = ⋂ j : ℤ, ((f.toHomeomorph ^ j : M ≃ₜ M) : M → M) '' U := by
    refine ⟨Hdatum.isolatingNeighborhood, Hdatum.isolating_open,
      Hdatum.subset_isolating, ?_⟩
    ext x
    rw [Hdatum.locally_maximal]
    simp only [mem_iInter]
    constructor
    · intro hx j
      refine ⟨(f.toHomeomorph ^ (-j)) x, hx (-j), ?_⟩
      rw [← Homeomorph.mul_apply, ← zpow_add]
      simp
    · intro hx j
      obtain ⟨y, hy, heq⟩ := hx (-j)
      change (f.toHomeomorph ^ j) x ∈ Hdatum.isolatingNeighborhood
      rw [← heq, ← Homeomorph.mul_apply, ← zpow_add]
      simpa using hy
  let F := BowenBasicSetCoding.restrictedDynamics f.toHomeomorph Λ hinv
  have htrans :
      ∀ U V : Set Λ, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ k : ℕ, (((F ^ k : Λ ≃ₜ Λ) : Λ → Λ) '' U ∩ V).Nonempty := by
    intro U V hU hUne hV hVne
    obtain ⟨k, x, hxU, hfxV⟩ := htransOriginal U V hU hV hUne hVne
    refine ⟨k, (F ^ k) x, ⟨x, hxU, rfl⟩, ?_⟩
    obtain ⟨v, hv, hvx⟩ := hfxV
    have hpower : ((F ^ k) x).val = ((f : M → M)^[k]) x.val := by
      change (((f.toHomeomorph.subtype hinv) ^ k) x).val = _
      have h := CarrierAdapter.restricted_iterate_val f.toHomeomorph Λ hinv x k
      simpa only [CarrierAdapter.homeomorph_pow_coe, Diffeomorph.coe_toHomeomorph] using h
    have hv' : v = (F ^ k) x := Subtype.ext (hvx.trans hpower.symm)
    exact hv' ▸ hv
  have hprovider :=
    BowenBasicSetCoding.hyperbolic_basic_set_markov_coding
      (E := EuclideanSpace ℝ (Fin n)) (M := M) f hmetric
      Λ Hdatum.nonempty Hdatum.compact hinv stable unstable hstablec hunstablec hcompl
      hstableinv hunstableinv
      Hdatum.C Hdatum.rate Hdatum.one_le_C Hdatum.rate_pos Hdatum.rate_lt_one
      hstablebound hunstablebound hlocal htrans
  obtain ⟨N₁, D₁, hN₁, hD₁, δ₁, hδ₁top, γ₁, hγ₁, R₁, hrect₁, hdisj₁,
      hcover₁, hmarkov₁, coding₁, hcode₁, hcont₁, honto₁, hcov₁, hfibre₁,
      hlabel₁, hperiodic₁, hsplice₁⟩ :=
    hprovider 1 zero_lt_one
  have hcoverOrig : ∀ x : Λ, ∃ i, x ∈ R₁ i := by
    intro x
    have hx : x ∈ ⋃ i, R₁ i := by rw [hcover₁]; exact mem_univ x
    exact Set.mem_iUnion.mp hx
  let : MetricSpace Λ := originalMetricΛ
  have hexpAdapted : ∀ x y : Λ,
      (∀ j : ℤ, δ₁.dist ((F ^ j) x) ((F ^ j) y) ≤ γ₁) → x = y := by
    intro x y hxy
    obtain ⟨i, hxi⟩ := hcoverOrig x
    obtain ⟨z, hz, hunique⟩ := (hrect₁ i).1.2.2.2 x hxi x hxi
    have hxz : x = z := (hunique x).mp (by
      constructor <;> intro k <;> simpa only [δ₁.dist_self] using hγ₁.le)
    have hyz : y = z := (hunique y).mp (by
      constructor
      · intro k
        simpa only [zpow_natCast, δ₁.dist_comm] using hxy (k : ℤ)
      · intro k
        simpa only [δ₁.dist_comm] using hxy (-(k : ℤ)))
    exact hxz.trans hyz.symm
  have hcompactAdapted : @CompactSpace Λ δ₁.toUniformSpace.toTopologicalSpace :=
    hδ₁top.symm ▸ originalCompactΛ
  obtain ⟨expScale, hexpScale, hexpModulus⟩ :=
    @MetricAdapter.compatible_metric_modulus Λ δ₁ hcompactAdapted
      originalMetricΛ hδ₁top.symm γ₁ hγ₁
  have hexpOrig : ∀ x y : Λ,
      (∀ j : ℤ, originalMetricΛ.dist ((F ^ j) x) ((F ^ j) y) ≤ expScale / 2) →
        x = y := by
    intro x y hxy
    apply hexpAdapted x y
    intro j
    exact (hexpModulus _ _ ((hxy j).trans_lt (half_lt_self hexpScale))).le
  have hbracketOrig : ∃ ε > 0,
      ∃ B : {p : Λ × Λ // originalMetricΛ.dist p.1 p.2 ≤ ε} → Λ,
      Continuous B ∧
      (∀ p, (∀ n : ℕ, originalMetricΛ.dist ((F ^ (n : ℤ)) (B p))
          ((F ^ (n : ℤ)) p.val.1) ≤ expScale / 8) ∧
        (∀ n : ℕ, originalMetricΛ.dist ((F ^ (-(n : ℤ))) (B p))
          ((F ^ (-(n : ℤ))) p.val.2) ≤ expScale / 8)) ∧
      (∀ p z, (∀ n : ℕ, originalMetricΛ.dist ((F ^ (n : ℤ)) z)
          ((F ^ (n : ℤ)) p.val.1) ≤ expScale / 8) →
        (∀ n : ℕ, originalMetricΛ.dist ((F ^ (-(n : ℤ))) z)
          ((F ^ (-(n : ℤ))) p.val.2) ≤ expScale / 8) → z = B p) := by
    obtain ⟨d, ht, κ, γ, ⟨prod⟩⟩ :=
      BowenBasicSetCoding.original_factOne_gives_compact_product_data f Λ Hdatum hinv
    let : MetricSpace M := d.replaceTopology ht.symm
    let : MetricSpace Λ := @Subtype.metricSpace M (fun x ↦ x ∈ Λ) (d.replaceTopology ht.symm)
    let : CompactSpace Λ := originalCompactΛ
    exact MetricAdapter.compact_product_original_bracket F prod originalMetricΛ rfl
      (by positivity) (by linarith) hexpOrig
  obtain ⟨closeRadius, hcloseRadius, bracket, hbracketCont, hbracketMem, hbracketUnique⟩ := hbracketOrig
  -- The first coding family supplies an expansive bound; now request a family
  -- whose mesh and splice errors are chosen after that bound is fixed.
  have hsmallPositive : 0 < min η (min (expScale / 4) (closeRadius / 2)) :=
    lt_min hη (lt_min (by positivity) (by positivity))
  obtain ⟨mesh₂, hmesh₂, hmeshTransfer₂⟩ :=
    @MetricAdapter.compatible_metric_mesh Λ originalMetricΛ originalCompactΛ
      (@Subtype.metricSpace M (fun x ↦ x ∈ Λ) bowenMetricM) rfl (min η (min (expScale / 4) (closeRadius / 2))) hsmallPositive
  obtain ⟨splice₂, hsplice₂, htransfer₂⟩ :=
    @MetricAdapter.compatible_metric_splicing_partition Λ originalMetricΛ originalCompactΛ
      (@Subtype.metricSpace M (fun x ↦ x ∈ Λ) bowenMetricM) rfl F
      (expScale / 2) (expScale / 8) (by positivity) (by linarith) hexpOrig
  obtain ⟨N₂, D₂, hN₂, hD₂, δ₂, hδ₂top, γ₂, hγ₂, R₂, hrect₂, hdisj₂,
      hcover₂, hmarkov₂, coding₂, hcode₂, hcont₂, honto₂, hcov₂, hfibre₂,
      hlabel₂, hperiodic₂, hspliceCode₂⟩ :=
    hprovider (min mesh₂ splice₂) (lt_min hmesh₂ hsplice₂)
  have hmeshOrig₂ : ∀ i, @Metric.diam Λ originalMetricΛ.toPseudoMetricSpace (R₂ i) < η ∧
      @Metric.diam Λ originalMetricΛ.toPseudoMetricSpace (R₂ i) < (expScale / 2) / 2 := by
    intro i
    have hm := hmeshTransfer₂ (R₂ i) ((hrect₂ i).2.trans_le (min_le_left _ _))
    refine ⟨hm.trans_le (min_le_left _ _), ?_⟩
    have hh := (hm.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    linarith
  have horbit₂ : ∀ a : BowenBasicSetCoding.CodeSpace
      (BowenBasicSetCoding.transition F R₂), ∀ j : ℤ,
      (F ^ j) (coding₂ a) ∈ R₂ (a.val j) := by
    intro a
    have hmem : coding₂ a ∈ {x : Λ | ∀ j : ℤ, (F ^ j) x ∈ R₂ (a.val j)} := by
      rw [hcode₂ a]
      exact Set.mem_singleton _
    exact hmem
  have hlabelZero₂ : ∀ x i, x ∈ R₂ i →
      ∃ a : BowenBasicSetCoding.CodeSpace (BowenBasicSetCoding.transition F R₂),
        coding₂ a = x ∧ a.val 0 = i := by
    intro x i hx
    exact (hlabel₂ x 0 i).mp (by simpa using hx)
  obtain ⟨hrectOriginal₂, hmarkovOriginal₂⟩ := htransfer₂ N₂ R₂
    (BowenBasicSetCoding.transition F R₂) coding₂
    (fun i ↦ ⟨(hrect₂ i).1.1, (hrect₂ i).1.2.1, (hrect₂ i).1.2.2.1⟩)
    hdisj₂ horbit₂ hlabelZero₂ (by
      intro a d had
      obtain ⟨c, hp, hf, hs, hu⟩ := hspliceCode₂ a d had
      exact ⟨c, hp, hf, fun j hj ↦ (hs j hj).trans_le (min_le_right _ _),
        fun j hj ↦ (hu j hj).trans_le (min_le_right _ _)⟩)
  let : MetricSpace M := originalMetricM
  let : MetricSpace Λ := originalMetricΛ
  let s := min η (min (expScale / 4) (closeRadius / 2))
  have hsclose : s ≤ closeRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (half_le_self hcloseRadius.le))
  have hsmall₂ : ∀ i, Metric.diam (R₂ i) ≤ s := by
    intro i
    exact (hmeshTransfer₂ (R₂ i) ((hrect₂ i).2.trans_le (min_le_left _ _))).le
  have hbmem : ∀ p, bracket p ∈ relativeClosedStablePlaque F (expScale / 8) p.val.1 ∩
      relativeClosedUnstablePlaque F (expScale / 8) p.val.2 := by
    intro p
    simpa only [CarrierAdapter.stable_plaque_homeomorph_pow,
      CarrierAdapter.unstable_plaque_homeomorph_pow, Set.mem_inter_iff, Set.mem_ofPred_eq,
      zpow_natCast] using hbracketMem p
  have hbunique : ∀ p, ∀ z : Λ,
      z ∈ relativeClosedStablePlaque F (expScale / 8) p.val.1 ∩
      relativeClosedUnstablePlaque F (expScale / 8) p.val.2 → z = bracket p := by
    intro p z hz
    apply hbracketUnique p z
    · simpa only [CarrierAdapter.stable_plaque_homeomorph_pow, Set.mem_ofPred_eq,
        zpow_natCast] using hz.1
    · simpa only [CarrierAdapter.unstable_plaque_homeomorph_pow, Set.mem_ofPred_eq] using hz.2
  let P : ProperRelativeMarkovPartition f.toHomeomorph Λ :=
    CarrierAdapter.originalRectanglesToPublicPartition f.toHomeomorph Λ
      Hdatum.nonempty Hdatum.compact F (fun x ↦ rfl)
      (expScale / 8) closeRadius s (by positivity) hcloseRadius hsmallPositive hsclose
      bracket hbracketCont hbmem hbunique R₂
      (fun i ↦ ⟨(hrect₂ i).1.1, (hrect₂ i).1.2.1, (hrect₂ i).1.2.2.1⟩)
      hsmall₂ (by
        intro i x hx y hy
        obtain ⟨z, hz, hunique⟩ := (hrectOriginal₂ i).2.2.2 x hx y hy
        have hmem := (hunique z).mpr rfl
        refine ⟨z, hz, ?_⟩
        simpa only [CarrierAdapter.stable_plaque_homeomorph_pow,
          CarrierAdapter.unstable_plaque_homeomorph_pow, BowenBasicSetCoding.localStable,
          BowenBasicSetCoding.localUnstable, Set.mem_inter_iff, Set.mem_ofPred_eq] using hmem)
      (by
        intro x
        have hx : x ∈ ⋃ i, R₂ i := by rw [hcover₂]; exact Set.mem_univ x
        exact Set.mem_iUnion.mp hx)
      hdisj₂ (by
        simpa only [BowenBasicSetCoding.HasMarkovInclusions,
          BowenBasicSetCoding.stableSlice, BowenBasicSetCoding.unstableSlice,
          CarrierAdapter.stable_plaque_homeomorph_pow,
          CarrierAdapter.unstable_plaque_homeomorph_pow, BowenBasicSetCoding.localStable,
          BowenBasicSetCoding.localUnstable] using hmarkovOriginal₂)
  refine ⟨P, expScale / 2, by positivity, ?_, hmeshOrig₂, ?_⟩
  · intro x y hxy
    apply hexpOrig x y
    simpa only [P, CarrierAdapter.originalRectanglesToPublicPartition,
      ← CarrierAdapter.homeomorph_zpow_equiv, Homeomorph.coe_toEquiv] using hxy
  have hfibreQ : ∀ x : Λ, (∃ m : ℕ, 0 < m ∧ (F ^ m) x = x) →
      Nat.card {a : BowenBasicSetCoding.CodeSpace (BowenBasicSetCoding.transition F R₂) //
        coding₂ a = x} ≤ overlapMultiplicity R₂ := by
    intro x hx
    exact CodingAdapter.coding_fibre_card_le_overlapMultiplicity R₂
      (BowenBasicSetCoding.transition F R₂) coding₂ x
      (fun a ↦ by simpa using horbit₂ a 0) (hperiodic₂ x hx).2.1
  suffices hremaining : ∀ (m : ℕ) (hm : 0 < m),
      (Nat.card {x : Λ // ((P.onSet : Λ → Λ)^[m]) x = x} : ℤ) =
        signedTraceSum P.rectangles (originalTransition P) (overlapMultiplicity P.rectangles) m by
    intro m hm
    refine ⟨hremaining m hm, ?_⟩
    intro c
    have hbound : ∀ x : Λ,
        Nat.card {w : PeriodicWord P.rectangles (originalTransition P) c.2 hm //
          x ∈ periodicPhysicalPoints P.rectangles (originalTransition P) c.2 P.onSet hm w} ≤
            (overlapMultiplicity P.rectangles + 1) ^ overlapMultiplicity P.rectangles := by
      intro x
      apply CodingAdapter.periodicWord_fibre_bound_of_coding F R₂
        (BowenBasicSetCoding.transition F R₂) coding₂ (originalTransition P)
        (by
          intro i j
          change (if (F '' interior (R₂ i) ∩ interior (R₂ j)).Nonempty then (1 : ℤ) else 0) = 1 ↔ _
          simp only [BowenBasicSetCoding.transition]
          simp)
        hexpOrig (fun i ↦ (hmeshOrig₂ i).2) horbit₂ c.2 hm (by
          change c.1.val + 1 ≤ overlapMultiplicity P.rectangles
          exact Nat.succ_le_of_lt c.1.isLt) x
      · intro hx
        apply (hperiodic₂ x ?_).2.1
        exact ⟨m, hm, by simpa only [CarrierAdapter.homeomorph_pow_coe] using hx⟩
      · intro j i hi
        exact (hlabel₂ x j i).mp hi
    have himage : ∀ w : PeriodicWord P.rectangles (originalTransition P) c.2 hm,
        ∃ x : Λ, x ∈ periodicPhysicalPoints P.rectangles (originalTransition P)
          c.2 P.onSet hm w := by
      intro w
      apply CodingAdapter.periodicWord_physical_image_exists F R₂
        (BowenBasicSetCoding.transition F R₂) coding₂ (originalTransition P)
        (by
          intro i j
          change (if (F '' interior (R₂ i) ∩ interior (R₂ j)).Nonempty then (1 : ℤ) else 0) = 1 ↔ _
          simp only [BowenBasicSetCoding.transition]
          simp)
        (by positivity) hexpOrig (fun i ↦ (hmeshOrig₂ i).2) horbit₂ c.2 hm w
    refine ⟨himage, ?_, hbound⟩
    intro w t k
    obtain ⟨x, hx⟩ := himage w
    have hper : ∃ m : ℕ, 0 < m ∧ (F ^ m) x = x := by
      refine ⟨m, hm, ?_⟩
      simpa only [CarrierAdapter.homeomorph_pow_coe, P,
        CarrierAdapter.originalRectanglesToPublicPartition] using hx.1
    apply CodingAdapter.periodicWord_matching_unique F R₂
      (BowenBasicSetCoding.transition F R₂) coding₂ (originalTransition P)
      (by
        intro i j
        change (if (F '' interior (R₂ i) ∩ interior (R₂ j)).Nonempty then (1 : ℤ) else 0) = 1 ↔ _
        simp only [BowenBasicSetCoding.transition]
        simp)
      hexpOrig (fun i ↦ (hmeshOrig₂ i).2) horbit₂ c.2 hm w hx
      (hperiodic₂ x hper).2.1 (fun j i hi ↦ (hlabel₂ x j i).mp hi) t k
  intro m hm
  have hT : ∀ i j, originalTransition P i j = 1 ↔
      BowenBasicSetCoding.transition F R₂ i j := by
    intro i j
    change (if (F '' interior (R₂ i) ∩ interior (R₂ j)).Nonempty then (1 : ℤ) else 0) = 1 ↔ _
    simp only [BowenBasicSetCoding.transition]
    simp
  apply signedTrace_of_physical_fibre_counts P.onSet P.rectangles (originalTransition P) hm
  · apply finite_periodicPoints_of_expansive P.onSet (e := expScale / 2)
      (by positivity) ?_ hm
    intro x y hxy
    apply hexpOrig x y
    simpa only [P, CarrierAdapter.originalRectanglesToPublicPartition,
      ← CarrierAdapter.homeomorph_zpow_equiv, Homeomorph.coe_toEquiv] using hxy
  · intro c w
    exact CodingAdapter.periodicWord_physical_image_exists F R₂
      (BowenBasicSetCoding.transition F R₂) coding₂ (originalTransition P) hT
      (by positivity) hexpOrig (fun i ↦ (hmeshOrig₂ i).2) horbit₂ c.2 hm w
  · intro c w
    apply periodicPhysicalPoints_subsingleton P (expScale / 2)
      (fun x y hxy ↦ hexpOrig x y (by
        simpa only [P, CarrierAdapter.originalRectanglesToPublicPartition,
          ← CarrierAdapter.homeomorph_zpow_equiv, Homeomorph.coe_toEquiv] using hxy))
      (fun i ↦ (hmeshOrig₂ i).2.trans (half_lt_self (by positivity))) c.2 hm w
  · intro x hx
    have hper : ∃ m : ℕ, 0 < m ∧ (F ^ m) x = x := by
      refine ⟨m, hm, ?_⟩
      simpa only [CarrierAdapter.homeomorph_pow_coe, P,
        CarrierAdapter.originalRectanglesToPublicPartition] using hx
    exact CodingAdapter.coding_local_signed_count F R₂
      (BowenBasicSetCoding.transition F R₂) coding₂ (originalTransition P) hT
      hexpOrig (fun i ↦ (hmeshOrig₂ i).2) horbit₂ hm x hx (honto₂ x)
      (hperiodic₂ x hper).2.1 (fun j i hi ↦ (hlabel₂ x j i).mp hi) (hfibreQ x hper)

end

end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7


