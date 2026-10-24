# Small acyclic complex foundations

This family develops the small acyclic subcomplex input to the single
transfinite K-injective replacement route. It does not construct an exhaustive
acyclic filtration or a K-injective replacement.

- [EpiLifting](EpiLifting.lean) proves
  `Subobject.hasCardinalLT_of_epi` by the native subobject/quotient duality.
  For a separator `G` and an epimorphism `p : M ⟶ N`,
  `exists_epi_comp_from_subobject_coproduct` constructs an actual map
  from the coproduct of `G` indexed by `Shrink.{w} (Subobject N)` into `M`
  whose composite with `p` is epi. Its image is a subobject of `M` that
  still covers `N`; `exists_subobject_epi_of_subobject_coproduct_bound`
  transfers a strict subobject-cardinality bound from this coproduct to
  that image. The separator need not be projective.
- [SizeBound](SizeBound.lean) proves
  `exists_regular_cardinal_lifting_bound`: given `κ : Cardinal.{w}`, one
  regular `μ : Cardinal.{w}` works uniformly for every epimorphism onto
  an object with at most `κ` subobjects. The bound comes from the native
  subobject set of the coproduct of `κ.out` copies of `G`. Enlarging the
  index set uses a native monomorphism of coproducts.

- [ExactStep](ExactStep.lean) proves
  `exists_regular_cardinal_exact_step`: one regular bound works for every
  exact native short complex and every restricted second differential
  `δ : A ⟶ B` with a monomorphism from `A` into its middle term. It
  constructs an actual monomorphism into the first ambient term and an
  epimorphism onto `kernel δ`, preserving the original differential
  equation. The resulting restricted short complex is exact. The proof
  pulls back the ambient epimorphism onto cycles and applies `SizeBound`.

- [CardinalLadder](CardinalLadder.lean) chooses the proved exact-step cardinal
  operation, iterates it from a bound on the separator, and constructs a
  single regular cardinal above every entry of that countable ladder.
- [AdjacentPair](AdjacentPair.lean) constructs compatible pairs of terms
  inside an actual natural-number chain complex. Its successor retains the
  previous left term and inclusion literally as the new right term and
  inclusion, and proves exactness of the resulting two differentials.
- [Countable](Countable.lean) assembles those pairs using `ChainComplex.of`.
  It gives an actual acyclic complex, a termwise monic chain map into an
  ambient complex exact in positive degrees, the common cardinal bound,
  and a factorization of the specified separator map in degree one.
- [Cochain](Cochain.lean) transports the countable construction through
  the native `truncLE'` and `extend` constructions. Its
  `CochainComplex.exists_small_acyclic_subcomplex` retains the original
  separator map into degree `n`, a termwise monic map into the original
  acyclic integer complex, acyclicity, support in degrees at most `n + 1`,
  and the uniform bound on every term.

- [ObjectRepresentatives](ObjectRepresentatives.lean) proves that every object
  with at most `κ` subobjects is a quotient of a fixed coproduct of `κ.out`
  copies of the separator. Its opposite-category subobjects provide an actual
  `Type w` family representing all such objects up to native isomorphism.

- [ComplexRepresentatives](ComplexRepresentatives.lean) encodes the term labels,
  shrunk differential morphisms, and complex equations in `Type w`. It decodes
  to native cochain complexes and constructs termwise-conjugation isomorphisms,
  giving actual small representatives for all termwise bounded complexes.

- [Family](Family.lean) filters the actual small complex codes by acyclicity,
  bounded-above support and the common term-size bound. Every separator map
  into an acyclic complex factors through a termwise monic map from a member
  of this family. No K-injective detection property is assumed.

- [ChosenFamily](ChosenFamily.lean) fixes the index and native objects supplied
  by the proved existence theorem, exposing their acyclicity, support, size,
  and factorization properties for a single family shared by all stages.

- [ShiftFamily](ShiftFamily.lean) exposes the one final family
  `smallAcyclicTests`, indexed by the chosen family index times `ℤ`. Its
  native shift-zero and shift-add isomorphisms make every source shift
  explicit, so replacement and detection can share one family without
  inferring full Hom-complex acyclicity from degree-zero vanishing alone.

The ambient category is the original `C : Type u`, with `Category.{v} C`,
`Abelian C`, and `IsGrothendieckAbelian.{w} C`. The auxiliary universe `w`
is retained separately from both `u` and `v`; only subobject index types
are shrunk. These results use no derived-category choice and introduce no
new complex or localization carrier. The eventual complexes remain native
`CochainComplex C ℤ`.

## Mathematical source and remaining steps

The construction follows [Stacks 079J](https://stacks.math.columbia.edu/tag/079J).
For each proper subobject of `N`, the separator supplies a map into `M`
whose composite misses it. Their coproduct is epimorphic onto `N`; its
image in `M` is the desired covering subobject. The cardinal bound is
measured by subobjects, not by a presumed set of elements of an abstract
abelian-category object.

The construction of [Stacks 079K](https://stacks.math.columbia.edu/tag/079K)
starts with the image of a separator map and the image of its restricted
differential. The countable recursion applies `ExactStep` to each successive
restricted differential. Its compatible terms and maps are assembled as an
actual native complex, rather than an abstract existence predicate. Native
truncation and extension place the result in the original integer complex.

The object representatives follow
[Stacks 079E](https://stacks.math.columbia.edu/tag/079E): enlarge the separator
coproduct using a retraction of its index embedding, and parameterize its
quotients using well-poweredness of the opposite abelian category. The complex codes retain countably many such terms
and their locally small differential data; native isomorphisms transport
the complex along its chosen term representatives. The family
interface restricts these codes to the required acyclic bounded-above objects.

Finally [Stacks 079L](https://stacks.math.columbia.edu/tag/079L) needs a
transfinite exhaustive acyclic filtration and compatible null homotopies.
At each successor, extend the existing homotopy using termwise injectivity
and the small acyclic quotient. At a limit, take the compatible colimit
homotopy. Alternatively prove the continuous inverse-system Hom-complex
lemma with surjectivity onto every preceding limit, not just pairwise
surjective transition maps. Arbitrary inverse limits are not exact, and
existence of unrelated homotopies at each stage is insufficient.
