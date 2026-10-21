# R5 source/native correspondence

The [exact 15 addendum](r5-source-addendum-83.json) gives 63 declaration-level map and guard arguments over the [frozen 877-row baseline](r5-source-baseline-68.json). Source module and SHA256 identify each selected source. The baseline is historical and unchanged; the addendum does not infer coverage for unrelated declarations or cuts, or claim the whole migration is complete.

The existing map table is anchored at mathematical commit `83bf521fb13f792f2058026d6d4f4598ac888153` and cotangent name correspondence `f300ff0c5486eaf10536dbcb0b009e89528deb6d`. These identify that historical source correspondence; they do not assign every mathematical endpoint described below to those commits.

## Maps and native owners

The current small-etale owner is `AlgebraicGeometry.EtaleCohomology`, with declaration namespace `AlgebraicGeometry.Scheme.EtaleCohomology`. The [upstream migration guide](../ETALE_COHOMOLOGY_MIGRATION.md) and its [exact module map](etale-cohomology-layout.json) retarget the historical native paths in this correspondence. Zariski module/coherent cohomology and formal functions keep `AlgebraicGeometry.Cohomology`; their original structural actions and canonical maps are unchanged. The frozen historical source tables retain their original basis.

The source resolutions distinguish direct native declarations, exact expression/composite reuse, and R5 applications that retain their original marked or model-specific data. They include the actual finite-normalization tensor map, field/sheaf descent composites, faithful fibre evaluation, the one-variable localization, the import-only degree facade, and the residue-field universal-injectivity criterion.

For literal kernels, native `schemeSquare` supplies both projections of the comparison with the source pullback. The point equivalence and Galois precomposition use that same comparison; an abstract object isomorphism alone does not establish these maps. Tensor/Hom composites retain the actual scalar tower, pure-tensor order and inverse in the contragredient argument. Actual-model, polygon, minimum and classifier wrappers continue to refer to the same original source, target, origin and component maps.

The generic rational-point cotangent owner is [RationalPoint/Cotangent.lean](../../Aglib/AlgebraicGeometry/RationalPoint/Cotangent.lean), corresponding to the historical author file `Group/Cotangent.lean`. Its incoming generic helper and naturality names use `stalkConstantsMorphism` in place of `stalkConstants`. This naming correspondence preserves the same categorical stalk structure map and its scalar/naturality equations.

## Mathematical conclusions and premises

The [multiplication cotangent](../../Aglib/AlgebraicGeometry/Group/MultiplicationCotangent.lean) construction gives the actual identity-stalk formula `phi_n(a)−n*a ∈ m²` and cotangent pullback `n*id`. The [invertible-level multiplication](../../Aglib/AlgebraicGeometry/Group/MultiplicationInvertible.lean) theorem applies over every field k to the original group with `Curve.Properties G.X` and `IsUnit(n:k)`: the same literal `(id G.X)^n` is finite, étale and surjective. The every-positive-level corollary uses characteristic zero; arbitrary levels divisible by the characteristic are not inferred.

The native [MultiplicationDegree](../../Aglib/AlgebraicGeometry/Group/MultiplicationDegree.lean) endpoint has an additional, explicit genus hypothesis. For any field k and the same actual `G : Grp (FScheme k)`, assume `hG : Curve.Properties G.X`, `hg : coherentGenus k G.X = 1` and `IsUnit(n:k)`. Then `multiplication_hasGeometricDegree` and `multiplication_finite_etale_degree` give geometric degree `n*n` for the literal `(id G.X)^n`, together with finiteness and étaleness. The native finrank of that same morphism is `n*n` at every target point.

The [positive-level multiplication](../../Aglib/AlgebraicGeometry/Group/MultiplicationFiniteDegree.lean) theorem needs only `0 < n`, with the same actual curve properties and native genus-one hypothesis. It proves that the literal multiplication is finite, flat and surjective, and that its direct-image structure sheaf has locally free rank `n*n` at every point, even when the characteristic divides n. This schematic rank includes nonreduced fibre multiplicities; geometric point counts retain the separate invertibility premise.

The [PointDivisor](../../Aglib/AlgebraicGeometry/Group/PointDivisor.lean) construction uses actual point divisors and normalized Abel classes. Over an algebraically closed base, its multiplication and power identities hold for every test object, with no reducedness or Noetherianity assumption on that test object. The Riemann–Roch, Cartier and related arguments are bound to genuine native suppliers, without representability. This does not assert Abel-class injectivity for arbitrary nonreduced test objects.

The [actual Picard dual](../../Aglib/AlgebraicGeometry/Group/DualIsogeny.lean) is constructed from native cross-curve degree-zero pullback and the normalized Abel classes. Over an algebraically closed field, its source multiplication triangle is proved from the actual geometric degree, then identifies a supplied reverse with that triangle. No reverse-degree or Picard-representability premise is added.

The [arithmetic kernel pairing](../../Aglib/AlgebraicGeometry/Group/IsogenyPairing/Galois.lean) is constructed on the original geometric point kernels of `f : E → D` and `d : D → E`. It assumes both actual curve properties and native coherent genera one, finite étale surjectivity of f, actual geometric degree N, and the source triangle `f ≫ d = [N]`. Positive frame transport proves biadditivity and the native absolute-Galois/cyclotomic equation. With `IsUnit(N:F)` the same map is perfect over every field F. The field-fundamental-group corollary additionally retains characteristic zero. Its multiplication specialization has the actual alternating Weil construction described below.

The [native group-curve genus theorem](../../Aglib/AlgebraicGeometry/Group/CurveGenus.md) now proves `coherentGenus k G.X = 1` from the actual group object and `Curve.Properties G.X` over every field. It supplies the genus premise of the native multiplication, torsion and pairing theorems. The generic [differential/diagonal comparison](../../Aglib/AlgebraicGeometry/Modules/Differentials/Diagonal.md) identifies the actual canonical map over any affine base. The packet’s external `B.genus` function is not identified by this theorem; source adapters retain their actual typed curve conditions.

Conditional normalization/inertia extension statements retain actual Hopf/coordinate data, Galois-category/fibre-functor classes, Ext/Stacks and level premises. Their three-factor decomposition preserves the same Q and inertia maps. For arbitrary field Ω, the term is “Ω-valued point”; no full faithfulness for arbitrary Ω is asserted.

For a commutative local ring R, the actual finite-étale-cover base-change functor along `Spec κ(R) → Spec R` is faithful and essentially surjective. These local residue-lifting conclusions require neither Henselianity nor Noetherianity; their cover comparisons preserve both original projections.

For any Henselian local base, [HenselianEquivalence](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/HenselianEquivalence.lean) proves fullness and equivalence for this exact residue base-change functor. No completeness or Noetherian hypothesis is needed. The native adic equivalence retains its marked-residue interface over a complete Noetherian base. The comparison for finite-étale covers of a proper scheme over the base remains a separate obligation.

For any universally closed `Y → Spec R` over a local ring, [ProperResidue](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/ProperResidue.lean) proves that restriction of finite étale covers to the actual closed fibre is faithful and reflects isomorphisms. No Henselianity, Noetherianity or flatness is needed for uniqueness. The separate [finite-algebra idempotent theorem](../../Aglib/RingTheory/Henselian/FiniteAlgebraIdempotents.lean) lifts every prescribed idempotent modulo the maximal ideal in a finite algebra over a Henselian local ring. For a proper flat model over a Henselian DVR, [Fullness](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/ProperResidue/Fullness.md) now constructs actual morphism lifts through the literal closed-fibre functor. Together with faithfulness this gives full faithfulness, without smoothness, connectedness, completeness or excellence. Essential surjectivity and the full proper-model equivalence remain separate.

Unrestricted `ProperHenselianComparison R` remains distinct from proved `NormalProperCurveGenericExtension`. Concrete polygon projection and point lifts do not prove the unrestricted proper-Henselian finite-étale category equivalence. The normal-proper-curve extension supplier includes constant generic maps and has no dominance premise on that map.

Exact smooth-field regularity, closed-point dimension, total dimension and proper-curve product-formula suppliers are available at their stated scope. Their appearance as source parameters does not make them missing producers. The [full flat-local theorem](../../Aglib/RingTheory/RegularLocalRing/FlatDescent.md) now proves regularity descent along the same actual flat local homomorphism from a Noetherian local ring to a regular local ring, with independent universes and no finite-type, unramified, characteristic or completion condition. The exact original [FlatLocalRegularityDescent](../../Aglib/AlgebraicGeometry/Properties/Regular/Descent/FlatLocal.md) family has a native inhabitant. Its proof uses actual finite minimal free resolutions, the native Koszul linear-part theorem, finite-projective-dimension descent, and the proved residue-field regularity criterion.

The [formal-functions family](../../Aglib/AlgebraicGeometry/Cohomology/FormalFunctions/README.md) proves the canonical completion-to-cohomology-tower equivalence for a proper morphism over a Noetherian affine base, arbitrary coherent coefficients, every ideal and every natural cohomological degree. It also proves the actual geometric-thickening comparison, the complete-base form under adic completeness, and both local higher-direct-image stalk comparisons over a locally Noetherian target. No flatness, projective embedding or additional Rees-finiteness premise is required. These cohomology comparisons do not assert effectivity of a formal cover object.

The [nilpotent algebra lifting theorem](../../Aglib/RingTheory/Etale/NilpotentLift.md) constructs actual étale lifts across arbitrary nilpotent ideals and finite lifts when the original algebra is finite. The [affine quotient adapter](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/ProperResidue/Existence.md) proves essential surjectivity of the literal affine quotient pullback. This result requires no Noetherian, Henselian or completeness condition. The [global nilpotent equivalence](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/Nilpotent.md) constructs actual cover and Hom lifts across a nilpotent closed immersion of arbitrary schemes, with the original base-change functor. Its nilpotence premise is a global exponent; no proper algebraization is asserted.

The [proper-birational functions theorem](../../Aglib/AlgebraicGeometry/Morphisms/Proper/BirationalFunctions.md) proves the actual structure-sheaf map is an isomorphism for a universally closed dominant birational morphism of integral schemes with normal target, without Noetherianity or flatness. The stronger [geometric-connectedness theorem](../../Aglib/AlgebraicGeometry/Morphisms/Proper/ConnectedFibres.md) proves `GeometricallyConnected f` for proper surjective `f` over a locally Noetherian target with `IsIso f.c`. Its birational specialization retains integral source and target, locally Noetherian normal target, properness, dominance and invertibility of the actual function-field map. It uses the affine image theorem and flat geometric comparisons, independently of the ordinary-stalk image specialization.

The [affine idempotent-image theorem](../../Aglib/AlgebraicGeometry/Cohomology/Proper/FibreFormalFunctions.md) gives an arbitrary original global-function preimage for every idempotent on an actual ideal thickening of a proper scheme over any Noetherian commutative ring and any ideal. The [ordinary-stalk specialization](../../Aglib/AlgebraicGeometry/Cohomology/Proper/FibreFormalFunctions/Stalk.md) gives an arbitrary preimage under the same canonical ordinary stalk-to-literal-fibre map for proper `f` over a locally Noetherian target. Neither preimage is asserted idempotent. The [degree-zero unit square](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/DegreeZero.md) identifies the installed higher-image map with the original Cartesian mate on an actual square with flat base arrow and arbitrary module coefficient; it adds no properness, finiteness or quasicoherence premise. These statements assume no Grothendieck existence, Artin approximation, Henselianity or object effectivity.

The [height-one principal theorem](../../Aglib/RingTheory/RegularLocalRing/HeightOnePrincipal.md) concerns actual height-one prime ideals in regular local rings of dimension at most two, including their singleton ideal bases. The [regular-surface consumer](../../Aglib/AlgebraicGeometry/IdealSheaf/Invertible/RegularSurface.md) proves native local rank one of the actual `idealModule i` for a closed immersion `i : C ⟶ X`, retaining integral `C`, locally Noetherian `X`, regular ambient stalks of dimension at most two, and height one of every actual kernel `RingHom.ker (i.stalkMap c).hom`. Their bounded interfaces remain available alongside the unrestricted suppliers below. The [surface isomorphism-locus theorem](../../Aglib/AlgebraicGeometry/Surfaces/Birational/README.md) concerns integral source and normal Noetherian integral target of dimension at most two, properness, dominance and invertibility of the actual function-field map. It gives the maximal actual isomorphism open with finite closed-point complement, without source regularity or excellence. It supplies no factorization, contraction or minimal-model existence theorem.

The [general Milnor patching theorem](../../Aglib/RingTheory/Etale/MilnorPatching/README.md) now supplies `RingHom.Etale.MilnorPatching.etalePatching : EtalePatching` in the [FinitePresentation](../../Aglib/RingTheory/Etale/MilnorPatching/FinitePresentation.lean) leaf. It retains the original six same-universe commutative rings, seven maps, two commutative squares, surjectivity of `f`, etaleness of the two component maps, and both specified tensor boundary equivalences with their original pure-tensor formulas. Its pointwise `etale_fiberMap` concludes etaleness of the literal fibre-product map. General component reconstruction, flatness descent and finite-presentation descent supply the conclusion without finite-module, Noetherian, flatness-of-`g`, output-flatness, output-finite-presentation or input-patching premises. The parent retains the single original proposition; the finite-free split-power theorem remains a separate concrete result.

[Proper fibre descent](../../Aglib/AlgebraicGeometry/Morphisms/Proper/FibreDescent.md) proves `∃! h : Y ⟶ Z, f ≫ h = g` for a given proper surjective `f : X ⟶ Y` with actual `IsIso f.c` and a given `g : X ⟶ Z` pointwise constant on its fibres. The schemes are arbitrary; no Noetherianity, normality, integrality or separation of `Z` is assumed. This is descent of an actual given map, not contraction existence, and uses neither Grothendieck existence nor Artin approximation.

The [regular-point blowup](../../Aglib/AlgebraicGeometry/Blowup/RegularPoint.md)
now has an actual inverse-image-centre isomorphism with the native projective
line over the original residue field, for every two-dimensional regular local
ring. The chosen ordered regular parameters govern the same chart maps,
Laurent transition and structural projection. The
[ambient regularity theorem](../../Aglib/AlgebraicGeometry/Blowup/RegularPoint/Regularity.md)
now proves regular locality at every actual stalk of that same constructed
blowup, from only native regular locality and dimension two of the original
ring. The lower regular-principal quotient lifting theorem, actual chart
stalk maps, literal fibre cover and regular complement supply the proof.
The [scheme-level point theorem](../../Aglib/AlgebraicGeometry/Blowup/RegularPoint/Scheme.md)
then proves regularity of every actual stalk of the blowup of a closed point
on a locally Noetherian regular scheme, assuming dimension two only at that
original stalk. It identifies the actual centre under the original local
spectrum map and preserves both flat-base-change projections. No excellence,
trait or global dimension premise is added. Normal-line identification,
contraction and factorization remain separate. The [proper finite-fibre theorem](../../Aglib/AlgebraicGeometry/Morphisms/Proper/QuasiFinite.md)
gives literal isomorphism restrictions near finite actual point fibres of a
proper dominant morphism of integral schemes with normal target and invertible
actual function-field map, with no Noetherianity or dimension bound.

The general [Cartier operations](../../Aglib/AlgebraicGeometry/IdealSheaf/Cartier/README.md)
now have native suppliers. Integral avoidance proves invertibility of the
original canonical pullback map without flatness or Noetherianity. The ideal
tensor comparison retains its exact multiplication triangle; product equals
intersection when the actual intersection is Cartier on the second divisor.
The flat DVR closed-fibre ideal is explicitly trivialized with its original
inclusion. The shared [stalk-kernel criterion](../../Aglib/AlgebraicGeometry/IdealSheaf/Invertible/StalkKernel.md)
and [explicit-factorial consumer](../../Aglib/AlgebraicGeometry/IdealSheaf/Invertible/Factorial.md)
work with the actual stalk-map kernels, retaining local Noetherianity and
height one; the latter assumes factorial domains at all ambient stalks and
has no dimension bound.

The unrestricted [regular-local factoriality theorem](../../Aglib/RingTheory/RegularLocalRing/Factorial.md)
now derives native unique factorization, principality and actual singleton
bases for every height-one prime from the native regular-local-ring
hypothesis, with no dimension bound. The lower prime-local regularity,
finite-projective-dimension base change and rank-one stable-cancellation
proofs retain the actual rings, localizations and ideals. The
[regular-stalk Cartier supplier](../../Aglib/AlgebraicGeometry/IdealSheaf/Cartier/Regular.md)
therefore inhabits the original codimension-one family in arbitrary
dimension. It retains local Noetherianity of the ambient scheme, integral
closed source, regularity of every actual ambient stalk, and height one of
every actual stalk-map kernel. The bounded surface specialization remains
available with its unchanged statement.

The original [cohomology field-extension comparison](../../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/FieldExtension.md)
is now an actual canonical linear equivalence in every degree for qcqs
schemes with quasicoherent coefficients. It preserves the unit-tensor
pullback map, reflects vanishing faithfully, and gives dimension equality
without a cohomological-finiteness premise. The
[actual-fibre H⁰ neighbourhood](../../Aglib/AlgebraicGeometry/Cohomology/Proper/H0Vanishing/FieldExtension.md)
uses this comparison and proper semicontinuity to produce an open containing
the original point from vanishing after any field extension of its residue
field. It retains properness, local Noetherianity, finite-type quasicoherent
coefficient and relative flatness. Identification with a specified external
field fibre and coefficient remains part of the actual model application.

The [literal Weierstrass geometry](../../Aglib/AlgebraicGeometry/EllipticCurve/Weierstrass/Geometry.md)
now supplies the exact all-fields nonsingular-geometry family.
[Structural H¹](../../Aglib/AlgebraicGeometry/EllipticCurve/Weierstrass/Genus.md)
is linearly isomorphic to the original coefficient field for every equation,
including singular cubics, by the actual two-chart Laurent quotient. This
is coherent arithmetic genus. The
[pointed-isomorphism theorem](../../Aglib/AlgebraicGeometry/EllipticCurve/Weierstrass/PointedIsomorphism.md)
derives the admissible coordinate change from the actual origin-preserving
scheme isomorphism and proves the original j-invariance family over every
field. The [coordinate-operation comparison](../../Aglib/AlgebraicGeometry/EllipticCurve/Weierstrass/GroupCompatibility.md)
proves the retained characteristic-zero families for every given pointed
group law, including the original group's points over arbitrary field
extensions. Group-law construction retains external Picard representability.

The [general finite-presentation descent theorem](../../Aglib/AlgebraicGeometry/Descent/FinitePresentation/Schemes.md)
constructs actual stage models for every finitely presented qcqs scheme
over a filtered ring colimit, with the literal original base-change
comparison. Finite-category descent includes all arrows, identities and
composition equations and returns an actual stage functor and native
pullback natural isomorphism. The common-stage map and open-gluing
suppliers retain nonseparated schemes and arbitrary ring transitions.

The [finite-base curve producer](../../Aglib/AlgebraicGeometry/Morphisms/SpreadingOut.md)
constructs a proper smooth geometrically integral family over a finitely
generated integer subalgebra containing prescribed finite constants,
with its actual field-pullback isomorphism to the original curve. It
also restores the properties on a literal later pullback of an arbitrary
given finitely presented qcqs stage model, without flatness or injectivity
of the stage ring maps. The final field comparison uses canonical pasting
followed by the original supplied comparison. Its
[generic-open supplier](../../Aglib/AlgebraicGeometry/Morphisms/GeometricallyIntegral/Open.md)
retains the proper smooth relative-curve and integral locally Noetherian
base hypotheses; unrestricted proper-flat-family openness is not claimed.

The [prime-away criterion](../../Aglib/RingTheory/IntegralClosure/PrimeAway.md)
proves normality from the actual localization at a prime element without
Noetherianity. The [DVR Weierstrass theorem](../../Aglib/AlgebraicGeometry/EllipticCurve/Weierstrass/Normality.md)
uses it on the original affine and infinity charts to prove normal stalks
of the literal projective cubic from its nonzero generic discriminant.
The [trait graph construction](../../Aglib/AlgebraicGeometry/Surfaces/Birational/TraitGraph.md)
gives an actual common proper integral Noetherian flat graph, its original
generic comparisons, projection-induced function-field equivalences and
compatible section lifts. Regular common domination still needs regularity
of this graph; no resolution is asserted by the graph construction.

[Projective Grothendieck existence](../../Aglib/AlgebraicGeometry/Cohomology/GrothendieckExistence/README.md)
now proves that the original coherent completion functor is an equivalence
for an actual closed embedding into finite projective space over a complete
Noetherian base. Its structural morphism is the embedding followed by the
projective-space projection. The ideal is arbitrary, and the forward functor
is literally native completion into the original coherent adic systems.
Proper completion full faithfulness is also proved without flatness.
General proper essential surjectivity remains outside this endpoint.

The [Artin approximation progress](../../Aglib/RingTheory/Henselian/README.md)
proves exact solutions in the original polynomial-origin local-ring
henselization over any field, and in its actual finite local algebras,
approximating native-completion roots for every proper ideal. The finite-local
endpoint retains a common universe for the field and algebra, but no
flatness, freeness, structural-locality or cofinality oracle. Selected
DVR/residue/separability and Néron-modification suppliers retain their
displayed conditions. Full excellent-DVR and general geometric-local Artin
approximation remain open.

## Remaining mathematical frontiers

The active non-surface frontier is finitely presented quasicoherent
module-sheaf object, map and finite-diagram descent, including eventual
local rank one on a given model. Their native interfaces and actual
pullback comparisons are being completed without a Noetherian or
coherence restriction. Surface contraction and minimal-model existence
remain separate obligations. Picard/Hilbert representability retains its
external ownership. The imported projective existence and field-origin
approximation cases apply at their displayed scope; general proper
effectivity and full excellent-DVR approximation retain their deferred
external ownership boundaries.

The native genus producer is proved above; an equality involving the packet’s separate external genus function is not asserted. [MultiplicationTorsion](../../Aglib/AlgebraicGeometry/Group/MultiplicationTorsion.lean) now constructs a `Fin 2` basis over `ZMod n` on the literal geometric torsion subgroup, with the actual curve properties, native coherent genus one, positive level and invertibility hypotheses. The construction covers level one and preserves the canonical scalar, Galois and reduction maps; the basis is noncanonical. The external genus identification remains separate. The constructed Cartier kernel pairing has perfectness and the actual arithmetic equivariance under the premises above. The [actual Weil construction](../../Aglib/AlgebraicGeometry/Group/WeilPairing.md) proves alternation of its multiplication specialization and returns all six fields of `PerfectWeilPairing` for every positive invertible level, including even/composite levels and one. It retains the native genus-one premise and actual torsion/root Galois actions; its rank-two basis remains noncanonical.

The [resolved cyclic-fibre comparison](../../Aglib/AlgebraicGeometry/Surfaces/PowerNode/Comparison/CyclicFibre.md) now constructs an isomorphism over the original residue field from the actual positive-exponent resolved fibre to the literal polygon. It preserves the original equation, run, component maps, both tangent orderings and structural triangles; the exponent-one branch also preserves the original infinity section. Concrete adapters use the proved blowup, curve-extension, DVR-locus and étale-chart suppliers. The original DVR, critical-neighborhood, unit-power and split-tangent hypotheses remain explicit. Actual model or integral-presentation existence, genuine minima, contraction and normalized-one-gon criteria remain separate. ModelGeometry and SplitModelCoverTheory assembly does not supply those geometric premises.

Picard/Hilbert representability implementation and excluded subparts remain outside adoption. Conditional mathematical conclusions retain their exact hypotheses.
