# R5 source/native correspondence

The [exact 15 addendum](r5-source-addendum-83.json) gives 63 declaration-level map and guard arguments over the [frozen 877-row baseline](r5-source-baseline-68.json). Source module and SHA256 identify each selected source. The baseline is historical and unchanged; the addendum does not infer coverage for unrelated declarations or cuts, or claim the whole migration is complete.

The existing map table is anchored at mathematical commit `83bf521fb13f792f2058026d6d4f4598ac888153` and cotangent name correspondence `f300ff0c5486eaf10536dbcb0b009e89528deb6d`. These identify that historical source correspondence; they do not assign every mathematical endpoint described below to those commits.

## Maps and native owners

The source resolutions distinguish direct native declarations, exact expression/composite reuse, and R5 applications that retain their original marked or model-specific data. They include the actual finite-normalization tensor map, field/sheaf descent composites, faithful fibre evaluation, the one-variable localization, the import-only degree facade, and the residue-field universal-injectivity criterion.

For literal kernels, native `schemeSquare` supplies both projections of the comparison with the source pullback. The point equivalence and Galois precomposition use that same comparison; an abstract object isomorphism alone does not establish these maps. Tensor/Hom composites retain the actual scalar tower, pure-tensor order and inverse in the contragredient argument. Actual-model, polygon, minimum and classifier wrappers continue to refer to the same original source, target, origin and component maps.

The generic rational-point cotangent owner is [RationalPoint/Cotangent.lean](../../Aglib/AlgebraicGeometry/RationalPoint/Cotangent.lean), corresponding to the historical author file `Group/Cotangent.lean`. Its incoming generic helper and naturality names use `stalkConstantsMorphism` in place of `stalkConstants`. This naming correspondence preserves the same categorical stalk structure map and its scalar/naturality equations.

## Mathematical conclusions and premises

The [multiplication cotangent](../../Aglib/AlgebraicGeometry/Group/MultiplicationCotangent.lean) construction gives the actual identity-stalk formula `phi_n(a)−n*a ∈ m²` and cotangent pullback `n*id`. The [invertible-level multiplication](../../Aglib/AlgebraicGeometry/Group/MultiplicationInvertible.lean) theorem applies over every field k to the original group with `Curve.Properties G.X` and `IsUnit(n:k)`: the same literal `(id G.X)^n` is finite, étale and surjective. The every-positive-level corollary uses characteristic zero; arbitrary levels divisible by the characteristic are not inferred.

The native [MultiplicationDegree](../../Aglib/AlgebraicGeometry/Group/MultiplicationDegree.lean) endpoint has an additional, explicit genus hypothesis. For any field k and the same actual `G : Grp (FScheme k)`, assume `hG : Curve.Properties G.X`, `hg : coherentGenus k G.X = 1` and `IsUnit(n:k)`. Then `multiplication_hasGeometricDegree` and `multiplication_finite_etale_degree` give geometric degree `n*n` for the literal `(id G.X)^n`, together with finiteness and étaleness. The native finrank of that same morphism is `n*n` at every target point.

The [positive-level multiplication](../../Aglib/AlgebraicGeometry/Group/MultiplicationFiniteDegree.lean) theorem needs only `0 < n`, with the same actual curve properties and native genus-one hypothesis. It proves that the literal multiplication is finite, flat and surjective, and that its direct-image structure sheaf has locally free rank `n*n` at every point, even when the characteristic divides n. This schematic rank includes nonreduced fibre multiplicities; geometric point counts retain the separate invertibility premise.

The [PointDivisor](../../Aglib/AlgebraicGeometry/Group/PointDivisor.lean) construction uses actual point divisors and normalized Abel classes. Over an algebraically closed base, its multiplication and power identities hold for every test object, with no reducedness or Noetherianity assumption on that test object. The Riemann–Roch, Cartier and related arguments are bound to genuine native suppliers, without representability. This does not assert Abel-class injectivity for arbitrary nonreduced test objects.

The [actual Picard dual](../../Aglib/AlgebraicGeometry/Group/DualIsogeny.lean) is constructed from native cross-curve degree-zero pullback and the normalized Abel classes. Over an algebraically closed field, its source multiplication triangle is proved from the actual geometric degree, then identifies a supplied reverse with that triangle. No reverse-degree or Picard-representability premise is added.

The [arithmetic kernel pairing](../../Aglib/AlgebraicGeometry/Group/IsogenyPairing/Galois.lean) is constructed on the original geometric point kernels of `f : E → D` and `d : D → E`. It assumes both actual curve properties and native coherent genera one, finite étale surjectivity of f, actual geometric degree N, and the source triangle `f ≫ d = [N]`. Positive frame transport proves biadditivity and the native absolute-Galois/cyclotomic equation. With `IsUnit(N:F)` the same map is perfect over every field F. The field-fundamental-group corollary additionally retains characteristic zero. Weil alternation remains separate.

The packet’s `B.genus_one` is an equality for an external genus function. It is not yet an identification with native `coherentGenus`. That identification, and a theorem deriving coherent genus one solely from the bare group and `Curve.Properties`, remain separate obligations. The native degree theorem under `hg` therefore does not by itself close the packet’s unrestricted `EllipticMultiplicationGeometry` family.

Conditional normalization/inertia extension statements retain actual Hopf/coordinate data, Galois-category/fibre-functor classes, Ext/Stacks and level premises. Their three-factor decomposition preserves the same Q and inertia maps. For arbitrary field Ω, the term is “Ω-valued point”; no full faithfulness for arbitrary Ω is asserted.

For a commutative local ring R, the actual finite-étale-cover base-change functor along `Spec κ(R) → Spec R` is faithful and essentially surjective. These local residue-lifting conclusions require neither Henselianity nor Noetherianity; their cover comparisons preserve both original projections.

For any Henselian local base, [HenselianEquivalence](../../Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/HenselianEquivalence.lean) proves fullness and equivalence for this exact residue base-change functor. No completeness or Noetherian hypothesis is needed. The native adic equivalence retains its marked-residue interface over a complete Noetherian base. The comparison for finite-étale covers of a proper scheme over the base remains a separate obligation.

Unrestricted `ProperHenselianComparison R` remains distinct from proved `NormalProperCurveGenericExtension`. Concrete polygon projection and point lifts do not prove the unrestricted proper-Henselian finite-étale category equivalence. The normal-proper-curve extension supplier includes constant generic maps and has no dominance premise on that map.

Exact smooth-field regularity, closed-point dimension, total dimension and proper-curve product-formula suppliers are available at their stated scope. Their appearance as source parameters does not make them missing producers. Essentially étale local/stalk descent does not prove unrestricted `FlatLocalRegularityDescent`.

## Remaining mathematical frontiers

The remaining degree boundary is the genus identification needed by the original packet family, rather than the native genus-one degree theorem proved above. [MultiplicationTorsion](../../Aglib/AlgebraicGeometry/Group/MultiplicationTorsion.lean) now constructs a `Fin 2` basis over `ZMod n` on the literal geometric torsion subgroup, with the actual curve properties, native coherent genus one, positive level and invertibility hypotheses. The construction covers level one and preserves the canonical scalar, Galois and reduction maps; the basis is noncanonical. The external genus identification remains separate. The constructed Cartier kernel pairing has perfectness and the actual arithmetic equivariance under the premises above. Alternation of the multiplication specialization remains the additional Weil-pairing obligation; a supplied pairing record alone does not construct it.

Complete same-presentation and whole-fibre closure is not inferred from individual component/intersection constructions. Actual model or integral-presentation existence, genuine minima, contraction and normalized-one-gon criteria remain wherever the source asks for them. Component maps, both tangent orderings, overlap conditions, and generic/section triangles must concern the same actual model and presentation. ModelGeometry and SplitModelCoverTheory assembly does not supply these missing geometric premises.

Picard/Hilbert representability implementation and excluded subparts remain outside adoption. Conditional mathematical conclusions retain their exact hypotheses.
