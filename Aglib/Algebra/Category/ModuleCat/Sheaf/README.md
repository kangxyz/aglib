# Module sheaves on arbitrary sites

The objects are actual module sheaves over a ring sheaf on a site, before scheme specialization. Tensor statements retain commutative coefficient rings where required. [Tensor/Basic](Tensor/README.md) owns the single sheafified tensor bifunctor and unit/braiding maps.

[ConstantRing/Basic](ConstantRing/Basic.lean), [Equivalence](ConstantRing/Equivalence.lean)
and [Pullback](ConstantRing/Pullback.lean) construct actual module sheaves over
an arbitrary constant ring and compare them with module-valued sheaves. Native
ring and module sheafification, image adjunctions, and their original units
and counits are retained. Ring and module-carrier universes remain independent.
The étale coefficient, open-restriction and constructibility families specialize
these constructions; commutativity is not required for this bridge.

[ConstantRing/UnitUnderlying](ConstantRing/UnitUnderlying.lean) gives the
lifted unit, its section map, local injectivity and surjectivity, and the
underlying constant-abelian-sheaf isomorphism on an arbitrary site under the
displayed sheafification and local-bijectivity hypotheses.
[ConstantRing/ZMod](ConstantRing/ZMod.lean) supplies full lifted-ZMod scalar
forgetting and native constant-ring sheaf forgetting, and identity annihilation
for every modulus. The scheme adapters use these constructors and maps.

[ConstantRing/RingPullback](ConstantRing/RingPullback.lean) compares the actual
native RingCat-valued inverse image of a constant ring with the target
constant ring. It uses continuity, weak ring sheafification, native
right-adjoint existence, and a specified source terminal object whose image
is terminal. Its adjoint transpose is the original `constantRingMap`; the
native unit, counit and original sheafification-unit equations are retained.

[InternalHom/PresheafSource](InternalHom/PresheafSource.lean) constructs the
sheaf of componentwise ring-linear maps from an arbitrary module presheaf to a
module sheaf. [Basic](InternalHom/Basic.lean) specializes its source and identifies
sections with actual module morphisms on the slice site. For site-object,
site-morphism and module universes `uC`, `vC`, `uM`, its output lies in
`max uC vC uM`; the ring universe remains independent. The
[scheme Hom family](../../../../AlgebraicGeometry/Modules/InternalHom/README.md)
uses these same constructors with the native Opens category.

[Pullback/AdjunctionSquare](Pullback/AdjunctionSquare.lean) constructs a
left-adjoint comparison from a specified square of right adjoints. Its partial
mate and original unit and counit equations are explicit. Scheme open
restriction uses this construction with its original geometric square.
Invertibility of the partial mate is a separate conclusion.

[Linear](Linear.lean) sends sections of a commutative ring sheaf on a
specified initial presheaf object to the native category center.
`scalarEndomorphismOfInitial` is actual module-linear multiplication by
the restricted section; `linearOfInitial` uses native
`CategoryTheory.Linear.ofRingMorphism`. Ring, module, site-object and
site-morphism universes are independent. This construction needs neither
sheafification nor quasicoherence or finiteness.

[Colimits](Colimits.lean) proves that the original
`SheafOfModules.toSheaf` preserves every colimit shape available in the
additive target, by the original presheaf-colimit/sheafification argument.
It also bundles finite-colimit preservation and forgetting of epimorphisms
for exact-functor and Ext consumers. Ring, coefficient, site and colimit
universes remain independent. The older names in
[scheme module epimorphisms](../../../../AlgebraicGeometry/Modules/Epimorphisms.lean)
are compatibility aliases to these sole native instances.

Imports use `Aglib.Algebra.Category.ModuleCat.Sheaf` followed by the named leaf. General scheme module tensors, finite-locally-free tensor exactness, Godement and projection formula are consumers. Invertible sheaves specialize the generic tensor rather than defining another implementation.

[Epimorphisms](Epimorphisms.lean) proves that forgetting scalars preserves the displayed shaped colimits and epimorphisms, and that an epi of module sheaves is locally surjective. The site, sheafification, local-bijectivity and sheaf-composition hypotheses remain explicit; this does not assert surjectivity of sections over every object.

[Presentation](Presentation.lean) owns `SheafOfModules.generatingSections_ofEpi_isIso`, `finitePresentation_map_isFinite` and the basis-preserving presentation transport helpers. The supplied unit isomorphism, colimit preservation and original generator/relation index types are retained. [Quasicoherent pushforward](Quasicoherent/README.md) transports these actual finite presentations along compatible site functors. [Local bases](LocallyFree/README.md) supplies the corresponding local-basis pushforward and arbitrary-site locality before scheme specializations.

[Ext](Ext.lean) proves `SheafOfModules.hasExt` for the original abelian
category of module sheaves. Ring, module, site-object and site-morphism
universes are independent; the standard Ext bound is
`max u u' v' (v + 1)` for the corresponding native parameters.

The generic result remains a theorem, allowing callers to choose a smaller
Ext universe when a separate smallness theorem applies. The
[scheme specialization](../../../../AlgebraicGeometry/Modules/Ext.lean)
registers the library's standard `u + 1` choice for actual scheme module
sheaves, including the literal unfolded native category.

[Homology](Homology.lean) gives `sheafificationHomologyIso` for any actual
module-sheaf complex of any shape: sheafification of the original
underlying module-presheaf homology is its original sheaf homology.
`homologyPresheafUnit` is the canonical unit, whose sheafification is
invertible and satisfies the original counit normalization. These
constructions use exact native sheafification, without assuming that
forgetting the sheaf condition preserves homology. The ring, module,
site-object, site-morphism and index universes remain independent under
the stated native sheafification and local-bijectivity hypotheses.

[Evaluation](Evaluation.lean) registers additivity of the unchanged native
variable-ring evaluation functor, with independent ring, coefficient, site
and morphism universes. It unfolds the existing forget/evaluation composite;
there is no second section functor. The scheme-complex basis criterion
consumes it and retains the explicit installed scheme module structures.

[LowerShriekTransport](LowerShriekTransport.lean) constructs the original
three-factor left functor through two actual coefficient equivalences,
its adjunction, finite-limit transfer and unit. The native module lower
shriek specializes this construction.
[ValuedComparison](ValuedComparison.lean) constructs the inverse-valued
comparison and original exchanged isomorphism, proving their whole unit,
preimage and direct-image comparison laws before taking components. The
coefficient categories and their genuinely distinct worlds are retained.
