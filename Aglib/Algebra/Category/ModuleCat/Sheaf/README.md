# Module sheaves on arbitrary sites

The objects are actual module sheaves over a ring sheaf on a site, before scheme specialization. Tensor statements retain commutative coefficient rings where required. [Tensor/Basic](Tensor/README.md) owns the single sheafified tensor bifunctor and unit/braiding maps.

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
