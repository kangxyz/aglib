# Native module sheaves

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
