# Native scalar coinduction and its derived composition

[Coinduction](../Coinduction.lean) proves additivity of the original native
`ModuleCat.coextendScalars` and its preservation of injective objects.
Scalar restriction is its genuine exact left adjoint. The canonical
`coextendScalarsComp` is the original right-adjoint uniqueness comparison
for the native restriction-of-scalars composition isomorphism. Its unit
and counit formulas retain those same adjunctions.

[Derived](Derived.lean) constructs
`ModuleCat.derivedCoextendScalarsPlusCompIso` between the installed
bounded-below right-derived coinduction for a composite ring map and the
composite installed right-derived functors. The unit formula retains the
mapped original cochain comparison and both installed units. Rings may be
noncommutative, their universes are independent, and all three supplied
derived-category size universes remain independent. No flatness,
regularity or finiteness hypothesis is used.

The ordinary leaf passed `1792140329491573000-53466`, the derived leaf
passed `1792141014746584000-59763`, and the combined public consumer passed
`1792141388265718000-63068`. The consumer checks the original comparison
maps at independent universes and reports only the standard axioms.

Regular-embedding purity is a later consumer. This composition theorem
does not itself identify homology with Ext, prove concentration, normalize
a Koszul quotient line, or compare the affine functor with geometric Ri!.

[Ext](Ext.lean) identifies homology of the actual installed D+ coinduction
at the original degree-zero single with native Ext from the restricted
regular target ring. The additive equivalence uses the original Hom complex,
native forgetful homology comparison and any supplied injective resolution.
Its cochain component retains the original linear map. Ring and module
carrier universes are common, while Ext and both supplied derived sizes
remain independent. No commutativity, flatness or finiteness premise is
added. The leaf passed `1792142067048567000-68407` and its public consumer
passed `1792142200367839000-69227`, with only the standard axioms.
The quotient-ring scalar action and original Koszul-class normalization
remain separate proof obligations for purity.
