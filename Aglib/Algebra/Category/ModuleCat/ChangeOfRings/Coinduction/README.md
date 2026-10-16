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
The native cycle comparison retains each original linear map and identifies
target-ring scalars with original restricted right multiplication.
`coextendScalarsResolutionExtAddEquiv_homologyπ` sends each actual cycle
class to its unchanged injective-resolution Ext class. The cycle/projection
source and public consumer passed `1792145518226095000-1614` and
`1792145827305212000-4124`; the consumer needs no extra options and checks
all natural degrees and degree zero with only the standard axioms.

The `_smul` equations for original R^n and the installed D+ comparison
identify that same scalar action with original Yoneda precomposition.
They require no commutativity, regularity, flatness or finiteness and passed
source check `1792146354600396000-7346`. Their public independent-derived-size
consumer passed `1792146664073794000-9365` without extra options and with
only the standard axioms.

Original coefficient cochain maps now give literal cocycle postcomposition.
Every native coefficient-resolution lift induces original Yoneda
postcomposition, both on native higher coinduction and on homology of the
installed D+ functor. Both comparisons are independent of the supplied
injective resolution. No commutativity or additional hypothesis is used.
This extension passed `1792149290569566000-26194`; the public noncommutative
consumer passed `1792149367685045000-27013`, with independent Ext and derived
sizes, six standard-axiom lists and no extra proof options.

[Quotient](Quotient.lean) upgrades that unchanged additive comparison to an
`R/I`-linear equivalence using `Ext.quotientSourceModule`. Its underlying
additive equivalence is definitionally the original one. Arbitrary ideals,
coefficients and natural degrees are allowed, with independent Ext and derived
sizes and no regularity, flatness, finiteness or Noetherian premise. Original
Yoneda coefficient naturality and resolution independence are retained.
The final source passed `1792149718119709000-30321`; the public consumer
passed `1792150146467176000-34212` with five standard-axiom lists and no extra
proof options. Koszul-class normalization and concentration are supplied
by the next leaf.

[Principal](Principal.lean) computes the actual installed derived coinduction
for a regular principal equation. Degree-one homology is the original
coefficient quotient as an `R/(a)`-module; inverse quotient representatives
retain the original transported Koszul class. Coefficient regularity alone
gives the lower bound one, while ring regularity alone gives the upper bound
one. With both, the actual D+ object is its coefficient quotient in degree one.
For the ring coefficient, the target is the actual ring `R/(a)` in that degree.
The two homology equations retain the original quotient-linear comparisons
and homology-normalized native single map. All three comparisons are
independent of the supplied resolution. No Noetherian, flatness or finiteness
premise is added. The final source passed `1792149988379734000-32635`;
the public consumer passed `1792150144251703000-34185` with thirteen
standard-axiom lists and no extra proof options. Regular-list determinant
normalization and geometric sheaf purity remain separate consumers.
