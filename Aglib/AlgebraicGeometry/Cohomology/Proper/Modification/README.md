# Original modification maps and closed-support descent

[Unit](Unit.lean) constructs
`Scheme.Modules.ordinaryModificationUnitNatTrans π` and its component
`ordinaryModificationUnit π M` on the original native bounded-below
derived categories. Its factors are exactly the native single of the
ordinary pullback/pushforward adjunction unit and the existing
`rightDerivedSingleComparison`. The expanded formula retains the
original installed `derivedPushforwardPlusUnit` and original
single-complex comparison. Coefficient naturality uses the same
ordinary pullback and installed derived direct-image maps.

This map is available for every scheme morphism and every module
coefficient. A scheme isomorphism makes the same map invertible.
Properness, Noetherianity, quasicoherence and coefficient flatness are
not needed for its construction. Its pulled coefficient is ordinary
`π^* M`; this construction makes no identification with `Lπ^* M`.

The exact source passed with receipt `1792119742738234000-6204` in
3.1 seconds at the default budget. The independent arbitrary-universe
`ModificationUnitConsumer.lean` passed with receipt
`1792119881688840000-7888`; all four inspected declarations use only
the three standard axioms.

The next consumers are the original open mate and installed derived
open comparison, then support of the cone on the closed complement.
Such a cone can have homology in degree `-1`; no monomorphism of the
ordinary adjunction unit or scheme-theoretic dominance is assumed.
Coherent boundary homology descends directly to a positive ideal-power
thickening through the sole closed-immersion descent interface. The
finite Postnikov argument is shared with the general derived layer.

[Restriction](Restriction.lean) proves the actual open-restriction square
for `ordinaryModificationUnit`. The equality uses the installed
`derivedOpenBaseChangeIso`, the original exact restriction-single maps,
and the actual ordinary `cartesianPullbackBaseChangeMate`. Its proof
retains the original ordinary open-unit equation and the installed
derived-composition units. The native single-complex comparison is also
recorded explicitly. Two private computations keep the original unit
normalization within the default compiler budget.

`ordinaryModificationUnit_open_isIso a b π j h M` makes the literal
restricted original map invertible if the local morphism `b` in the
supplied cartesian open square is an isomorphism. The exported interface
explicitly retains `h : IsPullback a b π j` and both open immersions.
`ordinaryModificationUnit_restrict_isIso π U M` specializes to the native
inverse-image open and `π ∣_ U`. Every actual coefficient is allowed; no
quasicoherence, Noetherianity, flatness or monomorphism of the ordinary
unit is assumed. The exact leaf passed with receipt
`1792121591759871000-37845` in 15 seconds at the default budget. The
arbitrary-universe `ModificationRestrictionConsumer.lean` passed with
receipt `1792121663232883000-38528`; all five inspected declarations use
only the three standard axioms.

[Support](Support.lean) applies the same original map in any actual native
distinguished triangle. Its third object becomes zero under installed
derived restriction to an open on which the original morphism restricts
to an isomorphism. Exact restriction and the original derived homology
comparison give `ordinaryModificationCone_homology_support_subset` for
every integer degree. The result uses actual stalk support and the closed
set complement of the open, with no quasicoherence premise.

`ordinaryModificationCone_isGE` retains the possible degree `-1` homology.
`ordinaryModificationCone_isLE` retains an actual nonnegative upper bound
on the derived pulled coefficient. Neither result assumes the ordinary
adjunction unit monic. Coherent native homology of the source coefficient
and the actual modification image gives coherence of the third object
through the shared triangulated property. The native distinguished-cocone
axiom assembles these results in
`exists_ordinaryModificationCone_bounded_coherent`, with an actual triangle
on the original map, bounds `[-1,N]`, and all-degree boundary support.
The exact source passed with receipt `1792121853244353000-40433` in
2.9 seconds at the default budget. The independent arbitrary-universe
`ModificationSupportConsumer.lean` passed with receipt
`1792121908508443000-41191`; all six inspected declarations use only the
three standard axioms. The exported lower-bound interface explicitly
retains the actual distinguished-triangle hypothesis.
