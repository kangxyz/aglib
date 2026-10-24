# Original residue-field vanishing

The construction implements
[Stacks Project, Lemma 54.7.6 (0AXC)](https://stacks.math.columbia.edu/tag/0AXC),
over a normal Noetherian Nagata local domain of
dimension two. The proper birational map has integral normal source and
the original function-field map is an isomorphism.

`closedFibreQuotient_restrict_isZero` identifies the actual ideal quotient
with the pushforward from the actual closed fibre and proves vanishing on
the punctured inverse image. `closedFibreExtension_quotient_lift_of_isNagata`
uses the original Ext/H1 restriction equation and the graph construction's
punctured H1 injectivity to lift the original quotient. The section theorem
passes this lift to `ClosedFibreExtensions`' original scalar correction.
`closedFibreExt_one_eq_zero_of_isNagata` retains the actual Ext class through
its short-exact representative.

`structuralPullbackGlobalSectionsAdjunction` is the original tilde/pullback
adjunction transported through the structural global-section comparison.
`structuralPullbackQuotientIso` identifies the image of the actual quotient
module with the actual ideal-image quotient, preserving the quotient arrow.
The finite presentation's explicit homotopy annihilates H-minus-one after
pullback. A nonzero original scalar is injective on the structure module,
so that negative homology has no maps to it. The actual truncation triangle
then reduces degree-one Hom to the original Ext class.

`residueField_hom_derivedGlobalSections_eq_zero_of_isNagata` concludes for
the original residue field in degree one and the original right-derived
global-section object. Its target uses
`f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom`.
The comparison uses the supplied native injective resolution only through
its original derived-unit isomorphism. No flatness, projectivity of the
geometric source, or vanishing of higher negative Tor is assumed.
