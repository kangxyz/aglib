# Finite Koszul complexes and original quotient resolutions

This family extends `ChainComplex.Koszul` on mathlib's actual nonnegative
chain complexes of module categories. Its present consumer is the local
regular-immersion calculation for Serre duality. The source selection and
hashes are recorded in [the migration record](../../../../docs/migration/motivic-koszul.json).
The supplied Motivic archive has the same Lean and Mathlib pins; contributor
and license headers are retained. Only these generic lower results are
admitted, with one implementation and native namespaces.

[Single](Single.lean) constructs the two-term multiplication complex for
an arbitrary module over a commutative ring, with independent ring and module
universes. Its original augmentation targets the literal scalar-image quotient.
Regular scalar multiplication makes that augmentation a quasi-isomorphism;
a projective coefficient gives the actual native projective resolution.

[Basic](Basic.lean) constructs the finite-list complex recursively using the
native tensor total complex. The empty list is its monoidal unit; singleton
and concatenation comparisons are actual chain isomorphisms. Terms above the
list length vanish, and every term of the ring complex is projective.
[Differential](Differential.lean) proves the original signed two-column rule:
the new-factor column contributes scalar multiplication minus the old
differential. No acyclicity is an input to this construction.

[Augmentation](Augmentation.lean) computes original degree-zero homology from
the actual degree-one boundary. [Ideal](Ideal.lean) identifies that boundary
ideal with `Ideal.ofList` and targets the literal generated ideal quotient.
[Resolution](Resolution.lean) proves positive-degree exactness for mathlib's
native weakly regular list on the coefficient, and proves the actual ideal
augmentation is a quasi-isomorphism for weak regularity on the ring.
`finiteProjectiveResolution` and `regularProjectiveResolution` construct native
`ProjectiveResolution` objects: their complex and augmentation equations are
`rfl`. Neither a resolution family nor Noetherianity is supplied as an input.

[Coefficient](Coefficient.lean) and its [guide](Coefficient/README.md) retain
module coefficients. The [single-factor guide](Single/README.md) records the
literal quotient and two-column tensor comparisons used in the induction.
The elementwise homology criterion is owned lower by
[ShortComplex/ModuleQuasiIso](../ShortComplex/ModuleQuasiIso.lean).

The tensor construction uses the native same-universe module monoidal category
in the finite-list leaves; the independent universes of the single factor are
retained. [Top](Top.lean) identifies the original ordered highest term with
the ring module, including the empty list and without regularity. This is an
ordered top frame, rather than an identification of the whole complex with
exterior powers.

[Ext](Ext.lean) is a native downstream calculation from the supplied
resolution, not another imported source implementation. A weakly regular
list gives the actual quotient `R / Ideal.ofList s` projective dimension at
most `s.length`. Every original Ext class above that bound vanishes for
arbitrary coefficient modules and arbitrary supported Ext universes. The
ring need not be Noetherian, the coefficient need not be finite, and the
empty list is included. For ring coefficients, the
[regular-list coinduction](../../Category/ModuleCat/ChangeOfRings/Coinduction/RegularList.lean)
also proves vanishing in every degree different from the list length. Lower
vanishing for arbitrary coefficients is a different assertion and needs its
own coefficient hypotheses. The [single-factor Ext guide](Single/README.md)
records the degree-one quotient class and its concentration conditions.

[Ext/Top](Ext/Top.lean) constructs the original top Koszul cocycle for every
coefficient and proves surjectivity onto native top Ext.
[Ext/Quotient](Ext/Quotient.lean) identifies the ring-coefficient top line with
`R / Ideal.ofList s`. [Ext/Coefficients](Ext/Coefficients.lean) identifies
top Ext for arbitrary `N` with the actual quotient
`N ⧸ ((Ideal.ofList s) • ⊤)`, linearly over `R ⧸ Ideal.ofList s`.
These results assume weak regularity of `s` on the commutative ring `R` and
the displayed `HasExt` size, without regularity, flatness or finiteness of
`N`, Noetherianity or properness of the ideal. Literal quotient representatives
retain the original top cocycles and native Yoneda coefficient maps.

[Ext/GeneratorChange](Ext/GeneratorChange.lean) proves determinant covariance
of the original ring-coefficient top class. Both lists must be weakly regular,
the displayed matrix expresses the second ordered list in terms of the first,
and their generated ideals agree. The matrix need not be invertible over `R`;
the result uses the actual quotient map and the required length transport.
[Ext/Localization](Ext/Localization.lean) proves that native Yoneda
postcomposition by a supplied coefficient-localization map localizes this
same top Ext. The base ring and quotient source stay fixed. These local
suppliers do not themselves provide geometric gluing or a global
regular-immersion purity theorem.

[LinearPart](LinearPart.md) treats the actual tensor differential for a finite
list with linearly independent cotangent classes over a commutative local ring.
In every degree, `d(z) ∈ m² • K` implies `z ∈ m • K`. No Noetherianity,
regular-sequence or residue-characteristic assumption is required.
