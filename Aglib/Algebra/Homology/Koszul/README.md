# Finite Koszul complexes and original quotient resolutions

This family extends `ChainComplex.Koszul` on mathlib's actual nonnegative
chain complexes of module categories. Its present consumer is the local
regular-immersion calculation for Serre duality. The source selection and
hashes are recorded in [the migration record](../../../../doc/migration/motivic-koszul.json).
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

The current tensor construction uses the native same-universe module monoidal
category in the finite-list leaves; the independent universes of the single
factor are retained. These results do not supply a canonical exterior basis,
a determinant-valued top class, arbitrary change-of-generators compatibility,
or geometric regular-immersion purity. Those remain separate Serre inputs.

[Ext](Ext.lean) is a native downstream calculation from the supplied
resolution, not another imported source implementation. A weakly regular
list gives the actual quotient `R / Ideal.ofList s` projective dimension at
most `s.length`. Every original Ext class above that bound vanishes for
arbitrary coefficient modules and arbitrary supported Ext universes. The
ring need not be Noetherian, the coefficient need not be finite, and the
empty list is included. This supplies the upper bound for purity; the
lower-degree vanishing and determinant-normalized top class for a general
list remain separate proof obligations. The [single-factor Ext guide](Single/README.md)
records the proved degree-one quotient class and concentration calculation.
