# Principal closed adjunction with an arbitrary coefficient

`Principal.lean` treats the literal quotient map `R -> R/(a)` over a
Noetherian commutative ring. The ambient coefficient `M` is quasicoherent;
coherent coefficients are included. The equation is regular on `R`, and
concentration additionally requires that it act injectively on the actual
module `Gamma(Spec R,M)`. No local freeness, domain, Gorenstein, or nonzero
coefficient hypothesis is used.

The quotient carries the original `R/(a)` action. FiniteSource's original
injective-resolution map and tilde/global-sections counit reconstruct its
sheaf. `derivedClosedImmersionRightAdjointPrincipalKoszulHomologyIso` and
`derivedClosedImmersionRightAdjointPrincipalKoszulIso` preserve the existing
Koszul representative: a quotient element represented by `x` is sent to
`singleIdealExtOneClass a ha (Gamma M) x`. Other homology vanishes using the
original principal Ext calculation and coefficient regularity.

There is a separately named positive comparison. The original scalar row is

    0 -> M --a--> M -> i_*Q -> 0.

Its quotient map is transported only through the original affine counits.
`principalCoefficientExtensionMate` is the actual installed derived adjoint
of this row's native positive `extClass`. For every quotient-source module
sheaf `T`, the equation acts by zero on `i_*T`, whereas it acts injectively
on `M`. The native covariant Ext sequence consequently makes

    Hom(T,Q) -> Ext^1(i_*T,M),   f |-> f^* extClass,

bijective. The already constructed concentration and full faithfulness of
native singles then prove that the mate is an isomorphism. Its inverse gives
`derivedClosedImmersionRightAdjointPrincipalDegreeOneIso`; native shift and
single full faithfulness give `derivedClosedImmersionRightAdjointPrincipalIso`.
The latter's homology comparison is
`derivedClosedImmersionRightAdjointPrincipalHomologyIso`.

The two `_counit` theorems state the actual inverse derived-adjunction formula,
with the positive extension class of the original row. Positivity is therefore
proved from that row and the actual adjunction, rather than supplied as a
compatibility premise. The original cohomology boundary formula is retained.
This is a covariant coefficient boundary; it must not be replaced by Mathlib's
signed contravariant `Ext.delta`.

Coefficient naturality uses the actual cokernel map and the same derived
coefficient arrow. A unit change `a -> u*a` uses identity on the left term,
multiplication by `u` on the middle term, and its actual induced quotient map.
The displayed quotient and extension-class laws retain this same unit. The
principal ideals agree by their canonical equality. The raw geometric
principal-open homology map is identified with the original exact
scalar-extension Ext map and its original source/coefficient isomorphisms.
The positive extension class also retains exact sheaf restriction.

The raw Koszul and positive comparisons have **not been identified with each
other**. Full compatibility of the positive comparison with the installed
derived open exchange is also not asserted. The localization statements just
described do not assert either missing identity. These remain separate
normalization obligations. No global Cartier theorem,
canonical curve concentration, Serre pairing, field descent, or surface
Gorenstein theorem follows from this pair alone.
