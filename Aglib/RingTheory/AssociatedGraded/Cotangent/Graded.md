# The original graded polynomial map

For a commutative ring `A`, an ideal `I`, and a displayed family `g : ι → I`,
this module constructs the native graded algebra map

`MvPolynomial ι (A/I) → gr_I(A)`.

Its target is the literal Rees quotient from `AssociatedGraded.Basic`, with
the canonical coefficient-quotient action from `AssociatedGraded.Cotangent`.
Every variable goes to the original degree-one Rees symbol of `g i`.
Every coefficient class uses the original quotient action, and every
coefficient lifted from `A` uses the original coefficient map.

The existing homogeneous components are initially submodules over `A`.
`associatedGradedQuotientGrading` expresses these same components over
`A/I`. The native scalar-span theorem and surjectivity of `A → A/I` prove
that the carrier is unchanged; `Submodule.copy` keeps that original carrier
definitionally. The graded-algebra instance reuses the existing graded
multiplication and decomposition. The restriction-of-scalars and
`associatedGradedQuotientGrading_decompose` equalities expose this identity.
No alternative decomposition or associated graded model is introduced.

`cotangentPolynomialMap` is the ordinary algebra map on the chosen original
ideal elements. Its variable and coefficient formulas are explicit. The
images of degree-one variables belong to the original degree-one component.
Native degree-one generation of the homogeneous polynomial components and
the existing graded multiplication prove preservation of every degree.
`cotangentGradedPolynomialMap` bundles this result as a `GradedAlgHom`.

`cotangentGradedPolynomialMap_surjective_of_cotangent_span` assumes only
that the actual classes of `g i` span the actual cotangent quotient over
`A/I`. Linearity puts every cotangent symbol in the polynomial map's image.
Induction in the native symmetric algebra, followed by the previously
proved canonical symmetric-algebra surjection, proves surjectivity.

`cotangent_span_of_ideal_span` derives that cotangent spanning from the
actual equation `Ideal.span (range fun i => (g i : A)) = I`, using the
original subtype and cotangent quotient maps. Thus
`cotangentGradedPolynomialMap_surjective` supplies the original graded
surjection directly from actual ideal generation. No finiteness of the
index type, Noetherianity, basis or minimality condition is required.

For a local ring with its actual maximal ideal and three displayed
generators, this is the graded polynomial map needed by the monic quadratic
kernel theorem. The actual quadratic relation and genuine geometric
Hilbert function remain separate inputs to that theorem. Normality,
rationality, Gorensteinness, same-field Case-II data and the RDP or resolution
application are not conclusions of this module.
