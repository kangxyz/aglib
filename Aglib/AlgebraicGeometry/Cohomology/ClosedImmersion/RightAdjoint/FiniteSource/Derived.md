# Original derived closed-adjoint homology

`Derived.lean` transports the finite-source quotient-resolution calculation to
the original installed `derivedClosedImmersionRightAdjointPlus` on the original
coefficient in degree zero. Its model arrow is the inverse original
injective-resolution comparison followed by the native homology factorization.
Its open arrow uses exact restriction, the installed derived open exchange, and
the exact-single comparison.

For a closed immersion into a locally Noetherian scheme and a finitely
presented ambient coefficient, every homology sheaf is finitely presented and
has closed ordinary stalk support. The affine proof obtains the actual
quotient presentation from `IsClosedImmersion.Spec_iff`; the global proof uses
the original affine restrictions. Neither coherence nor a comparison
isomorphism for the output is a hypothesis. Negative homology vanishes from
the original nonnegative injective resolution.

For the literal affine quotient, the actual derived homology stalk is
identified with Ext over the actual ambient stalk with its original quotient
source and coefficient stalk. The displayed germ law retains the inverse
derived-model map and the lower original section-homology germ; the lower
stalk theorem identifies this with the original exact-functor Ext map.

The module does not assert concentration, identify a trace, or make a
canonical module locally free. Its consumer is the chosen-embedding
normal-surface concentration argument; that assembly is outside this
frozen prerequisite cohort.
