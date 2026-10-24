# Formal fibres over an actual complete surface base

[SurfaceFormalFiber.lean](SurfaceFormalFiber.lean) gives the formal-fibre
argument corresponding to Section 3 of the R.F1c complete-base source
packet, revision 2, SHA-256
`9a953be7a5616a242d86dfeb0fe7ab02183196e5e8efc0c84f0e61e1334a38fe`.

The source and target are the original local domains `A` and `B`, both of
dimension two, with `B` Noetherian. The hypotheses retain the original `Algebra A B`, its
injectivity and locality, completeness of `A`, and finiteness of the canonical
residue extension. The target completion is literally
`AdicCompletion (IsLocalRing.maximalIdeal B) B`.

The lower helper derives module finiteness from base completeness, finite
residue degree, and a maximal-primary extended maximal ideal. A generic
formal prime of positive height would give a quotient of dimension at most
one. Its map from `A` is injective, its extended maximal ideal is primary, and
its residue module is finite, so the helper makes it finite over `A`.
Lying over then forces `A` itself to have dimension at most one, a contradiction.
No normality, reducedness or domain premise is imposed on the completion.

The public conclusions are minimality of primes over zero, incomparability
of primes in every formal fibre, and dimension zero of the actual
`p.Fiber` tensor algebra. The last step uses Mathlib's
`PrimeSpectrum.primesOverOrderIsoFiber`, preserving its canonical residue-field
and completion coefficient maps.

The mathematical method is the dimension-two specialization recorded in the
R.F1c packet, related to Đoàn Trung Cường, *Local rings with zero-dimensional
formal fibers*, VIASM 12.30, Theorem 1.4(a), pp. 4–5. The upper consumer is
[NormalSurface](NormalSurface.md); this leaf does not assert a G-ring or
excellence theorem.
