# Low-degree multiplication cones

Import the base leaf `Aglib.Algebra.Homology.MultiplicationCone` for
`AddCommGrpCat.MultiplicationCone.Complex`: four actual additive groups with
three explicit differentials and the two consecutive-zero identities. These
finite truncation data permit independent term universes. Its coefficient-cone
cocycles use `d₁ a = n • b` and `d₂ b = 0`; their boundary and all quotient maps
are constructed from these differentials.

The constructed connecting map has image exactly the `n`-torsion in integral
second cohomology. Its kernel is the image of the integral-to-finite map, whose
kernel is exactly the multiples of `n`. Coefficient insertion multiplies only
the first component by the cofactor, while reduction multiplies only the
second. Their connecting-map identities and chain-map naturality retain these
original formulas, including coefficients zero and one.

[Quotient](Quotient.lean) compares cone cohomology with the actual termwise
quotient complex by first-component projection. Surjectivity requires
injectivity of multiplication by `n` in degree three; injectivity requires it
in degree two. These are separate hypotheses. The ordinary quotient insertion
and reduction squares use the same coefficient maps.

[HomologyTransport](HomologyTransport.lean) compares the finite-truncation
homology maps with Mathlib's actual short-complex homology maps. Supplied
`QuasiIso` or `QuasiIsoAt` evidence gives the stated bijectivity. The full
chain-complex low-degree adapter keeps the original differentials and chain
map components. It supplies no external cohomology comparison theorem.

The neighboring [UnitsComplex](../UnitsComplex.lean) computes a single nonzero
units term in degree two, its root classes and connecting map. All these
calculations use this same cone interface.
