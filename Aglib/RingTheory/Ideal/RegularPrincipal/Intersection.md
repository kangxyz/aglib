# Regular images and ideal intersection

`Intersection.lean` proves two statements for arbitrary commutative rings.
Every displayed principal generator of an ideal linearly equivalent to the
ring is regular. The proof uses the existing regular generator and the fact
that every factor of a regular product is regular.

For an actual ring homomorphism `φ : R →+* S`, if `I = Ideal.span {a}` and
`φ a` is regular in `S`, then `I * RingHom.ker φ = I ⊓ RingHom.ker φ`.
Indeed, `r * a` in the kernel forces `r` into the kernel by cancellation in
`S`. Neither surjectivity of `φ` nor regularity of `a` in `R` is required.

The Cartier product/intersection comparison supplies these hypotheses on
actual affine section rings. No tensor or ideal map is redefined here.
