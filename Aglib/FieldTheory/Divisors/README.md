# Fields with supplied divisor data

`Basic.lean` defines `Field.DivisorData C K Div`: an actual constant-field
embedding, an additive divisor homomorphism on `Additive Kˣ`, and the explicit
hypothesis `kernel_eq_constants`. It constructs the literal quotient by
principal divisors. There is no curve, Picard-group realization, or producer of
the kernel hypothesis here.

`FiniteConstants.lean` proves relative algebraic closedness of the actual
constant image when `C` is finite and `Div` is torsion free. `UnitPowers.lean`
proves positive-power descent and injectivity on constant unit-power quotients
under the same divisor-kernel and torsion-free hypotheses. Its separate finite
field quotient-cardinality theorem uses the actual finite cyclic unit group.

These are conditional field/divisor suppliers for downstream symbol and curve
arguments; a consumer must supply this exact divisor data.
