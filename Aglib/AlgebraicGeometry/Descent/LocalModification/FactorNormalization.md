# Finite normalization from the specified local terminal factor

Source: [FactorNormalization.lean](FactorNormalization.lean).

`genericNormalization_isFinite_of_stalk_factor` assumes normal integral
locally Noetherian original base `X`, a closed nongeneric point, and the
actual integral proper target `B → X` isomorphic off that point. The
supplied integral normal proper dominant stalk modification is isomorphic
on the actual punctured local spectrum, with an actual arrow into `B`
and its original commuting triangle.

`FactorReplacement` constructs a proper factor `R.Y → B`. Its source is
normal and integral by the already proved original-stalk replacement
criteria. The factor is isomorphic over the nonempty unchanged open,
giving its original birational function-field map. The native
proper-birational normalization theorem proves finiteness of the literal
generic normalization of `B`.

Thus no global normal model or finite normalization is an input oracle.
The proof still requires the specified local factor: in the point-chain
consumer this must be the factor through the actual first ordinary blowup.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/SupportedChain](SupportedChain.md).
