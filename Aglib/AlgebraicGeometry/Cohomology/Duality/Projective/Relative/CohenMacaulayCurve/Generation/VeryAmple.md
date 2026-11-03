# Evaluation and descent for coefficient canonical generation

Source: [VeryAmple.lean](VeryAmple.lean).

`globalSectionsEval_sections_surjective` proves surjectivity on sections
of the original all-sections evaluation without assuming global generation.
The isomorphism and finite-sum variants retain the actual coproduct
inclusions and given coefficient maps.

The descent criterion uses a surjective flat affine-base Cartesian
change of a qcqs scheme and a quasicoherent target. Naturality of the
original H0 scalar mate proves epimorphy without requiring the source
mate invertible. The exact evaluation-plus-section transport also keeps
the specified hyperplane-line isomorphism.

The ambient coefficient comparison uses the same ordered determinant,
twisting-sheaf pullback and original tilde coefficient pullback, without
choosing a basis of the arbitrary coefficient module `V`.
Bijectivity of the original structural H0 map is derived when that H0
module is finite and has dimension one, using the original unital
section formula.

The field-extension adapters retain the same projective pullback curve,
its structural square, original cohomology tensor map and twisting
comparison. `cmCurveCohomologyFieldExtension_subsingleton` transports
vanishing through that same map.

These evaluation and field-extension interfaces do not supply the global
canonical own-homology comparison or final arbitrary-field coefficient
canonical generation. The actual coefficient line remains explicit.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert/ScalarExtension](../AnticanonicalHilbert/ScalarExtension.md).
