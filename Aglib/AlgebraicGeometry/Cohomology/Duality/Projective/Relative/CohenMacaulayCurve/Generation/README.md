# Cartier sections and coefficient canonical generation

[Hyperplane](Hyperplane.lean) constructs a regular finite hyperplane through
a supplied rational point on the original closed projective curve over an
infinite field with finite coordinates. Its closed stalks have a regular
nonunit whose principal ideal has maximal-ideal radical. The result retains
the pulled polynomial section, its actual zero scheme and the original
rational-point lift; the curve need not be reduced.

[RegularCanonicalSection](RegularCanonicalSection.lean) uses the original
chosen-embedding coefficient canonical sheaf and a finite rank-one
coefficient module. For an actual finite Cartier closed subscheme, it proves
monicity of the original Cartier tensor section and short exactness of its
coefficient row, with the actual finite-support quotient.

[VeryAmple](VeryAmple.lean) supplies all-sections evaluation and flat-pullback
descent interfaces. These preparatory maps do not assert full
arbitrary-field coefficient canonical generation. A consumer must supply
the actual canonical comparison and generation argument with its original
coefficient line.

Present consumers include [Hyperplane powers on the full coefficient curve](../AnticanonicalHilbert/README.md), [Cohomology of projective curves with a coefficient line](../README.md).
