# Homology of a two-stage cochain square

Source: [TwoStageSquare.lean](TwoStageSquare.lean).

`HomologicalComplex.homologyMap_twoStage_square` derives the complete homology
square from the supplied original cochain square. The four exact additive
functors, actual complexes, coefficient arrows, comparison isomorphism and
independent object and morphism universes remain explicit. No counit or desired
homology square is assumed invertible or supplied as a replacement premise.

The original proof uses the existing exact comparison and two-stage counit laws.
This leaf keeps that general result separate from existing projective-duality
compatibility imports.
