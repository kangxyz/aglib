# Actual tensor powers and specified power trivializations

The leaves retain actual line bundles, their recursively constructed tensor
powers and specified trivializations. Pullback uses the native canonical
tensor comparison, its adjunction mate and the proved unit comparisons.
`Pullback.lean` and `PullbackNaturality.lean` give the corresponding power and
pair maps with the original identity and composition coherences.

`TrivializedPower.lean` records actual pairs and their isomorphism quotient.
`Coherence.lean` gives the recursive formulas used by generic and Kummer
applications. These constructions apply to arbitrary schemes. Integer-level,
unit or etale conditions are retained at their actual torsor consumers; no
Picard representability or curve inverse law is supplied here.

Source: R5 packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
selected `R5Lab.Aglib.AlgebraicGeometry.Picard` power leaves. The torsor,
associated-bundle, descent and H1 consumers have their native Picard import
paths and native `Scheme.Modules.Invertible` declaration owners.
