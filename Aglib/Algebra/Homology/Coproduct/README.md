# Native homology of exact coproducts

Import `Aglib.Algebra.Homology.Coproduct.Homology`.

For an abelian category `C`, an arbitrary complex shape `c`, and a family
`K : κ → HomologicalComplex C c`, `HomologicalComplex.coproductHomologyIso K i`
identifies the original homology of the categorical coproduct with the
categorical coproduct of the original homology objects. The exact hypothesis
is `HasExactColimitsOfShape (Discrete κ) C`, together with existence of those
colimits. No boundedness or finiteness of `κ` is required. Module categories
supply exactness through their native AB4 instance.

The construction views the original family as a complex of discrete diagrams
and applies the native `ShortComplex.mapHomologyIso` for the actual colimit
functor. Its degreewise colimit complex is compared with the actual categorical
coproduct through its original colimiting cofan. The theorem
`homologyMap_sigma_ι_coproductHomologyIso_hom` retains every original `Sigma.ι`:
the actual homology map of an inclusion, followed by the comparison, is the
original inclusion of the corresponding homology object. Thus consumers can
transport actual summand and coefficient maps, rather than only dimensions.

Category, morphism, family-index and complex-degree universes are independent.
The leaf was compiled alone through the shared serialized wrapper, receipt
`1792084112572414000-90470`. The external task probe
`work/proper-validation/CoproductHomologyConsumer.lean` checks the general
abelian statement, inclusion normalization, and module coefficients with
independent ring and index universes.
For those independent module universes the probe obtains exactness through
the native additive-group AB4 instance, shrunk to the actual index universe,
and the original forgetful functor; it does not assume a ring-universe equality.
The successful consumer receipt is `1792084336817993000-96727`; the comparison
and inclusion formula use only `propext`, `Classical.choice` and `Quot.sound`.
