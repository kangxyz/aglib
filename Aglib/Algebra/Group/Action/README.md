# Torsor augmentation algebra

`TorsorAugmentation` owns `AddAction.TorsorAugmentation`. An additive action with
unique transport between existing sections gives differences, the free-abelian
augmentation and its kernel-difference map. Surjectivity conclusions retain the
stated nonempty-carrier assumption; the general transport predicate permits an
empty carrier.

The naturality formulas keep the specified equivariant coefficient/carrier
maps. The construction is generic additive-action algebra; actual small-etale
torsor extension classes are its current consumer.

[CyclicCoefficients](CyclicCoefficients.lean) owns
`ZMod.unitCharacterAction`, `inverseUnitCharacterAction` and
`addHomEvalOneEquiv`. The unit character and its continuity are supplied inputs;
the coefficient reduction and insertion maps are in [Data/ZMod](../../../Data/ZMod/README.md).
