# Arbitrary module colimits under closed pushforward

[Colimits](Colimits.lean) proves that the actual pushforward along a
topologically closed embedding preserves any colimit whose image diagram
has a colimit. The diagram-object and diagram-morphism universes are independent.
For a closed immersion this gives `PreservesColimitsOfSize` in the scheme
universe on all module sheaves, without quasicoherence or Noetherianity.
The original mapped cocone is detected by native joint stalk reflection:
at image points it is the scalar-restricted original stalk cocone, while
off the closed image the entire stalk functor is zero.

[The parent leaf](../ClosedImmersion.lean) owns exactness. These actual
all-module results provide the ordinary closed-immersion right adjoint
through the native special adjoint functor theorem; they do not assert
that closed pushforward is fully faithful on derived categories.
