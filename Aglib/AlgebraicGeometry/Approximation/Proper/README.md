# Proper finite-presentation approximation over an affine base

```lean
import Aglib.AlgebraicGeometry.Approximation.Proper.FiniteType
```

[FiniteType](FiniteType.lean) proves, in
`AlgebraicGeometry.Scheme.Approximation`:

```lean
theorem nonempty_properFinitePresentationSystem
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] :
    Nonempty (ProperFinitePresentationSystem f)
```

The base is any affine scheme. Properness of `f` is the only morphism
hypothesis; finite presentation, Noetherianity, flatness and projectivity are
not additional premises.

[ProperSystem](../ProperSystem.lean), imported as
`Aglib.AlgebraicGeometry.Approximation.ProperSystem`, defines
`ProperFinitePresentationSystem f`. It contains a small cofiltered
`diagram : index ⥤ Over S`, a cone, the explicit equality
`point : cone.pt = Over.mk f`, and a limiting proof for the cone forgotten to
schemes. Every stage is proper and locally finitely presented over the same
`S`. Every transition and every original cone projection is a closed
immersion. These data retain the original scheme and structural map through
`point`; the stages are not asserted to be nilpotent thickenings.

The proof first constructs a separated finitely presented
[closed envelope](../FinitePresentationEnvelope/README.md) over `S`.
Finite-type kernel ideals give a cofiltered system of closed superschemes
with the original source as limit. A constructed weak Chow modification of
the envelope and eventual closedness of the modified sources yield a proper
stage. `ProperFinitePresentationSystem.ofProperStage` takes the cofinal tail
below that stage, keeping the original point and limit proof.

The lower `isProper_of_closed_modified_stage` in `ProperSystem` takes
`Y W P : Over S`, maps `p : W ⟶ Y` and `q : W ⟶ P`, and
`Z : Over Y.left`. It assumes that `p.left` is surjective, `P.hom` is
proper, and the original structure map `Z.hom ≫ Y.hom` is separated and
locally of finite type. If the modified map
`pullback.snd Z.hom p.left ≫ q.left` is a closed immersion, the original
structure map `Z.hom ≫ Y.hom` is proper.

[Proper](../Proper.lean) exposes
`nonempty_properSystem_of_closed_finitePresentation_envelope` when the closed
envelope is supplied. The theorem in `FiniteType` constructs that envelope
and therefore removes it from the public premises.

The [proper henselian finite-étale theorem](../../Morphisms/FiniteEtale/ProperHenselian/README.md)
uses this system to descend a closed-fibre cover to a proper finitely
presented stage over the unchanged local base, then lifts at that stage.
This is a fixed-base approximation theorem; the
[arithmetic system](../FinitePresentationEnvelope/README.md) has a different
base and different transition hypotheses.
