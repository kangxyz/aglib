# Generic stalks of literal special-fibre components

[ComponentKernel](ComponentKernel.lean), in `Scheme.FlatDVR`, defines the actual
constant pullback followed by the actual germ as a transparent `stalkScalar`
adapter to `Scheme.Hom.stalkScalar` from [Scalar](../Scalar.lean). The bridge
`stalkScalar_eq_canonical` is `rfl`. The lower owner proves flatness of this
actual map and preservation of every base nonzerodivisor for a flat scheme
morphism, over any commutative base ring.

[ComponentKernelProof](ComponentKernelProof.lean) supplies the exact original
`FlatDVRFibreComponentKernel` family through `flatDVRFibreComponentKernel`.
For a flat map from a locally Noetherian scheme to a domain DVR and an integral
closed component of the literal special fibre, every actual uniformizer image
is a nonzerodivisor, and the original composite stalk-map kernel is minimal
above its principal ideal at every component point. All original quantifiers
and hypotheses remain. No regularity, excellence, properness, whole-fibre
reducedness or component inventory is added.

The minimal-prime half uses neither flatness nor local Noetherianity. It combines
the actual closed-component kernel theorem in
[ComponentStalk](../../Morphisms/ClosedImmersion/ComponentStalk.lean), the actual
principal projection-stalk kernel in [PrincipalBaseChange](../PrincipalBaseChange.lean),
and surjective ideal correspondence. Flatness supplies the nonzerodivisor half
through the canonical scalar map.

[Component](Component.lean) derives actual dimension one at the image of the
component's generic point from that family. It constructs a genuine
`Scheme.CodimensionOnePoint`; normal actual stalks then give its DVR structure.
These corollaries retain their explicit family argument and use the original
integral-source and local-Noetherian hypotheses; the separate proved supplier
can now fill that argument. Broader surface-dimension and flat-local
regularity-descent families remain explicit inputs in their respective owners.

The lower [codimension-one provider](../CodimensionOne.lean) owns the actual
point subtype, its stalk and residue field, the canonical generic-stalk map,
unit maps and global-germ compatibility. Its DVR instance uses integrality,
local Noetherianity, dimension one and integral closedness of all actual stalks.
The component proof reuses `Ideal.minimalPrime_height_one` from
[HeightOne](../../../RingTheory/Ideal/HeightOne.lean).

The source component/model constructions consume this exact point and these
maps. No component count or intersection-degree statement is assumed here.
