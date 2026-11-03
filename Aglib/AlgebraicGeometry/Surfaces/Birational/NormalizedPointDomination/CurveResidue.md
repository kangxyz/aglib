# The contracted curve and its image-point scalars

Source: [CurveResidue.lean](CurveResidue.lean).

Let `C` be an irreducible closed curve contracted by a proper map `p : X ⟶ Y`.
`CurveResidue.curve C` is the schematic image of the residue-field inclusion
at its original generic point. It is integral; its closed immersion
`inclusion C` has range exactly `C`, and `curveHomeomorph` proves its
dimension is one.

The image of that generic point is closed.
`toPoint` factors the original composite through `Spec κ(p(η_C))`,
and `toPoint_comp` records its original triangle.
`exists_affine_transcendental_unit` gives a unit on a nonempty affine chart
of this curve, transcendental for that structural scalar map, using
`GraphInput.exists_affine_transcendental_unit`.

`GenericResidueSection` transports this section through the original generic
residue map and lifts it into the ambient curve-generic stalk.

Present consumers: [GenericResidueSection](GenericResidueSection.md).
