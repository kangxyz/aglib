# Actual coefficient transport for node schemes

[CoordinateTransport](CoordinateTransport.lean), in `Scheme.PowerNode`, proves
that the spectrum of the literal coefficient node ring is the actual pullback
of the original node scheme. Both projection equations use the original
structural and coefficient ring maps. No flatness or field assumption is
required for this tensor comparison.

Pure node algebra belongs to [PlaneNode](../../../RingTheory/PlaneNode/README.md)
and its saturated power-node chart computations to
[PowerNode.Rees](../../../RingTheory/Blowup/PowerNode/README.md). The coefficient
comparison does not construct a global blowup or a node resolution.

Focused interface guides: [Pinching two points of a line](PinchedLine.md).
