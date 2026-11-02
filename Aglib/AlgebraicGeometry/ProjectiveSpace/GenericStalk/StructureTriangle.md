# Original generic-image structural triangles

Source: [StructureTriangle.lean](StructureTriangle.lean).

Import `Aglib.AlgebraicGeometry.ProjectiveSpace.GenericStalk.StructureTriangle`.
The namespace is `AlgebraicGeometry.ProjectiveSpace`.

`genericImageBaseMap_eq_comp_of_structureTriangle` retains a commutative
DOMAIN R, actual integral X/Y, an original dominant f:Y -> X, actual maps
into the two projective spaces with dominant structural maps, and their
literal structural triangle. It proves the original genericImageBaseMap
composition through the original functionFieldMap f. The maps need not be
closed immersions; no finite coordinates, properness, normality,
Noetherianity or dimension premise is used.

`genericImageBaseMap_finite_of_structureTriangle` adds the genuine iso of
the original intervening field map and original generic-image finiteness.
It derives finiteness of the second original generic-image map. The proof
uses the SAME equation and native finite-map composition, not a chosen
fraction field, alternate scalar action or finite structural morphism.

These two calculations are moved once from ProjectiveSurfaceChain. That
actual consumer retains its full public signature and all output objects,
maps and triangles, and calls these exact lower theorems. The new native
ProjectiveStages consumer uses them on the original prefix maps.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/ProjectiveSurfaceChain](../../Descent/LocalModification/ProjectiveSurfaceChain.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveStages](../../Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveStages.md).
