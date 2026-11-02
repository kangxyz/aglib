# Survivor projections and residue transport

Source: [CurveSurvival.lean](CurveSurvival.lean).

For proper composable maps, `Hom.irreducibleClosedImage_comp` identifies
successive proper images with the image under their original composite.
`Hom.genericPoint_image_eq` turns an equality of proper-image closed subsets
into the equality of their original generic points.

`transcendental_residue_stalkMap` pulls the retained stalk element through
the original projection and preserves transcendence over the old image-point
residue field. Its scalar map is the original composite residue-field map;
residue naturality and `residueFieldMap_comp` give the required equation.
`SelectedStep` then passes to the new image-point scalars using the finite
residue-extension theorem.

These laws also identify the composite curve embedding in `Comparison`,
without assuming finiteness of an accumulated fibre-product pair.

Present consumers: [Comparison](Comparison.md), [SelectedStep](SelectedStep.md).
