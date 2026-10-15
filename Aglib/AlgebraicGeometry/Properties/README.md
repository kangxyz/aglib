# Scheme object properties

[Normal](Normal/README.md) owns normal-stalk and component properties. The quasi-compact category and affine-induction principles below are separate general scheme interfaces. It uses actual domain/integrally closed stalks, proves reducedness from that condition, and derives open components and connected integrality under local Noetherianity.

This extends the object-property subject of Mathlib's native `AlgebraicGeometry/Properties.lean`. Morphism properties and their field-relative hypotheses have their own [Morphisms](../Morphisms/README.md) owner; the directory grouping does not change the types of the underlying Mathlib predicates.

[QuasiCompactCategory](QuasiCompactCategory.lean) defines the actual `Scheme.QuasiCompactSchemes` full category and its inclusion. [AffineInduction](AffineInduction.lean) gives `Scheme.AffineInduction.of_qcqs`: an isomorphism-invariant property with its affine case and compact binary-open-union closure follows on quasi-compact quasi-separated schemes. Union closure explicitly requires the property on both opens and their intersection; the induction does not manufacture the overlap premise. The compact-open and separated variants retain their corresponding compactness/separation hypotheses.
