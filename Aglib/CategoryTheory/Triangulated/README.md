# Natural transformations on distinguished triangles

[NatTransIso](NatTransIso.lean), imported as `Aglib.CategoryTheory.Triangulated.NatTransIso`, gives `CategoryTheory.NatTrans.mapTriangleHom` for the actual shift-compatible transformation between triangulated functors. It retains the original triangle arrows and shift comparison.

`isIso_app_middle_of_distinguished` proves invertibility at the middle vertex of an actual distinguished triangle from invertibility at its two ends. Triangulated functors, transformation/shift compatibility and distinguishedness are premises. The statement is not a two-out-of-three assertion for arbitrary diagrams.

Bounded homotopy/D+ term comparisons and the actual short-exact triangle constructions are current consumers. Exact source conditions and locators appear in [latest-homology](../../../doc/migration/latest-homology.json).
