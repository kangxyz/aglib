# Natural transformations and endpoint transport of triangles

[NatTransIso](NatTransIso.lean), imported as `Aglib.CategoryTheory.Triangulated.NatTransIso`, gives `CategoryTheory.NatTrans.mapTriangleHom` for the actual shift-compatible transformation between triangulated functors. It retains the original triangle arrows and shift comparison.

`isIso_app_middle_of_distinguished` proves invertibility at the middle vertex of an actual distinguished triangle from invertibility at its two ends. Triangulated functors, transformation/shift compatibility and distinguishedness are premises. The statement is not a two-out-of-three assertion for arbitrary diagrams.

[EndpointTransport](EndpointTransport.lean), imported as `Aglib.CategoryTheory.Triangulated.EndpointTransport`, owns `CategoryTheory.Pretriangulated.Triangle.transportEndpoints` and `transportEndpointsIso`. For a functor `A : J ⥤ Triangle C` and specified isomorphisms `e₁,e₂,e₃` from functors `F₁,F₂,F₃ : J ⥤ C` to its vertex functors, the construction transports all three arrows through those isomorphisms. The third arrow uses the shifted inverse of `e₁`; `transportEndpointsIso` identifies the transported triangle functor naturally with `A`. This construction requires only category structures and `HasShift C ℤ`, without a pretriangulated structure or distinguishedness premise.

Bounded homotopy/D+ term comparisons and the actual short-exact triangle constructions are current consumers. Exact source conditions and locators appear in [latest-homology](../../../doc/migration/latest-homology.json).
