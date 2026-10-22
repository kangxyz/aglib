# Extension of an original generic projective map

Import `Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension`.

`exists_pointBlowupChain_projectiveExtension` starts with an integral Noetherian regular scheme X of dimension at most two, an actual map p:X→Spec R, a finite original coordinate type I, and an original gη:Spec K(X)→ProjectiveSpace R I satisfying its original base triangle. It constructs an actual finite `PointBlowupChain β`, with a proper birational map β:Y→X, regular integral source of local dimension at most two, and an actual h:Y→ProjectiveSpace R I. Its base triangle is h≫toSpec=β≫p. Its generic triangle is jY≫h=Spec.map(functionFieldMap β)≫gη, using the original canonical function-field map. No dominance of gη is assumed.

The original standard-chart factorization of gη supplies its actual rational coordinates with one coordinate equal to one. The native denominator and base-ideal construction supplies the original denominator line, original epimorphic coordinate row, nonzero base ideal and actual Artinian quotient. Finite point principalization makes the original inverse-image base ideal Cartier.

The source of `pulledCoordinateMap` is the literal pullback of the original denominator line. The original coordinate maps are pulled into the pulled base module and composed with the original canonical epimorphism onto the actual inverse-image ideal module. No identification of the whole pulled base module with its image, flatness of the point blowup, or denominator-comap identification is assumed. The original numerator and coordinate-one denominator inclusion equations remain exact.

`mapAfterPrincipalization` uses that same row with the existing line-source projective constructor. It retains the actual structural triangle, twisting pullback isomorphism and original indexed coordinate triangle. The coefficient line is the tensor of the dual of the literal pulled denominator with the actual inverse-image ideal module.

Generic recovery transposes the original numerator equation through the original generic-point pullback adjunction. An actual nonzero affine denominator section proves that the pulled denominator inclusion is nonzero, hence an isomorphism over the original function field. The actual generic-point square and canonical pullback-composition and unit maps transport these equations to K(Y). The selected coordinate and the actual base-ideal inclusion become isomorphisms there, so cancellation gives precisely the original function-field coordinate scalars.

The original pullback-tensor comparison carries those same scalars to the canonical projective section family; it does not require an assumed identification of a pulled dual with a dual of a pullback. The inverse selected section identifies the family with the original field-valued coordinate row. The native field-point/chart comparison then recovers the original gη and its base map. It needs no full coefficient-span, finite-field-extension, excellence, perfectness or algebraic-closure premise.

This owner extends a single original generic projective map. Composition for finite projective products and the integral lift through the actual Chow modification belong to the common-domination consumer. Native evidence is recorded separately against the exact frozen source vector.
