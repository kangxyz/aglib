# Actual mapping cones, cone maps and exactness

[QuasiIso](QuasiIso.lean), imported as `Aglib.Algebra.Homology.MappingCone.QuasiIso`, proves `CochainComplex.quasiIso_of_mappingCone_acyclic`. [Acyclicity](Acyclicity.lean) proves the converse `CochainComplex.mappingCone_acyclic_of_quasiIso`. For an actual integer-indexed cochain map in any abelian category, these are the two directions of the criterion relating quasi-isomorphism to acyclicity of its actual cone. They use Mathlib's original mapping-cone triangle and homotopy quotient.

[Map](Map.lean), imported as `Aglib.Algebra.Homology.MappingCone.Map`, exposes `CochainComplex.mappingCone.map_add`: the actual mapping-cone map is additive in the two maps of a commutative square. This law holds for integer-indexed cochain complexes in any preadditive category with binary biproducts.

[Identity](Identity.lean), imported as `Aglib.Algebra.Homology.MappingCone.Identity`, constructs `CochainComplex.identityConeFunctor`, sending `K` to `mappingCone (𝟙 K)`. Its `identityConeTermIso` identifies degree `n` with `K.X (n + 1) ⊞ K.X n`; `identityConeTermIso_naturality` identifies the actual component maps. The functor is additive, preserves displayed pushouts and monomorphisms, maps zero objects to zero objects, and preserves actual short exact sequences. `coneSequence_shortExact` supplies the original rotated cone short complex. These identity-cone statements retain the arbitrary abelian coefficient category and make no boundedness assumption.

[WeakMap](WeakMap.lean), imported as `Aglib.Algebra.Homology.MappingCone.WeakMap`, proves `CochainComplex.mappingCone_map_quasiIso`. For a commutative square `f ≫ b = a ≫ g` of integer-indexed cochain complexes in an abelian category, quasi-isomorphisms `a` and `b` induce a quasi-isomorphism of the literal `mappingCone.map f g a b h`. `mappingCone_triangle_shortExact` and `mappingConeTriangleShortComplexMap` retain the original signed rotated cone sequences: their outer maps are `b` and the shift of `a` by one. No term bound is required.

[ShortExact](ShortExact.lean), imported as `Aglib.Algebra.Homology.MappingCone.ShortExact`, constructs `CochainComplex.mappingConeNatTransFunctor α` for `α : F ⟶ G`, where `F,G : D ⥤ CochainComplex A ℤ` and `A` is abelian. Its degree-`n` comparison `mappingConeTermIso` is with `K.X (n + 1) ⊞ L.X n`; `mappingConeTermIso_naturality` identifies the actual cone map with the block-diagonal endpoint maps. If `D` is preadditive and both functors are additive, `mappingConeNatTransFunctor_shortExact` says that a short complex `S` has a short exact cone image whenever both `S.map F` and `S.map G` are short exact. The lower `CategoryTheory.ShortComplex.biprodMap` and `shortExact_biprodMap` supply the corresponding block-diagonal short-exact sequence in an abelian category.

The identity-cone pushout argument uses the lower [biproduct and cokernel pushout interfaces](../../../CategoryTheory/Limits/README.md). [Basis exactness](../../../Topology/Sheaves/README.md) and [flasque cohomology](../../../AlgebraicGeometry/Cohomology/Flasque/README.md) consume cone criteria. The identity-cone construction is admitted as generic homological algebra; its original cylinder or perfect-complex applications remain provenance.

[NullHomotopy](NullHomotopy.lean) proves that, in an arbitrary abelian category,
a nullhomotopy of a chain map followed by the original cone inclusion supplies
an actual chain lift up to an actual chain homotopy. Its proof uses the native
homotopy-category cone triangle and retains the original signed cone maps.

`WeakMap` and `ShortExact` were selected unchanged from local upstream commit
`451aeda`; their source/archive provenance and SHA-256 values remain in the
leaf headers. They provide native cone-square and term comparisons for the
finite-projective replacement of bounded flat complexes, without a new
cone object or replacement cohomology theory.

[Homology](Homology.lean) exposes the two exact native homology short
complexes `mappingCone.homologyLeftShortComplex` and
`homologyRightShortComplex`. Their arrows are the original homology maps
and Mathlib's `CochainComplex.homologyδOfTriangle`, with the original signed
cone triangle. `mappingCone.isZero_homology_of_epi` kills the cone homology
in degree `i` when the original degree-`i` homology map is epic and the
next source homology is zero. `mappingCone.isLE_of_epi_top` consequently
lowers the cohomological upper bound from `n` to `n-1`. These results hold
in an arbitrary abelian category and assume neither term bounds nor flatness
or module finiteness. Native standard derived localization occurs only
inside the proofs; no derived-model or chosen-localization premise is added.
The leaf passed with receipt `1792097779046128000-41106`.
The external `work/proper-validation/MappingConeHomologyConsumer.lean`
passed with receipt `1792097841622995000-43232`. It checks arbitrary abelian
coefficient universes, original maps by definitional equality, exactness,
top vanishing and the lowered bound. All four inspected declarations use
only `propext`, `Classical.choice`, and `Quot.sound`.

[Rotation](Rotation.lean) uses the actual native double rotation to construct
`mappingCone.rotateTwiceHomotopyEquiv` from the original cone projection's
mapping cocone to the original middle complex. It passes through a genuine
native isomorphism in the homotopy category and the native lift of that
isomorphism to an actual homotopy equivalence. Its quotient normalization
retains precisely this chosen homotopy-category isomorphism; it does not
infer a complex comparison from homology isomorphisms.

`mappingCone.reassemblyMap φ s` is the actual map from
`mappingCocone (s ≫ (mappingCone.triangle φ).mor₃)` to the original target
of `φ`. Its definition and `_eq` theorem retain the literal native cone
square, shift by minus one, and cancellation map. In an abelian category,
`reassemblyMap_quasiIso` proves it is a quasi-isomorphism whenever the
original `s` is. `reassemblyTermIso` identifies its source term with the
actual `Q.X i ⊞ K.X i`; it requires only a preadditive category with binary
biproducts. The cancellation data additionally uses a zero object. No term
bounds, projectivity or finiteness enter these generic constructions.
The leaf passed with receipt `1792098400411176000-55379`.
The external `work/proper-validation/MappingConeRotationConsumer.lean`
passed with receipt `1792098489413419000-57063`. It checks the actual
homotopy equivalence, chain map, native term transport and quasi-isomorphism
in independent coefficient-category universes. All four inspected
constructions use only the same three standard axioms.

The shared single-leaf wrapper compiled `WeakMap` with receipt
`1792096482648885000-11410` and then `ShortExact` with receipt
`1792096521480140000-12363`. The external
`work/proper-validation/MappingConeImportedConsumer.lean` passed with receipt
`1792096587783023000-13452`, checking the literal cone map, signed short exact
sequence, term naturality, and coefficient short exactness for independent
category universes. All four inspected declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Both source files were also checked byte
for byte against their selected upstream revision.
