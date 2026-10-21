# Proper birational isomorphism at a valuation-ring stalk

Native owner: [BirationalDVR.lean](BirationalDVR.lean).

The new theorem `AlgebraicGeometry.Scheme.properBirationalDVRIsomorphismLocus`
supplies the existing `Scheme.ProperBirationalDVRIsomorphismLocus` proposition.
For integral schemes `X` and `Y`, a locally Noetherian `Y`, and a proper dominant
`f : X ⟶ Y`, it uses the supplied isomorphism of the actual contravariant
`Scheme.functionFieldMap f`. At every point `y` with an actual DVR stalk, it
constructs a target open neighborhood `U` containing `y` and proves
`IsIso (f ∣_ U)`.

The stronger theorem
`Scheme.exists_isIso_restrict_of_isProper_birational_at_valuationRing` requires
only a valuation-ring stalk at `y` and does not require local Noetherianity.
Neither result adds global normality, a dimension bound, or a lifting,
spreading, or isomorphism-locus family premise.

## Argument and exact maps

The inverse of `Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap f))`,
followed by the original generic-stalk map of `X`, defines an actual map
`g : Spec Y.functionField ⟶ X`. The naturality theorem
`Scheme.fromSpecStalk_genericPoint_naturality` proves that `g` lies over the
original generic-stalk map of `Y`. Since the function-field map is invertible,
`g` is dominant.

The existing theorem `Scheme.exists_open_extension` extends `g` over
`Spec (Y.presheaf.stalk y)` by the properness valuative criterion and spreads
that extension to a map `s : U.toScheme ⟶ X`. It preserves both the generic
triangle and `s ≫ f = U.ι`. Its use of Mathlib's
`spread_out_of_isGermInjective'` requires only local finite type and injective
germs, supplied respectively by properness of `f` and integrality of `Y`.
The literal function field is the fraction field of the literal stalk via
Mathlib's existing instance. No substitute field or arbitrary birational
identification is introduced.

The generic triangle makes `s` dominant. The new general theorem
`Scheme.isIso_restrict_of_dominant_section` lifts `s` to the actual pullback
open `f ⁻¹ᵁ U`. This lift is a section of `f ∣_ U` and remains dominant.
The pullback open is reduced. Mathlib's
`ext_of_isDominant_of_isSeparated` proves the other inverse identity, since
the restricted morphism is separated and the two endomorphisms agree after
the dominant section. This proves invertibility on the entire inverse image
of `U`, in addition to the local-spectrum statement.

## Source identity and consumer

The accepted statement is at lines 37–42 of
[BirationalInterfaces.lean](BirationalInterfaces.lean), original Aglib checkout
HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4`; its source SHA-256 is
`d759b5781eb8c442f7a545e5f3302d9348c506f2021e7184bb6cb42eea8f8f60`.
That interface records the R5 origin at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, source SHA-256
`150d0c411e909cb01dfc6df85d20fb12c3a5db18797b35882c4ac67b3ec87b6c`.
The supplier is a new proof, not an extraction of an existing R5 supplier.

The reused [GenericExtension.lean](GenericExtension.lean) source SHA-256 is
`ab6b4efb6aede54825396dc316aed860a350a0e15bba7297a9fe90440a33cec5`.
The actual function-field map is owned by
[FunctionField/Map.lean](../../FunctionField/Map.lean), source SHA-256
`195b3d34ad67dbf32d7e102bcb7733404e36d2a5b130c76c7dcbb7de84ddcc54`.
The pinned dependencies are Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

[ProperBirationalDVR.lean](../../../../AglibTest/ProperBirationalDVR.lean)
checks the exact universe-polymorphic family, the stronger valuation-ring
statement, and direct use of the supplier by the existing
`Scheme.Hom.isIso_of_dvr_off_generic` consumer. Existing interfaces and
consumers retain their explicit arguments; this leaf does not edit them.

Compilation evidence and hashes of the new files are returned in the assigned
scratch manifest. Compilation is scoped elaboration evidence; separate
package validation and mathematical-adoption requirements retain their own
evidence boundaries.
