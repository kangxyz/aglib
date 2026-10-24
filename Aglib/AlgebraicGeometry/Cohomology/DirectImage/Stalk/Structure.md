# Original local structure cohomology and the R1 stalk

[Structure.lean](Structure.lean) constructs the cohomological comparison for
a supplied actual local-spectrum pullback square. It retains the caller's
schemes and original maps

```lean
h : Y ⟶ X
x : X
a : T ⟶ Y
p : T ⟶ Spec (X.presheaf.stalk x)
square : IsPullback a p h (X.fromSpecStalk x)
```

The only geometric hypotheses of this callback are `QuasiCompact h` and
`QuasiSeparated h`. Properness supplies them in its intended application.
Normality, Noetherianity, dimension and completeness are unnecessary here.
Flatness of the original `X.fromSpecStalk x` is derived, and QC+QS for the
original p follow from the supplied Cartesian square.

`originalStructureH1StalkLinearEquiv` identifies the actual stalk of
`((pushforward h).rightDerived 1).obj O_Y` with H1(T,O_T), linearly over
the original ring `X.presheaf.stalk x`. Its symmetry is the requested
H1-to-stalk equivalence. Both structure modules are the original native
unit modules. The action on local cohomology is exactly

```lean
p.appTop.hom.comp (ΓSpecIso (X.presheaf.stalk x)).inv.hom
```

This is the original structural action of p. The construction introduces
no replacement field, transported scalar action, or arbitrary additive
equivalence.

The comparison is the composite of four specified original factors:

1. `stalkFromSpecStalkSectionsIso` on the original R1 sheaf, retaining the
   native scalar-extension unit and original pullback-stalk/germ maps.
2. Global sections of `higherDirectImageFlatBaseChangeIso` for the supplied
   a, p, h and `X.fromSpecStalk x`. Its forward arrow is the original flat
   higher-image base-change map.
3. Global sections of the original higher-image functor applied to
   `pullbackUnitIso a`, the canonical map identifying a*O_Y with O_T.
4. `moduleHigherDirectImageAffineSectionsLinearEquiv` for the actual p
   and O_T, with its original section/resolution normalization.

The existing canonical-pullback stalk comparison supplies the same pattern.
This variant applies directly to the caller's actual T and Cartesian
square, with the canonical structure-coefficient comparison included.

`original_localStructureH1_subsingleton_of_R1_isZero` applies the original
stalk functor to a proved zero result for the global R1 sheaf and transfers
that vanishing through this specific linear equivalence. The input is
the previous global R1 theorem's conclusion; desired local H1 vanishing
is not assumed.

Construction of an actual proper normal birational local replacement is a
separate geometric supplier. Its output must give the original Cartesian
square above, along with any normality and birationality properties needed
to obtain global R1 vanishing. This module does not assert that such a
replacement exists for every local model, or conclude universal local
rationality or resolution.

Source basis: Aglib HEAD `f27c5fa9b8f76147e16caacf52f56f26eabddb87`,
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
