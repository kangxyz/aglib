# Coefficient naturality for the same original section family

Let `φ : R →+* S` be any homomorphism of commutative rings in the same
universe, let `p : X → Spec S`, and retain one actual module `M` and
one actual generating-section family on `X`. The theorem
`ProjectiveSpace.FromSections.SectionFrames.map_coefficients` proves

```text
F.map p ≫ ProjectiveSpace.map φ I
  = F.map (p ≫ Spec.map (CommRingCat.ofHom φ)).
```

Both sides use the identical supplied `SectionFrames F`. The original
scheme, module, sections, coordinate index, normalized frame coefficients,
and structure triangles are retained. There is no flatness, Noetherianity,
or nonemptiness assumption.

The proof first identifies the original base coefficient map on each
source open with composition by `φ`, using the native `ΓSpecIso`
naturality equation. The native projective chart map
`coordinateRingMap φ I i` preserves coordinate ratios and applies `φ`
to ring coefficients. These generator identities give equality of the
actual chart-ring homomorphisms. The original `coordinateRingMap_awayι`
formula then identifies the local scheme maps, and the same frame cover
proves equality globally. No alternative projective morphism is built.

`mapOfGeneratingSections_coefficients` and
`mapOfFiniteFamily_coefficients` specialize this equality to the native
maps from an original finite generating family. In the latter theorem,
the same actual `s : I → (unit X.ringCatSheaf → M)` and its epimorphic
coproduct map are used over both coefficient rings. The locally rank-one
condition and finiteness of `I` are exactly those of that existing map.

The short wrapper `LineSource.mapOfFamily_coefficients` applies the same
result to the canonical coefficient module and sections of the original
epimorphic family `d i : D → J`. It changes neither the dual evaluation
comparison nor the original line-source morphisms.

The current contraction consumer compares its actual `S`-based affine
row map with the original `R`-based coordinate map over the affine base.
The coefficient equality supplies this comparison; closedness of the
relative graph and the global contraction induction remain with their
own suppliers.

Input basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `4.34.1`.
