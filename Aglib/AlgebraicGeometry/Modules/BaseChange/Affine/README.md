# Affine module base change

[Isomorphism](Isomorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Isomorphism`, supplies the existing `Scheme.Modules.AffineModuleBaseChange` interface. For affine `f`, quasicoherent `M` and arbitrary `g`, the original canonical `moduleBaseChangeMap f g M` is invertible. No flatness of `g`, finiteness, Noetherianity, reducedness, dimension or curve condition is added.

The namespace is `Scheme.Modules.BaseChange.Affine`, with the square construction in `.Square`. [GlobalSections](GlobalSections.lean) uses actual top-open evaluation and the affine tilde adjunction. [Square](Square.lean) identifies the actual cartesian-square mate, including the definitional equation with `Scheme.Modules.moduleBaseChangeMap`, and compares its Gamma map with the original scalar-pushout mate. [Locality](Locality.lean) proves the literal open-local restriction and whiskering equations used by the final gluing argument.

Lower ring/module scalar-extension and tensor-pushout objects live in [ModuleCat/BaseChange](../../../../Algebra/Category/ModuleCat/BaseChange.lean); generic adjunction comparison and mate whiskering live in [Adjunction/Mates](../../../../CategoryTheory/Adjunction/Mates.lean). The existing native affine tilde/pullback/pushforward comparisons remain in [QuasiCoherent/Affine](../../QuasiCoherent/Affine/README.md), and canonical scheme pullback/open restriction remains in [Pullback](../../Pullback/README.md).

The public result is a supplier of the existing family on the original map. The internal affine-square reduction introduces no new public theorem-family input. Native module-fibre, finite locally free and relative-family consumers may use this supplier; the theorem does not assert proper cohomology base change.
