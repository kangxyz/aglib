# Finite-type quasicoherent sheaves

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic`, defines `Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X`: every actual affine open restriction is quasicoherent with finite global sections. `FiniteTypeSheaves X` is the full category and `finiteTypeSheavesToModules` is the actual inclusion. These objects are defined for every scheme, with essential-smallness bound in the sheaf-object universe `u+1`.

[FinitePresentation](FinitePresentation.lean) proves that actual local finite presentation implies this finite-type property. The result belongs below the locally Noetherian coherent category. The converse uses local Noetherianity and is supplied by the lower [Noetherian finite-presentation constructions](../../FinitePresentation/Noetherian.lean). [Restriction](Restriction.lean) preserves the property under actual open restriction and compares the restricted inclusion with the ambient sheaf functor.

The lower affine condition and module equivalence are in [Affine](../Affine/README.md). Canonical finite/closed direct image, locally free inclusion and the locally Noetherian [coherent specialization](../../Coherent/README.md) consume these genuine object properties. No abelian/Serre structure on every scheme's finite-type category is asserted.

[Pushforward](Pushforward.lean) now owns `Scheme.Modules.QuasiCoherent.finiteTypePushforward` for an arbitrary finite scheme morphism, on these actual finite-type sheaves. `finiteTypePushforwardOpenBaseChange`, `finiteTypePushforwardIdIso`, `finiteTypePushforwardCompIso`, `finiteTypePushforwardSpec` and its scalar/presentation squares are the canonical lower comparisons. No Noetherian class is needed here. The guarded coherent aliases and exact functors are higher specializations.

[Pullback](Pullback.lean) owns `Scheme.Modules.QuasiCoherent.finiteTypePullback` for a morphism `X ⟶ Y` with locally Noetherian target `Y` and arbitrary receiving scheme `X`. `finiteTypePullback_comp_inclusion` is the literal equality with ambient module pullback. `finiteTypePullbackIdIso` requires the identity scheme to be locally Noetherian. `finiteTypePullbackCompIso` requires the intermediate and final target schemes to be locally Noetherian, with arbitrary receiving scheme; `finiteTypeRestrictionIsoPullback` adds the actual open-immersion hypothesis. These comparisons use the original geometric maps. The [coherent pullback](../../Coherent/Pullback.lean) is a transparent specialization with both locally Noetherian guards. The target hypothesis on this lower construction is retained; it is not an all-scheme finite-type pullback theorem.

[Sections](Sections.lean) owns two interface results. `finite_sections_of_affineLocallyFiniteType` says the sections on an actual affine open form a finite module over its ring of functions. `affineLocallyFiniteType_pullback_of_finitePresentation` says the module-sheaf pullback of a finitely presented sheaf along an arbitrary morphism satisfies the chart condition. The library does not yet supply the general theorem that the pullback of a finite-type quasicoherent sheaf is of finite type. Until it does, consumers such as the [Fitting ideal sheaves](../../FittingIdeal/README.md) take that finite type as an argument or obtain it from finite presentation.

[Support](Support.lean) proves closedness of ordinary stalk support on arbitrary schemes.
[Extension](Extension/README.md) gives affine finite-type approximation over arbitrary
commutative rings; [restriction comparisons](Restriction/README.md) retain the actual
open-range, top-open and principal restriction maps.

[LocalSpectrum](LocalSpectrum.lean) derives finite-type quasicoherence of the
actual local-spectrum base change of a proper coefficient over a locally
Noetherian target. Source local Noetherianity is derived, not assumed.

## Locality and extension over qcqs schemes

[Locality](Locality.lean), imported as
`Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality`, proves
`Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_of_openImmersionCover`.
For a quasicoherent `M`, the finite-type condition descends from any jointly
surjective family of actual open immersions, with no Noetherian or
compactness hypothesis on the ambient scheme. The cover index has an
independent universe. The binary-cover and open-union forms retain their
specified restriction maps.

[Extension/Global](Extension/Global.lean), imported as
`Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Extension.Global`,
constructs finite-type subobjects over a qcqs `X`. In the same native
namespace, `affineLocallyFiniteType_subobject_extension_of_qcqs` takes a
quasi-compact open immersion `j : U ⟶ X`, a quasicoherent `M`, and a finite-type
subobject `i : A.obj ⟶ M.restrict j`. It returns a finite-type subobject
`b : B.obj ⟶ M` and `e : B.obj.restrict j ≅ A.obj` with the actual equation

```lean
(restrictFunctor j).map b = e.hom ≫ i
```

The ambient qcqs condition and quasi-compactness of `j` are retained.
[Extension/Sections](Extension/Sections.lean) proves
`exists_finiteType_subsheaf_section`: every section of a quasicoherent sheaf
on a specified affine open of a qcqs scheme lies in the image of the actual
inclusion of a global finite-type subobject. Its equation is
`i.app U.val y = x`. [Ideal extension](../../../IdealSheaf/FiniteTypeExtension.lean)
and [finite-type ideal approximation](../../../IdealSheaf/FiniteTypeApproximation.lean)
consume these constructions.

The lower [preimage](../Subobjects/Preimage.lean) and
[gluing](../Subobjects/Gluing.lean) results extend quasicoherent subobjects
along quasi-compact open immersions on arbitrary schemes. Their output need
not be of finite type; the global finite-type conclusion uses the additional
qcqs hypotheses above. The locally Noetherian specializations remain
available.
