# Affine-base resolution comparison

[Homology](Homology.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine.Homology`,
proves invertibility of the original resolution-section homology mate and
quasi-isomorphism of the original section-complex tensor map. The square is
an arbitrary supplied Cartesian square over `Spec.map σ`, the original
morphism is quasi-compact and quasi-separated, `σ` is flat, and the
coefficient is quasicoherent. Both original injective resolutions remain
supplied explicitly. No Noetherianity or cohomological finite generation is
assumed.

The proof uses the already proved original cohomology tensor map and the
exact unit formula from
[ResolutionSections/Pullback](../../../DirectImage/ResolutionSections/Pullback.lean).
The actual homology map equals the transported original canonical map;
no independently chosen isomorphism replaces it. Scalar flatness makes
the native tensor-homology comparison invertible. Negative homology
vanishes by the original resolution term bounds. The public theorems are
`moduleResolutionPullbackSectionsHomologyMap_isIso_of_isPullback` and
`moduleResolutionPullbackSectionsTensorMap_quasiIso_of_isPullback`.

The affine derived comparison uses this actual chain map, the original
affine tilde counits and the installed resolution-unit equation in
[Resolution](../Resolution.lean).

[Sections](Sections.lean) expresses that same tensor map in the original
native affine section complexes of the actual pushed-forward resolutions.
`affineBaseChangeResolutionSectionsMap_f_eq_scalarMate` identifies every
component with the scalar adjoint of the actual resolved geometric
base-change component. Its proof uses the original ordinary mate's unit
equation. No resolution term is assumed quasicoherent, and the actual
component comparison needs neither scalar flatness nor geometric
finiteness. `affineBaseChangeResolutionSectionsMap_quasiIso` retains the
qcqs, flat-scalar and quasicoherent-coefficient hypotheses above.

[Counit](Counit.lean) applies the original native affine scalar counit
compatibility termwise. `affineBaseChangeResolution_counit` is the actual
complex equation through the original source and target counits and
original tilde pullback comparison; resolution terms need not be
quasicoherent. `flatBaseChangeResolutionMapPlus_quasiIso_of_spec` proves
quasi-isomorphism of the same original resolved geometric map under the
qcqs, flat-scalar and quasicoherent-coefficient hypotheses. Both leaves
use the original native `φ : R ⟶ S` between bundled rings, passing its
unchanged `φ.hom` to scalar extension.

The parent [Affine](../Affine.lean) proves
`Scheme.Modules.derivedFlatBaseChangeMap_isIso_single_of_spec` for the
existing original comparison on every quasicoherent coefficient single.
The square remains supplied, the original direct-image morphism is qcqs,
and the native ring map is flat. The proof localizes the actual resolved
geometric map and uses its original installed-unit equation. It assumes
neither Noetherianity nor cohomological finiteness, and introduces no
additional theorem-family premise.

[Postnikov](Postnikov.lean) proves
`Scheme.Modules.derivedFlatBaseChangeMap_isIso_of_spec` on every original
bounded-below derived object whose native integer homology sheaves are
quasicoherent. The original transformation's shift compatibility gives
all integer singles, and the shared native Postnikov comparison supplies
the bounded-below extension. No new induction, termwise quasicoherence,
upper bound, cohomological dimension or convergence premise is used.
