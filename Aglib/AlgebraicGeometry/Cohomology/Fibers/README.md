# Original cohomology on fibres over arbitrary scheme points

[Basic](Basic.lean) defines `modulePointFiberCohomology f M q y` for
`f : X ⟶ Y` and any point `y : Y`. It is a native module over the actual
`Y.residueField y`, with the original additive `Sheaf.H` as its carrier.
The scheme is literally `f.fiber y`, the pullback along
`Y.fromSpecResidueField y`, and the coefficient is the ordinary pullback
along `f.fiberι y`. Scalars use `f.fiberToSpecResidueField y` and the
original `ΓSpecIso`; carrier and scalar-action identities are `rfl`.
The schemes and residue rings remain in universe `u`, and the original
cohomology carrier remains in universe `u+1`.

`modulePointFiberCohomologyDimension f M q` is the resulting function
`Y → ℕ`, using native `Module.finrank`. These definitions require no
quasicoherence, properness, Noetherianity, flatness or finite-dimensionality.
Native `finrank` retains its convention for infinite-dimensional modules;
proper cohomological finiteness is a separate result. Empty bases have
vacuous point statements, with no nonempty or nontriviality premise.

[Affine](Affine.lean) compares the intrinsic construction with the
unchanged [affine fibre-dimension function](../Modules/Fibers.lean).
For an actual open immersion `j : Spec R ⟶ Y` and `p : PrimeSpectrum R`,
the canonical residue-field isomorphism is
`asIso (j.residueFieldMap p) ≪≫ Scheme.Spec.residueFieldIso (.of R) p`.
It compares the actual `κ(j p)` with the actual `p.asIdeal.ResidueField`.
`modulePointFiberAffineIso` identifies the original affine residue-field
pullback with `f.fiber (j p)` and preserves both its map to `X` and its
structural map through this same residue-field isomorphism.
`modulePointFiberAffineCoefficientIso` uses the native ordinary pullback
composition and equality comparisons.

`modulePointFiberCohomologyAffineIso` is the original geometric cohomology
isomorphism with affine fibre scalars restricted along that canonical
residue-field map. It directly uses the sole
[`moduleCohomologyRestrictionIsoOfPullbackIso`](../Functoriality/Modules/Isomorphism.lean),
whose forward-map theorem retains the original `moduleCohomologyMapAlong`,
the module adjunction unit and the actual coefficient isomorphism.
Rank invariance then proves
`modulePointFiberCohomologyDimension_eq_moduleFiberCohomologyDimension`:
the intrinsic value at `j p` equals the old affine function for
`pullback.snd f j` and the ordinary pullback of `M` along `pullback.fst f j`.
No finiteness assumption enters this coordinate equality.

`modulePointFiberEulerChar` in [Basic](Basic.lean) is the honest native
`finsum` of `(-1)^q` times these original dimensions. It has no chosen
cohomological bound in its definition. A proved pointwise vanishing bound
gives `modulePointFiberEulerChar_eq_sum_range`; native `finsum` retains its
zero value for infinite support outside the geometric finiteness setting.
`modulePointFiberEulerChar_eq_moduleFiberEulerChar` in [Affine](Affine.lean)
identifies the full intrinsic sum with the unchanged affine Euler function
term by term, without a finiteness premise.

The existing proper [semicontinuity](../Proper/Semicontinuity.lean) and
[Euler characteristic](../Proper/EulerCharacteristic.lean) owners now
provide intrinsic upper semicontinuity in every degree and intrinsic Euler
local constancy over any locally Noetherian target, for proper `f`, coherent
`M` and intrinsic relative flatness. Reducedness and quasi-compactness of
the target are not required. Their actual affine models provide the locally
bounded cohomology used for the Euler meaning; no global bound is selected.

This normalization supplies the pointwise numerical prerequisite for
descent of the affine proper results over arbitrary target affine covers.
Those local arguments need no quasi-compactness of the whole target or
uniform bound across its affine opens. A nonflat higher-direct-image
base-change sheaf map is a separate interface: the existing flat map keeps
its flatness guard, and ordinary coefficient pullback is not identified
with derived pullback merely from relative flatness over the target.

The [field-extension vanishing comparison](../Proper/H0Vanishing/FieldExtension.md)
retains the same point fibre and its literal further field pullback. It
reflects vanishing in every degree for qcqs morphisms and quasicoherent
coefficients. Its H⁰ consequence for a proper finite-type quasicoherent
relatively flat coefficient over a locally Noetherian target produces an
actual open containing the given point, with vanishing on every original
fibre. Taking that point to be generic gives the finite-base spreading
application, once its actual external fibre and coefficient are identified.

[FieldPoint](FieldPoint.lean) defines `moduleCohomologyDimension b M q`, the dimension over a
field `K` of the original `H^q(Y, M)` for `b : Y ⟶ Spec K`, with its structural action, and
`moduleEulerChar b M`. They are invariant under module isomorphism and transport along
isomorphisms over `Spec K` (`moduleCohomologyDimension_eq_of_isIso`); for qcqs `b` and
quasicoherent `M` they are unchanged by field extension
(`moduleCohomologyDimension_fieldBaseChange`, from `moduleCohomology_finrank_fieldBaseChange`).
`residueFieldBaseChange p s t : X ×_S Spec κ(t) ⟶ X ×_S T` is the base change at a point, and
`modulePointFiberCohomologyDimension_eq_pullbackMap` identifies the point fibre of
`X ×_S T ⟶ T` at `t` with this base change through the pasting isomorphism. No properness,
Noetherian or flatness hypothesis is used.

[BaseChange](BaseChange.lean) treats a morphism `b : T' ⟶ T` over `S` and
`familyBaseChange p s s' b hb : X ×_S T' ⟶ X ×_S T` (definitionally the map of
`RelativePicard.familyScheme p`). The fibre at `t'` is the base change of the fibre at `b t'`
along `Spec κ(t') ⟶ Spec κ(b t')` (`isPullback_fiberBaseChange`), compatibly with the maps to
`X ×_S T` (`residueFieldBaseChange_comp_familyBaseChange`); coefficients transport naturally
(`familyBaseChangeFiberNatIso`). For qcqs `p` and quasicoherent `M`, point-fibre dimensions and
Euler characteristics of `b^* M` at `t'` and of `M` at `b t'` agree
(`modulePointFiberCohomologyDimension_familyBaseChange`,
`modulePointFiberEulerChar_familyBaseChange`), and so does vanishing
(`subsingleton_modulePointFiberCohomology_familyBaseChange_iff`). Consumer: the Picard strata.
