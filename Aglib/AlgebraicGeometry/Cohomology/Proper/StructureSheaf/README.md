# The structure sheaf after base change of a proper flat geometrically integral morphism

This family proves universal O-connectedness (Picard plan target 2; Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, Ex. 3.11, p. 25, in the geometrically
integral case). Let `S` be locally Noetherian and `f : X ⟶ S` proper and flat
with geometrically integral fibres (Mathlib's `GeometricallyIntegral f`). For
every `g : T ⟶ S` and `φ = pullback.snd f g`:

- `AlgebraicGeometry.isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`:
  `IsIso φ.c`, the original map of presheaves of rings `O_T ⟶ φ_* O_{X ×_S T}`;
- `AlgebraicGeometry.bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`:
  `Function.Bijective (φ.app V)` for every open `V : T.Opens`.

The test scheme `T` is arbitrary; it need not be Noetherian, reduced or affine.
Finite presentation of `f` is not a hypothesis. No theorem-family input is
retained, and the retained `LocalFreeCohomologyBaseChange` family is not used.

## Leaves

| Leaf | Content |
| --- | --- |
| [Coefficient](Coefficient.lean) | `Scheme.Modules.unit_isFinitePresentation`, `affineLocallyFiniteType_unit` (every scheme); re-exports `unitStalkIso`, `unit_stalk_flat` and `relativeFlat_unit_of_flat` (`[Flat f]`) from [Modules/Flat/Relative/Unit](../../../Modules/Flat/Relative/Unit.lean). |
| [Sections](Sections.lean) | `Scheme.Cohomology.unitSections`, `pullbackUnitSections` (via `Sheaf.H.equiv₀` and `pullbackUnitIso`), `pullbackUnitSections_moduleCohomologyPullback` and `pullbackUnitSections_moduleCohomologyTensorMap_tmul`: on any commutative square `p ≫ f = q ≫ Spec.map σ`, the original degree-zero tensor map of the structure module sends `b ⊗ x` to `β b * p.appTop x`. |
| [LocalBase](LocalBase.lean) | Over a local Noetherian ring `R`, with `f : X ⟶ Spec R` proper and flat and `[GeometricallyIntegral (closedFibreMap f)]`: `epi_moduleCohomologyBaseChangeMap_residue_unit` (constants theorem), `bijective_structureMap_of_proper_geometricallyIntegral_closedFibre` (`R → Γ(X, ⊤)`), and, for every `σ : R →+* B`, `bijective_structureMap_pullback_of_proper_geometricallyIntegral_closedFibre` (actual fibre product) and `bijective_appTop_of_isPullback_of_proper_geometricallyIntegral_closedFibre` (every supplied cartesian square). Also `IsLocalRing.bijective_smul_of_bijective_residueField_tmul` (finite flat module with one-dimensional residue tensor). |
| [Localization](Localization.lean) | `CommRingCat.bijective_localizedModuleMap_of_isPushout` (pushout along a localization at a prime) and the instance `Scheme.flat_fromSpecStalk`. |
| [Pushforward](Pushforward.lean) | The stalk step `bijective_appTop_pullback_fromSpecStalk_of_isProper_of_flat_of_geometricallyIntegral`, the affine-open step `bijective_app_pullback_snd_of_isAffineOpen_of_isProper_of_flat_of_geometricallyIntegral`, and the two endpoints above. |

## Route

The constants theorem `Scheme.constants_bijective_of_proper_geometricallyIntegral`
makes the degree-zero residue comparison of the structure module surjective
(`Sections` identifies it with `c ⊗ x ↦ β c * p.appTop x`). The proper local
criterion `moduleCohomologyBaseChangeMap_isIso_of_epi_residue_of_proper` and
`moduleCohomology_free_zero_of_epi_residue_of_proper`, with
`moduleCohomology_finite_of_proper`, give invertible base-change maps after every
ring map and a finite free `H⁰(X, O_X)`; its residue tensor is one-dimensional, so
Mathlib's `Module.IsLocalRing.linearCombination_bijective_of_flat` makes
`R → Γ(X, ⊤)` bijective. For a test scheme, each point `t` over `s` gives a
pullback square over `Spec (g.stalkMap t)` from `X ×_S Spec O_{S,s}`, a local
Noetherian base. Mathlib's flat base change of sections
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` along the flat
`T.fromSpecStalk t` and `bijective_of_localized_maximal` give every affine open;
`TopCat.Sheaf.isIso_iff_isIso_basis` on affine opens gives the sheaf statement.

## Hypotheses, owners and consumers

The coefficient and section statements need no properness, flatness of `f` or
Noetherianity except where displayed. The local-base statements assume only the
closed fibre geometrically integral. Intended owners of the general helpers:
`Coefficient` with `Modules/QuasiCoherent/FiniteType`,
`Sections` with `Cohomology/BaseChange/Modules`, and the ring lemmas with
`RingTheory` localization and local-ring modules. Planned consumers are the
Picard comparison (plan row F7) and `Q`/linear systems (row F15).

The focused consumer is `AglibTest/AlgebraicGeometry/Cohomology/Proper/StructureSheaf.lean`.
All leaves and the test passed the shared locked build route; the endpoint
theorems use only `propext`, `Classical.choice` and `Quot.sound`.
