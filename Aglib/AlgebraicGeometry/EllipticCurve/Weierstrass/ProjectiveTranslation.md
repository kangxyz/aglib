# ProjectiveTranslation

Native module: `Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveTranslation`.

Original W, actual scale-one translate W r t, homogeneous x↦x+r*z,y↦y+t*z,z↦z. Same quotient grading, Proj, affine chart and infinity. Critical specialization requires actual equation and both gradients. Generic part only Field k; no splitness/Henselian hypothesis.

Source: `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Ranges: `[[34, 570]]`. SHA-256 `e632ed2e94958560002dc6bb265bd07c35e94b00885c15cc7698e55178416e4a`.

| Source declaration | Native declaration or exact reuse |
| --- | --- |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.shiftPolynomial_cubic` | `WeierstrassCurve.Projective.Translation.shiftPolynomial_cubic` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.unshiftPolynomial_cubic` | `WeierstrassCurve.Projective.Translation.unshiftPolynomial_cubic` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.toTranslatedHomogeneous` | `WeierstrassCurve.Projective.Translation.toTranslatedHomogeneous` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.fromTranslatedHomogeneous` | `WeierstrassCurve.Projective.Translation.fromTranslatedHomogeneous` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.toTranslatedGraded` | `WeierstrassCurve.Projective.Translation.toTranslatedGraded` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.fromTranslatedGraded` | `WeierstrassCurve.Projective.Translation.fromTranslatedGraded` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.from_to_graded` | `WeierstrassCurve.Projective.Translation.from_to_graded` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.to_from_graded` | `WeierstrassCurve.Projective.Translation.to_from_graded` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.graded_irrelevant_mem` | `WeierstrassCurve.Projective.Translation.graded_irrelevant_mem` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.irrelevant_le_of_inverse` | `WeierstrassCurve.Projective.Translation.irrelevant_le_of_inverse` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.toTranslated_irrelevant` | `WeierstrassCurve.Projective.Translation.toTranslated_irrelevant` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.fromTranslated_irrelevant` | `WeierstrassCurve.Projective.Translation.fromTranslated_irrelevant` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedProjectiveMap` | `WeierstrassCurve.Projective.Translation.translatedProjectiveMap` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.inverseTranslatedProjectiveMap` | `WeierstrassCurve.Projective.Translation.inverseTranslatedProjectiveMap` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.nativeProjMap_congr` | `WeierstrassCurve.Projective.Translation.nativeProjMap_congr` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedProjectiveIso` | `WeierstrassCurve.Projective.Translation.translatedProjectiveIso` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.native_away_constant` | `WeierstrassCurve.Projective.Translation.native_away_constant` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedProjectiveOverIso` | `WeierstrassCurve.Projective.Translation.translatedProjectiveOverIso` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.native_powers_le` | `WeierstrassCurve.Projective.Translation.native_powers_le` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.nativeAwayMap_spec` | `WeierstrassCurve.Projective.Translation.nativeAwayMap_spec` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.nativeAwayMap_mk` | `WeierstrassCurve.Projective.Translation.nativeAwayMap_mk` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translated_z_powers` | `WeierstrassCurve.Projective.Translation.translated_z_powers` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedZChartMap` | `WeierstrassCurve.Projective.Translation.translatedZChartMap` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedZChartMap_mk` | `WeierstrassCurve.Projective.Translation.translatedZChartMap_mk` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.dehomogenize_translation` | `WeierstrassCurve.Projective.Translation.dehomogenize_translation` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedZChartMap_dehomogenize` | `WeierstrassCurve.Projective.Translation.translatedZChartMap_dehomogenize` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.nativeProjMap_infinityPoint` | `WeierstrassCurve.Projective.Translation.nativeProjMap_infinityPoint` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.translatedProjectiveMap_infinityPoint` | `WeierstrassCurve.Projective.Translation.translatedProjectiveMap_infinityPoint` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.projectiveEquationCastIso` | `WeierstrassCurve.Projective.Translation.projectiveEquationCastIso` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.projectiveEquationCastOverIso` | `WeierstrassCurve.Projective.Translation.projectiveEquationCastOverIso` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.OriginalCubicTranslation.originalToCriticalOverIso` | `WeierstrassCurve.Projective.Translation.originalToCriticalOverIso` |

Compilation scope and actual cold imports are recorded in the author handoff. Source correspondence supplies no model-existence, representability, purity, independent review or adoption verdict.

B34 repair: preserve the shared public noncomputable scope across the four original source blocks, and use the fully qualified actual `Scheme.OverField.extensionPointSource` alias. The homogeneous substitutions, affine/infinity triangles, original fields and hypotheses are unchanged. Candidate002 awaits the principal's repaired aggregate remote graph; B34's failed projective attempt is not fresh coverage of this repaired source.
