# Smooth relative curves and actual Cartier ideals

| Focused import | Actual interface and conditions |
| --- | --- |
| `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Field` | Over every field, a locally Artinian closed subscheme of a smooth relative-dimension-one scheme has invertible actual ideal. A regular principal kernel with Artinian quotient has the stated regular generator; conversely an invertible closed ideal cuts out a locally Artinian scheme. Empty and nonreduced subschemes are included. |
| `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Fibre` | Quotient-flat ideal comparison gives actual singleton field-fibre bases and lifted principal generators. Locally quasi-finite and flat quotient-to-base morphisms remain the exact spectral premises. The intermediate all-base ring-regularity input stays explicitly conditional. |
| `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Ideal` | `Scheme.Hom.idealModule_isLocallyRankOne_of_smooth_of_finite_flat`: smooth relative dimension one, a closed immersion, and a finite, flat, locally finitely presented composite imply local rank one of its actual ideal module. The final producer supplies its technical regularity input using the proved ring criterion. |
| `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Locality` | Smooth relative dimension one, a closed immersion with locally rank-one actual ideal and flat composite imply that composite is locally quasi-finite and locally of finite presentation. |

The base can be nonreduced and non-Noetherian. Finiteness and local finite presentation are separate premises at the finite-flat public root. Original spectral and restricted-open helpers retain local quasi-finiteness where finiteness would not survive the restriction. Generic localization squares live under [Spec/Localization](../../Spec/Localization.lean), and the actual quotient-flat kernel comparison lives under [IdealSheaf/BaseChange](../../IdealSheaf/BaseChange/README.md).
