# ChartSections

Native owner: `AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover.ChartSections`.

Separate arbitrary integral birational-model chart/fraction-field and extension maps from declarations that literally name Cover.Nagata.fieldAlgebra, Cover.pi/normalization/eta or its chart ambient action. Generic block replaces baseFieldIso by its same native asIso term; retain independent vK and vL.

The public declarations are `modelFunctionFieldEquiv_extension`, `chartExtensionMap_eq`, `chartExtensionFieldEquiv`, `chartExtensionFieldEquiv_toRingEquiv`, `chartExtensionFieldEquiv_coe`, `coverPi_isAffineHom`, `coverChartFieldIso`, `normalizedChartSectionsEquiv`, `normalizedChartSectionsEquiv_coe`, `normalizedChartSectionsEquiv_coefficients`, `normalizedChartSectionsEquiv_val_comp`, `normalizedChartSectionsEquiv_restriction`, `normalizedChartSections_isLocalization_basicOpen`, `normalizedChart_coefficientBase`, `normalizedChartSectionsEquiv_coefficientBase`, `normalizedChartSectionsEquiv_coefficientBase_ambient`.

They use the original objects and maps; relocation adds no mathematical premise or replacement realization.

The principal-localization theorem also allows the ambient affine open and its
principal subopen to be empty; it requires no `Nonempty U` instance.
