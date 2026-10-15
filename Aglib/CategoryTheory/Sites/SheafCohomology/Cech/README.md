# Generic Cech exactness and coefficient comparison

Import `Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness` for `CategoryTheory.Cech.splitCech_exactAt_succ` and `restrictedCech_exactAt_succ`. A specified section from an actual terminal object into a cover member gives positive-degree exactness; restriction to a cover member gives the corresponding restricted result. Coefficients are abelian and the exact product-universe existence assumptions are retained.

[Comparison](Comparison.lean) gives `cechComplexCoefficientIso`, `cechCosimplicialCoefficientIso` and `cechCosimplicialIntersectIso` for actual coefficient/alternating-coface/intersection comparison. [ExactSequences](ExactSequences.lean) supplies native module-cochain formulas, cocycle/coboundary calculations and `cech_shortExact_of_sections` with the original sectionwise short-exact premises.

[FiniteCoefficients](FiniteCoefficients.lean) separately supplies `CategoryTheory.Cech.finiteCechCosimplicialCoefficientIso` and `finiteCechComplexCoefficientIso` for a finite family and a coefficient functor preserving finite products. It has no scheme, field or covering hypothesis. Agreement with the all-product comparison retains the separately stated `PreservesLimitsOfSize.{w,w}` premise.

The focused `Aglib.CategoryTheory.Sites.SheafCohomology.Cech` leaves are lower inputs to scheme injective Cech exactness, affine principal-cover exactness and canonical comparison with `Sheaf.H`. They make no automatic sectionwise-exactness conclusion from merely having a cover.
