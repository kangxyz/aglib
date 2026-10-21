# ArbitraryGalois

Extend the existing canonical field fibre reconstruction proof to the source arbitrary Omega/K IsGalois point, proving actual galoisToFibre bijective/continuous equivalence and H1 restriction injectivity; final genericCoefficientRestriction injectivity is a specialization.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.FieldGaloisComparison`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `4fb444d936b1374d0bc1c06cebeb35f888cb411417aa941980bf07f501820b17`.

Conditions: K,Omega fields in same u and actual Algebra K Omega + IsGalois K Omega. No IsAlgClosed Omega is needed for reconstruction itself. Do not call this fibre geometric without separately having IsAlgClosed. Existing native Field/Basic fixes AlgebraicClosure K and cannot alone instantiate arbitrary Omega by changing a name.

Declarations through galoisRestriction_injective stay in this field module.
The normalization-specific genericCoefficientRestriction_onH1_injective (source:444–468)
is placed in GenericPullback after its actual coefficient action is constructed.

The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.
