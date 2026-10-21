# SheafClass

Turn actual SAME normalization scheme action into its represented coefficient sheaf torsor and Ext-H1 class; derive finite locally constant/killedBy/FiniteCoefficient and exact comparison/restriction identities.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.SheafClass`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `47702896ef6326c5b66041f693d74dc5f079e45532a10c841c1a0b55dd9099dc`.

Conditions: Native InertiaTorsor.Basic already supplies actual normalizationCover/normalizationSchemeAction. Source keeps HasExt.{w}, displayed Stacks03AJ/03RV, n>0, hkill and LevelInvertible where used. Actual finite discrete Lambda is coordinated with same finite-etale Hopf H and chosen f,Q,hvan. No universal Ext/descent/etale-H1 theorem is supplied by this extraction.

The surjectivity input of torsorOfSchemeAction is the already-derived native
normalizationCover_surjective, not a duplicate cover construction.

The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.
