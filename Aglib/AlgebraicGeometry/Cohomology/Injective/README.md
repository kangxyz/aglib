# Actual injective-resolution section comparisons

[SectionCycles](SectionCycles.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles`, identifies actual global-section cycles of an additive injective resolution with the original `Sheaf.H`. Cycles surject onto cohomology, and in positive degree a cycle is zero precisely when it is a global-section boundary. The quotient comparison uses the same resolution and original Ext-defined object.

[DegreeZero](DegreeZero.lean) gives the actual degree-zero section-homology comparison for module injective resolutions. [RestrictionSections](RestrictionSections.lean) extends the native restriction-section isomorphism to complexes. [Restriction](Restriction.lean) proves preservation of actual injective module sheaves under open restriction, using the genuine exact extension-by-zero adjunction.

Focused imports are these four leaves. The supplied-resolution kernel sequences in [CategoryTheory](../../../CategoryTheory/Abelian/Injective/README.md) and actual [open restriction](../../Modules/Restriction/README.md) are lower inputs. Affine/Cech, flasque, Mayer–Vietoris and canonical geometric comparison are consumers. Forgetting module structure is not assumed to preserve injectives.
