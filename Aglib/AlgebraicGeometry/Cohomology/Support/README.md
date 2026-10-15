# Actual skyscraper and finite-support cohomology

[Skyscraper](Skyscraper.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Support.Skyscraper`, constructs the actual additive stalk/skyscraper adjunction. For any scheme point and abelian coefficient group, skyscraper positive `Sheaf.H` vanishes and H0 is naturally equivalent to that group. The point need not be closed.

[Finite](Finite.lean) computes actual cohomology of a finite biproduct of additive skyscrapers through native projection maps. Its positive degrees vanish and H0 is the product of coefficient groups. For a general sheaf concentrated on finitely many distinct closed points, the reduction retains actual zero-stalk conditions outside them and identifies the sheaf through those stalks.

The native field action on module stalks is identified separately in [Modules/StalkScalars](../Modules/StalkScalars.lean). Finite-dimensional structural-field stalk hypotheses are used only where finite-dimensional conclusions are needed. [Finite-support Euler](../Exact/README.md) consumes these actual comparisons. Lower generic [closed-embedding support](../../../Topology/Sheaves/ClosedSupport.lean) and native Ext/stalk adjunctions supply the proof route; forgotten module injectives are not assumed injective.
