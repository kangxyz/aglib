# Open restriction, sections and extension by zero

[Sections](Sections.lean) constructs actual section and cochain-complex isomorphisms under open restriction. [Square](Square.lean) compares the original restriction functors in an actual commuting square, retaining the specified morphism equality and unit compatibility.

[ExtensionByZero](ExtensionByZero.lean), imported as `Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero`, gives `Scheme.Modules.extensionByZero`, its restriction adjunction and stalk formulas. The extension is zero outside the actual open range, fully faithful, and exact on the original short exact module-sheaf sequences. The flat-stalk transport keeps its own coefficient-flatness hypotheses.

These maps feed [preservation of injectives by open restriction](../../Cohomology/Injective/README.md), local basis/presentation transport and the canonical [open-base-change](../BaseChange/README.md) comparison. Open immersion is a geometric input; no Noetherian or finite-type hypothesis is imposed merely to define the functors.
