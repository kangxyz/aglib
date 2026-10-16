# Original two-column tensor calculations

[Coordinates](Coordinates.lean) defines the actual column inclusions and
projections of a one-element Koszul complex tensored with an arbitrary
nonnegative module complex. Their original decomposition detects maps.
[Differential](Differential.lean) proves the projected signed differential;
[Elements](Elements.lean) gives its element formulas and cycle calculations.

[Functor](Functor.lean) uses this decomposition to compare an additive module
functor applied to the original tensor with the tensor of its image complex.
Compatibility with scalar multiplication is an explicit hypothesis for the
chain isomorphism. [Quotient](Quotient.lean) defines the actual tensor
augmentation to the degreewise scalar quotient. If the scalar acts regularly
on every original coefficient term, cycles lift and boundaries reflect;
the lower native short-complex criterion proves this same augmentation is a
quasi-isomorphism. No termwise quasicoherence or geometric exactness is assumed.
