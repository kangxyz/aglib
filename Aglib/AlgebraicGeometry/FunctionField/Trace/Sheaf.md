# Original finite-morphism trace on the structure module

For a finite dominant morphism `f : X → Y` of integral schemes with normal
target, `Modules.finiteStructureTrace` constructs the structure-linear map

`f_* O_X → O_Y`.

Its value on every nonempty open is the trace in the original extension
`functionFieldMap f : K(Y) → K(X)`, tested using the original section germs.
The affine producer is [Trace](../Trace.lean). The original stalk criterion
in [SectionRange](../SectionRange.lean) extends those values to arbitrary
nonempty opens; the map on an empty open is zero. Injectivity of the target
germ map proves restriction compatibility, addition and scalar linearity.
The resulting arrow uses the original module-sheaf pushforward and scalar
action, without a new descent-data category.

No separability, source normality, Noetherianity, or local freeness of the
finite section algebra is assumed. The trace is field trace restricted to
regular sections. It is not defined as algebra trace of a possibly nonfree
finite section algebra.

`finiteSectionTrace_germ` records the original field value and
`finiteSectionTrace_restrict` records the actual restriction equation.
`Modules.finiteStructureTrace_app` identifies every component of the sheaf
arrow with that section map. The current consumer is the separable surface
H1 bound: its fixed Gram matrix, original-map compatibility and uniform
cohomology estimate remain separate results.
