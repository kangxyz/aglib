# Original finite-morphism field trace on affine sections

For a finite dominant `f : X → Y` of integral schemes with normal target,
`finiteAffineSectionTrace` constructs a linear map

`Γ(X,f⁻¹U) → Γ(Y,U)`

for every nonempty affine open `U` in `Y`. Scalars act through the original
section map `f.app U`. The section algebra is finite but need not be free.
No separability, source normality or Noetherian hypothesis is imposed.

The extension of function fields uses `functionFieldMap f` itself.
`functionFieldMap_germ_app` proves its square with the original section
maps on each nonempty open. The finite affine section algebras have these
same fraction fields. The base-valued field trace from
[TraceLattice](../../RingTheory/IntegralClosure/TraceLattice.lean) therefore
gives a section, characterized by its original generic value. Integral
closedness is obtained from the target's actual normal stalks.

`finiteAffineSectionTrace_germ` is the exact original field-trace equation,
and `finiteAffineSectionTrace_unique` gives uniqueness in the original
target section ring. The linear map is defined by those unique values;
its addition and scalar laws use the same equation and field-trace
linearity. Ordinary algebra trace of a nonfree finite algebra is not
substituted for field trace.

The current consumer is the ordinary trace sheaf for the finite diagram
in the separable surface H1 bound. Passing from these affine values to a
global structure-linear morphism, identifying the fixed base Gram matrix,
and proving the H1 estimate remain separate obligations. The generic
regular-section criterion in [SectionRange](SectionRange.lean) supports
the all-open extension. This file asserts neither a global trace sheaf
nor a uniform H1 bound.
