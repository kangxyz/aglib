# Flatness over an actual quotient kernel

`Aglib.RingTheory.Flat.KernelCriterion` extends `Module.Flat` for arbitrary
commutative rings and modules in independent universes. The original
surjection and its actual kernel remain explicit.

`rTensor_injective_of_flat_baseChange_of_quotient_cokernel` assumes that
`S ⊗[R] M` is flat over `S` and that tensoring the actual kernel inclusion
of the surjection `R → S` with `M` is injective. It proves tensor
injectivity for an injection whose cokernel has a compatible `S`-action.
`rTensor_injective_of_flat_baseChange_of_annihilated_cokernel` constructs
that action from explicit annihilation by the same kernel. These are
restricted tensor statements, not unrestricted flatness criteria.

`rTensor_injective_of_flat_baseChange` handles injections between modules
already carrying compatible `S`-actions; it does not require the algebra map
to be surjective. Canonical tensor cancellation identifies the actual maps.

`of_ideal_rTensor_injective_below_kernel` proves that `M` is flat over `R`
when its quotient base change is flat and every ideal contained in the
actual quotient kernel has injective tensor inclusion. The proof reduces
an arbitrary ideal to its intersection with the kernel and its image in `S`.
No Noetherian, nilpotence, Jacobson or local-ring condition is added.

The presentation diagram generalizes Christian Merten's argument in
`Mathlib.RingTheory.Flat.Equalizer`; kangxyz supplies the extended quotient
criteria. The current [Milnor flatness consumer](../Etale/MilnorPatching/Flat.md)
uses both ring components to establish the kernel-ideal hypotheses.
