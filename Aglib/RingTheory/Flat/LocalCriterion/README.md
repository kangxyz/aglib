# Local criteria for module flatness

These leaves concern actual modules, linear maps, tensor products and cokernels. They introduce no replacement for `Module.Flat` and have no scheme imports.

| Focused import | Native interface and conditions |
| --- | --- |
| `Aglib.RingTheory.Flat.LocalCriterion.Tensor` | `Module.Flat.injective_and_flat_iff_lTensor_quotient_injective`: for an exact sequence `M → N → P → 0` with `N` flat over an arbitrary commutative `R`, injectivity of the first map together with flatness of `P` is equivalent to injectivity after tensoring with every cyclic quotient `R/I`. Also supplies exact-sequence and scalar-extension injectivity transport. |
| `Aglib.RingTheory.Flat.LocalCriterion.Adic` | `Module.Flat.injective_of_residue_injective_of_isHausdorff` lifts residue injectivity through every ideal-adic thickening and uses the stated adic separation of the source. Its Noetherian local variant assumes a local `R`-algebra `S`, local structure map, `S` Noetherian, the source finite over `S`, and the target flat over `R`; it adds no separate Noetherian premise on `R`. |
| `Aglib.RingTheory.Flat.LocalCriterion.ResidueSyzygies` | `Module.Flat.ResidueSyzygies` contains the right-factor tensor action, actual linear scalar-extension maps, finite fibre-kernel generators and finite tests for relation lifts. The transported action is activated locally; it is not a competing global tensor-action instance. |
| `Aglib.RingTheory.Flat.LocalCriterion.Residue` | `Module.Flat.injective_and_flat_of_residue_injective_noetherian` proves the complete residue criterion for the actual cokernel, with the same local/Noetherian acting-algebra and source-finiteness conditions. `Module.Flat.flat_quotient_of_residue_subtype_injective_noetherian` uses the actual ideal inclusion and quotient. |

`Algebra.FlatApproximation.injective_of_kernel_killed_after_baseChange` in `Tensor` is the lower linear-algebra step used by the finite-presentation approximation argument. `ResidueSyzygies` supplies its finite relation witnesses, while `Residue` supplies the Noetherian local criterion. The [principal-quotient family](../PrincipalQuotient/README.md) and [finite-presentation prerequisites](../FinitePresentation/README.md) are present consumers.

The source statements and proof bodies were transferred from the pure ring/module blocks of `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/FibrewiseRegularity.lean`, frozen revision `79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256 `79621aa63046ca16c5f98424d77f16bc8cd45b99a84ddc8bc561fc8f9ccfe923`. Localized/Noetherian conditions remain on their original intermediate results. This transfer does not introduce an explicit local-flatness theorem-family input.
