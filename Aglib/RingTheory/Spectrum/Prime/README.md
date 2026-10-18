# Prime spectra, residue fibres and dimensions

[Surjectivity](Surjectivity.lean) identifies surjectivity of the original
residue-field base-change map with the complement of the original cokernel
support. It has the same condition as surjectivity of the original localized
map. For a finite target this locus is open, and each point in it has an
actual basic open neighbourhood on which every fibre map is surjective.
The source module need not be finite and the ring need not be Noetherian.

[FiberDimension](FiberDimension.lean) proves
`Module.exists_basicOpen_finrank_fiber_le` and
`Module.upperSemicontinuous_finrank_fiber` for every finite module over an
arbitrary commutative ring. The function uses the original `Ideal.Fiber`
and `Module.finrank` over the actual residue field. A basis chosen from
the original elements `1 ⊗ m` lifts to a finite free source; the open
surjectivity theorem gives the required neighbourhood dimension bound.
Ring and module universes are independent.

[FiberDimension/Flat](FiberDimension/Flat.lean) identifies fibre dimension
with the native stalk rank for finitely presented flat modules and deduces
local constancy. No global freeness or Noetherian hypothesis is needed.
The [focused guide](FiberDimension/README.md) records this extra scope.

[FiberInjectivity](FiberInjectivity.lean) detects injectivity of a map from
a free module over a reduced ring by its original scalar extensions to all
prime residue fields. No finite generation is required for this detection.
A surjection from a finite free module is therefore bijective when source
and target have equal original fibre dimensions everywhere. These statements
preserve independent ring, source and target universes.

[Bijectivity](Bijectivity.lean) shows that a linear map of finite modules with
projective target is bijective once it is bijective on every residue-field
fibre (`LinearMap.bijective_of_residueField_baseChange_bijective`). Its halves
are `LinearMap.surjective_of_residueField_baseChange_surjective` (finite
target; Nakayama at every prime) and
`LinearMap.injective_of_surjective_of_residueField_baseChange_injective`
(surjective map from a finite module onto a projective one). The latter has
other conditions than `LinearMap.injective_of_residueField_baseChange_injective`
of FiberInjectivity: no free source or reduced ring, but surjectivity, finite
source and projective target. No Noetherian hypothesis is needed.

[FiberDimension/Reduced](FiberDimension/Reduced.lean) proves freeness of a
finite module over a reduced local ring from local constancy of its original
fibre dimension, without flatness, finite presentation or Noetherianity.
Its exact closed-point normalization compares the native prime residue field
with the usual quotient residue field. The independent public consumer
passed `1792102760772343000-32015`, with only the three standard axioms.
