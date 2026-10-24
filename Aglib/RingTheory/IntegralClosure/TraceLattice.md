# A fixed trace lattice and its original principal localization

This module constructs a fixed trace lattice and its original principal
localization. It does not assert geometric finite domination or whole H¹
boundedness.

The namespace is `Algebra.TraceLattice`. The inputs are commutative domains
`A` and `B`, the original finite `A`-algebra structure on `B`, and supplied
fields `K` and `L` with their actual fraction-ring structures for `A` and `B`.
The supplied `A → L` and `K → L` algebra maps form the two original scalar
towers. They force injectivity of `A → B`: the composite `A → K → L` is
injective, and it equals `A → B → L`. An explicit ring homomorphism is used
by installing its original `toAlgebra` structure and these compatible maps.

The basis construction only needs those inputs. `IsIntegrallyClosed A`
supplies base-valued traces. Separability of `L/K` supplies the nonzero
discriminant, injective trace coordinates and the second adjugate identity.
Finite degree of `L/K` is derived from finite `B/A` by the existing
`IsFractionRing.finite_of_finite_algebra`; it is not an added premise.
The rings and fields share the current consumer's universe.

No Noetherianity, Nagata property, locality, dimension, normality of `B`,
freeness of `B` over `A`, invertibility of the field degree or separability
of residue fields is required.

`exists_fieldBasis`, `fieldBasis`, `basisElement` and
`algebraMap_basisElement` construct a fixed basis indexed by
`Fin (Module.finrank K L)` whose vectors are the images of original elements
of `B`. The original image of `B` spans `L`, by the native fraction-ring span
lemma; a basis is extracted from that span and reindexed. These choices are
made before any geometric model.

`fieldTrace : B →ₗ[A] A` is the original FIELD trace on `L/K`, restricted to
`B` and descended through the injective map `A → K`. Its values are integral
over `A`, so integral closedness supplies the descent. The constructor uses
the inverse of the original linear map onto its actual range.
`algebraMap_fieldTrace` and `fieldTrace_unique` retain the literal defining
equation. The construction does not use `Algebra.trace A B` as a substitute.

Write `b_i = basisElement A B K L i`. The remaining definitions are explicit:

| API | Original formula |
|---|---|
| `coordinates` | `φ(b)_i = fieldTrace (b_i * b)` |
| `gramMatrix` | `T_ij = fieldTrace (b_i * b_j)` |
| `discriminant` | `d = det T` in `A` |
| `expansion` | `ψ(v) = ∑ i, v_i • b_i` in the original `A`-module `B` |
| `adjugateExpansion` | `ξ(v) = ψ(adj(T) *ᵥ v)` |

`map_gramMatrix` and `algebraMap_discriminant` identify the original
base-valued matrix and determinant with the trace form of the same field
basis. The native separable trace-form theorem proves `discriminant_ne_zero`.
The original maps satisfy `φψ = T`; matrix adjugation gives
`coordinates_adjugateExpansion`, namely `φξ = d·id`. Trace nondegeneracy
proves `coordinates_injective`, so cancellation gives
`adjugateExpansion_coordinates`, namely `ξφ = d·id`. Both identities are
also exposed as equalities of the original `A`-linear maps. Their immediate
range consequence is `discriminant_smul_mem_range_expansion`.

The localization family uses the same elements and the same discriminant.
For compatible actual localizations `S = A[1/d]` and
`D = B[1/(algebraMap A B d)]`, `localizedBasis` is an `S`-basis of `D` and
`localizedBasis_apply` identifies each vector with `algebraMap B D b_i`.
`localized_finite_free` derives both finiteness and freeness. Independence
comes from the original field basis and the native localization theorem.
For spanning, write an original localized element with a denominator that
is a power of `d`, then use `d • b ∈ range ψ` and invertibility of that
denominator. No localized freeness is assumed.

`awayBasis` specializes to the literal `Localization.Away` rings. Its
displayed local algebra structure is native
`localizationAlgebra`, and the native scalar-tower theorem
retains the original commutative square. `awayBasis_apply` identifies its
vectors under the original localization homomorphism.

This is the algebraic fixed-denominator step of
[Stacks Lemma 54.8.6 (0AXL)](https://stacks.math.columbia.edu/tag/0AXL).
The original fraction fields and the native trace are kept throughout.
The new geometric trace sheaf, strict-transform finite domination and
the final original-H¹ length bound remain separate B3 obligations.
