# The original exceptional conormal map

This module proves that the original canonical conormal map
`(Modules.pullback i).map (Hom.idealPullbackMap j i q e.hom h)` is an
isomorphism when the two conormal lines have the displayed native
positive-twist comparisons over the same specified field.

The public interfaces are:

- `Scheme.isDiscreteValuationRing_stalk_genericPoint_of_cartier`: for an
  integral closed Cartier divisor `j : D → B` in an integral locally
  Noetherian scheme, the actual stalk at `j (genericPoint D)` is a DVR.
- `Scheme.conormalMap_ne_zero_of_isProper_birational`: the original
  conormal map is nonzero for a proper dominant map `q : W → B` inducing
  an isomorphism on its actual function fields, and an original divisor
  isomorphism `e : E ≅ D` with `e.hom ≫ j = i ≫ q`.
- `Scheme.conormalMap_isIso_of_isProper_birational_projectiveLine`: actual
  projective-line comparisons and positive conormal comparisons over
  the same field turn that original map into an isomorphism.

The last theorem assumes integral `W` and `B`, local Noetherianity of `B`,
properness and dominance of `q`, the displayed function-field-map
isomorphism, local rank one of the actual ideal modules of `i` and `j`,
and that `j` is a closed immersion. It receives actual structural maps
`pE` and `pD` to `Spec k`, the original equation `e.hom ≫ pD = pE`, and
actual isomorphisms over `k` from both divisors to native projective
space indexed by `ULift (Fin 2)`. The line comparisons identify the
pullback of its native `twistingSheaf k (ULift (Fin 2)) 1` with each
original conormal module. The proof derives integrality of `E` and `D`.
The stronger statement does not need `i` to be closed; the intended
closed Cartier source is a direct specialization.

The generic-stalk proof uses the original closed-immersion stalk map,
its kernel, and a regular generator of the actual ideal module. The
existing proper-birational valuation-ring theorem gives an actual open
isomorphism neighborhood. Canonical restriction and pullback comparisons
show that the original conormal map is nonzero there.

The line-map argument uses the native dual-tensor equivalence and the
existing degree-zero nonzero-section theorem. Actual global functions
on the original projective line make its resulting nonzero scalar a
unit. The final degree comparison uses the existing isomorphism
invariance theorem with its proved norm/order provider. Both conormals
are compared to the same native twist; its numerical degree need not
be computed.

There is no ambient regularity, dimension-two, normality, perfectness,
algebraic-closure, or ambient coefficient-field premise. No global
ideal-pullback isomorphism, conormal-map isomorphism, nonzero morphism,
or degree equality is assumed. Different residue fields of different
blowup centres must first be identified through their original scalar
maps; that distinct factorization obligation is not discharged here.
All degrees used here retain their actual residue-field weights.
