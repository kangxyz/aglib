# Castelnuovo–Mumford regularity on polynomial projective space

`Basic` defines `Scheme.Cohomology.IsProjectiveRegular R ι F m`: the original
cohomology `Sheaf.H` of the native tensor twist `O(m - q) ⊗ F` vanishes in every
positive degree `q` (Nitsure, arXiv:math/0504590v1, §2, p. 9, before Lemma 2.1;
Stacks, Tag 08A3). The base is an arbitrary
commutative ring and `ι` an arbitrary coordinate type in the base universe.

`exists_isProjectiveRegular` proves that every coherent module on projective
`n`-space over a Noetherian ring, with a labeling `ι ≃ Fin (n + 1)`, is
`m`-regular for some integer `m`. It combines `projectiveSerreVanishing` in the
degrees `1 ≤ q ≤ n` with `projectiveCohomology_subsingleton_of_gt` above `n`.

`CoordinateGeneration` starts a Koszul route to Lemma 2.1. Nitsure, Lemma 2.1,
and Stacks, Tag 08A6, are proved there by hyperplane sections over an infinite
field; the Koszul route planned here is a different proof of the same statements. For finitely many
coordinates, `coordinateMultiplicationSum` is the sum of the coordinate
multiplications `∐ᵢ O(0) ⊗ F → O(1 + 0) ⊗ F`. The instance
`epi_coordinateMultiplicationSum` proves it is an epimorphism for every module
`F` over every commutative base. Its cokernel is killed by every coordinate, so
it is zero by the Hilbert-polynomial family's `isZero_of_coordinate_eq_zero`.
This epimorphism is the last map of the Koszul complex of the coordinates
tensored with `F`. `twistingTensorMultiplyTo a d d' h s` is twist
multiplication with a free target degree, `h : a + d = d'`.
`twistingTensorMultiplyTo_comm` proves that multiplications by two global twist
sections commute through arbitrary intermediate degrees. The proof eliminates
the degree equations by `subst` and checks the coefficient maps of the twisting
sheaves on chart components. This is the identity behind `d² = 0` for the
Koszul differentials.

The conclusions of Nitsure, Lemma 2.1 over a field (that `m`-regular implies
`(m + 1)`-regular, global generation of `O(m) ⊗ F`, and surjectivity of
`H^0(O(1)) ⊗ H^0(O(r) ⊗ F) → H^0(O(r + 1) ⊗ F)` for `r ≥ m`) are not proved
here (Stacks, Tags 08A6, 08A7 and 08A8). Mumford's bound (Nitsure, Thm 2.3) is a
later consumer.
