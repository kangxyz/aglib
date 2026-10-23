# Canonical maps of actual conormal modules

Import `Aglib.AlgebraicGeometry.IdealSheaf.Modules.ConormalMap`.
The namespace is `AlgebraicGeometry.Scheme.Hom`.

For an original scheme morphism `i`, the module in this API is the literal
pullback `(Scheme.Modules.pullback i).obj (idealModule i)`. The canonical
map `conormalSquareMap i i' b a h` uses the original commutative square
`h : a ≫ i = i' ≫ b`, native pullback composition and equality comparisons,
and `idealPullbackMap`. Its source is the pullback along `a` of that same
conormal module. `conormalSquareMap_comp` retains these comparisons when
two original squares are pasted. `conormalSquareMap_id_source` retains the
native identity-pullback comparison. `conormalSquareMap_comp_ambient` and
`conormalMap_comp_square` specialize pasting to an ambient factorization
on either side, and `conormalSquareMap_source_congr` records equality of
the original source maps.

`conormalMap` is the same-source comparison for `i = i' ≫ b`.
`conormalMap_comp` gives its composition law. When `b` is an open immersion,
`conormalMap_isIso_of_isOpenImmersion` identifies the conormal with that
of the same source in the original open ambient neighbourhood. The maps
and composition laws require no affineness, flatness, closed-immersion,
Noetherian or quasicoherence assumptions.

The actual quotient-section overlap comparison and frame compatibility
in `ProjectiveBundle.RankTwoExtension` consume this API. Local coordinate
normalization and global frame compatibility are separate statements in
that family; they are not consequences of canonical-map functoriality alone.
