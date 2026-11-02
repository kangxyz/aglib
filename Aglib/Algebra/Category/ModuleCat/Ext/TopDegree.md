# Top-degree Ext over a Noetherian local ring

Let `R` be a Noetherian commutative local ring and let `M,N` be finite
`R`-modules, with `N` nonzero. If the native projective dimension of `M`
is at most `n + 1`, then vanishing of the original `Ext^(n+1)(M,N)` lowers
that bound to `n`. The Ext universe is independent of the module carrier
universe.

`hasProjectiveDimensionLE_of_top_ext_subsingleton` constructs a bounded
minimal finite free resolution using
`ModuleCat.exists_minimal_finite_free_resolution`. No terminal resolution
or regularity of the ring is an input. If its degree `n + 1` term were
nonzero, choose a basis vector and an element of `N` outside its maximal
ideal multiple, supplied by Nakayama's lemma. The corresponding linear map
from that top term is an actual cocycle. Its original Ext class cannot be
zero: the native boundary criterion would factor it through the minimal
differential, sending the chosen element into the maximal ideal multiple.
The contradiction makes the top term zero, and the same resolution gives
the lower projective-dimension bound.

`projective_of_self_ext_subsingleton` iterates this result. A finite module
of finite projective dimension whose positive self-Ext groups vanish is
projective. This statement includes the zero module. It does not claim
that vanishing in an arbitrary positive degree lowers projective dimension.

The canonical-module application must separately establish finite projective
dimension and positive self-Ext vanishing for the original canonical module.
This leaf supplies neither a Gorenstein definition nor a canonical
trivialization. Nakayama's lemma is the standard
[Stacks, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV).
