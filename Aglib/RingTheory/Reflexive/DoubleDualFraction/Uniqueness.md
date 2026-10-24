# Original evaluation fixes the generic bidual map

Let `f : M -> V` be the specified localization at the nonzero divisors
of `R`, with `M` finitely presented and the generic module `V` reflexive
over the specified fraction field `K`. The existing
`doubleDualToFraction f` embeds the actual double dual of `M` into `V`
and sends the original evaluation of `m` to `f(m)`.

Every bidual element `z` has a denominator multiple equal to an
original evaluation. Indeed, represent its generic image by `f(m)/s`.
Injectivity of the original embedding gives `s*z = eval(m)`.
Multiplication by `s` is invertible on the original localization
module. Thus two linear maps from the bidual to `V` that agree on
all original evaluations agree everywhere.

In particular, the equation `g(eval(m)) = f(m)` determines `g` uniquely
as `doubleDualToFraction f`. The coefficient field parameter and the
localization map remain the original ones. The raw module is not
assumed reflexive or torsion-free.

The current geometric consumer uses this uniqueness to compare
affine generic bidual maps on overlaps while preserving their original
evaluation equations. The lemma does not assume a global sheaf map,
a canonical-module comparison, or trace compatibility.
