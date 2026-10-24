# Original Cartier section and positive extension adapters

This module supplies lower producers for arbitrary-coefficient Cartier
adjunction. Its own statements do not include global Cartier purity.

For a closed immersion `i : D → X`, the section of the actual dual ideal is
`InternalHom.transpose X (idealInclusion i)`. The tensor transformation uses the
original left-unit inverse and original section coefficient map. When the
actual ideal is locally rank one, its evaluation on that ideal is the original
ideal inclusion, with positive sign.

The proof that this transformation vanishes on every `i_*T` has no hypothesis
on `T`. The original pullback/pushforward adjunction shows that the original
ideal inclusion pulls back to zero. Naturality of the original closed-immersion
projection formula therefore makes its tensor map zero on `i_*T`. The original
dual evaluation and associator give the same vanishing after tensoring the
section transformation by the ideal. Naturality with the original braiding and
faithfulness of tensor by an actual line bundle remove that tensor factor.
Thus arbitrary module-sheaf coefficients and nonreduced support are retained.

The separate twist-regularity theorem says that monicity of the actual section
on `M` implies monicity on `I^dual ⊗ M`. It uses exact tensor by the line bundle,
the original associator, and naturality with the original braiding. It does not
assume that `M` is locally free. Local regular-parameter hypotheses still need
to be converted to this monicity in the global coefficient-row producer.

The actual section then acts by zero on every native `Ext^n_X(i_*T,M)`. This
uses native exact-functor naturality for the transformation `Id → I^dual ⊗ -`;
the source action is the already proved zero map. It is not an assumed Ext
annihilation interface.

The categorical extension adapter has explicitly conditional scope. For an
exact additive endofunctor `K`, a transformation `τ : Id → K`, and an actual
short exact row `M → K M → F Q`, it sends `f : F T → F Q` to positive composition
with that row's `extClass`. Section annihilation and monicity on `K M` make
this map bijective by the native covariant Ext sequence. The actual derived
adjunction sends the original positive row class to one specified mate.
If its target is concentrated in the heart, represented by any heart object
`H`, Yoneda proves that this mate is invertible. The input does not identify
`H` with `Q`. Its inverse-adjunction law is exactly the original positive
extension class, and uniqueness uses that same adjunction.

This lower adapter takes a short exact row and heart concentration as
explicit inputs. The [global purity construction](Cartier/Purity/Global.md)
derives them from the actual Cartier ideal and coefficient regularity.
The row is

`0 → M → I^dual ⊗ M → i_*i^*(I^dual ⊗ M) → 0`

from the original ideal quotient and pullback/pushforward unit. Concentration
of the installed closed right adjoint is derived from regular equations and
coefficient regularity. The raw principal/positive comparison and full positive
derived-open compatibility remain separate obligations; this lower module
asserts neither. The principal closed-adjunction provider supplies the raw
purity and local homology comparisons used by the concentration construction.

The immediate consumer is the genuine CM-curve Cartier argument in the surface
resolution route. No coefficient orientation, canonical sheaf invertibility,
Gorensteinness, reducedness, geometric reducedness, perfectness or separability
is introduced. This pair does not provide the CM canonical concentration,
global Serre pairing, hyperplane generation or final rational-double-point
theorem.
