# Original global Cartier coefficient row

This global-row lower family constructs the actual Cartier coefficient row
and proves its exactness. Its own statements do not include installed global
right-adjoint concentration or a global purity isomorphism.

Let `i:D→X` be a closed immersion whose original kernel ideal `I` is locally
rank one. Let `L=I^dual`, and retain the original canonical transformation
`τ:Id→L⊗-` from the Cartier parent. The constructed row is

`M --τ_M--> L⊗M --unit_(L⊗M)--> i_*i^*(L⊗M) → 0`.

Its second arrow is literally the original pullback/pushforward adjunction
unit. Its first arrow is literally the positive transpose of the original
ideal inclusion, tensored using the original tensor unitor. The only extra
hypothesis for short exactness is monicity of this original coefficient
section. This is genuine regularity of multiplication by the Cartier
equation; no row-exactness premise is supplied. The row and its exactness hold
for arbitrary module sheaves before that regularity condition is imposed.

Right exactness reuses the existing sheaf-level
`Pullback.Tensor.tensorHomEquiv`. Naturality in its first tensor factor gives
an adjoint to the original right tensor functor, hence preservation of finite
colimits. The original tensor braiding gives the same result for left tensor.
This avoids a second stalk-based tensor construction. The original closed
projection formula, followed by the original right unitor under pushforward,
identifies the tensor of the structure quotient with the original adjunction
unit; its section formula is `n⊗a ↦ i(a)·unit(n)`.

The first-map normalization uses the original ideal algebra. For actual ideal
sections `a,b`, the equality `inclusion(a)·b=inclusion(b)·a` follows from the
native section-kernel equivalence. Applying a local dual section and retaining
its restriction naturality proves

`evaluation;transpose(inclusion) = (id_L⊗inclusion);rightUnitor`.

No invertibility is needed for this equality. Invertibility makes its existing
evaluation map an isomorphism. The specified cancellation
`(L⊗M)⊗I ≅ M` consists only of the original associator, braiding, evaluation
and left unitor. Its first-map equation is proved with positive sign. That
specific isomorphism transports the original ideal tensor row to the displayed
Cartier row. No arbitrary coefficient frame or substitute purity isomorphism
is used.

The [global purity construction](Purity/Global.md) constructs principal charts
of the Cartier ideal, transfers coefficient regularity to them, and applies
Principal with the original derived homology exchange. This gives global
degree-one concentration on a locally Noetherian target with quasicoherent
coefficient. The positive-mate adapter then applies to this derived short
exact row and concentration. Raw/positive representative equality and full
positive derived-open compatibility remain separately named claims.

The current consumer is the nonreduced CM-curve Cartier step in the surface
resolution route. No coefficient freeness, canonical-module invertibility,
Gorensteinness, reducedness, perfectness, separability or coefficient-line
orientation is added. No Serre pairing, generation, GR or RDP theorem is claimed.
