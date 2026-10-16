# One Koszul factor, scalar quotients and tensor columns

[The parent single-factor leaf](../Single.lean) owns the multiplication complex,
its original principal quotient augmentation and regularity theorem.
[Quotient](Quotient.lean) takes an arbitrary nonnegative module complex to its
literal degreewise scalar-image quotient, retaining the native quotient
projection and its vanishing criterion. [ScalarQuotientFunctor](../ScalarQuotientFunctor.lean)
is the actual additive module functor behind this degreewise quotient; it
preserves each scalar-multiplication morphism.

The [tensor guide](Tensor/README.md) records the signed columns, additive-functor
comparison and original augmentation to this quotient. None of these results
asserts that an arbitrary additive functor preserves homology.

[Ext](Ext.lean) computes native degree-one `Ext` from the original regular
one-element resolution. Its linear quotient equivalence sends the literal
coefficient class to the original Koszul cocycle and commutes with native
Yoneda coefficient postcomposition. The kernel is exactly scalar multiples.
Source regularity bounds projective dimension by one; coefficient regularity
kills degree zero, so regularity on both gives concentration in degree one.
The ring is arbitrary and the coefficient need not be finite, flat or
regular for the degree-one calculation. [Ideal](Ideal.lean) identifies the original module quotient with the actual
principal ideal quotient and constructs the native quotient-ring action on
arbitrary coefficient quotients. [Ext/Ideal](Ext/Ideal.lean) transports the
original calculation to `Ext_R(R/(a), N)`, linearly over `R/(a)`. Its scalar
action is exactly original Yoneda precomposition with source multiplication;
original cocycle representatives and coefficient postcomposition are retained.
Degree-zero vanishing only needs coefficient regularity. The actual ring
quotient has projective dimension at most one for source regularity, without
an Ext-existence premise. Localization and determinant normalization remain
further purity obligations. Source and independent public consumer passed with only
the standard three axioms.

The actual-ideal Ext source and independent public consumer passed
`1792127777119394000-2349` and `1792127830785831000-2948`, with only propext,
Classical.choice and Quot.sound. The ordinary quotient action preserves
independent ring and coefficient universes.

`singleQuotientIdealQuotientLinearEquiv` retains the original principal
quotient comparison and representatives while making its `R/(a)`-linearity
explicit. The extension passed `1792148189772184000-18901`. Its current
consumer is the actual [derived principal coinduction](../../../Category/ModuleCat/ChangeOfRings/Coinduction/Principal.lean),
whose homology normalization uses the unchanged Koszul class. The public
consumer `1792150144251703000-34185` checks both the ordinary map and the
actual concentrated derived object at independent derived sizes.
