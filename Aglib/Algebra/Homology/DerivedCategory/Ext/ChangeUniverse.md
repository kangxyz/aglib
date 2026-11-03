# The native Ext universe comparison is linear

`CategoryTheory.Abelian.Ext.chgUnivLinearEquiv` upgrades the original
`Ext.chgUniv` to an `R`-linear equivalence in an `R`-linear abelian category.
The scalar ring, category objects and morphisms, and both Ext sizes remain
independent. No commutativity or finiteness assumption is required.

The proof uses one native standard derived category internally: both native
Ext comparison maps have the same image there. Additivity and scalar
compatibility follow from the existing `Ext.add_hom` and `Ext.smul_hom`.
`chgUnivLinearEquiv_toEquiv` records that the underlying equivalence is
literally the existing `Ext.chgUniv`; no new universe-change map is chosen.

The current consumer is
[`Coinduction/Finite`](../../../Category/ModuleCat/ChangeOfRings/Coinduction/Finite.md),
which transports native standard-size Ext finiteness to the specified Ext
carrier before using its unchanged source-algebra action.
