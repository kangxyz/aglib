# Finite module-sheaf diagrams on given scheme limits

The global object, Hom and equality suppliers are constructed in the owning
modules. This leaf assembles their actual finite object and arrow models into
an actual functor with all of its original comparison equations.

`Scheme.Modules.exists_functor_above_of_isLimit F c hc i₀ D hD` descends
an actual finite-category functor `D : J ⥤ c.pt.Modules` with finitely
presented objects. The input is a native cofiltered diagram `F` of qcqs
schemes with affine transition maps, its original cone `c` and limit proof
`hc`, and a specified starting stage `i₀`.

The result is an actual later stage `i` and arrow `i ⟶ i₀`, an actual
functor `Dᵢ : J ⥤ (F.obj i).Modules` with finitely presented objects, and a
native natural isomorphism
`Dᵢ ⋙ Scheme.Modules.pullback (c.π.app i) ≅ D`. Finiteness is the native
`FinCategory` condition: both objects and all morphism sets are finite.
The finite indexing category can have an independent universe.

The proof puts the finite family of original object models at one stage
using a cofiltered common source. Every subsequent step pulls the whole
family back along the actual transition map. The original object
comparisons are updated using `pullbackConeCompIso`, which uses the exact
original cone equation and native pullback composition.

All arrows are descended using the finite sigma type of object pairs and
their original Hom sets. The identity equation for each object and the
composition equation for each composable pair are then descended through
the actual map-equality theorem. The resulting equations are the actual
`Functor.map_id` and `Functor.map_comp` proofs. The retained original map
comparisons supply the naturality proofs of `NatIso.ofComponents`.

`Scheme.Modules.exists_iso_above_of_isLimit` applies the same construction
to a specified isomorphism through the native two-object category
`Codiscrete Bool`. It returns an actual stage isomorphism, its inverse laws,
and object comparisons satisfying both original-map equations:

```
P.map d.hom ≫ eQ.hom = eP.hom ≫ e.hom
P.map d.inv ≫ eP.hom = eQ.hom ≫ e.inv
```

Here `P` is the native pullback by the original limit projection. No new
category or topology construction is added.

`Scheme.Modules.exists_functor_above_of_baseChange` is the direct
given-model specialization. For an original qcqs model map
`a : X ⟶ F.obj i₀`, it uses the literal `Scheme.baseChangeDiagram F i₀ a`,
`Scheme.baseChangeCone F c i₀ a` and native `isLimitBaseChangeCone`. Its
input functor lives on the actual `pullback (c.π.app i₀) a`, and its stage
functor lives on an actual object of that same canonical base-change
diagram. The comparison retains that cone's original projection.

The actual global object, Hom and equality suppliers are imported from
`Objects` and `Maps`. No desired object, Hom or diagram descent
family is an input to these public endpoints. The assumptions are qcqs
stages, affine transition maps and finite presentation of the actual module
sheaves; no flatness, injectivity or Noetherianity assumption is imposed.
Compilation evidence is separate from this API guide.
