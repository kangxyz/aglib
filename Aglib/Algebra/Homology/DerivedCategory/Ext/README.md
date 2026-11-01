# Original Ext maps and acyclic comparison

[AcyclicComparison](AcyclicComparison.lean) defines
`Functor.extPrecompMap` as the original `Ext.mapExactFunctor` followed by
precomposition with a specified original source morphism. Its degree-zero
formula and compatibility with Yoneda composition are proved.

`Functor.extPrecompMap_bijective_of_acyclic_injectives` needs an exact
additive functor, enough injectives in its source, a degree-zero bijection,
and actual positive Ext acyclicity of the images of source injectives for
the specified target source object. It proves bijectivity of that original
comparison in every degree. `extPrecompAddEquivOfAcyclicInjectives` packages
the same map as an additive equivalence. The functor is not required to
preserve injective objects or to be fully faithful.

The unit-module/additive-sheaf cohomology comparison uses this criterion
with the actual scalar-forgetting functor and its proved flasque injective
images. No scheme or quasicoherence hypothesis occurs in this lower family.

[Quotient](Quotient.lean) works over a commutative ring `R` and proves that
original Ext from `R/I` is annihilated by `I` and constructs its native
quotient-ring module action explicitly.
That action equals original Yoneda precomposition with multiplication on
`R/I`, the action used by scalar coinduction. All degrees and arbitrary
coefficients are included, without regularity, finiteness or Noetherianity.
The module action is not installed as a global instance. Its first consumer
is the [actual principal-ideal Koszul calculation](../../Koszul/Single/Ext/Ideal.lean).
Source and public consumer passed `1792127465949194000-98994` and
`1792127498584479000-99373` with only the standard three axioms.

[SingleShift](SingleShift.lean) proves that maps from the native same-degree
single of a projective object to a positive integer shift of any coefficient
single are zero. It retains the original single-functor shift and localization
comparisons. Only projectivity of the displayed source object is required;
there is no `HasExt`, enough-projectives, enough-injectives or coefficient
projectivity premise. Concentrated finite-free derived global sections in
relative projective Serre duality are a current consumer.

[YonedaPairing](YonedaPairing.lean) constructs `(c, e) ↦ c.comp
(e.mapExactFunctor L)` for an exact additive `L : C ⥤ D`, arbitrary
`A : D`, and independent source and target `HasExt` universes. It gives
the biadditive map, coefficient naturalities, unsigned connecting compatibility
and both curried maps into total degree `d` with their three squares. The
unsigned sign is `+1`; Mathlib's `Ext.δ` contributes `(-1)^(s+1)`, or
`(-1)^(d-r)` in the total-degree dual square.

[PairingComposition](PairingComposition.lean) supplies whole-map laws for
natural transformations and exact-functor composition. For `K ≅ P ⋙ Q` and
an exact adjunction `P ⊣ R`, it retains the original counit transformation
`R ⋙ K ⟶ Q`, its formula, composition and pairing/restriction squares. Counit
precomposition followed by `Adjunction.extEquiv` equals the native Ext map of
`R`; comparison evaluation uses the native Ext functor's `mapIso`.

[ZMod](ZMod.lean) proves Ext annihilation from `n • 𝟙 = 0` at either endpoint
and preservation by additive functors. For every modulus, including zero, it
provides named local canonical `ZMod n` actions, a bilinear pairing and both
curried linear maps, using `AddCommGroup.zmodModule`.

[PairingZero](PairingZero.lean) gives original degree-zero source and
coefficient maps and unit/scalar laws for the exact-functor Yoneda pairing,
with independent category and Ext universes.

[Effacement](Effacement.lean) kills each positive Ext class by an actual
epimorphism to its source, without enough injectives or projectives.
[Bifunctor](Bifunctor.lean) constructs the original external Ext product for
a genuine biexact additive bifunctor between abelian categories with the
stated `HasExt` instances. Its whole interchange law has sign `(-1)^(p*q)`;
it also supplies the unsigned source connecting-class laws (sign `+1` in
the first variable and `(-1)^p` in the second) and native signed connecting-map
compatibility. These categorical results do not identify a
geometric cohomology product or establish Künneth or degree-one duality.

[PairingBiproduct](PairingBiproduct.lean) gives the whole component-sum
law for the original trace-composed exact-functor Yoneda pairing and both
dual naturality laws. Component perfectness for the same trace implies
perfectness at the actual finite coefficient biproduct, and an actual
coefficient isomorphism preserves perfectness. The public index condition
is `Finite I`; the empty family and level one are included. Component
perfectness is an input, with no finite-free or domain assumption on the
Ext modules.

[LeftExactComparison](LeftExactComparison.lean) constructs the canonical
reverse map independently through the original derived single unit and
inverse composition comparison. On an actually acyclic target it is inverse
to the original forward comparison. Its original Ext degree-zero and target
naturality laws retain their stated hypotheses; ordinary-cohomology versions
require the displayed target acyclicity. Source connecting compatibility is
a separate obligation.
