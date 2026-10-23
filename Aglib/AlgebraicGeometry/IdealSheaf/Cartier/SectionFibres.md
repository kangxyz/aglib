# Actual Cartier sections after pullback

For `i : Z ⟶ X`, a global function `a` in the original kernel
`RingHom.ker i.appTop.hom` defines
`Scheme.Hom.idealGlobalSection i a ha : 𝒪_X ⟶ idealModule i` through the
original `idealSectionsEquiv` and `unitHomGlobalSectionsEquiv`.
`idealGlobalSection_germ_mem_stalkIdeal` sends that original global function
to its original stalk ideal at every point, with no rank-one hypothesis.

The hypotheses are `[QuasiCompact i]` and
`IsLocallyRankOne X (idealModule i)`. In particular they apply to the original
closed Cartier immersion. For an arbitrary morphism `j : C ⟶ X`, every
conclusion concerns the same literal pulled section

```lean
(Scheme.Modules.pullbackUnitIso j).inv ≫
  (Scheme.Modules.pullback j).map (Scheme.Hom.idealGlobalSection i a ha)
```

`idealGlobalSection_pullback_stalk_isIso_of_generator` proves its native
module-stalk map is an isomorphism at an actual point `c : C` when

```lean
i.ker.stalkIdeal (j c) =
  Ideal.span {X.presheaf.germ ⊤ (j c) trivial a}
```

`idealGlobalSection_pullback_ne_zero_of_generator` then proves that this
same pulled section is nonzero. Taking `c` to be the original generic point
gives the intended integral-component application; the theorem itself does
not require integrality or a generic point.

`idealGlobalSection_pullback_not_isIso_of_mem_maximal_mul` proves that the
same pulled section is not an isomorphism if, at an actual `c : C`,

```lean
X.presheaf.germ ⊤ (j c) trivial a ∈
  IsLocalRing.maximalIdeal (X.presheaf.stalk (j c)) * i.ker.stalkIdeal (j c)
```

The proof identifies the original ideal-module stalk with the original
stalk ideal using `IdealSheaf.Modules.Stalk`, preserving the actual section
germ. Local rank one supplies a linear trivialization of that actual stalk:
pullback to the local spectrum is a line bundle, native local-ring triviality
applies, and `stalkFromSpecStalkSectionsIso` retains the original local-ring
scalar action. A generating element has a unit coefficient in this
trivialization. An element in the maximal ideal times the ideal has its
coefficient in the maximal ideal. The original pullback-stalk comparison is
extension along the original local ring homomorphism `j.stalkMap c`; such a
homomorphism reflects units. Scalar extension of the original section map
therefore proves the two claims, without a desired fibre-map premise.

The current consumer is `Surfaces.Resolution.VerticalCartier`, which owns
the actual valuation, support, power-membership and component arguments.
No normality, Noetherianity, properness, field, degree or surface-resolution
hypothesis enters this lower criterion. The source basis is native Aglib
with Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1.
