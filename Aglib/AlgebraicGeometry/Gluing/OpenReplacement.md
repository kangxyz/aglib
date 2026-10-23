# Replacing one open chart by a proper contraction

[OpenReplacement.lean](OpenReplacement.lean) works with actual schemes and the
native open pushout. For open immersions `f : T ⟶ U`, `g : T ⟶ W` and an actual
map `b : U ⟶ V` such that `f ≫ b` is an open immersion, it constructs

`map f g b : pushout f g ⟶ pushout (f ≫ b) g`.

This is the native `pushout.map` with chart maps `b`, `𝟙 W` and overlap map
`𝟙 T`. Its two literal chart triangles are `inl_map` and `inr_map`.
`isPullback_inl` proves the replacement-chart square without further
hypotheses. `isPullback_inr` proves the unchanged-chart square under the actual
overlap condition

`H : IsPullback (𝟙 T) f (f ≫ b) b`.

`overlap_isPullback_of_preimage` and `overlap_preimage` identify this condition
with the exact equality `b ⁻¹ᵁ (f ≫ b).opensRange = f.opensRange`.
`isProper_map` assumes `IsProper b` and `H`; it checks properness on the two
actual target charts, where the maps are `b` and `𝟙 W`.
`isIso_restrict_unchanged` gives an isomorphism for the literal restriction to
the target copy of `W`.

`OfOpens` takes actual opens `U W : X.Opens` and `hcover : U ⊔ W = ⊤`.
It uses `Scheme.isPushout_opens_of_sup_eq_top` to identify the source pushout
with the original `X`. Its `map` therefore has literal source `X`, and
`left_map`, `right_map`, `isPullback_left` and `isPullback_right` retain the
original inclusions `U.ι` and `W.ι`. The properness and unchanged-open results
hold for this transported map with the same local hypotheses.

Both interfaces prove local Noetherianity and regularity of the actual target
stalks from those properties on `V` and `W`. These conclusions do not require
properness of `b` or the Cartesian overlap hypothesis. `fibre_inl` additionally
identifies the set-theoretic fibre over a point of `V` outside the overlap with
the original set-theoretic fibre of `b`.

`isClosedImmersion_inl_of_disjoint` applies to any actual open span
`a : T ⟶ V`, `g : T ⟶ W` and actual closed immersion `c : D ⟶ V`.
Its full avoidance hypothesis is `Disjoint (Set.range c) (Set.range a)`.
It proves `IsClosedImmersion (c ≫ pushout.inl a g)` by the two actual target
charts: the left base change is the original `c`, and the right base change
has empty source. Specializing `a = f ≫ b` propagates any supplied local closed
field point outside the overlap to the glued target. The helper itself assumes
no field, properness, Cartesian overlap condition or separation property.

For a surface contraction, the consumer must still construct the local proper
map `b`, the actual complement identification and its exact-preimage condition.
The construction of the local closed field point and verification that it
avoids the overlap remain inputs to the closed-immersion helper. The generic
fibre statement does not supply a scheme-theoretic fibre identification or
inverse-blowup recognition. A relative projectivity or relative ampleness
conclusion also remains a separate obligation. No separation, excellence,
perfectness or coefficient-field premise is used in this generic construction.
