# Native shifts of installed geometric direct images

[Shift](Shift.lean) gives transparent native shift, triangulated and unit
compatibility instances for the original `derivedPushforwardPlus` and
`derivedPushforwardPlusUnit`. It retains the same standard module-sheaf
derived models and actual right-derived shift structures. Any scheme
morphism is allowed; no coefficient or geometric condition is imposed.
Finite Postnikov arguments and original base-change descents consume the
installed geometric functor without selecting another model.

The native shift instance is `derivedPushforwardPlusCommShift`. Its former
name `derivedPushforwardPlus_commShift` remains a transparent deprecated alias
without registering another instance.

The [geometric-section comparison](../PushforwardSection.lean) imports and
reuses this same native shift instance.
