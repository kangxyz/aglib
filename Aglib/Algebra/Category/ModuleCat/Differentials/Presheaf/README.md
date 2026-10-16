# Relative differential presheaves

`Relative` completes the construction for Mathlib's original
`PresheafOfModulesOfCommRing.Derivation φ`, where `φ : S ⟶ F.op ⋙ R`
and the source and target categories may differ. The native
`DifferentialsConstruction.relativeDifferentials'` already covers the
identity-functor case; it remains unchanged.

The construction `DifferentialsConstruction.relativeDifferentials φ` is
the actual categorical cokernel of `absolutePullbackMap φ`. Absolute
differentials are the native differential presheaves relative to constant
`ULift ℤ`. The original presheaf pullback adjunction transposes the original
map on absolute differentials. `absolutePullbackMap_comp_eq_zero_iff`
identifies the cokernel condition with vanishing on the original base
sections. Thus `derivation φ`, `relativeDesc φ`, `isUniversal φ` and
`relativeDifferentialsHomEquiv φ M` retain the actual cokernel projection,
descent and derivation values. Coefficient postcomposition is compatible
with that same descent.

The theorem `hasDifferentials φ` supplies the existing native existence
class from this unconditional mathematical construction. It does not
register a competing instance or change the priority of the original
identity-case instance. `relativeDifferentialsIdIso` compares the new
general construction in that case with `relativeDifferentials'`; both
directions send the original `d a` to the original `d a`.

The ring/section universe and both category object and morphism universes
are explicit and independent. The existing native
`(pushforward.{u} φ).IsRightAdjoint` is retained, since it is precisely what
defines the native presheaf pullback. Mathlib supplies it automatically
for same-universe small categories, including scheme open categories.
No universal-derivation family, smoothness, finiteness, or geometric base
condition is assumed. The next consumer is the original module
sheafification, followed by the original scheme structure map for
relative differentials over arbitrary bases.
