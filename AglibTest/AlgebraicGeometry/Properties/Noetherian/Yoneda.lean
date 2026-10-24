/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.Yoneda

/-!
# Yoneda on locally Noetherian test schemes

The declarations below restate the locally Noetherian Yoneda tests for isomorphisms (absolute and
over a base), monomorphisms (through the diagonal, over a base, and for morphisms locally of finite
type), the factorization criteria for closed subschemes, the equality of closed subschemes with the
same locally Noetherian points, and the comparison of pulled-back closed subschemes used for
`p₁⁻¹Γ = p₂⁻¹Γ` in Nitsure's proof of Theorem 6.8, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AglibTest.LocallyNoetherianYoneda

/-- Isomorphisms of locally Noetherian schemes are detected on locally Noetherian points. -/
theorem isIso_of_bijective {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Bijective fun x : T ⟶ X => x ≫ f) : IsIso f :=
  Scheme.isIso_of_locallyNoetherian_yoneda_map_bijective f hf

/-- Over a base, isomorphisms are detected on locally Noetherian points over the base. -/
theorem isIso_over_of_bijective {S : Scheme.{u}} {X Y : Over S} [IsLocallyNoetherian X.left]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y)
    (hf : ∀ T : Scheme.LocallyNoetherianOver S, Function.Bijective fun x : T.obj ⟶ X => x ≫ f) :
    IsIso f ∧ IsIso f.left :=
  ⟨Scheme.LocallyNoetherianOver.isIso_of_yoneda_map_bijective f hf,
    Scheme.LocallyNoetherianOver.isIso_left_of_yoneda_map_bijective f hf⟩

/-- A morphism locally of finite type over a locally Noetherian scheme that is injective on
locally Noetherian points is a monomorphism, and its diagonal is an isomorphism. -/
theorem mono_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) :
    Mono f ∧ IsIso (pullback.diagonal f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨Scheme.mono_of_locallyNoetherian_yoneda_map_injective_of_locallyOfFiniteType f hf,
    Scheme.isIso_diagonal_of_locallyNoetherian_yoneda_map_injective f hf⟩

/-- **Nitsure's exercise (p. 33)**: a proper morphism into a locally Noetherian scheme that is
injective on locally Noetherian points is a closed immersion. -/
theorem isClosedImmersion_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (hf : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      Function.Injective fun x : T ⟶ X => x ≫ f) : IsClosedImmersion f :=
  Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective f hf

/-- Over a base, injectivity on locally Noetherian points over the base gives a monomorphism. -/
theorem mono_over_of_injective {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsLocallyNoetherian (pullback f.left f.left)]
    (hf : ∀ T : Scheme.LocallyNoetherianOver S, Function.Injective fun x : T.obj ⟶ X => x ≫ f) :
    Mono f ∧ Mono f.left :=
  ⟨Scheme.LocallyNoetherianOver.mono_of_yoneda_map_injective f hf,
    Scheme.LocallyNoetherianOver.mono_left_of_yoneda_map_injective f hf⟩

/-- A morphism factors through the closed subscheme of `I` exactly when `I` is contained in its
kernel; through `I.comap f` exactly when its composite with `f` factors through `I`. -/
theorem exists_lift_iff {X Y T : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (g : T ⟶ X) :
    ((∃ a : T ⟶ (I.comap f).subscheme, a ≫ (I.comap f).subschemeι = g) ↔
      ∃ b : T ⟶ I.subscheme, b ≫ I.subschemeι = g ≫ f) ∧
    ((∃ b : T ⟶ I.subscheme, b ≫ I.subschemeι = g ≫ f) ↔ I ≤ (g ≫ f).ker) :=
  ⟨Scheme.IdealSheafData.exists_lift_comap_subschemeι_iff I f g,
    Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker I (g ≫ f)⟩

/-- Closed subschemes of a locally Noetherian scheme with the same locally Noetherian points are
equal. -/
theorem eq_of_points {X : Scheme.{u}} [IsLocallyNoetherian X] {I J : X.IdealSheafData}
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ X),
      (∃ a : T ⟶ I.subscheme, a ≫ I.subschemeι = g) ↔
        ∃ b : T ⟶ J.subscheme, b ≫ J.subschemeι = g) :
    I = J :=
  Scheme.IdealSheafData.eq_of_locallyNoetherian_exists_lift_iff h

/-- Two closed immersions into a locally Noetherian scheme with the same locally Noetherian points
are isomorphic over the target. -/
theorem isIso_lift_of_points {X Z₁ Z₂ : Scheme.{u}} [IsLocallyNoetherian X] (i₁ : Z₁ ⟶ X)
    (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ X),
      (∃ a : T ⟶ Z₁, a ≫ i₁ = g) ↔ ∃ b : T ⟶ Z₂, b ≫ i₂ = g) :
    ∃ hk : i₁.ker = i₂.ker, IsIso (IsClosedImmersion.lift i₁ i₂ hk.le) :=
  have hk := Scheme.Hom.ker_eq_of_locallyNoetherian_exists_lift_iff i₁ i₂ h
  ⟨hk, IsClosedImmersion.isIso_lift i₁ i₂ hk⟩

/-- **The equality `p₁⁻¹Γ = p₂⁻¹Γ`** is tested on locally Noetherian points (Nitsure,
arXiv:math/0504590v1, proof of Theorem 6.8, pp. 34–35). -/
theorem comap_eq_comap_of_points {D E : Scheme.{u}} [IsLocallyNoetherian E]
    (Γ : D.IdealSheafData) (q₁ q₂ : E ⟶ D)
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (g : T ⟶ E),
      (∃ a : T ⟶ Γ.subscheme, a ≫ Γ.subschemeι = g ≫ q₁) ↔
        ∃ b : T ⟶ Γ.subscheme, b ≫ Γ.subschemeι = g ≫ q₂) :
    Γ.comap q₁ = Γ.comap q₂ :=
  Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff Γ q₁ q₂ h

/-- info: 'AglibTest.LocallyNoetherianYoneda.isIso_of_bijective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.isIso_of_bijective

/-- info: 'AglibTest.LocallyNoetherianYoneda.isIso_over_of_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.isIso_over_of_bijective

/-- info: 'AglibTest.LocallyNoetherianYoneda.mono_of_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.mono_of_injective

/-- info: 'AglibTest.LocallyNoetherianYoneda.isClosedImmersion_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.isClosedImmersion_of_injective

/-- info: 'AglibTest.LocallyNoetherianYoneda.mono_over_of_injective' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.mono_over_of_injective

/-- info: 'AglibTest.LocallyNoetherianYoneda.exists_lift_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.exists_lift_iff

/-- info: 'AglibTest.LocallyNoetherianYoneda.eq_of_points' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.eq_of_points

/-- info: 'AglibTest.LocallyNoetherianYoneda.isIso_lift_of_points' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.isIso_lift_of_points

/-- info: 'AglibTest.LocallyNoetherianYoneda.comap_eq_comap_of_points' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LocallyNoetherianYoneda.comap_eq_comap_of_points

end AglibTest.LocallyNoetherianYoneda
