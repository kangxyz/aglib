/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Divisor.Functor

/-! Focused consumer of the functor `Div^θ_X` of relative effective Cartier divisors with fibre
Hilbert polynomial `θ` (Kleiman, arXiv:math/0504020v1, Def. 3.6, p. 23, X-first): the points,
their base change, the closed-immersion form, the functor on `X ×_{Spec A} T` with the maps of
`RelativePicard.familyScheme`, and its identification with the subfunctor of divisors of the
Hilbert functor of `X`, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}

/-- A point of `Div^θ_X` is a relative effective Cartier divisor of `X_T` over `T` whose image in
`P^n_A ×_{Spec A} T` is a point of `Hilb^θ(T)`, flat over `T` and closed in `P^n_A ×_{Spec A} T`;
for a closed immersion the two conditions characterize the points. -/
example [Finite ι] (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] (θ : ℚ[X])
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (D : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    (hD : IsRelativeDivisorFamily i rfl θ g D) :
    Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd _ g) ∧
      IsHilbertFamily ι θ g (D.map (immersionBaseChange i rfl g)) ∧
      Flat (D.subschemeι ≫ pullback.snd _ g) ∧
      IsClosedImmersion (D.subschemeι ≫ immersionBaseChange i rfl g) ∧
      (IsRelativeDivisorFamily i rfl θ g D ↔
        Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd _ g) ∧
          IsHilbertFamily ι θ g (D.map (immersionBaseChange i rfl g))) :=
  ⟨hD.isRelativeEffectiveCartier, hD.isHilbertFamily_map, hD.flat, hD.isClosedImmersion,
    isRelativeDivisorFamily_iff_of_isClosedImmersion i rfl θ g D⟩

/-- For a closed immersion, a relative effective Cartier divisor whose image has fibre Hilbert
polynomial `θ` at every field point is a point of `Div^θ_X`. -/
example [Finite ι] (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] (θ : ℚ[X])
    {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))
    (D : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    (hD : Scheme.Hom.IsRelativeEffectiveCartier D.subschemeι (pullback.snd _ g))
    (hθ : ∀ (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ T),
      subschemeHilbertPolynomial ι K
        ((D.map (immersionBaseChange i rfl g)).comap (pointMap ι g x)) = θ) :
    IsRelativeDivisorFamily i rfl θ g D :=
  IsRelativeDivisorFamily.of_isRelativeEffectiveCartier i rfl θ hD hθ

/-- Base change of points of `Div^θ_X` along `f : T' ⟶ T`. -/
example (i : X ⟶ ProjectiveSpace A ι) [IsPreimmersion i] (θ : ℚ[X]) {T T' : Scheme.{u}}
    (g : T ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T)
    (D : (pullback (i ≫ toSpec A ι) g).IdealSheafData)
    (hD : IsRelativeDivisorFamily i rfl θ g D) :
    IsRelativeDivisorFamily i rfl θ (f ≫ g)
      (D.comap (pullback.map _ (f ≫ g) _ g (𝟙 X) f (𝟙 _) (by simp) (by simp))) :=
  hD.comap f rfl

/-- `Div^θ_X` on all schemes over `Spec A` and on locally Noetherian test schemes; its points are
closed subschemes of `X ×_{Spec A} T`, and morphisms act by the maps of the fibre products. -/
example (i : X ⟶ ProjectiveSpace A ι) [IsPreimmersion i] (θ : ℚ[X])
    {T T' : (Over (Spec (CommRingCat.of A)))ᵒᵖ} (f : T ⟶ T')
    (D : (relativeDivisorFunctor i rfl θ).obj T) :
    ((relativeDivisorFunctor i rfl θ).map f D).1 =
        D.1.comap (pullback.map _ T'.unop.hom _ T.unop.hom (𝟙 X) f.unop.left (𝟙 _) (by simp)
          (by rw [Category.comp_id, Over.w f.unop])) ∧
      IsRelativeDivisorFamily i rfl θ T.unop.hom D.1 ∧
      Nonempty ((Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u) :=
  ⟨relativeDivisorFunctor_map_coe i rfl θ f D, D.2,
    ⟨locallyNoetherianRelativeDivisorFunctor i rfl θ⟩⟩

/-- `Div^θ_X` is the subfunctor of divisors of the Hilbert functor of `X`, by the identity on the
underlying closed subschemes. -/
example (i : X ⟶ ProjectiveSpace A ι) [IsPreimmersion i] (θ : ℚ[X])
    (T : (Over (Spec (CommRingCat.of A)))ᵒᵖ) (V : (immersedHilbertFunctor i rfl θ).obj T)
    (D : (relativeDivisorFunctor i rfl θ).obj T) :
    (V ∈ (relativeDivisorSubfunctor i rfl θ).obj T ↔
        Scheme.Hom.IsRelativeEffectiveCartier V.1.subschemeι (pullback.snd _ T.unop.hom)) ∧
      ((relativeDivisorFunctorIso i rfl θ).inv.app T D).1.1 = D.1 :=
  ⟨mem_relativeDivisorSubfunctor_obj i rfl θ V, relativeDivisorFunctorIso_inv_app_coe i rfl θ T D⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsRelativeDivisorFamily.comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsRelativeDivisorFamily.comap

/--
info: 'AlgebraicGeometry.ProjectiveSpace.IsRelativeDivisorFamily.of_isRelativeEffectiveCartier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.IsRelativeDivisorFamily.of_isRelativeEffectiveCartier

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isRelativeDivisorFamily_iff_of_isClosedImmersion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isRelativeDivisorFamily_iff_of_isClosedImmersion

/--
info: 'AlgebraicGeometry.ProjectiveSpace.relativeDivisorFunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.relativeDivisorFunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.relativeDivisorSubfunctor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.relativeDivisorSubfunctor

/--
info: 'AlgebraicGeometry.ProjectiveSpace.relativeDivisorFunctorIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.relativeDivisorFunctorIso
