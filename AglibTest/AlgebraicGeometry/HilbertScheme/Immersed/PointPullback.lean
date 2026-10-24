/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.PointPullback

/-! Focused consumer of the pullback of points of the Hilbert functor of an immersed scheme
`Y ⊆ P^n_A` on locally Noetherian test schemes: the action on morphisms and the pullback form of
any representation, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] {ι : Type u} {Y : Scheme.{u}}

/-- The Hilbert functor of `Y` on locally Noetherian test schemes acts by pullback along the maps
`Y ×_{Spec A} Z ⟶ Y ×_{Spec A} T`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X])
    {T Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (V : (locallyNoetherianImmersedHilbertFunctor i rfl Φ).obj (op T)) (g : Z ⟶ T) :
    ((locallyNoetherianImmersedHilbertFunctor i rfl Φ).map g.op V).1 =
      V.1.comap (pullback.map (i ≫ toSpec A ι) Z.obj.hom (i ≫ toSpec A ι) T.obj.hom (𝟙 Y)
        g.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w g.hom])) :=
  locallyNoetherianImmersedHilbertFunctor_map_coe i rfl Φ V g

/-- **Any representation of the Hilbert functor of `Y` pulls back its universal point.** -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i] (Φ : ℚ[X])
    {H T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (E : (locallyNoetherianImmersedHilbertFunctor i rfl Φ).RepresentableBy H) (a : T ⟶ H) :
    (E.homEquiv a).1 = (E.homEquiv (𝟙 H)).1.comap (pullback.map (i ≫ toSpec A ι) T.obj.hom
      (i ≫ toSpec A ι) H.obj.hom (𝟙 Y) a.hom.left (𝟙 _) (by simp)
      (by rw [Category.comp_id, Over.w a.hom])) :=
  locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i rfl E a

/-- The same holds for a closed immersion, the case of the scheme of relative effective Cartier
divisors on a closed `X ⊆ P^n_A`. -/
example (i : Y ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] (Φ : ℚ[X])
    {H T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (E : (locallyNoetherianImmersedHilbertFunctor i rfl Φ).RepresentableBy H) (a : T ⟶ H) :
    (E.homEquiv a).1 = (E.homEquiv (𝟙 H)).1.comap (pullback.map (i ≫ toSpec A ι) T.obj.hom
      (i ≫ toSpec A ι) H.obj.hom (𝟙 Y) a.hom.left (𝟙 _) (by simp)
      (by rw [Category.comp_id, Over.w a.hom])) :=
  locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap i rfl E a

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctor_map_coe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctor_map_coe

/--
info: 'AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap
