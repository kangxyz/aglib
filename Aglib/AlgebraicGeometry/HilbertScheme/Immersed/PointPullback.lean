/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.Functor

/-!
# Pullback of points of the Hilbert functor of an immersed scheme

Let `A` be a ring, `ι` a coordinate type and `i : Y ⟶ P^n_A = ProjectiveSpace A ι` a preimmersion
over `Spec A` (`hi : i ≫ toSpec A ι = πY`), with Hilbert functor
`locallyNoetherianImmersedHilbertFunctor i hi Φ` on locally Noetherian test schemes over `Spec A`
(`HilbertScheme/Immersed/Functor`: closed subschemes of `Y ×_{Spec A} T` that are proper over `T`
and whose images in `P^n_A ×_{Spec A} T` are flat with fibre Hilbert polynomials `Φ`).

* `locallyNoetherianImmersedHilbertFunctor_map_coe`: for `g : Z ⟶ T`, the functor sends a point
  `V` at `T` to its pullback along `pullback.map πY _ πY _ (𝟙 Y) g (𝟙 _) : Y_Z ⟶ Y_T`, the base
  change of `Y ×_{Spec A} T ⟶ T` along `g` (`Scheme.isPullback_pullbackMap_snd`);
* `locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap`: hence for any representation `E`
  of the functor by `H`, the point given by `a : T ⟶ H` is the pullback of the universal point
  `E.homEquiv (𝟙 H)` along `Y ×_{Spec A} T ⟶ Y ×_{Spec A} H` (Mathlib's
  `Functor.RepresentableBy.homEquiv_eq`).

No hypothesis beyond `[IsPreimmersion i]` (needed for the functor) is used. This leaf imports only
the functor, so that consumers of these two formulas, such as the Hilbert scheme of an immersed
scheme (`HilbertScheme/Immersed/Representability`) and the scheme of relative effective Cartier
divisors, need not import a construction of the Hilbert scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {ι : Type u} {A : Type u} [CommRing A] {Y : Scheme.{u}}
  {πY : Y ⟶ Spec (CommRingCat.of A)} (i : Y ⟶ ProjectiveSpace A ι) (hi : i ≫ toSpec A ι = πY)

/-- **Pullback of points of the Hilbert functor of `Y`**: for `g : Z ⟶ T`, the pullback of a point
`V` of `locallyNoetherianImmersedHilbertFunctor i hi Φ` at `T` is its pullback along
`pullback.map πY _ πY _ (𝟙 Y) g (𝟙 _) : Y ×_{Spec A} Z ⟶ Y ×_{Spec A} T`. -/
theorem locallyNoetherianImmersedHilbertFunctor_map_coe [IsPreimmersion i] (Φ : ℚ[X])
    {T Z : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (V : (locallyNoetherianImmersedHilbertFunctor i hi Φ).obj (op T)) (g : Z ⟶ T) :
    ((locallyNoetherianImmersedHilbertFunctor i hi Φ).map g.op V).1 =
      V.1.comap (pullback.map πY Z.obj.hom πY T.obj.hom (𝟙 Y) g.hom.left (𝟙 _) (by simp)
        (by rw [Category.comp_id, Over.w g.hom])) :=
  rfl

/-- **A representation of the Hilbert functor of `Y` pulls back its universal point**: for a
representation `E` of `locallyNoetherianImmersedHilbertFunctor i hi Φ` by `H`, the point given by
`a : T ⟶ H` is the pullback of `E.homEquiv (𝟙 H)` along
`pullback.map πY _ πY _ (𝟙 Y) a (𝟙 _) : Y ×_{Spec A} T ⟶ Y ×_{Spec A} H`. -/
theorem locallyNoetherianImmersedHilbertFunctor_homEquiv_eq_comap [IsPreimmersion i] {Φ : ℚ[X]}
    {H : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))}
    (E : (locallyNoetherianImmersedHilbertFunctor i hi Φ).RepresentableBy H)
    {T : Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A))} (a : T ⟶ H) :
    (E.homEquiv a).1 = (E.homEquiv (𝟙 H)).1.comap (pullback.map πY T.obj.hom πY H.obj.hom (𝟙 Y)
      a.hom.left (𝟙 _) (by simp) (by rw [Category.comp_id, Over.w a.hom])) := by
  rw [E.homEquiv_eq a]
  rfl

end AlgebraicGeometry.ProjectiveSpace
