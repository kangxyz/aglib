/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.LocallyNoetherianPoint
public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver

/-!
# The Hilbert functor maps to the Grassmannian on locally Noetherian test schemes

On the locally Noetherian test schemes over `Spec A` (`Scheme.LocallyNoetherianOver`), the
Hilbert functor of `P^n_A` (`locallyNoetherianHilbertFunctor`, the restriction of
`hilbertFunctor`) maps to the functor of points of the Grassmannian
`Gr = Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ(r)⌋₊ N`, `N = (n + r).choose r`
(`locallyNoetherianGrassmannianFunctor`, the restriction of `yoneda.obj Gr`), for every natural
number `r ≥ hilbertRegularityBound n Φ`: the natural transformation
`locallyNoetherianGrassmannianNatTrans` sends a point `Z` of `Hilb^Φ(T)` to its Grassmannian point
`IsHilbertFamily.grassmannianMap`, the classifying map of the quotient
`𝒪_T^N ⟶ π_* 𝒪_Z(r)`. This is the morphism of functors `α : Hilb^Φ → Grass(Sym^r, Φ(r))` of
Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, for
`E = 𝒪` on `P^n_A`.

The components are the regular definition `locallyNoetherianGrassmannianNatTransApp`; their
naturality (`locallyNoetherianGrassmannianNatTransApp_naturality`) is
`IsHilbertFamily.grassmannianMap_comp` at the morphism `φ.unop.hom` of test schemes, through
`Over.homMk_eta`.

This file proves only that `α` is a natural transformation. Its components are injective for
every ring `A` (`locallyNoetherianGrassmannianNatTrans_app_injective`), and for a Noetherian ring
`A` the Hilbert functor is represented by a locally closed subscheme `G_Φ` of the Grassmannian,
with `α` given by composition with `G_Φ ⟶ Gr` (`locallyNoetherianHilbertFunctorRepresentableBy`,
`locallyNoetherianGrassmannianNatTrans_app_homEquiv`); both are in
`HilbertScheme/Representability`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]

/-- The Hilbert functor of `P^n_A` on locally Noetherian test schemes over `Spec A`: the
restriction of `hilbertFunctor ι Φ` along `Scheme.locallyNoetherianOverInclusion`. -/
abbrev locallyNoetherianHilbertFunctor (Φ : ℚ[X]) :
    (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  (Scheme.locallyNoetherianOverInclusion _).op ⋙ hilbertFunctor ι Φ

/-- The functor of points of the Grassmannian `Grassmannian.schemeOver (CommRingCat.of A) k N` on
locally Noetherian test schemes over `Spec A`. -/
abbrev locallyNoetherianGrassmannianFunctor (k N : ℕ) :
    (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type u :=
  (Scheme.locallyNoetherianOverInclusion _).op ⋙
    yoneda.obj (Grassmannian.schemeOver (CommRingCat.of A) k N)

/-- The component at a locally Noetherian test scheme `T` of
`locallyNoetherianGrassmannianNatTrans`: a point `Z` of `Hilb^Φ(T)` goes to its Grassmannian
point `IsHilbertFamily.grassmannianMap`. -/
def locallyNoetherianGrassmannianNatTransApp (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ) :
    (locallyNoetherianHilbertFunctor ι A Φ).obj T →
      (locallyNoetherianGrassmannianFunctor A ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).obj T :=
  fun Z =>
    haveI : IsLocallyNoetherian T.unop.obj.left := T.unop.property
    (show IsHilbertFamily ι Φ T.unop.obj.hom Z.1 from Z.2).grassmannianMap ι n e r hr

theorem locallyNoetherianGrassmannianNatTransApp_apply (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (Z : (locallyNoetherianHilbertFunctor ι A Φ).obj T) :
    haveI : IsLocallyNoetherian T.unop.obj.left := T.unop.property
    locallyNoetherianGrassmannianNatTransApp ι n e A Φ r hr T Z =
      (show IsHilbertFamily ι Φ T.unop.obj.hom Z.1 from Z.2).grassmannianMap ι n e r hr :=
  rfl

variable {A} in
/-- Naturality of `locallyNoetherianGrassmannianNatTransApp`: for a morphism `φ` of locally
Noetherian test schemes, the point of the pullback of `Z` is `φ` followed by the point of `Z`
(`IsHilbertFamily.grassmannianMap_comp`). -/
theorem locallyNoetherianGrassmannianNatTransApp_naturality (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    {T T' : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ} (φ : T ⟶ T')
    (Z : (locallyNoetherianHilbertFunctor ι A Φ).obj T) :
    locallyNoetherianGrassmannianNatTransApp ι n e A Φ r hr T'
        ((locallyNoetherianHilbertFunctor ι A Φ).map φ Z) =
      (locallyNoetherianGrassmannianFunctor A ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).map φ
        (locallyNoetherianGrassmannianNatTransApp ι n e A Φ r hr T Z) := by
  have : IsLocallyNoetherian T.unop.obj.left := T.unop.property
  have : IsLocallyNoetherian T'.unop.obj.left := T'.unop.property
  exact ((show IsHilbertFamily ι Φ T.unop.obj.hom Z.1 from Z.2).grassmannianMap_comp ι n e
    T'.unop.obj.hom φ.unop.hom.left (Over.w φ.unop.hom) r hr).symm

/-- **The natural transformation from the Hilbert functor to the Grassmannian on locally
Noetherian test schemes** (the morphism `α` of Nitsure, arXiv:math/0504590v1, §5, p. 26): for
`r ≥ hilbertRegularityBound n Φ`, the points `IsHilbertFamily.grassmannianMap` form a natural
transformation from `Hilb^Φ` to the functor of points of the Grassmannian of rank-`⌊Φ(r)⌋₊`
quotients of `𝒪^N`, `N = (n + r).choose r`, on locally Noetherian schemes over `Spec A`.
Injectivity of its components is `locallyNoetherianGrassmannianNatTrans_app_injective`
(`HilbertScheme/Representability`). -/
def locallyNoetherianGrassmannianNatTrans (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r) :
    locallyNoetherianHilbertFunctor ι A Φ ⟶
      locallyNoetherianGrassmannianFunctor A ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r) where
  app T := TypeCat.ofHom (locallyNoetherianGrassmannianNatTransApp ι n e A Φ r hr T)
  naturality _ _ φ := ConcreteCategory.hom_ext _ _ fun Z =>
    locallyNoetherianGrassmannianNatTransApp_naturality ι n e Φ r hr φ Z

theorem locallyNoetherianGrassmannianNatTrans_app_apply (Φ : ℚ[X]) (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (T : (Scheme.LocallyNoetherianOver (Spec (CommRingCat.of A)))ᵒᵖ)
    (Z : (locallyNoetherianHilbertFunctor ι A Φ).obj T) :
    (locallyNoetherianGrassmannianNatTrans ι n e A Φ r hr).app T Z =
      locallyNoetherianGrassmannianNatTransApp ι n e A Φ r hr T Z :=
  rfl

end ProjectiveSpace

end AlgebraicGeometry
