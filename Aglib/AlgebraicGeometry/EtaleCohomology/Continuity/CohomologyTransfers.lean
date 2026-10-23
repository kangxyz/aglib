/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition

/-! # Original cohomology transport with compatible coefficients

The Ext universe is independent of the scheme and coefficient universes.
All maps below are the original cohomological pullback followed by the original
coefficient map; no continuity or invertibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u e
attribute [local instance] hasSheafifyLarge
variable {X Y Z : Scheme.{u}}
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]

/-- Original pullback followed by the given inverse-image coefficient morphism. -/
def cohomologyTransfer (f : Y ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{e} F n) ⟶ AddCommGrpCat.of (Sheaf.H.{e} G n) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map φ n).comp (cohomologyPullback f F n))

lemma cohomologyTransfer_transport (f f' : Y ⟶ X) (h : f' = f)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    cohomologyTransfer f'
        (eqToHom (congrArg (fun k : Y ⟶ X => (inverseImage k).obj F) h) ≫ φ) n =
      cohomologyTransfer f φ n := by
  subst f'
  simp only [eqToHom_refl, Category.id_comp]

lemma cohomologyTransfer_id (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) :
    cohomologyTransfer (𝟙 X) ((inverseImageId X).hom.app F) n = 𝟙 _ := by
  ext x
  exact cohomologyPullback_id X F n x

lemma cohomologyTransfer_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : AbelianSheaf.{u, u + 1} X} {G : AbelianSheaf.{u, u + 1} Y}
    {H : AbelianSheaf.{u, u + 1} Z}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage g).obj G ⟶ H) (n : ℕ) :
    cohomologyTransfer f φ n ≫ cohomologyTransfer g ψ n =
      cohomologyTransfer (g ≫ f)
        ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) n := by
  ext x
  change Sheaf.H.map ψ n (cohomologyPullback g G n
    (Sheaf.H.map φ n (cohomologyPullback f F n x))) =
      Sheaf.H.map ((inverseImageComp f g).hom.app F ≫ (inverseImage g).map φ ≫ ψ) n
        (cohomologyPullback (g ≫ f) F n x)
  simp only [Sheaf.H.map_comp_apply]
  rw [cohomologyPullback_coefficientMap, cohomologyPullback_comp]

lemma cohomologyTransfer_naturality (f : Y ⟶ X)
    {F F' : AbelianSheaf.{u, u + 1} X} {G G' : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage f).obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : (inverseImage f).map a ≫ ψ = φ ≫ b) (n : ℕ) :
    cohomologyTransfer f φ n ≫ AddCommGrpCat.ofHom (Sheaf.H.map b n) =
      AddCommGrpCat.ofHom (Sheaf.H.map a n) ≫ cohomologyTransfer f ψ n := by
  ext x
  change Sheaf.H.map b n (Sheaf.H.map φ n (cohomologyPullback f F n x)) =
    Sheaf.H.map ψ n (cohomologyPullback f F' n (Sheaf.H.map a n x))
  rw [cohomologyPullback_coefficientMap, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply, h]

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
