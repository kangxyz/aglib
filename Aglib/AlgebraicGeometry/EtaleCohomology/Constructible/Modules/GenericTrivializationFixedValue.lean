/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisRefinement

/-! # Galois refinement with a fixed original module value

This indexed packet retains a supplied original module value literally, not
just as an unindexed chosen value isomorphic to it. It also retains the actual
finite-etale refinement arrow and its original module constant isomorphism.
The refinement arrow need not be surjective onto a disconnected original
cover; the refined structural morphism is surjective onto the base.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}} [ConnectedSpace X]

/-- A Galois refinement retaining the prescribed original module value. -/
structure GaloisRefinedConstantTrivialization (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) (M : ModuleCat.{u + 1} R) where
  /-- The actual refined finite etale cover. -/
  cover : Scheme.FiniteEtale X
  /-- The actual arrow over the original base to the given cover. -/
  refinement : cover ⟶ Y
  /-- The refined cover is Galois in the native category. -/
  galois_cover : PreGaloisCategory.IsGalois cover
  /-- The actual refined scheme is connected. -/
  connected_cover : ConnectedSpace cover.obj.left
  /-- The actual refined structural map is surjective. -/
  surjective_cover : Surjective cover.obj.hom
  /-- The same prescribed value is finite over the original coefficient ring. -/
  finite_value : Module.Finite R M
  /-- The native inverse image is constant with that literal prescribed value. -/
  iso : (moduleInverseImage R cover.obj.hom).obj F ≅
    (constantSheaf cover.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M

/-- An actual nonempty finite etale trivialization admits a connected Galois
refinement with its supplied module value kept literally as the same index. -/
def galoisRefinedConstantTrivialization (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) [Nonempty Y.obj.left]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    GaloisRefinedConstantTrivialization F Y M := by
  apply Classical.choice
  obtain ⟨Z, f, hZ, hconn, hsurj⟩ := Scheme.FiniteEtale.exists_galois_refinement Y
  refine ⟨{ cover := Z
            refinement := f
            galois_cover := hZ
            connected_cover := hconn
            surjective_cover := hsurj
            finite_value := inferInstance
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun q => (moduleInverseImage R q).obj F) f.hom.w.symm) ≪≫
    (moduleInverseImageComp R Y.obj.hom f.hom.left).app F ≪≫
      (moduleInverseImage R f.hom.left).mapIso e ≪≫
      (moduleInverseImageConstantIso R f.hom.left).app M

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
