/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisRefinement

/-! # Original module trivializations through actual Galois cover refinements

An already produced nonempty finite etale trivializing cover over a connected
base admits a genuine connected Galois refinement. The original module value,
its finite generation, and its native module-sheaf constant isomorphism are
retained. This does not assert that an arbitrary local system on a connected
scheme has a finite trivializing cover, or supply module-sheaf descent.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}} [ConnectedSpace X]

/-- An actual connected Galois finite etale cover with an original
finite-type constant-module trivialization. -/
structure GaloisCoverConstantTrivialization (F : ModuleSheaf R X) where
  /-- The actual finite etale cover over the original base. -/
  cover : Scheme.FiniteEtale X
  /-- This actual cover is Galois in the native finite-etale Galois category. -/
  galois_cover : PreGaloisCategory.IsGalois cover
  /-- Its underlying scheme is connected. -/
  connected_cover : ConnectedSpace cover.obj.left
  /-- Its actual structural morphism is surjective. -/
  surjective_cover : Surjective cover.obj.hom
  /-- The original module value, in the original universe. -/
  value : ModuleCat.{u + 1} R
  /-- Finite generation over the original coefficient ring. -/
  finite_value : Module.Finite R value
  /-- The original module inverse image is genuinely constant. -/
  iso : (moduleInverseImage R cover.obj.hom).obj F ≅
    (constantSheaf cover.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj value

/-- Refine an actual finite etale module trivialization to a connected Galois
one, retaining the original module and its original scalar structure. -/
def galoisCoverConstantTrivialization (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) [Nonempty Y.obj.left]
    (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    GaloisCoverConstantTrivialization F := by
  apply Classical.choice
  obtain ⟨Z, f, hZ, hconn, hsurj⟩ := Scheme.FiniteEtale.exists_galois_refinement Y
  refine ⟨{ cover := Z
            galois_cover := hZ
            connected_cover := hconn
            surjective_cover := hsurj
            value := M
            finite_value := inferInstance
            iso := ?_ }⟩
  exact eqToIso (congrArg (fun q => (moduleInverseImage R q).obj F) f.hom.w.symm) ≪≫
    (moduleInverseImageComp R Y.obj.hom f.hom.left).app F ≪≫
      (moduleInverseImage R f.hom.left).mapIso e ≪≫
      (moduleInverseImageConstantIso R f.hom.left).app M

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
