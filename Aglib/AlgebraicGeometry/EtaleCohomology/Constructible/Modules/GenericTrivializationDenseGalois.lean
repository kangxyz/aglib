/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationDense
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GenericTrivializationFixedValue

/-! # Actual connected Galois module trivializations on a dense affine open

The actual finite etale trivialization produced over a dense affine open is
refined through the native finite-etale Galois category. Its connected Galois
cover surjects onto that same open base. The final isomorphism still uses the
original composite scheme map, original module coefficient and original
finitely generated value. No sheaf-monodromy equivalence or descent exactness
is assumed or asserted.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- A dense affine open with an actual connected Galois finite etale
trivialization of the original finite-type module coefficient. -/
structure DenseGaloisConstantTrivialization {X : Scheme.{u}} (F : ModuleSheaf R X) where
  /-- The actual open base. -/
  base : Scheme.{u}
  /-- Its actual inclusion into the original scheme. -/
  inclusion : base ⟶ X
  /-- The open base is affine. -/
  affine_base : IsAffine base
  /-- Its actual inclusion is an open immersion. -/
  open_inclusion : IsOpenImmersion inclusion
  /-- Its actual inclusion has dense image. -/
  dense_inclusion : IsDominant inclusion
  /-- The open base is connected and nonempty. -/
  connected_base : ConnectedSpace base
  /-- The actual finite etale cover of that same base. -/
  cover : Scheme.FiniteEtale base
  /-- The cover is Galois in the original native finite-etale category. -/
  galois_cover : letI : ConnectedSpace base := connected_base
    PreGaloisCategory.IsGalois cover
  /-- The actual covering scheme is connected. -/
  connected_cover : ConnectedSpace cover.obj.left
  /-- The original structural map is surjective. -/
  surjective_cover : Surjective cover.obj.hom
  /-- The original value, in its original module universe. -/
  value : ModuleCat.{u + 1} R
  /-- Finite generation over the original coefficient ring. -/
  finite_value : Module.Finite R value
  /-- Trivialization using the literal composite map to the original scheme. -/
  iso : (moduleInverseImage R (cover.obj.hom ≫ inclusion)).obj F ≅
    (constantSheaf cover.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj value

/-- Every finite-type locally constant native module sheaf on an integral
scheme becomes constant on an actual connected Galois finite etale cover of
a dense affine open, retaining its original finite module value. -/
def denseGaloisConstantTrivialization {X : Scheme.{u}} [IsIntegral X]
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F) :
    DenseGaloisConstantTrivialization F := by
  let t := denseFiniteEtaleTrivialization F hF
  have : IsOpenImmersion t.inclusion := t.open_inclusion
  have : Nonempty t.base := t.nonempty_base
  have : IsIntegral t.base := isIntegral_of_isOpenImmersion t.inclusion
  have : IsFinite t.projection := t.finite_projection
  have : Etale t.projection := t.etale_projection
  have : Surjective t.projection := t.surjective_projection
  have : Module.Finite R t.value := t.finite_value
  let x : t.base := Classical.choice t.nonempty_base
  let y : t.cover := Classical.choose (t.projection.surjective x)
  have : Nonempty t.cover := ⟨y⟩
  let Y : Scheme.FiniteEtale t.base := Scheme.FiniteEtale.mk t.projection
  have : Nonempty Y.obj.left := (show Nonempty t.cover from ⟨y⟩)
  let e := ((moduleInverseImageComp R t.inclusion t.projection).app F).symm ≪≫ t.iso
  let g := galoisRefinedConstantTrivialization ((moduleInverseImage R t.inclusion).obj F)
    Y t.value e
  exact { base := t.base
          inclusion := t.inclusion
          affine_base := t.affine_base
          open_inclusion := t.open_inclusion
          dense_inclusion := t.dense_inclusion
          connected_base := inferInstance
          cover := g.cover
          galois_cover := g.galois_cover
          connected_cover := g.connected_cover
          surjective_cover := g.surjective_cover
          value := t.value
          finite_value := g.finite_value
          iso := (moduleInverseImageComp R t.inclusion g.cover.obj.hom).app F ≪≫ g.iso }

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
