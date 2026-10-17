/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# The pseudofunctor of module sheaves under pullback

`Scheme.Modules.pullbackPseudofunctor` sends a scheme `X` to the category `X.Modules` of
sheaves of modules and a morphism `f` to Mathlib's pullback functor
`Scheme.Modules.pullback f`, with Mathlib's `pullbackId` and `pullbackComp` as coherence
isomorphisms. It is the left-adjoint part `Scheme.Modules.pseudofunctor.comp Adj.forget₁` of
Mathlib's pseudofunctor to the bicategory of adjunctions
(`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`, `Scheme.Modules.pseudofunctor`).

Quasi-coherence (Mathlib's `SheafOfModules.IsQuasicoherent`) and local rank one
(`Scheme.Modules.Invertible.IsLocallyRankOne`) are object properties of this pseudofunctor that
are closed under pullback and under isomorphism. Their full subpseudofunctors are
`Scheme.Modules.quasicoherentPseudofunctor` and `Scheme.Modules.lineBundlePseudofunctor`;
morphisms are all module-sheaf morphisms.

Provenance: the line-bundle part ports `modules`, `rankOne` and `lineBundles` of R5Lab
`R5Lab/AlgebraicGeometry/Curves/Picard/EtaleDescent.lean` (lines 63–79), whose statements are
retained.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite Bicategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The pseudofunctor `X ↦ X.Modules` on `Schemeᵒᵖ` whose functors are the pullbacks
`Scheme.Modules.pullback f`: the left-adjoint part of `Scheme.Modules.pseudofunctor`. -/
def pullbackPseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  pseudofunctor.comp Adj.forget₁

@[simp]
lemma pullbackPseudofunctor_obj (X : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    pullbackPseudofunctor.obj X = Cat.of X.as.unop.Modules :=
  rfl

@[simp]
lemma pullbackPseudofunctor_map_toFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackPseudofunctor.map f.op.toLoc).toFunctor = pullback f :=
  rfl

-- `simp` must see the objects of `pullbackPseudofunctor.obj _` (a `Cat.of`) as `X.Modules`,
-- which needs relaxed instance transparency, and Mathlib's `pseudofunctor_mapComp_*` simp lemmas
-- are stated under `backward.defeqAttrib.useBackward`.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition isomorphisms of `pullbackPseudofunctor` are Mathlib's `pullbackComp`, up to
`pullbackCongr`. -/
lemma pullbackPseudofunctor_mapComp'_hom_app {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (h : b ≫ a = c) (M : X.Modules) :
    (pullbackPseudofunctor.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M =
      (pullbackCongr h.symm).hom.app M ≫ (pullbackComp b a).inv.app M := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackPseudofunctor, pullbackCongr]

-- As for `pullbackPseudofunctor_mapComp'_hom_app`.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma pullbackPseudofunctor_mapComp'_inv_app {X Y Z : Scheme.{u}} (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (h : b ≫ a = c) (M : X.Modules) :
    (pullbackPseudofunctor.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M =
      (pullbackComp b a).hom.app M ≫ (pullbackCongr h).hom.app M := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackPseudofunctor, pullbackCongr]

namespace pullbackPseudofunctor

/-- Quasi-coherence of module sheaves, as an object property of `pullbackPseudofunctor`. -/
def isQuasicoherent : pullbackPseudofunctor.{u}.ObjectProperty where
  prop X := SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf

instance : isQuasicoherent.{u}.IsClosedUnderMapObj where
  map_obj {X Y} {M} hM f := by
    have : SheafOfModules.IsQuasicoherent M := hM
    exact quasicoherent_pullback f.as.unop M

instance : isQuasicoherent.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := inferInstanceAs
    (SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).IsClosedUnderIsomorphisms

/-- Local rank one (`Invertible.IsLocallyRankOne`), as an object property of
`pullbackPseudofunctor`. -/
def isLocallyRankOne : pullbackPseudofunctor.{u}.ObjectProperty where
  prop X M := Invertible.IsLocallyRankOne X.as.unop M

instance : isLocallyRankOne.{u}.IsClosedUnderMapObj where
  map_obj hM f := Invertible.pullback_locallyRankOne f.as.unop _ hM

instance : isLocallyRankOne.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := ⟨fun e hM ↦ Invertible.isLocallyRankOne_of_iso X.as.unop e hM⟩

end pullbackPseudofunctor

/-- Quasi-coherent sheaves of modules, with all module morphisms and the pullback functors. -/
abbrev quasicoherentPseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  pullbackPseudofunctor.isQuasicoherent.fullsubcategory

/-- Line bundles (locally rank-one sheaves of modules), with all module morphisms and the
pullback functors. This is R5Lab's `Picard.EtaleDescent.lineBundles`. -/
abbrev lineBundlePseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  pullbackPseudofunctor.isLocallyRankOne.fullsubcategory

end AlgebraicGeometry.Scheme.Modules
