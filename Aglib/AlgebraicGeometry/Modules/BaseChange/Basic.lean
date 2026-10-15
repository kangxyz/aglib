/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Canonical module-sheaf base change and field fibres

The base-change map is the actual mate of the pullback/pushforward counit.
Its affine invertibility is retained as the general quasi-coherent base-change
family of Stacks Lemma 30.5.1 (02KG), inspected 2026-10-09. The assertion
allows every base-change morphism, without a flatness hypothesis.
Application: K2-018#prop:k2018-arithmetic-characters, mathematical source
e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose.tex lines 341–445;
engineering 7f86e4a1763cc4ec35e9b0a8acd659750355a0de with frozen pins.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y T : Scheme.{u}}
/-- The canonical map from pullback of the direct image of `M` along `g` to direct image of the
pulled-back `M` on the fibre product. -/
def moduleBaseChangeMap (f : X ⟶ Y) (g : T ⟶ Y) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward (Limits.pullback.snd f g)).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.snd f g)).homEquiv _ _
    ((Scheme.Modules.pullbackComp (Limits.pullback.snd f g) g).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (Limits.pullback.condition (f := f) (g := g)).symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp (Limits.pullback.fst f g) f).inv.app _ ≫
      (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M))

/-- The canonical base-change map for the direct image of the structure module along `f`. -/
def structureModuleBaseChangeMap (f : X ⟶ Y) (g : T ⟶ Y) :
    (Scheme.Modules.pullback g).obj (pushforwardStructureSheaf f) ⟶
      pushforwardStructureSheaf (Limits.pullback.snd f g) :=
  moduleBaseChangeMap f g (SheafOfModules.unit X.ringCatSheaf) ≫
    (Scheme.Modules.pushforward (Limits.pullback.snd f g)).map
      (SheafOfModules.pullbackObjUnitToUnit (Limits.pullback.fst f g).toRingCatSheafHom)
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules
universe u
open Opposite
variable (K : Type u) [Field K]
/-- Global sections of a module sheaf on `Spec K`. -/
abbrev fieldSections (M : (Spec (CommRingCat.of K)).Modules) :=
  M.val.obj (op ⊤)
noncomputable instance fieldSectionsModule (M : (Spec (CommRingCat.of K)).Modules) :
    Module K (fieldSections K M) :=
  Module.compHom _ (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/-- The `K`-linear map on global sections induced by a module-sheaf morphism on `Spec K`. -/
def fieldSectionsMap {M N : (Spec (CommRingCat.of K)).Modules} (a : M ⟶ N) :
    fieldSections K M →ₗ[K] fieldSections K N where
  __ := (a.val.app (op ⊤)).hom.toAddMonoidHom
  map_smul' _k x := (a.val.app (op ⊤)).hom.map_smul _ x

/-- The `K`-linear equivalence on global sections induced by a module-sheaf isomorphism. -/
def fieldSectionsIso {M N : (Spec (CommRingCat.of K)).Modules} (e : M ≅ N) :
    fieldSections K M ≃ₗ[K] fieldSections K N :=
  LinearEquiv.ofBijective (fieldSectionsMap K e.hom)
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf _).mapIso e).app (op ⊤)).hom)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- Global sections over `Spec K` of the pullback of `M` along the field-valued point `p`. -/
def moduleFibre (M : Y.Modules) (p : Spec (CommRingCat.of K) ⟶ Y) :=
  fieldSections K ((Scheme.Modules.pullback p).obj M)

noncomputable instance moduleFibreModule (M : Y.Modules)
    (p : Spec (CommRingCat.of K) ⟶ Y) : Module K (moduleFibre K M p) :=
  fieldSectionsModule K _

/-- The assertion that the canonical module base-change map is invertible for affine `f` and
quasicoherent `M`, after every base change `g`. -/
def AffineModuleBaseChange : Prop :=
  ∀ (X Y T : Scheme.{u}) (f : X ⟶ Y) (g : T ⟶ Y)
    (M : X.Modules), IsAffineHom f → M.IsQuasicoherent →
    IsIso (moduleBaseChangeMap f g M)

set_option maxHeartbeats 800000 in
-- Transporting free generators through the over-functor uses about 504000
-- heartbeats; this individual budget gives the sheaf coercions headroom.
theorem unit_isLocallyFree (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsLocallyFree := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u+1} ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  let q :=
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u+1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  let q' : (SheafOfModules.unit X.ringCatSheaf).LocalGeneratorsData.{u} := {
    I := q.I
    X := q.X
    coversTop := q.coversTop
    generators i := (q.generators i).ofEpi
      ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).map e.hom) }
  haveI : q'.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [q']
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    letI := hq.isIso i
    infer_instance
  exact q'.isLocallyFree

/-- The pullback of the structure module along `q`, identified with the structure module on `T`. -/
def pullbackStructureUnitIso {T : Scheme.{u}} (q : T ⟶ X) :
    (Scheme.Modules.pullback q).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      (show T.Modules from SheafOfModules.unit T.ringCatSheaf) := by
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit q.toRingCatSheafHom)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

theorem structureModuleBaseChangeMap_isIso
    (hbase : AffineModuleBaseChange.{u}) (g : Scheme.{u}) (p : g ⟶ Y)
    [IsAffineHom f] : IsIso (structureModuleBaseChangeMap f p) := by
  letI := unit_isLocallyFree X
  haveI : IsIso (moduleBaseChangeMap f p (SheafOfModules.unit X.ringCatSheaf)) :=
    hbase X Y g f p _ inferInstance inferInstance
  haveI : IsIso (show (Scheme.Modules.pullback (Limits.pullback.fst f p)).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶
      (show (Limits.pullback f p).Modules from
        SheafOfModules.unit (Limits.pullback f p).ringCatSheaf) from
      SheafOfModules.pullbackObjUnitToUnit (Limits.pullback.fst f p).toRingCatSheafHom) :=
    (pullbackStructureUnitIso (Limits.pullback.fst f p)).isIso_hom
  unfold structureModuleBaseChangeMap
  infer_instance
end AlgebraicGeometry.Scheme.Modules
