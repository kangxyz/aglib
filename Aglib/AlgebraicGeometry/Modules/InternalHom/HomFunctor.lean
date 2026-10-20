/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomSection
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.HomFunctor` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`44db15b42757d618aa2483fad2d6d7592f0ad8d1dbadcea4b8828ffc3185e2b0`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.InternalHom
  (RawHom sectionHomEquiv sheaf unitSourceIso)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (dualSheaf evaluationPresheaf evaluationSheaf)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual internal-Hom maps and evaluation naturality

The bifunctor map is literal precomposition and postcomposition on every
restricted linear sheaf morphism. Composition, induced isomorphisms,
transpose naturality and the actual sheaf evaluation square are proved.
The dual of a section is the actual Hom map followed by Hom(O,O) ≅ O.
No mathematical theorem family is retained; no class-only substitute is used.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u
variable (X : Scheme.{u}) {M M' N N' : SheafOfModules.{u} X.ringCatSheaf}
def map (a : M' ⟶ M) (b : N ⟶ N') : sheaf X M N ⟶ sheaf X M' N' where
  val.app U := ModuleCat.ofHom {
    toFun s := (sectionHomEquiv X M' N' U.unop).symm
      ((SheafOfModules.overFunctor X.ringCatSheaf U.unop).map a ≫
        sectionHomEquiv X M N U.unop s ≫
        (SheafOfModules.overFunctor X.ringCatSheaf U.unop).map b)
    map_add' s t := by
      apply Subtype.ext
      change (_ : RawHom X M' N' U.unop) = _
      ext V m
      exact (b.val.app (op V.unop.left)).hom.map_add _ _
    map_smul' r s := by
      apply Subtype.ext
      change (_ : RawHom X M' N' U.unop) = _
      ext V m
      exact (b.val.app (op V.unop.left)).hom.map_smul _ _ }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom X M' N' V.unop) = _
    ext W m
    rfl
@[simp] theorem map_apply (a : M' ⟶ M) (b : N ⟶ N') (U : X.Opens)
    (s : (sheaf X M N).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (m : M'.val.obj (op V.unop.left)) :
    ((map X a b).val.app (op U) s).val.app V m =
      b.val.app (op V.unop.left) (s.val.app V (a.val.app (op V.unop.left) m)) := rfl
@[simp] theorem map_id : map X (𝟙 M) (𝟙 N) = 𝟙 (sheaf X M N) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change (_ : RawHom X M N U.unop) = _
  ext V m
  rfl
variable {M'' N'' : SheafOfModules.{u} X.ringCatSheaf}
@[reassoc] theorem map_comp (a : M' ⟶ M) (b : N ⟶ N')
    (c : M'' ⟶ M') (d : N' ⟶ N'') :
    map X a b ≫ map X c d = map X (c ≫ a) (b ≫ d) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change (_ : RawHom X M'' N'' U.unop) = _
  ext V m
  rfl
def iso (e : M ≅ M') (f : N ≅ N') : sheaf X M N ≅ sheaf X M' N' where
  hom := map X e.inv f.hom
  inv := map X e.hom f.inv
  hom_inv_id := by rw [map_comp, e.hom_inv_id, f.hom_inv_id, map_id]
  inv_hom_id := by rw [map_comp, e.inv_hom_id, f.inv_hom_id, map_id]
@[reassoc] theorem transpose_map (a : M' ⟶ M) (b : N ⟶ N') (φ : M ⟶ N) :
    transpose X φ ≫ map X a b = transpose X (a ≫ φ ≫ b) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change (_ : RawHom X M' N' U.unop) = _
  ext V m
  exact (b.val.app (op V.unop.left)).hom.map_smul _ _
theorem evaluation_map_presheaf (a : M' ⟶ M) (b : N ⟶ N') :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (map X a b).val (𝟙 M'.val) ≫ evaluationPresheaf X M' N' =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 (sheaf X M N).val) a.val ≫ evaluationPresheaf X M N ≫ b.val := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s m
  rfl

@[reassoc] theorem evaluation_map (a : M' ⟶ M) (b : N ⟶ N') :
    tensorSheafMap X (map X a b) (𝟙 M') ≫ evaluationSheaf X M' N' =
      tensorSheafMap X (𝟙 (sheaf X M N)) a ≫ evaluationSheaf X M N ≫ b := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have hev (P Q : SheafOfModules.{u} X.ringCatSheaf) :
      evaluationSheaf X P Q = (adj.homEquiv _ _).symm (evaluationPresheaf X P Q) := by
    have he : adj.homEquiv
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
          (sheaf X P Q).val P.val) Q =
        PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [he]
    rfl
  rw [hev, hev]
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (map X a b).val (𝟙 M'.val)) ≫
      (adj.homEquiv _ _).symm (evaluationPresheaf X M' N') =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (𝟙 (sheaf X M N).val) a.val) ≫
      (adj.homEquiv _ _).symm (evaluationPresheaf X M N) ≫ b
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact evaluation_map_presheaf X a b

/-- The actual dual of a section, evaluated using Hom(O,O) ≅ O. -/
def dualSection (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    dualSheaf X M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  map X σ (𝟙 _) ≫ (unitSourceIso X (SheafOfModules.unit X.ringCatSheaf)).hom

@[simp] theorem dualSection_apply
    (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M) (U : X.Opens)
    (s : (dualSheaf X M).val.obj (op U)) :
    (dualSection X σ).val.app (op U) s =
      s.val.app (op (Over.mk (𝟙 U))) (σ.val.app (op U) (1 : Γ(X,U))) := rfl

end AlgebraicGeometry.Scheme.Modules.InternalHom
