/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Picard.HomSection` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`84453d077683ef7d82fad54472d0573abf95cc55b7f7dfaf74bf011ab2e49177`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.InternalHom (RawHom sectionHomEquiv sheaf)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (LineBundle dualEvaluationIso dualEvaluationIso_hom evaluationPresheaf evaluationSheaf)
open _root_.AlgebraicGeometry.Scheme.Modules
  (tensorSheafLeftUnit tensorSheafMap)
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Canonical sections of the actual internal Hom sheaf

An actual structure-linear sheaf morphism determines a canonical morphism
from the structure sheaf to the actual internal Hom. On every smaller open,
its value is the original morphism multiplied by the restricted scalar.
Evaluation recovers the original morphism, and nonzero morphisms give
nonzero sections. No additional mathematical theorem family is retained.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Incoming HomSheaf SHA256:
2e744b782488e8ad27bf61f4f4450f8ef6156b5ca884e075129e7d83a5920a27.
Incoming Dual SHA256:
f982da32fc32b8e5e60b4086ee86f98635f840b81e999e37f747101d845a4d77.
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
variable (X : Scheme.{u}) {M N : SheafOfModules.{u} X.ringCatSheaf}

/-- The section on an open corresponding to restriction of an actual morphism. -/
def sectionOfHom (φ : M ⟶ N) (U : X.Opens) : (sheaf X M N).val.obj (op U) :=
  (sectionHomEquiv X M N U).symm ((SheafOfModules.overFunctor X.ringCatSheaf U).map φ)

-- Keep section evaluation; simpNF only unfolds the implicit restricted-module component types.
@[nolint simpNF, simp] theorem sectionOfHom_apply (φ : M ⟶ N) (U : X.Opens)
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left)) :
    (sectionOfHom X φ U).val.app V m = φ.val.app (op V.unop.left) m := rfl

@[simp] theorem sectionOfHom_restrict (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) :
    (sheaf X M N).val.map i.op (sectionOfHom X φ U) = sectionOfHom X φ V := by
  apply Subtype.ext
  rfl

/-- The canonical transpose of a genuine morphism into the internal Hom sheaf. -/
def transpose (φ : M ⟶ N) : SheafOfModules.unit X.ringCatSheaf ⟶ sheaf X M N where
  val.app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (sectionOfHom X φ U.unop))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (X.presheaf.map i r) • sectionOfHom X φ V.unop =
      (sheaf X M N).val.map i (r • sectionOfHom X φ U.unop)
    rw [PresheafOfModules.map_smul]
    congr 1

@[simp] theorem transpose_app (φ : M ⟶ N) (U : X.Opens) (r : Γ(X, U)) :
    (transpose X φ).val.app (op U) r = r • sectionOfHom X φ U := rfl

/-- The literal formula on any smaller open, using the actual scalar restriction. -/
theorem transpose_apply (φ : M ⟶ N) (U : X.Opens) (r : Γ(X, U))
    (V : (Over U)ᵒᵖ) (m : M.val.obj (op V.unop.left)) :
    ((transpose X φ).val.app (op U) r).val.app V m =
      X.presheaf.map V.unop.hom.op r • φ.val.app (op V.unop.left) m := rfl

theorem transpose_one (φ : M ⟶ N) (U : X.Opens) :
    (transpose X φ).val.app (op U) (1 : Γ(X, U)) = sectionOfHom X φ U := by
  rw [transpose_app, one_smul]

theorem transpose_one_evaluate (φ : M ⟶ N) (U : X.Opens)
    (m : M.val.obj (op U)) :
    ((transpose X φ).val.app (op U) (1 : Γ(X, U))).val.app
      (op (Over.mk (𝟙 U))) m = φ.val.app (op U) m := by
  rw [transpose_one, sectionOfHom_apply]
  rfl

/-- The original morphism is recoverable, so transposition is injective. -/
theorem transpose_injective : Function.Injective (transpose X (M := M) (N := N)) := by
  intro φ ψ h
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have he := congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ sheaf X M N =>
    (f.val.app U (1 : Γ(X, U.unop))).val.app (op (Over.mk (𝟙 U.unop))) m) h
  change ((transpose X φ).val.app (op U.unop) (1 : Γ(X, U.unop))).val.app
      (op (Over.mk (𝟙 U.unop))) m =
    ((transpose X ψ).val.app (op U.unop) (1 : Γ(X, U.unop))).val.app
      (op (Over.mk (𝟙 U.unop))) m at he
  rw [transpose_one_evaluate, transpose_one_evaluate] at he
  exact he

@[simp] theorem transpose_zero : transpose X (0 : M ⟶ N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  change (_ : RawHom X M N U.unop) = _
  ext V m
  change X.presheaf.map V.unop.hom.op r • (0 : N.val.obj (op V.unop.left)) = 0
  exact smul_zero _

@[simp] theorem transpose_eq_zero_iff (φ : M ⟶ N) : transpose X φ = 0 ↔ φ = 0 := by
  rw [← transpose_zero X]
  exact (transpose_injective X).eq_iff

/-- In particular an actual nonzero ideal inclusion gives a nonzero dual section. -/
theorem transpose_ne_zero {φ : M ⟶ N} (hφ : φ ≠ 0) : transpose X φ ≠ 0 := by
  exact fun h => hφ ((transpose_eq_zero_iff X φ).mp h)

/-- Evaluation of the transpose agrees with scalar multiplication followed by the map,
first on the genuine sectionwise tensor presheaf. -/
theorem transpose_evaluationPresheaf (φ : M ⟶ N) :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (transpose X φ).val (𝟙 M.val) ≫ evaluationPresheaf X M N =
      (MonoidalCategory.leftUnitor
        (C := PresheafOfModulesOfCommRing.{u} X.presheaf) M.val).hom ≫ φ.val := by
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r m
  change X.presheaf.map (𝟙 U.unop).op r • φ.val.app U m = φ.val.app U (r • m)
  rw [show X.presheaf.map (𝟙 U.unop).op r = r by simp]
  exact ((φ.val.app U).hom.map_smul r m).symm

/-- The actual sheaf evaluation square: tensoring the canonical section with M,
then evaluating, is precisely the original map after the tensor unit isomorphism. -/
@[reassoc] theorem transpose_evaluation (φ : M ⟶ N) :
    tensorSheafMap X (transpose X φ) (𝟙 M) ≫ evaluationSheaf X M N =
      (tensorSheafLeftUnit X M).hom ≫ φ := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let l := (MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing.{u} X.presheaf) M.val).hom
  have hl : (tensorSheafLeftUnit X M).hom = (adj.homEquiv _ _).symm l :=
    (adj.homEquiv_counit _ _ l).symm
  have hev : evaluationSheaf X M N = (adj.homEquiv _ _).symm
      (evaluationPresheaf X M N) := by
    have he : adj.homEquiv
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
          (sheaf X M N).val M.val) N =
        PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [he]
    rfl
  rw [hl, hev]
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (transpose X φ).val (𝟙 M.val)) ≫
      (adj.homEquiv _ _).symm (evaluationPresheaf X M N) =
    (adj.homEquiv _ _).symm l ≫ φ
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  erw [Equiv.apply_symm_apply]
  exact transpose_evaluationPresheaf X φ

/-- The evaluation square in the dual-line-bundle form used by ideal inclusions. -/
@[reassoc] theorem transpose_dualEvaluation (L : LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorSheafMap X (transpose X φ) (𝟙 L.val) ≫ (dualEvaluationIso X L).hom =
      (tensorSheafLeftUnit X L.val).hom ≫ φ := by
  rw [dualEvaluationIso_hom]
  exact transpose_evaluation X φ

end AlgebraicGeometry.Scheme.Modules.InternalHom
