/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Affine.HomPrecomposition
public import Aglib.AlgebraicGeometry.Morphisms.Flat.StructureSheafIso
public import Aglib.AlgebraicGeometry.Sites.AffineSheafification
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic

/-! # The original finite-constant unit from an isomorphism on structure sheaves

For a qcqs map to an affine scheme with its actual structure-sheaf map an
isomorphism, affine étale tests preserve that isomorphism by flat base change.
The original Gamma--Spec adjunction then descends maps to the same finite
representative. Its literal represented unit is identified with the original
adjunction unit. No connected-fibre, universal-openness or proper-base-change
hypothesis is inserted. Only the affine-target statement is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable {X Y : Scheme.{u}} [IsAffine Y] (q : X ⟶ Y)
  [QuasiCompact q] [QuasiSeparated q] [IsIso q.c]

/-- Literal pullback of maps into an affine represented target is bijective
on each actual affine étale test. -/
theorem affineEtaleTest_pullbackHom_bijective_of_structureIso
    (U : Y.Etale) [IsAffine U.left] (Z : Over Y) [IsAffine Z.left] :
    Function.Bijective (fun b : (Scheme.Etale.forget Y).obj U ⟶ Z =>
      (Over.pullback q).map b) := by
  let V := (Scheme.Etale.forget Y).obj U
  let a := (Over.mapPullbackAdj q).counit.app V
  have : IsIso (pullback.snd q U.hom).c :=
    Scheme.isIso_c_pullback_snd_of_flat_of_isIso_c q U.hom
  have : IsIso (pullback.snd q U.hom).appTop := by
    change IsIso ((pullback.snd q U.hom).c.app (op ⊤))
    infer_instance
  have : IsIso (pullbackSymmetry U.hom q).hom.appTop := by
    change IsIso (Scheme.Γ.map (pullbackSymmetry U.hom q).hom.op)
    infer_instance
  have : IsIso a.left.appTop := by
    change IsIso (pullback.fst U.hom q).appTop
    rw [← pullbackSymmetry_hom_comp_snd U.hom q, Scheme.Hom.comp_appTop]
    infer_instance
  let e := (Over.mapPullbackAdj q).homEquiv ((Over.pullback q).obj V) Z
  have he (b : V ⟶ Z) : e (a ≫ b) = (Over.pullback q).map b := by
    apply e.symm.injective
    rw [Equiv.symm_apply_apply]
    change a ≫ b = ((Over.mapPullbackAdj q).homEquiv _ _).symm
      ((Over.pullback q).map b)
    rw [Adjunction.homEquiv_counit]
    exact ((Over.mapPullbackAdj q).counit.naturality b).symm
  have hpre : Function.Bijective (fun b : V ⟶ Z => a ≫ b) := by
    simpa only [Functor.id_obj] using
      (Scheme.bijective_over_precomp_of_isIso_appTop (Z := Z) a)
  have hb := e.bijective.comp hpre
  have hb' : Function.Bijective (fun b : V ⟶ Z => (Over.pullback q).map b) := by
    simpa only [Function.comp_def, he] using hb
  exact hb'

/-- The literal represented coefficient unit is bijective on affine tests. -/
theorem representedCoefficientUnit_bijective_affine_of_structureIso
    (H : Grp (Over Y)) [IsCommMonObj H.X] [IsFinite H.X.hom]
    (U : Y.Etale) [IsAffine U.left] :
    Function.Bijective
      ((SchemeTorsorBaseChange.representedCoefficientUnit q H).hom.app (op U)) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hb := affineEtaleTest_pullbackHom_bijective_of_structureIso q U H.X
  constructor
  · intro a b hab
    apply ULift.ext
    change a.down.toMul = b.down.toMul
    apply hb.injective
    exact congrArg (fun z => z.down.toMul) hab
  · intro b
    obtain ⟨a, ha⟩ := hb.surjective b.down.toMul
    refine ⟨⟨Additive.ofMul a⟩, ?_⟩
    apply ULift.ext
    change Additive.ofMul ((Over.pullback q).map a) = b.down
    exact congrArg Additive.ofMul ha

/-- Affine-test detection applies to the same original represented unit. -/
theorem representedCoefficientUnit_isIso_of_structureIso
    (H : Grp (Over Y)) [IsCommMonObj H.X] [IsFinite H.X.hom] :
    IsIso (SchemeTorsorBaseChange.representedCoefficientUnit q H) := by
  let a := SchemeTorsorBaseChange.representedCoefficientUnit q H
  have h (U : Y.Etale) (hU : IsAffine U.left) : Function.Bijective (a.hom.app (op U)) := by
    let : IsAffine U.left := hU
    exact representedCoefficientUnit_bijective_affine_of_structureIso q H U
  have hmono : Sheaf.IsLocallyInjective a :=
    Scheme.Etale.locallyInjective_of_affine Y a.hom (fun U hU => (h U hU).injective)
  have hepi : Sheaf.IsLocallySurjective a :=
    Scheme.Etale.locallySurjective_of_affine Y a.hom (fun U hU => (h U hU).surjective)
  exact (Sheaf.isLocallyBijective_iff_isIso a).mp ⟨hmono, hepi⟩

/-- The represented section map is the actual adjunction unit, not an
unrelated isomorphism between the same coefficient objects. -/
theorem represented_adjunctionUnit_isIso_of_structureIso
    (H : Grp (Over Y)) [IsCommMonObj H.X] [IsFinite H.X.hom] [Etale H.X.hom] :
    IsIso ((inverseImageAdjunction q).unit.app (representedSheaf H)) := by
  have : IsIso (SchemeTorsorBaseChange.representedCoefficientUnit q H) :=
    representedCoefficientUnit_isIso_of_structureIso q H
  have hcomp : IsIso ((inverseImageAdjunction q).unit.app (representedSheaf H) ≫
      (directImage q).map (representedSheafBaseChangeIso q H).hom) := by
    rw [SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hcomp

/-- The original finite constant coefficient uses its existing representation.
The target is affine; no arbitrary-target claim is made. -/
theorem finiteConstant_adjunctionUnit_isIso_of_structureIso
    (A : Type u) [AddCommGroup A] [Finite A] :
    IsIso ((inverseImageAdjunction q).unit.app (ConstantFinite.coefficient A Y)) := by
  let t := ConstantFinite.representation A Y
  have : IsIso ((inverseImageAdjunction q).unit.app (representedSheaf t.group)) :=
    represented_adjunctionUnit_isIso_of_structureIso q t.group
  exact (NatTrans.isIso_app_iff_of_iso (inverseImageAdjunction q).unit t.iso).mp inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology
