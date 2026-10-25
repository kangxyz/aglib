/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalLocalCoverMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # The original finite constant adjunction unit under finite purely inseparable extension

Finite-cover invariance is applied over every etale test scheme. The section
maps are the original represented coefficient units, and the conclusion is
invertibility of the original inverse-image/direct-image adjunction unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [IsPurelyInseparable k K] [Module.Finite k K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The actual field-extension projection restricts to the finite-cover equivalence
over every test scheme, without affine or finiteness assumptions on that test. -/
theorem finitePure_testBaseChange_isEquivalence {U : Scheme.{u}} (i : U ⟶ X) :
    (FiniteEtale.baseChange
      (pullback.fst i (pullback.fst p (Spec.algebraMap k K)))).IsEquivalence := by
  let e := pullbackRightPullbackFstIso p (Spec.algebraMap k K) i
  let g := pullback.fst (i ≫ p) (Spec.algebraMap k K)
  let := FiniteEtale.PurelyInseparable.Global.finitePureBaseChange_isEquivalence k K (i ≫ p)
  apply FiniteEtale.PurelyInseparable.Global.baseChange_isEquivalence_of_isoSquare
    e.symm (Iso.refl U) _ g
  simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    pullbackRightPullbackFstIso_inv_fst p (Spec.algebraMap k K) i

private theorem finitePure_overMap_sections_bijective
    (U : Over X) (V : Scheme.FiniteEtale X) :
    Function.Bijective ((Over.pullback (pullback.fst p (Spec.algebraMap k K))).map :
      (U ⟶ V.obj) → _) := by
  let f := pullback.fst p (Spec.algebraMap k K)
  let G := Over.pullback f
  let : Flat f := inferInstanceAs (Flat (pullback.fst p (Spec.algebraMap k K)))
  let : Surjective f := inferInstanceAs (Surjective (pullback.fst p (Spec.algebraMap k K)))
  let : QuasiCompact f := inferInstanceAs (QuasiCompact (pullback.fst p (Spec.algebraMap k K)))
  let := finitePure_testBaseChange_isEquivalence k K p U.hom
  constructor
  · exact G.map_injective
  · intro q
    let T := Scheme.FiniteEtale.terminalCover U.left
    let e : (Over.map U.hom).obj T.obj ≅ U := Over.isoMk (Iso.refl _) (by
      change U.hom = (𝟙 U.left) ≫ U.hom
      exact (Category.id_comp U.hom).symm)
    let eV : (Over.map (𝟙 X)).obj V.obj ≅ V.obj := (Over.mapId X).app V.obj
    let q' := (G.mapIso e).hom ≫ q ≫ (G.mapIso eV).inv
    obtain ⟨a, ha⟩ := FiniteEtale.PurelyInseparable.Global.local_overMap_surjective
      f U.hom (𝟙 X) U.hom (Category.comp_id _) T V q'
    refine ⟨e.inv ≫ a ≫ eV.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, ha]
    simp [q']

variable (G : Grp (Over X)) [IsCommMonObj G.X] [IsFinite G.X.hom] [Etale G.X.hom]

/-- On every original etale test, actual represented coefficient sections pull back
bijectively. Consequently the original represented coefficient unit is invertible. -/
theorem finitePure_representedCoefficientUnit_isIso :
    IsIso (SchemeTorsorBaseChange.representedCoefficientUnit
      (pullback.fst p (Spec.algebraMap k K)) G) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective (C := AddCommGrpCat.{u + 1})
    ((SchemeTorsorBaseChange.representedCoefficientUnit
      (pullback.fst p (Spec.algebraMap k K)) G).hom.app U)).mpr
  have hmap := finitePure_overMap_sections_bijective k K p
    ((Scheme.Etale.forget X).obj U.unop) (Scheme.FiniteEtale.mk G.X.hom)
  constructor
  · intro a b hab
    apply ULift.ext
    apply Additive.toMul.injective
    apply hmap.injective
    exact congrArg (fun z => z.down.toMul) hab
  · intro b
    obtain ⟨a, ha⟩ := hmap.surjective b.down.toMul
    refine ⟨ULift.up (Additive.ofMul a), ?_⟩
    apply ULift.ext
    apply Additive.toMul.injective
    exact ha

/-- The native represented coefficient comparison identifies the actual original
adjunction unit with the proved sectionwise isomorphism. -/
theorem finitePure_representedAdjunctionUnit_isIso :
    IsIso ((inverseImageAdjunction (pullback.fst p (Spec.algebraMap k K))).unit.app
      (representedSheaf G)) := by
  let f := pullback.fst p (Spec.algebraMap k K)
  let e : (inverseImage f).obj (representedSheaf G) ≅
      representedSheaf (baseChangedGroup f G) := representedSheafBaseChangeIso f G
  let := finitePure_representedCoefficientUnit_isIso k K p G
  have hu : (inverseImageAdjunction f).unit.app (representedSheaf G) ≫
      (directImage f).map e.hom =
        SchemeTorsorBaseChange.representedCoefficientUnit f G :=
    SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit f G
  have heq : (inverseImageAdjunction f).unit.app (representedSheaf G) =
      SchemeTorsorBaseChange.representedCoefficientUnit f G ≫ (directImage f).map e.inv := by
    rw [← hu, Category.assoc, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact (@CategoryTheory.Category.comp_id (AbelianSheaf.{u, u + 1} X) _
      (representedSheaf G) ((directImage f).obj ((inverseImage f).obj (representedSheaf G)))
      ((inverseImageAdjunction f).unit.app (representedSheaf G))).symm
  rw [heq]
  infer_instance

omit G in
/-- The original unit on the literal native finite constant abelian sheaf is an
isomorphism under finite purely inseparable field extension, on every scheme. -/
theorem finitePure_adjunctionUnit_isIso
    (A : Type u) [AddCommGroup A] [Finite A] :
    IsIso ((inverseImageAdjunction (pullback.fst p (Spec.algebraMap k K))).unit.app
      (coefficient A X)) := by
  let f := pullback.fst p (Spec.algebraMap k K)
  let D := representation A X
  let e : representedSheaf D.group ≅ coefficient A X := D.iso
  let unitNat := (inverseImageAdjunction f).unit
  let := finitePure_representedAdjunctionUnit_isIso k K p D.group
  have hn := unitNat.naturality e.hom
  change e.hom ≫ unitNat.app (coefficient A X) =
    unitNat.app (representedSheaf D.group) ≫
      (directImage f).map ((inverseImage f).map e.hom) at hn
  have heq : unitNat.app (coefficient A X) = e.inv ≫
      unitNat.app (representedSheaf D.group) ≫
      (directImage f).map ((inverseImage f).map e.hom) := by
    rw [← hn]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [heq]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
