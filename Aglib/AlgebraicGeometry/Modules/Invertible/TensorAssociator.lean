/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Associativity of line-bundle tensor products

The sectionwise tensor associator induces an actual associator on line
bundles after sheafification. Local trivializations show that the intermediate
tensoring maps are locally bijective. The resulting associativity, together
with the tensor unit and symmetry, gives an additive commutative monoid on
isomorphism classes. No tensor law is assumed as a theorem-family premise.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.TensorAssociator`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u v

variable (X : Scheme.{u})
/-- The restricted tensor presheaf identified with the unit presheaf using the supplied
trivializations over `U`. -/
def tensorPresheafLocalIso (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
  tensorPresheafOverIso X M N U ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f) ≪≫
    CategoryTheory.MonoidalCategory.leftUnitor
      (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val

theorem restrictedTensorUnit_isIso (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso (_root_.PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf U
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val
  have hP : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj P).presheaf :=
    (Presheaf.isSheaf_of_iso_iff ((_root_.PresheafOfModules.toPresheaf _).mapIso
      (tensorPresheafLocalIso X M N U e f))).mpr (SheafOfModules.unit _).isSheaf
  have := _root_.PresheafOfModules.Restriction.restrictedSheafificationUnit_locallyInjective
    X.ringCatSheaf U P
  have := _root_.PresheafOfModules.Restriction.restrictedSheafificationUnit_locallySurjective
    X.ringCatSheaf U P
  exact _root_.PresheafOfModules.isIso_of_locallyBijective
    (J := (Opens.grothendieckTopology X).over U)
    _ hP ((tensorSheaf X M N).over U).isSheaf

theorem tensorUnitWhiskerRight_locallyBijective (M N O : SheafOfModules.{u} X.ringCatSheaf)
    (hM : IsLocallyRankOne X M) (hN : IsLocallyRankOne X N) :
    let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val
    let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
      (𝟙 O.val)
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f ∧
      _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f := by
  dsimp only
  apply locallyBijective_of_local_isIso X
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X M).mp hM x
  obtain ⟨V, hxV, ⟨f⟩⟩ := (isLocallyRankOne_iff_local_unit X N).mp hN x
  let W := U ⊓ V
  have hunit := restrictedTensorUnit_isIso X M N W
    (restrictUnitIso X M (homOfLE inf_le_left) e)
    (restrictUnitIso X N (homOfLE inf_le_right) f)
  refine ⟨W, ⟨hxU, hxV⟩, ?_⟩
  change IsIso (PresheafOfModulesOfCommRing.Monoidal.tensorHom
    (R := (Over.forget W).op ⋙ X.presheaf)
    (_root_.PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf W
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val))
    (𝟙 (O.over W).val))
  change IsIso (CategoryTheory.MonoidalCategory.tensorHom
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget W).op ⋙ X.presheaf)) _ _)
  infer_instance

theorem tensorUnitWhiskerLeft_locallyBijective (M N O : SheafOfModules.{u} X.ringCatSheaf)
    (hN : IsLocallyRankOne X N) (hO : IsLocallyRankOne X O) :
    let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) N.val O.val
    let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (𝟙 M.val)
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f ∧
      _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f := by
  dsimp only
  apply locallyBijective_of_local_isIso X
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X N).mp hN x
  obtain ⟨V, hxV, ⟨f⟩⟩ := (isLocallyRankOne_iff_local_unit X O).mp hO x
  let W := U ⊓ V
  have hunit := restrictedTensorUnit_isIso X N O W
    (restrictUnitIso X N (homOfLE inf_le_left) e)
    (restrictUnitIso X O (homOfLE inf_le_right) f)
  refine ⟨W, ⟨hxU, hxV⟩, ?_⟩
  change IsIso (PresheafOfModulesOfCommRing.Monoidal.tensorHom
    (R := (Over.forget W).op ⋙ X.presheaf) (𝟙 (M.over W).val)
    (_root_.PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf W
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) N.val O.val)))
  change IsIso (CategoryTheory.MonoidalCategory.tensorHom
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget W).op ⋙ X.presheaf)) _ _)
  infer_instance

/-- The isomorphism on associated module sheaves induced by a locally injective and locally
surjective map `f`. -/
def sheafificationMapIsoOfLocallyBijective {P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj}
    (f : P ⟶ Q) (h : _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f ∧
      _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ≅
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj Q := by
  have hf : IsIso ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
    apply Functor.IsLocalization.inverts
      (W := (Opens.grothendieckTopology X).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj))
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)
    exact ((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).mpr h
  exact asIso ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)

/-- Actual associativity is obtained from the sectionwise associator and
proved locally invertible sheafification-unit tensor maps. -/
def tensorLineBundleAssociator (L M N : LineBundle X) :
    tensorSheaf X (tensorSheaf X L.val M.val) N.val ≅
      tensorSheaf X L.val (tensorSheaf X M.val N.val) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.val.val M.val.val
  let Q := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val.val N.val.val
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)
    (𝟙 N.val.val)
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 L.val.val)
    ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app Q)
  exact (sheafificationMapIsoOfLocallyBijective X f
    (tensorUnitWhiskerRight_locallyBijective X L.val M.val N.val L.property M.property)).symm ≪≫
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (CategoryTheory.MonoidalCategory.associator
        (C := PresheafOfModulesOfCommRing.{u} X.presheaf) L.val.val M.val.val N.val.val) ≪≫
    sheafificationMapIsoOfLocallyBijective X g
      (tensorUnitWhiskerLeft_locallyBijective X L.val M.val N.val M.property N.property)

theorem tensorClass_assoc (a b c : LineBundleClass X) :
    tensorClass X (tensorClass X a b) c = tensorClass X a (tensorClass X b c) := by
  induction a using Quotient.inductionOn with | h L =>
    induction b using Quotient.inductionOn with | h M =>
      induction c using Quotient.inductionOn with | h N =>
        exact Quotient.sound ⟨tensorLineBundleAssociator X L M N⟩

/-- The actual line-bundle isomorphism classes form a commutative monoid
under tensor product. Dual inverses are a subsequent construction. -/
instance lineBundleClassAddCommMonoid : AddCommMonoid (LineBundleClass X) where
  add := tensorClass X
  zero := Quotient.mk (lineBundleSetoid X) (trivialLineBundle X)
  add_assoc := tensorClass_assoc X
  zero_add := tensorClass_trivial_left X
  add_zero := tensorClass_trivial_right X
  add_comm := tensorClass_comm X
  nsmul := @nsmulRec (LineBundleClass X)
    ⟨Quotient.mk (lineBundleSetoid X) (trivialLineBundle X)⟩ ⟨tensorClass X⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
