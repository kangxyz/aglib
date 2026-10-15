/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Tensor products of line bundles

The tensor sheaf is the sheafification of the actual sectionwise module
tensor product. Sheafification commutes with restriction because its unit is
locally bijective and restriction preserves this property. Local unit charts
prove that the tensor product of two line bundles is again a line bundle.
Tensor descends to isomorphism classes, with unit and symmetry laws induced by
actual sheaf isomorphisms. Associativity and dual inverses are supplied separately.
The braiding specializes the shared generic site tensor braiding.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.Tensor`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})
/-- Sheafification of the underlying module presheaf of `M`, identified with `M`. -/
def sheafifyForgetIso (M : SheafOfModules.{u} X.ringCatSheaf) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  asIso ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app M)
/-- The left unit isomorphism for the sheafified tensor product with the structure module. -/
def tensorSheafLeftUnit (M : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheaf X (SheafOfModules.unit X.ringCatSheaf) M ≅ M := by
  letI : MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))
  exact (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (CategoryTheory.MonoidalCategory.leftUnitor M.val) ≪≫ sheafifyForgetIso X M
/-- The symmetry isomorphism for the sheafified tensor product of module sheaves `M` and `N`. -/
def tensorSheafBraiding (M N : SheafOfModules.{u} X.ringCatSheaf) :
    tensorSheaf X M N ≅ tensorSheaf X N M :=
  SheafOfModulesOfCommRing.tensorBraiding X.sheaf M N

open Opposite TopologicalSpace

/-- Restriction of the tensor presheaf to `U`, identified with the tensor of the restrictions. -/
def tensorPresheafOverIso (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) ≅
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ X.presheaf) (M.over U).val (N.over U).val :=
  _root_.PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- A trivialization over `U` of the tensor sheaf, constructed from the supplied trivializations
of `M` and `N`. -/
def tensorOverTrivialization (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (tensorSheaf X M N).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := by
  let S := _root_.PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)
  let e' := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e
  let f' := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso f
  let t := CategoryTheory.MonoidalCategory.tensorIso
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf)) e' f'
  let l := CategoryTheory.MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val
  exact (_root_.PresheafOfModules.Restriction.sheafificationOverIso X.ringCatSheaf U _).symm ≪≫
    S.mapIso (tensorPresheafOverIso X M N U) ≪≫ S.mapIso t ≪≫ S.mapIso l ≪≫
    asIso
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
      (SheafOfModules.unit (X.ringCatSheaf.over U)))

theorem isLocallyRankOne_iff_local_unit (M : SheafOfModules.{u} X.ringCatSheaf) :
    IsLocallyRankOne X M ↔ ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  constructor
  · rintro ⟨q, hq, hr⟩ x
    let := hq
    obtain ⟨V, _, ⟨i, ⟨j⟩⟩, hxV⟩ := q.coversTop ⊤ x (by trivial)
    refine ⟨q.X i, j.le hxV, ?_⟩
    let e := (hr i).some
    exact ⟨(asIso (q.generators i).π).symm ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso e.toIso ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over (q.X i))))⟩
  · intro h
    choose U hx e using h
    let e' (x : X) : SheafOfModules.free (R := X.ringCatSheaf.over (U x)) PUnit.{u + 1} ≅
        M.over (U x) :=
      CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over (U x))) ≪≫
          (e x).some.symm
    let q : M.LocalGeneratorsData.{u} := {
      I := X
      X := U
      coversTop := by
        intro V x hxV
        exact ⟨U x ⊓ V, homOfLE inf_le_right,
          ⟨x, ⟨homOfLE inf_le_left⟩⟩, hx x, hxV⟩
      generators x := (SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (U x)) PUnit.{u + 1}).ofEpi (e' x).hom }
    refine ⟨q, ?_, fun _ => ⟨Equiv.refl _⟩⟩
    constructor
    intro x
    dsimp [q]
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance

/-- Restrict a supplied trivialization of `M` over `V` to the smaller open `U`. -/
def restrictUnitIso (M : SheafOfModules.{u} X.ringCatSheaf) {U V : X.Opens}
    (i : U ⟶ V) (e : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
      SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i

theorem tensorSheaf_locallyRankOne (M N : SheafOfModules.{u} X.ringCatSheaf)
    (hM : IsLocallyRankOne X M) (hN : IsLocallyRankOne X N) :
    IsLocallyRankOne X (tensorSheaf X M N) := by
  rw [isLocallyRankOne_iff_local_unit] at hM hN ⊢
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨f⟩⟩ := hN x
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact tensorOverTrivialization X M N (U ⊓ V)
    (restrictUnitIso X M (homOfLE inf_le_left) e)
    (restrictUnitIso X N (homOfLE inf_le_right) f)

/-- Tensor product of actual locally rank-one sheaves. -/
def tensorLineBundle (L M : LineBundle X) : LineBundle X :=
  ⟨tensorSheaf X L.val M.val, tensorSheaf_locallyRankOne X L.val M.val L.property M.property⟩

/-- Tensor multiplication on actual isomorphism classes. -/
def tensorClass (a b : LineBundleClass X) : LineBundleClass X :=
  Quotient.liftOn₂ a b
    (fun L M => Quotient.mk (lineBundleSetoid X) (tensorLineBundle X L M))
    (by
      intro L L' M M' ⟨e⟩ ⟨f⟩
      exact Quotient.sound ⟨tensorSheafIso X e f⟩)

theorem tensorClass_comm (a b : LineBundleClass X) : tensorClass X a b = tensorClass X b a := by
  induction a using Quotient.inductionOn with | h L =>
    induction b using Quotient.inductionOn with | h M =>
      exact Quotient.sound ⟨tensorSheafBraiding X L.val M.val⟩

theorem tensorClass_trivial_left (a : LineBundleClass X) :
    tensorClass X (Quotient.mk (lineBundleSetoid X) (trivialLineBundle X)) a = a := by
  induction a using Quotient.inductionOn with | h L =>
    apply Quotient.sound
    exact ⟨tensorSheafIso X
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
      (Iso.refl L.val) ≪≫ tensorSheafLeftUnit X L.val⟩

theorem tensorClass_trivial_right (a : LineBundleClass X) :
    tensorClass X a (Quotient.mk (lineBundleSetoid X) (trivialLineBundle X)) = a := by
  rw [tensorClass_comm, tensorClass_trivial_left]
end AlgebraicGeometry.Scheme.Modules.Invertible
