/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverTerminalPullback.RootCharacter
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RepresentedCharacterPullback

/-! The original terminal cover class pushed along the original root character. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.OverField Scheme.Group Scheme.Group.BaseChange Scheme.EtaleCohomology
open Scheme.EtaleCohomology.RepresentedKernel
open Scheme.Group.MultiplicativeGroup GroupCohomology.Kummer.Coefficients
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u w w'

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  groupSchemeBaseChange_isCommMonObj
  successiveBaseChangeComm

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Coefficients

variable {S : Scheme.{u}}

private theorem representedSheafMap_three_eq {A B C D : Grp (Over S)}
    [IsCommMonObj A.X] [IsCommMonObj B.X] [IsCommMonObj C.X] [IsCommMonObj D.X]
    (r : A ⟶ B) (s : B ⟶ C) (t : C ⟶ D) (c : A ⟶ D) (h : r ≫ s ≫ t = c) :
    representedSheafMap r ≫ representedSheafMap s ≫ representedSheafMap t =
      representedSheafMap c := by
  rw [← representedSheafMap_comp s t, ← representedSheafMap_comp, h]

private theorem coefficientMap_of_nested_eq [HasExt.{w} (AbelianSheaf.{u, u + 1} S)]
    {A B C D : AbelianSheaf.{u, u + 1} S}
    {r : A ⟶ B} {s : B ⟶ C} {x : H1Etale S A} {b : H1Etale S C}
    (hb : coefficientMap s (coefficientMap r x) = b)
    (t : C ⟶ D) (c : A ⟶ D) (h : r ≫ s ≫ t = c) :
    coefficientMap t b = coefficientMap c x := by
  calc
    _ = coefficientMap t (coefficientMap s (coefficientMap r x)) :=
      congrArg (coefficientMap t) hb.symm
    _ = coefficientMap (r ≫ s ≫ t) x := by
      rw [coefficientMap_comp r (s ≫ t), coefficientMap_comp s t]
      rfl
    _ = _ := congrArg (fun z => coefficientMap z x) h

end Coefficients

section SchemeCover

variable {S Z : Scheme.{u}} {K G B : Grp (Over S)} {q : G ⟶ B}
  [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj B.X]
  (m : KernelMarking K G B q)
  [Etale K.X.hom] [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]

set_option hygiene false in
local notation "B₀" => Group.BaseChange.baseChangedGroup (𝟙 S) B
set_option hygiene false in
local notation "K₀" => Group.BaseChange.baseChangedGroup (𝟙 S) K
set_option hygiene false in
local notation "q₀" => (groupSchemeBaseChange (𝟙 S)).functor.map q
set_option hygiene false in
local notation "m₀" => Group.BaseChange.kernelMarking (𝟙 S) m
set_option hygiene false in
local notation "g" => (B₀).X.hom
set_option hygiene false in
local notation "L" => Group.BaseChange.baseChangedGroup (g) (K₀)

/-- The original quotient is finite after terminal base change. -/
local instance terminalQuotientFinite : IsFinite (q₀).hom.hom.left :=
  Group.BaseChange.map_finite (𝟙 S) q inferInstance

/-- The original quotient is étale after terminal base change. -/
local instance terminalQuotientEtale : Etale (q₀).hom.hom.left :=
  Group.BaseChange.map_etale (𝟙 S) q inferInstance

/-- The original quotient is surjective after terminal base change. -/
local instance terminalQuotientSurjective : Surjective (q₀).hom.hom.left :=
  Group.BaseChange.map_surjective (𝟙 S) q inferInstance

/-- The original kernel is étale after terminal base change. -/
local instance terminalKernelEtale : Etale (K₀).X.hom :=
  Scheme.EtaleCohomology.baseChangedGroup_etale (𝟙 S) K

/-- The original coefficient kernel is étale over the cover target. -/
local instance terminalCoverCoefficientEtale : Etale (L).X.hom :=
  Scheme.EtaleCohomology.baseChangedGroup_etale (g) (K₀)

variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} (B₀).X.left)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} Z)]

/-- The original direct graph boundary pushed by the original character gives the pullback of
the pushed original cover class. -/
theorem terminalCoverRootBoundary_of_eq
    (f : Z ⟶ (B₀).X.left) (a : Z ⟶ B.X.left) (d : Z ⟶ S)
    (hb : f ≫ (g) = d) (ha : a ≫ B.X.hom = d)
    (hf : f ≫ pullback.fst B.X.hom (𝟙 S) = a)
    (P : CategoryTheory.Sheaf.Torsor (representedSheaf (L)))
    (hP : P = relativeCoverTorsor (m₀))
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ((B₀).X.left, ⊤)))
    (χ₀ : (K₀) ⟶ rootsGroupScheme S n) :
    let hD := markedKernelSequence_baseChange_shortExact m d
    let p := (Over.mapPullbackAdj d).homEquiv (Over.mk (𝟙 Z)) B.X
      (Over.homMk a (ha.trans (Category.id_comp d).symm))
    let χ : (L) ⟶ rootsGroupScheme (B₀).X.left n :=
      (groupSchemeBaseChange (g)).functor.map χ₀ ≫
        (MultiplicativeBaseChange.rootsBaseChangeIso (g) n).hom
    coefficientMap (representedSheafMap (terminalRootCharacterBaseChange d K n χ₀))
        ((Ext.mk₀ (representedIntegerSection _ p)).comp hD.extClass (zero_add 1)) =
      Kummer.rootsCohomologyPullback.{u, w', w} f n hn hinv 1
        (coefficientMap (representedSheafMap χ) (torsorExtClass P)) := by
  intro hD p χ
  let θ := terminalRootCharacterBaseChange d K n χ₀
  let U := (groupSchemeBaseChangeComp f (g)).inv.app (K₀)
  let V := (terminalGroupComparison hb).hom.app K
  let c := (Over.pullback f).mapGrp.map χ ≫ (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
  let hχ := terminalRootCharacterBaseChange_comp f (g) d hb K n χ₀
  let hC := representedSheafMap_three_eq U V θ c hχ
  let hB := relativeCoverH1Pullback_terminal_of_eq m f a d hb ha hf P hP
  let hDirect := coefficientMap_of_nested_eq hB
    (representedSheafMap θ) (representedSheafMap c) hC
  let hPush := Kummer.rootsH1Pullback_representedCharacter f n hn hinv χ (torsorExtClass P)
  exact hDirect.trans hPush.symm

end SchemeCover

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
