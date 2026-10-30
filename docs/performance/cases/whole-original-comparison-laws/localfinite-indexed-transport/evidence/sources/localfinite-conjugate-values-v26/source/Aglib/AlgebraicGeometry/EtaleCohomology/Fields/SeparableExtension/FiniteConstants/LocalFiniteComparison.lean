/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparisonValues
public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection

/-! # Reverse finite-image transfer of the local projective-line comparison

The original finite cohomology square transfers closed-fibre comparison on
the finite direct-image coefficient to the original coefficient on the source.
The local projective-line theorem supplies this comparison for every coefficient
killed by a positive integer. No field-extension theorem is an input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u eX eS eX' eS'

attribute [local instance] hasSheafifyLarge

/-- Identify the complete original pullback family before any other geometric
map, direct image, coefficient or degree is substituted. -/
private theorem cohomologyPullback_originalFamily
    {X S : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    (k : S ⟶ X) :
    cohomologyPullback.{u, eX, eS} k =
      (inverseImage k).extPrecompMap
        (((inverseImageConstantIso k).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) := rfl

/-- The actual finite cohomology square also transports bijectivity from the
finite direct-image coefficient back to its source. -/
theorem cohomologyPullback_source_bijective_of_finiteDirectImage
    {X S X' S' : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) [IsFinite f]
    (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : IsPullback g' f' f g) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : Function.Bijective (cohomologyPullback.{u, eS, eS'} g
      ((directImage f).obj F) q)) :
    Function.Bijective (cohomologyPullback.{u, eX, eX'} g' F q) :=
  by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let U := (constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A
  let c := inverseImageComp g f'
  let d := eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h.w.symm) ≪≫ inverseImageComp f g'
  have hSquare : inverseImageSquareIso f f' g g' h.w.symm = c.symm ≪≫ d :=
    inverseImageSquareIso_eq_comp f f' g g' h.w.symm
  have hMate : baseChangeMap f f' g g' h.w.symm =
      (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
        (TwoSquare.mk (inverseImage g) (inverseImage f) (inverseImage f') (inverseImage g')
          (c.symm ≪≫ d).hom)).natTrans := by
    rw [baseChangeMap_eq_nativeMate, hSquare]
  have hs : ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫ c.hom.app U =
      ((inverseImageConstantIso f').app A).inv ≫
        (inverseImage f').map ((inverseImageConstantIso g).app A).inv := by
    simpa only [Iso.app_inv] using inverseImageComp_constant_inv g f' A
  have ht : ((inverseImageConstantIso (f' ≫ g)).app A).inv ≫ d.hom.app U =
      ((inverseImageConstantIso g').app A).inv ≫
        (inverseImage g').map ((inverseImageConstantIso f).app A).inv := by
    have he := Functor.sourceInverse_eq_transport
      (fun k : X' ⟶ S => inverseImage k) (fun k => inverseImageConstantIso k) h.w.symm A
    simp only [Iso.app_inv, d, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    rw [← Category.assoc, he]
    exact inverseImageComp_constant_inv f g' A
  let : IsIso ((baseChangeMap f f' g g' h.w.symm).app F) :=
    Finite.finiteBaseChange_app_isIso f f' g g' h F
  exact Adjunction.originalExtSourceComparison_bijective_of_mate_values.{
    u + 2, u + 1, eS, u + 2, u + 1, eX, u + 2, u + 1, eS', u + 2, u + 1, eX'}
    (inverseImageAdjunction f) (inverseImageAdjunction f') (inverseImage g) (inverseImage g')
    ((inverseImageConstantIso f).app A) ((inverseImageConstantIso f').app A)
    (inverseImage (f' ≫ g)) c d ((inverseImageConstantIso g).app A).inv
    ((inverseImageConstantIso g').app A).inv ((inverseImageConstantIso (f' ≫ g)).app A).inv
    hs ht (baseChangeMap f f' g g' h.w.symm) hMate
    (cohomologyPullback.{u, eS, eS'} g) (cohomologyPullback_originalFamily g)
    (cohomologyPullback.{u, eX, eX'} g') (cohomologyPullback_originalFamily g') F q hF

attribute [local instance] HasExt.standard

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]

/-- Every bounded coefficient on a scheme finite over the local projective line
has bijective original closed-fibre pullback in every degree. -/
theorem finite_projectiveLine_residuePullback_bijective_of_killed_of_isNoetherian
    (n : ℕ) (hn : n ≠ 0) (F : AbelianSheaf.{u, u + 1} Y)
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) F q) := by
  have hD : n • 𝟙 ((directImage f).obj F) = 0 := by
    have h := congrArg (fun a : F ⟶ F => (directImage f).map a) hF
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero] using h
  exact cohomologyPullback_source_bijective_of_finiteDirectImage f (finiteResidueMap f)
    (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
    (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
    (finiteResidueMap_isPullback f) F q
    (projectiveLine_residuePullback_bijective_of_killed_of_isNoetherian n hn
      ((directImage f).obj F) hD q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {Y : Scheme.{u}} (f : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite f]

/-- The literal original finite-constant restriction to the closed fibre is
bijective in every degree over a Noetherian strictly henselian local base. -/
theorem finite_projectiveLine_constantRestriction_bijective_of_isNoetherian
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) :
    Function.Bijective (constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)) q) := by
  classical
  let : Fintype (ConstantFinite.value A) := Fintype.ofFinite _
  let n := Fintype.card (ConstantFinite.value A)
  have hn : n ≠ 0 := Nat.ne_of_gt Fintype.card_pos
  have hA : n • 𝟙 (ConstantFinite.value A) = 0 := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change Fintype.card (ConstantFinite.value A) • a = 0
    exact card_nsmul_eq_zero (G := ConstantFinite.value A) (x := a)
  have hF : n • 𝟙 (ConstantFinite.coefficient A Y) = 0 := by
    have h := congrArg
      (fun a : ConstantFinite.value A ⟶ ConstantFinite.value A =>
        (constantSheaf (Scheme.smallEtaleTopology Y) AddCommGrpCat.{u + 1}).map a) hA
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero] using h
  exact (cohomologyMapIso_bijective ((inverseImageConstantIso
    (pullback.fst (f ≫ ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))).app
      (ConstantFinite.value A)) q).comp
    (Proper.finite_projectiveLine_residuePullback_bijective_of_killed_of_isNoetherian
      f n hn (ConstantFinite.coefficient A Y) hF q)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
