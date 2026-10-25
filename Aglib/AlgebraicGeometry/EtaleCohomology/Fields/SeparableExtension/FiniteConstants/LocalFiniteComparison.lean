/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.NoetherianComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ProjectiveLineTests
public import Mathlib.GroupTheory.OrderOfElement

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
    Function.Bijective (cohomologyPullback.{u, eX, eX'} g' F q) := by
  let : IsFinite f' := MorphismProperty.of_isPullback h (inferInstance : IsFinite f)
  let E : Sheaf.H.{eS} ((directImage f).obj F) q ≃+ Sheaf.H.{eX} F q :=
    Finite.finiteCohomologyDirectImageAddEquiv f F q
  let E' : Sheaf.H.{eS'} ((directImage f').obj ((inverseImage g').obj F)) q ≃+
      Sheaf.H.{eX'} ((inverseImage g').obj F) q :=
    Finite.finiteCohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
  let β := (baseChangeMap f f' g g' h.w.symm).app F
  have : IsIso β := Finite.finiteBaseChange_app_isIso f f' g g' h F
  have hb : Function.Bijective (fun a : Sheaf.H.{eX} F q =>
      E' (Sheaf.H.map β q
        (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q (E.symm a)))) :=
    E'.bijective.comp ((cohomologyMapIso_bijective (asIso β) q).comp
      (hF.comp E.symm.bijective))
  have heq : (fun a : Sheaf.H.{eX} F q =>
      E' (Sheaf.H.map β q
        (cohomologyPullback.{u, eS, eS'} g ((directImage f).obj F) q (E.symm a)))) =
      cohomologyPullback.{u, eX, eX'} g' F q := by
    funext a
    calc
      _ = cohomologyPullback.{u, eX, eX'} g' F q (E (E.symm a)) :=
        Finite.finiteCohomologyDirectImageAddEquiv_baseChange f f' g g' h F q (E.symm a)
      _ = cohomologyPullback.{u, eX, eX'} g' F q a := by rw [E.apply_symm_apply]
  rw [heq] at hb
  exact hb

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
