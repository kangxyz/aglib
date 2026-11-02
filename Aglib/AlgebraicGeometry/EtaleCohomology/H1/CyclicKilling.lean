/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorTrivial
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisRefinement
public import Mathlib.Data.ZMod.Basic

/-!
# Finite étale covers killing the original finite-coefficient H1 class

The existing finite locally constant torsor representative has a tautological
section after pullback to its total space. The original torsor-class pullback
theorem therefore kills the original cohomology class. Representability and
classification are proved suppliers, not additional premises. No curve,
compactification, Galois or prime-to-characteristic hypothesis is needed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

namespace Torsor

variable (P : Torsor L) (Y : Scheme.FiniteEtale X)
  (e : finiteRepresentedSetSheaf Y ≅ P.carrier)

include P e in
/-- Local nonemptiness of the original torsor makes its actual finite étale
representative surjective, for every finite locally constant coefficient. -/
theorem surjective_of_finiteRepresentedIso : Surjective Y.obj.hom := by
  constructor
  intro x
  have h := P.locally_nonempty (etaleTerminal X)
  let Pét : MorphismProperty Scheme.{u} :=
    fun {A B : Scheme.{u}} (f : A ⟶ B) => AlgebraicGeometry.Etale f
  change _ ∈ X.smallGrothendieckTopology Pét (etaleTerminal X) at h
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
    (P := Pét) (Q := Pét) X le_rfl] at h
  have hcover := (Scheme.mem_toGrothendieck_smallPretopology
    (P := Pét) (Q := Pét) (etaleTerminal X) _).mp h
  obtain ⟨V, f, v, ⟨t⟩, _, hv⟩ := hcover x
  let q := (e.inv.hom.app (op V) t).down
  refine ⟨q.left v, ?_⟩
  have hq := Over.w q
  have hf := MorphismProperty.Over.w f
  have hh : q.left ≫ Y.obj.hom = f.left :=
    (hq.trans hf.symm).trans (Category.comp_id f.left)
  change (q.left ≫ Y.obj.hom) v = x
  rw [hh]
  exact hv

/-- The identity of the representing scheme gives a section of the actual
set inverse image, using the original étale-restriction comparison. -/
def finiteRepresentedPullbackSection
    (a : finiteRepresentedSetSheaf Y ⟶ P.carrier) :
    (torsorInverseImage Y.obj.hom P).carrier.obj.obj
      (op (etaleTerminal Y.obj.left)) := by
  change ((setInverseImage Y.obj.hom).obj P.carrier).obj.obj
    (op (etaleTerminal Y.obj.left))
  refine ((setInverseImageEtaleIso Y.obj.hom).inv.app P.carrier).hom.app
    (op (etaleTerminal Y.obj.left)) ?_
  exact a.hom.app
    (op ((siteEtalePostcompose Y.obj.hom).obj (etaleTerminal Y.obj.left)))
    (ULift.up (Over.homMk (𝟙 Y.obj.left) rfl))

/-- The original H1 pullback of the torsor class vanishes on its representative.
The two Ext universes remain independent. -/
theorem h1Pullback_eq_zero_of_finiteRepresentedMap
    (a : finiteRepresentedSetSheaf Y ⟶ P.carrier)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)] :
    h1Pullback Y.obj.hom L (torsorExtClass P) = 0 := by
  rw [← torsorExtClass_inverseImage]
  exact torsorExtClass_eq_zero_of_section _ (finiteRepresentedPullbackSection P Y a)

end Torsor

/-- Every actual H1 class with finite locally constant coefficients is killed
by an actual surjective finite étale cover. The chosen cover works in every
displayed target Ext realization, independently of the source Ext universe. -/
theorem exists_finiteEtale_h1Pullback_eq_zero
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (hL : IsFiniteLocallyConstant L) (c : H1Etale X L) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom L c = 0 := by
  obtain ⟨a, ha⟩ := (torsorClassToH1_bijective L).surjective c
  revert ha
  refine Quotient.inductionOn a ?_
  intro P hP
  change torsorExtClass P = c at hP
  let Y := Torsor.finiteEtaleRepresentative (P := P) (stacks03RV X) hL
  let e := Torsor.finiteEtaleRepresentativeIso (P := P) (stacks03RV X) hL
  refine ⟨Y, Torsor.surjective_of_finiteRepresentedIso P Y e, ?_⟩
  intro hY
  rw [← hP]
  exact Torsor.h1Pullback_eq_zero_of_finiteRepresentedMap P Y e.hom

/-- Over a connected scheme the killing cover can be chosen connected and
Galois, using an actual refinement and the same original torsor section. -/
theorem exists_galois_finiteEtale_h1Pullback_eq_zero
    [ConnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (hL : IsFiniteLocallyConstant L) (c : H1Etale X L) :
    ∃ Y : Scheme.FiniteEtale X,
      PreGaloisCategory.IsGalois Y ∧ ConnectedSpace Y.obj.left ∧ Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom L c = 0 := by
  obtain ⟨a, ha⟩ := (torsorClassToH1_bijective L).surjective c
  revert ha
  refine Quotient.inductionOn a ?_
  intro P hP
  change torsorExtClass P = c at hP
  let T := Torsor.finiteEtaleRepresentative (P := P) (stacks03RV X) hL
  let e := Torsor.finiteEtaleRepresentativeIso (P := P) (stacks03RV X) hL
  let : Surjective T.obj.hom := Torsor.surjective_of_finiteRepresentedIso P T e
  let : Nonempty T.obj.left := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, _⟩ := T.obj.hom.surjective x
    exact ⟨y⟩
  obtain ⟨Y, f, hgal, hconn, hsurj⟩ := Scheme.FiniteEtale.exists_galois_refinement T
  refine ⟨Y, hgal, hconn, hsurj, ?_⟩
  intro hY
  rw [← hP]
  exact Torsor.h1Pullback_eq_zero_of_finiteRepresentedMap P Y
    (finiteRepresentedSetSheafMap f.hom ≫ e.hom)

namespace ConstantFinite

/-- A finite constant class is killed for the original constant-coefficient
pullback, including its canonical inverse-image coefficient isomorphism. -/
theorem exists_finiteEtale_pullbackH1_eq_zero
    (A : Type u) [AddCommGroup A] [Finite A]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (c : H1Etale X (coefficient A X)) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        pullbackH1 A Y.obj.hom c = 0 := by
  obtain ⟨Y, hY, hzero⟩ := exists_finiteEtale_h1Pullback_eq_zero
    (isFiniteLocallyConstant A X) c
  refine ⟨Y, hY, ?_⟩
  intro hExt
  rw [pullbackH1_apply, hzero, map_zero]

end ConstantFinite

/-- Every positive cyclic level is killed on an actual finite étale surjection,
using the single original constant value `ULift (ZMod n)` and H1 pullback. -/
theorem exists_finiteEtale_cyclic_h1Pullback_eq_zero
    (n : ℕ) [NeZero n] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    (c : H1Etale X ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))) :
    ∃ Y : Scheme.FiniteEtale X, Surjective Y.obj.hom ∧
      ∀ [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y.obj.left)],
        h1Pullback Y.obj.hom _ c = 0 := by
  apply exists_finiteEtale_h1Pullback_eq_zero
  exact ⟨{
    index := PUnit.{u + 1}
    chart _ := etaleTerminal X
    covers x := ⟨PUnit.unit, x, rfl⟩
    value _ := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
    finite_value _ := inferInstance
    trivialization _ := (inverseImageConstantIso (𝟙 X)).app _ }⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
