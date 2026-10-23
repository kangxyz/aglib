/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.Proper.FiniteType
public import Aglib.AlgebraicGeometry.Cover.AffineBinary.Limit
public import Aglib.AlgebraicGeometry.Limits.FixedBaseChange
public import Aglib.AlgebraicGeometry.Modules.Invertible.Descent.Limit
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# Proper residue-fibre lifting from finitely presented lifting

An actual affine binary cover descends to one proper finitely presented
approximant over the unchanged local base. The original residue-fibre bundle
descends above that stage. Affine pullback preserves the descended cover, so
the explicit finitely presented lifting hypothesis applies at their common
stage. Every recovery map is the original cone or residue-fibre projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

private theorem exists_residue_lift_of_properFPLimit
    (R : Type u) [CommRing R] [IsLocalRing R]
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u})
    [∀ {j k} (r : j ⟶ k), IsAffineHom (D.map r)]
    (a : D ⟶ (Functor.const J).obj (Spec (CommRingCat.of R)))
    [∀ j, IsProper (a.app j)] [∀ j, LocallyOfFinitePresentation (a.app j)]
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ Spec (CommRingCat.of R))
    (hp : ∀ j, c.π.app j ≫ a.app j = p) (A : AffineBinaryCover c.pt)
    (hFP : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))
      [IsProper g] [LocallyOfFinitePresentation g] (_B : AffineBinaryCover Y)
      (C : LineBundle (Limits.pullback g (LocalRing.residueSpecMap R))),
      ∃ N : LineBundle Y,
        Nonempty ((pullback (Limits.pullback.fst g (LocalRing.residueSpecMap R))).obj
          N.val ≅ C.val))
    (L : LineBundle (Limits.pullback p (LocalRing.residueSpecMap R))) :
    ∃ M : LineBundle c.pt,
      Nonempty ((pullback (Limits.pullback.fst p (LocalRing.residueSpecMap R))).obj
        M.val ≅ L.val) := by
  have (j : J) : CompactSpace (((Functor.const J).obj (Spec (CommRingCat.of R))).obj j) :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of R)))
  have (j : J) : QuasiSeparatedSpace
      (((Functor.const J).obj (Spec (CommRingCat.of R))).obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of R)))
  have (j : J) : CompactSpace (D.obj j) :=
    QuasiCompact.compactSpace_of_compactSpace (a.app j)
  have (j : J) : QuasiSeparatedSpace (D.obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (a.app j)
  obtain ⟨i₀, B, _, _⟩ := AffineBinaryCover.exists_model_of_isLimit D c hc A
  let b := LocalRing.residueSpecMap R
  let E := FixedBaseChange.diagram D a b
  let d := FixedBaseChange.cone D a b c p hp
  have hd : IsLimit d := FixedBaseChange.isLimitCone D a b c p hp hc
  have {j k : J} (r : j ⟶ k) : IsAffineHom (E.map r) :=
    inferInstanceAs (IsAffineHom ((FixedBaseChange.diagram D a b).map r))
  have (j : J) : CompactSpace (E.obj j) :=
    inferInstanceAs (CompactSpace ((FixedBaseChange.diagram D a b).obj j))
  have (j : J) : QuasiSeparatedSpace (E.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace ((FixedBaseChange.diagram D a b).obj j))
  obtain ⟨j, r, C, ⟨eC⟩⟩ := exists_lineBundle_above_of_isLimit E d hd i₀ L
  obtain ⟨N, ⟨eN⟩⟩ := hFP (a.app j) (B.pullback (D.map r)) C
  refine ⟨pullbackLineBundle (c.π.app j) N, ⟨?_⟩⟩
  have w : Limits.pullback.fst p b ≫ c.π.app j =
      d.π.app j ≫ Limits.pullback.fst (a.app j) b := by
    change Limits.pullback.fst p b ≫ c.π.app j =
      Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst (a.app j) b
    rw [Limits.pullback.lift_fst]
    rfl
  exact (pullbackComp (Limits.pullback.fst p b) (c.π.app j)).app N.val ≪≫
    (pullbackCongr w).app N.val ≪≫
    ((pullbackComp (d.π.app j) (Limits.pullback.fst (a.app j) b)).app N.val).symm ≪≫
    (pullback (d.π.app j)).mapIso eN ≪≫ eC

/-- Actual residue-fibre lifting for an arbitrary proper scheme with an affine
binary cover follows from the same lifting property for proper locally finitely
presented schemes with such a cover over the original local ring. -/
theorem exists_lineBundle_lift_residue_affineBinary_of_finitePresentation_lifts
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (A : AffineBinaryCover X)
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hFP : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))
      [IsProper g] [LocallyOfFinitePresentation g] (_B : AffineBinaryCover Y)
      (C : LineBundle (Limits.pullback g (LocalRing.residueSpecMap R))),
      ∃ N : LineBundle Y,
        Nonempty ((pullback (Limits.pullback.fst g (LocalRing.residueSpecMap R))).obj
          N.val ≅ C.val))
    (L : LineBundle (Limits.pullback f (LocalRing.residueSpecMap R))) :
    ∃ M : LineBundle X,
      Nonempty ((pullback (Limits.pullback.fst f (LocalRing.residueSpecMap R))).obj
        M.val ≅ L.val) := by
  obtain ⟨P⟩ := Approximation.nonempty_properFinitePresentationSystem f
  rcases P with @⟨J, hJ, hcof, F, ⟨Y, π⟩, hpoint, hc, hproper, hfp, hclosed, _⟩
  let := hJ
  let := hcof
  cases hpoint
  let D := F ⋙ Over.forget (Spec (CommRingCat.of R))
  let a : D ⟶ (Functor.const J).obj (Spec (CommRingCat.of R)) := {
    app j := (F.obj j).hom
    naturality j k r := by
      change (F.map r).left ≫ (F.obj k).hom = (F.obj j).hom ≫ 𝟙 _
      rw [(F.map r).w, Category.comp_id] }
  let c := (Over.forget (Spec (CommRingCat.of R))).mapCone
    (⟨Over.mk f, π⟩ : Cone F)
  have {j k : J} (r : j ⟶ k) : IsAffineHom (D.map r) := by
    let := hclosed r
    exact inferInstanceAs (IsAffineHom (F.map r).left)
  have (j : J) : IsProper (a.app j) := hproper j
  have (j : J) : LocallyOfFinitePresentation (a.app j) := hfp j
  exact exists_residue_lift_of_properFPLimit R D a c hc f
    (fun j => (π.app j).w) A hFP L

end AlgebraicGeometry.Scheme.Modules.Invertible
