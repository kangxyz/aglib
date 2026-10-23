/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineStalkExactness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricAffineChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # Finite direct image is exact on the original small étale sites -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

private theorem epi_map_of_natIso {C D : Type*} [Category C] [Category D]
    {L M : C ⥤ D} (e : L ≅ M) {X Y : C} (f : X ⟶ Y) [Epi (M.map f)] :
    Epi (L.map f) := by
  apply (epi_comp_iff_of_isIso (L.map f) (e.hom.app Y)).mp
  rw [e.hom.naturality]
  infer_instance

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
  {F G : AbelianSheaf.{u, u + 1} X} (α : F ⟶ G) [Epi α]

/-- The original direct-image coefficient map is epic at every original
geometric point, by genuine affine-chart restriction. -/
theorem finiteDirectImage_geometricStalkMap_epi
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S) :
    Epi ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1}) |>.map
      ((directImage f).map α)) := by
  obtain ⟨i, φ, hφ⟩ := exists_affineOpenCover_point_factorization η
  let R : Type u := S.affineOpenCover.X i
  let : CommRing R := inferInstanceAs (CommRing (S.affineOpenCover.X i))
  let alg : Algebra R Ω := φ.toAlgebra
  let g := S.affineOpenCover.f i
  let η' : Spec (.of Ω) ⟶ Spec (.of R) := Spec.algebraMap R Ω
  have hη : η' ≫ g = η := hφ
  let T := (pointSmallEtale η').sheafFiber (A := AddCommGrpCat.{u + 1})
  let : (etaleRestriction (pullback.snd g f)).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (inverseImageEtaleIso (pullback.snd g f))
  let β := (etaleRestriction (pullback.snd g f)).map α
  have hβ : Epi (T.map ((directImage (pullback.fst g f)).map β)) := by
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (@GeometricNeighborhood.finiteAffineDirectImage_stalkMap_surjective R Ω
        inferInstance inferInstance alg inferInstance _ (pullback.fst g f)
        inferInstance _ _ β inferInstance)
  let : Epi ((etaleRestriction (pullback.snd g f) ⋙
      directImage (pullback.fst g f) ⋙ T).map α) := hβ
  let E : directImage f ⋙
      (pointSmallEtale (η' ≫ g)).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
        etaleRestriction (pullback.snd g f) ⋙ directImage (pullback.fst g f) ⋙ T :=
    Functor.isoWhiskerLeft (directImage f) (StalkInverseImage.stalkUnitNatIso g η') ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (directImage f) (inverseImageEtaleIso g)) T ≪≫
        Functor.isoWhiskerRight (etaleDirectImageRestrictionIso f g) T
  have h : Epi ((pointSmallEtale (η' ≫ g)).sheafFiber
      (A := AddCommGrpCat.{u + 1}) |>.map ((directImage f).map α)) :=
    epi_map_of_natIso E α
  exact hη ▸ h

/-- A finite morphism preserves epimorphisms of arbitrary original abelian
sheaves. No finite-presentation or Noetherian hypothesis is imposed. -/
instance finiteDirectImage_preservesEpimorphisms : (directImage f).PreservesEpimorphisms where
  preserves {F G} α hα := by
    let := hα
    have hstalk (x : FibrewiseClosed.Index (𝟙 S)) :
        Epi ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
          (A := AddCommGrpCat.{u + 1}) |>.map ((directImage f).map α)) :=
      finiteDirectImage_geometricStalkMap_epi f α (FibrewiseClosed.geometricPoint x.val)
    exact (StalkUniverse.originalStalks_jointlyReflectIsomorphisms (𝟙 S)).epi
      ((directImage f).map α)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
