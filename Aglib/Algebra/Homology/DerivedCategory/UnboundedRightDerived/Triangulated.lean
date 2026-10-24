/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated

/-!
# Triangulatedness of the native unbounded right-derived functor

The original localization unit descends to the homotopy category. For every
derived arrow, the actual functorial replacement gives an isomorphic arrow
between K-injective complexes. The right orthogonal to the acyclic complexes
supplies a distinguished triangle all of whose objects are K-injective.
The native left-extension criterion proves triangulatedness.

No additive or triangulated structure on the chain-level replacement functor
is assumed or introduced.
-/

@[expose] public noncomputable section

universe u v w u' v' w'

open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
  (η : 𝟭 (CochainComplex C ℤ) ⟶ R)
  (hη : ∀ K, QuasiIso (η.app K))
  (hR : ∀ K, (R.obj K).IsKInjective)

/-- The original quotient comparison for the degreewise functor. -/
def rightDerivedFunctorHomotopySourceFactors :
    HomotopyCategory.quotient C (.up ℤ) ⋙
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso D)

/-- The original quotient comparison for the localized right-derived functor. -/
def rightDerivedFunctorOfKInjectiveReplacementHomotopyFactors :
    HomotopyCategory.quotient C (.up ℤ) ⋙
      (DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR) ≅
        DerivedCategory.Q ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedCategory.quotientCompQhIso C) _

/-- The degreewise functor lifted through the original homotopy quotient. -/
local instance sourceLifting : Localization.Lifting (HomotopyCategory.quotient C (.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
  ⟨rightDerivedFunctorHomotopySourceFactors F⟩

/-- The derived functor lifted through the original homotopy quotient. -/
local instance targetLifting : Localization.Lifting (HomotopyCategory.quotient C (.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (.up ℤ))
    (DerivedCategory.Q ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR)
    (DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR) :=
  ⟨rightDerivedFunctorOfKInjectiveReplacementHomotopyFactors F R η hη hR⟩

local instance sourceLifting_commShift :
    (Localization.Lifting.iso (HomotopyCategory.quotient C (.up ℤ))
      (HomologicalComplex.homotopyEquivalences C (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).hom.CommShift ℤ := by
  dsimp [Localization.Lifting.iso, rightDerivedFunctorHomotopySourceFactors]
  infer_instance

local instance targetLifting_commShift :
    NatTrans.CommShift (Localization.Lifting.iso (HomotopyCategory.quotient C (.up ℤ))
      (HomologicalComplex.homotopyEquivalences C (.up ℤ))
      (DerivedCategory.Q ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR)
      (DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR)).hom ℤ := by
  dsimp [Localization.Lifting.iso, rightDerivedFunctorOfKInjectiveReplacementHomotopyFactors]
  infer_instance

/-- The original universal unit descended through the actual homotopy quotient. -/
def rightDerivedFunctorOfKInjectiveReplacementUnith :
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR :=
  Localization.liftNatTrans (HomotopyCategory.quotient C (.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (.up ℤ)) _ _ _ _
    (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR)

instance rightDerivedFunctorOfKInjectiveReplacementUnith_commShift :
    (F.rightDerivedFunctorOfKInjectiveReplacementUnith R η hη hR).CommShift ℤ := by
  dsimp only [rightDerivedFunctorOfKInjectiveReplacementUnith]
  infer_instance

/-- The descended unit uses exactly the original chain unit and quotient factors. -/
lemma rightDerivedFunctorOfKInjectiveReplacementUnith_app (K : CochainComplex C ℤ) :
    (F.rightDerivedFunctorOfKInjectiveReplacementUnith R η hη hR).app
        ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (rightDerivedFunctorHomotopySourceFactors F).hom.app K ≫
        (F.rightDerivedFunctorOfKInjectiveReplacementUnit R η hη hR).app K ≫
          (rightDerivedFunctorOfKInjectiveReplacementHomotopyFactors F R η hη hR).inv.app K := by
  apply Localization.liftNatTrans_app

instance isIso_rightDerivedFunctorOfKInjectiveReplacementUnith_app
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso ((F.rightDerivedFunctorOfKInjectiveReplacementUnith R η hη hR).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
  rw [rightDerivedFunctorOfKInjectiveReplacementUnith_app]
  infer_instance

private lemma isIso_unith_of_rightOrthogonal (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal X) :
    IsIso ((F.rightDerivedFunctorOfKInjectiveReplacementUnith R η hη hR).app X) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have : CochainComplex.IsKInjective K := (CochainComplex.isKInjective_iff_rightOrthogonal K).2 hX
  infer_instance

/-- The actual unbounded right-derived functor is triangulated. -/
instance rightDerivedFunctorOfKInjectiveReplacement_isTriangulated :
    (F.rightDerivedFunctorOfKInjectiveReplacement R η hη hR).IsTriangulated := by
  apply Functor.isTriangulated_of_leftExtension _
    (F.rightDerivedFunctorOfKInjectiveReplacementUnith R η hη hR)
  intro X Y f
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (DerivedCategory.Qh (C := C)).mapArrow) (Arrow.mk f)
  obtain ⟨K, L, g, rfl⟩ := Arrow.mk_surjective a
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  have := hR K
  have := hR L
  let q := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨Z, hZ, b, c, hT⟩ :=
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.distinguished_cocone_triangle
      (q.map (R.map g)) (CochainComplex.IsKInjective.rightOrthogonal (R.obj K))
      (CochainComplex.IsKInjective.rightOrthogonal (R.obj L))
  have hηK : HomotopyCategory.quasiIso C (.up ℤ) (q.map (η.app K)) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (hη K)
  have hηL : HomotopyCategory.quasiIso C (.up ℤ) (q.map (η.app L)) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (hη L)
  have := Localization.inverts DerivedCategory.Qh _ _ hηK
  have := Localization.inverts DerivedCategory.Qh _ _ hηL
  refine ⟨Triangle.mk (q.map (R.map g)) b c, hT,
    isIso_unith_of_rightOrthogonal F R η hη hR (q.obj (R.obj K))
      (CochainComplex.IsKInjective.rightOrthogonal (R.obj K)),
    isIso_unith_of_rightOrthogonal F R η hη hR (q.obj (R.obj L))
      (CochainComplex.IsKInjective.rightOrthogonal (R.obj L)),
    isIso_unith_of_rightOrthogonal F R η hη hR Z hZ, ⟨?_ ≪≫ ea⟩⟩
  exact (Arrow.isoMk (asIso (DerivedCategory.Qh.map (q.map (η.app K))))
    (asIso (DerivedCategory.Qh.map (q.map (η.app L)))) (by
      change DerivedCategory.Qh.map (q.map (η.app K)) ≫
        DerivedCategory.Qh.map (q.map (R.map g)) =
          DerivedCategory.Qh.map (q.map g) ≫ DerivedCategory.Qh.map (q.map (η.app L))
      simpa only [Functor.id_map, Functor.map_comp] using
        congrArg (fun t => DerivedCategory.Qh.map (q.map t)) (η.naturality g).symm)).symm

end CategoryTheory.Functor
