/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityBranches

/-!
# Identity coherence of the original derived module inverse-image comparisons

Both unit laws are transported by the existing generic exact-composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original derived inverse-image comparison is normalized at the base identity. -/
theorem moduleDerivedInverseImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedInverseImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (moduleDerivedInverseImageIdIso Λ X)
          (moduleDerivedInverseImage Λ f) ≪≫
        Functor.leftUnitor (moduleDerivedInverseImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDerivedInverseImage Λ k)
        (Category.comp_id f)) := by
  let F := moduleInverseImage f Λ
  let I := moduleInverseImage (𝟙 X) Λ
  let P := moduleInverseImage (f ≫ 𝟙 X) Λ
  let e := moduleInverseImageIdIso Λ X
  let c := moduleInverseImageCompIso Λ (𝟙 X) f
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_leftUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleInverseImageCompIso_id_comp Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology I F) ≪≫
      Functor.isoWhiskerRight (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf X Λ)) F.rightDerivedFunctorPlus ≪≫
      Functor.leftUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerRight_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology I F),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

/-- The original derived inverse-image comparison is normalized at the source identity. -/
theorem moduleDerivedInverseImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)] :
    moduleDerivedInverseImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImage Λ f)
          (moduleDerivedInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleDerivedInverseImage Λ f) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDerivedInverseImage Λ k)
        (Category.id_comp f)) := by
  let F := moduleInverseImage f Λ
  let I := moduleInverseImage (𝟙 S) Λ
  let P := moduleInverseImage (𝟙 S ≫ f) Λ
  let e := moduleInverseImageIdIso Λ S
  let c := moduleInverseImageCompIso Λ f (𝟙 S)
  have hn := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_right F e
  have hu := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_rightUnitor F
  have hp := congrArg (fun z : P ≅ F => P.rightDerivedFunctorPlusIso z)
    (moduleInverseImageCompIso_comp_id Λ f)
  simp only [Functor.rightDerivedFunctorPlusIso_trans,
    Functor.rightDerivedFunctorPlusIso_eqToIso] at hp
  change (P.rightDerivedFunctorPlusIso c ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology F I) ≪≫
      Functor.isoWhiskerLeft F.rightDerivedFunctorPlus (I.rightDerivedFunctorPlusIso e ≪≫
        Functor.rightDerivedFunctorPlusIdIso (ModuleSheaf S Λ)) ≪≫
      Functor.rightUnitor F.rightDerivedFunctorPlus = _
  simp only [Functor.isoWhiskerLeft_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology F I),
    ← hn]
  simp only [Iso.trans_assoc]
  rw [hu]
  exact hp

end AlgebraicGeometry.Scheme.EtaleCohomology
