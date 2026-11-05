/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FilteredPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FreeRepresentablePullback
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineObjects

/-! # Original native module stages under affine base change

Actual affine source models for the base-changed generators, together with the
original inverse-image free comparison, preserve native finite-colimit stages.
No coefficient object or arrow is replaced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

variable (R : Type (u + 1)) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

/-- The original free module on an unchanged etale object. -/
abbrev free (X : Scheme.{u}) (U : X.Etale) :=
  ModuleCat.Sheaf.freeRepresentable.{u + 1, u + 1, u, 0} X.smallEtaleTopology R U

/-- The pullback of an original affine-etale generator along an affine map
has an actual affine-etale model and the native original free-sheaf iso. -/
theorem exists_affineGeneratorInverseImageIso {X S : Scheme.{u}}
    (f : S ⟶ X) [IsAffineHom f] (U : X.AffineEtale) :
    ∃ V : S.AffineEtale,
      Nonempty ((moduleInverseImage R f).obj
        (free R X ((Scheme.AffineEtale.Spec X).obj U)) ≅
          free R S ((Scheme.AffineEtale.Spec S).obj V)) := by
  let W : S.Etale := (siteBaseChange f).obj ((Scheme.AffineEtale.Spec X).obj U)
  have htotal : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  have : IsAffine W.left := by
    change IsAffine (pullback ((Scheme.AffineEtale.Spec X).obj U).hom f)
    let P : MorphismProperty Scheme.{u} := @IsAffineHom
    let : P.IsStableUnderBaseChange := isAffineHom_isStableUnderBaseChange
    have hfst : IsAffineHom (pullback.fst ((Scheme.AffineEtale.Spec X).obj U).hom f) :=
      MorphismProperty.pullback_fst (P := P) _ _ (inferInstance : IsAffineHom f)
    exact @isAffine_of_isAffineHom
      (pullback ((Scheme.AffineEtale.Spec X).obj U).hom f)
      ((Scheme.AffineEtale.Spec X).obj U).left
      (pullback.fst ((Scheme.AffineEtale.Spec X).obj U).hom f) hfst htotal
  let V := EtaleAffineBasis.affineModel W
  let e : (moduleInverseImage R f).obj
      (free R X ((Scheme.AffineEtale.Spec X).obj U)) ≅
      free R S ((Scheme.AffineEtale.Spec S).obj V) :=
    freeModuleInverseImageIso R f ((Scheme.AffineEtale.Spec X).obj U) ≪≫
      (ModuleCat.Sheaf.freeRepresentableFunctor.{u + 1, u + 1, u, 0}
        S.smallEtaleTopology R).mapIso (EtaleAffineBasis.affineModelIso W).symm
  exact ⟨V, ⟨e⟩⟩

/-- The original native stage predicate is stable under the actual affine
base changes used in the projective-line coefficient-ring system. -/
theorem finiteColimitStage_inverseImage {X S : Scheme.{u}}
    (f : S ⟶ X) [IsAffineHom f]
    (F : ModuleSheaf R X)
    (hF : finiteColimitStages R X F) :
    finiteColimitStages R S ((moduleInverseImage R f).obj F) := by
  let : (moduleInverseImage R f).IsLeftAdjoint := (moduleImageAdjunction R f).isLeftAdjoint
  let P := finiteColimitStages R S
  let Q : ObjectProperty (ModuleSheaf R X) :=
    P.inverseImage (moduleInverseImage R f)
  have : P.IsClosedUnderIsomorphisms := by
    dsimp only [P, finiteColimitStages]
    infer_instance
  have : Q.IsClosedUnderIsomorphisms := by
    dsimp only [Q]
    infer_instance
  have hgen : generators R X ≤ Q := by
    rintro F ⟨U⟩
    obtain ⟨V, ⟨e⟩⟩ := exists_affineGeneratorInverseImageIso R f U
    have hp : P (free R S ((Scheme.AffineEtale.Spec S).obj V)) :=
      (generators R S).le_colimitsCardinalClosure
        Cardinal.aleph0.{u + 1} _ ⟨V⟩
    exact P.prop_of_iso e.symm hp
  have hclosure : finiteColimitStages R X ≤ Q := by
    apply (generators R X).colimitsCardinalClosure_le
      Cardinal.aleph0.{u + 1} ?_ hgen
    intro J _ hJ
    have : P.IsClosedUnderColimitsOfShape J :=
      (generators R S).isClosedUnderColimitsOfShape_colimitsCardinalClosure
        Cardinal.aleph0.{u + 1} J hJ
    dsimp only [Q]
    infer_instance
  exact hclosure F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
