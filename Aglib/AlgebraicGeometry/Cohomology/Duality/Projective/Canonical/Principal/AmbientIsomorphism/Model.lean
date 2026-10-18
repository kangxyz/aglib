/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.SourceIsomorphism

/-!
# Actual affine-open transport on the original closed-adjoint model

The original restriction unit and closed-adjoint open comparison act on the
supplied injective resolution. The original extension comparison retains
its nonnegative terms, and native homology carries these same maps to the
affine Ext model.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open HomologicalComplex CochainComplex CochainComplex.HomComplex
open scoped TensorProduct ChangeOfRings

universe u w v
namespace AlgebraicGeometry.Scheme.Modules

section Geometry
variable {A A' B B' : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))

private def ambientOpenSectionsNat :
    closedImmersionRightAdjoint (Spec.map σ) ⋙ moduleSpecΓFunctor (R := B) ⟶
      (restrictFunctor (Spec.map φ) ⋙ closedImmersionRightAdjoint (Spec.map τ)) ⋙
        (moduleSpecΓFunctor (R := B') ⋙ ModuleCat.restrictScalars ψ.hom) :=
  Functor.whiskerLeft (closedImmersionRightAdjoint (Spec.map σ))
      (affineOpenRestrictionSectionsNat ψ) ≫
    (Functor.associator (closedImmersionRightAdjoint (Spec.map σ))
      (restrictFunctor (Spec.map ψ))
      (moduleSpecΓFunctor (R := B') ⋙ ModuleCat.restrictScalars ψ.hom)).inv ≫
    Functor.whiskerRight
      (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
        (Spec.map σ) (Spec.map φ) h).hom
      (moduleSpecΓFunctor (R := B') ⋙ ModuleCat.restrictScalars ψ.hom)

private theorem ambientOpenSectionsNat_app (N : (Spec A).Modules) :
    (ambientOpenSectionsNat φ σ τ ψ h).app N =
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N := by
  simp only [ambientOpenSectionsNat, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
    affineOpenRestrictionSectionsNat_app]
  rfl

/-- The original affine open comparison commutes with every coefficient arrow. -/
@[reassoc] theorem canonicalAmbientOpenSections_naturality
    {N P : (Spec A).Modules} (f : N ⟶ P) :
    moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map σ)).map f) ≫
        closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h P =
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h N ≫
        (ModuleCat.restrictScalars ψ.hom).map
          (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map τ)).map
            ((restrictFunctor (Spec.map φ)).map f))) := by
  simpa only [ambientOpenSectionsNat_app, Functor.comp_map, Functor.comp_obj] using
    (ambientOpenSectionsNat φ σ τ ψ h).naturality f

variable {L : (Spec A).Modules} (J : InjectiveResolution L)

/-- The original closed-adjoint open comparison on the supplied sheaf resolution,
with its unchanged restriction and extension isomorphisms. -/
@[no_expose] def canonicalAmbientModelOpenIso :
    ((restrictFunctor (Spec.map ψ)).mapHomologicalComplex (.up ℤ)).obj
      (((closedImmersionRightAdjoint (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex) ≅
      ((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).obj
        (affineOpenRestrictedInjectiveResolution φ J).cochainComplex :=
  (Functor.mapHomologicalComplexCompIso
      (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
        (Spec.map σ) (Spec.map φ) h) (.up ℤ)).app J.cochainComplex ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictFunctor (Spec.map φ) ⋙ closedImmersionRightAdjoint (Spec.map τ)))
      (.up ℤ)).symm.app J.cochainComplex) ≪≫
    ((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).mapIso
      (J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ)) ComplexShape.embeddingUpNat)

/-- The model isomorphism retains the actual ordinary open comparison at every degree. -/
theorem canonicalAmbientModelOpenIso_hom_f (n : ℤ) :
    (canonicalAmbientModelOpenIso φ σ τ ψ h J).hom.f n =
      (closedImmersionRightAdjointOpenIso (Spec.map ψ) (Spec.map τ)
        (Spec.map σ) (Spec.map φ) h).hom.app (J.cochainComplex.X n) ≫
        (closedImmersionRightAdjoint (Spec.map τ)).map
          ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ))
            ComplexShape.embeddingUpNat).hom.f n) := by
  rfl

private def ambientRawResolutionMap :
    closedImmersionSourceResolutionComplex J σ ⟶
      ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := B')).mapHomologicalComplex (.up ℤ)).obj
          (((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).obj
            (((restrictFunctor (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj
              J.cochainComplex))) where
  f n := closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cochainComplex.X n)
  comm' n m _ := (canonicalAmbientOpenSections_naturality φ σ τ ψ h
    (J.cochainComplex.d n m)).symm

/-- The actual geometric affine-open map on the original sections resolution. -/
@[no_expose] def canonicalAmbientResolutionMap :
    closedImmersionSourceResolutionComplex J σ ⟶
      ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionSourceResolutionComplex (affineOpenRestrictedInjectiveResolution φ J) τ) :=
  ambientRawResolutionMap φ σ τ ψ h J ≫
    ((ModuleCat.restrictScalars ψ.hom).mapHomologicalComplex (.up ℤ)).map
      (((moduleSpecΓFunctor (R := B')).mapHomologicalComplex (.up ℤ)).map
        (((closedImmersionRightAdjoint (Spec.map τ)).mapHomologicalComplex (.up ℤ)).map
          (J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ))
            ComplexShape.embeddingUpNat).hom))

/-- Each original sections component is the open-square map followed by the
same restriction-extension component. -/
theorem canonicalAmbientResolutionMap_f (n : ℤ) :
    (canonicalAmbientResolutionMap φ σ τ ψ h J).f n =
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cochainComplex.X n) ≫
        (ModuleCat.restrictScalars ψ.hom).map
          (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map τ)).map
            ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ))
              ComplexShape.embeddingUpNat).hom.f n))) := by
  rfl

/-- The sections resolution map is induced by the actual sheaf-model open isomorphism. -/
theorem canonicalAmbientResolutionMap_model_f (n : ℤ) :
    (canonicalAmbientResolutionMap φ σ τ ψ h J).f n =
      affineOpenRestrictionSectionsMap ψ
        ((closedImmersionRightAdjoint (Spec.map σ)).obj (J.cochainComplex.X n)) ≫
      (ModuleCat.restrictScalars ψ.hom).map
        (moduleSpecΓFunctor.map ((canonicalAmbientModelOpenIso φ σ τ ψ h J).hom.f n)) := by
  rw [canonicalAmbientResolutionMap_f, canonicalAmbientModelOpenIso_hom_f]
  simp only [closedImmersionRightAdjointAffineOpenSections,
    affineOpenRestrictionSectionsMap, Functor.map_comp, Category.assoc]

/-- Native homology of the original affine-open sections map. -/
def canonicalAmbientHomologyMap (n : ℤ) :
    (closedImmersionSourceResolutionComplex J σ).homology n ⟶
      (ModuleCat.restrictScalars ψ.hom).obj
        ((closedImmersionSourceResolutionComplex
          (affineOpenRestrictedInjectiveResolution φ J) τ).homology n) :=
  homologyMap (canonicalAmbientResolutionMap φ σ τ ψ h J) n ≫
    (((closedImmersionSourceResolutionComplex
      (affineOpenRestrictedInjectiveResolution φ J) τ).sc n).mapHomologyIso
        (ModuleCat.restrictScalars ψ.hom)).hom

private def ambientCyclesMap (n : ℤ)
    (z : (closedImmersionSourceResolutionComplex J σ).cycles n) :
    (closedImmersionSourceResolutionComplex
      (affineOpenRestrictedInjectiveResolution φ J) τ).cycles n :=
  (((closedImmersionSourceResolutionComplex
    (affineOpenRestrictedInjectiveResolution φ J) τ).sc n).mapCyclesIso
      (ModuleCat.restrictScalars ψ.hom)).hom
    (cyclesMap (canonicalAmbientResolutionMap φ σ τ ψ h J) n z)

private theorem ambientCyclesMap_i (n : ℤ)
    (z : (closedImmersionSourceResolutionComplex J σ).cycles n) :
    (closedImmersionSourceResolutionComplex
      (affineOpenRestrictedInjectiveResolution φ J) τ).iCycles n
        (ambientCyclesMap φ σ τ ψ h J n z) =
      (canonicalAmbientResolutionMap φ σ τ ψ h J).f n
        ((closedImmersionSourceResolutionComplex J σ).iCycles n z) := by
  have h₁ := ConcreteCategory.congr_hom
    (((closedImmersionSourceResolutionComplex
      (affineOpenRestrictedInjectiveResolution φ J) τ).sc n).mapCyclesIso_hom_iCycles
        (ModuleCat.restrictScalars ψ.hom))
    (cyclesMap (canonicalAmbientResolutionMap φ σ τ ψ h J) n z)
  have h₂ := ConcreteCategory.congr_hom
    (cyclesMap_i (canonicalAmbientResolutionMap φ σ τ ψ h J) n) z
  exact h₁.trans h₂

private theorem ambientHomologyMap_π (n : ℤ)
    (z : (closedImmersionSourceResolutionComplex J σ).cycles n) :
    canonicalAmbientHomologyMap φ σ τ ψ h J n
        ((closedImmersionSourceResolutionComplex J σ).homologyπ n z) =
      (closedImmersionSourceResolutionComplex
        (affineOpenRestrictedInjectiveResolution φ J) τ).homologyπ n
          (ambientCyclesMap φ σ τ ψ h J n z) := by
  have h₁ := ConcreteCategory.congr_hom
    (homologyπ_naturality (canonicalAmbientResolutionMap φ σ τ ψ h J) n) z
  have h₂ := ConcreteCategory.congr_hom
    (ShortComplex.homologyπ_mapHomologyIso_hom (ModuleCat.restrictScalars ψ.hom)
      ((closedImmersionSourceResolutionComplex
        (affineOpenRestrictedInjectiveResolution φ J) τ).sc n))
    (cyclesMap (canonicalAmbientResolutionMap φ σ τ ψ h J) n z)
  exact (congrArg (fun y => (((closedImmersionSourceResolutionComplex
    (affineOpenRestrictedInjectiveResolution φ J) τ).sc n).mapHomologyIso
      (ModuleCat.restrictScalars ψ.hom)).hom y) h₁).trans h₂

/-- At each retained resolution degree, the actual geometric map is precisely
the original ordinary open-square map. -/
theorem canonicalAmbientResolutionMap_term (n : ℕ)
    (m : (closedImmersionSourceResolutionComplex J σ).X (n : ℤ)) :
    moduleSpecΓFunctor.map
        ((closedImmersionRightAdjoint (Spec.map τ)).map
          ((affineOpenRestrictedInjectiveResolution φ J).cochainComplexXIso n n rfl).hom)
      ((canonicalAmbientResolutionMap φ σ τ ψ h J).f (n : ℤ) m) =
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cocomplex.X n)
        (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map σ)).map
          (J.cochainComplexXIso n n rfl).hom) m) := by
  have hn := ConcreteCategory.congr_hom
    (canonicalAmbientOpenSections_naturality φ σ τ ψ h (J.cochainComplexXIso n n rfl).hom) m
  have he := J.cocomplex.mapExtendIso_hom_f_extendXIso
    (restrictFunctor (Spec.map φ)) ComplexShape.embeddingUpNat (i := n) (j := (n : ℤ)) rfl
  rw [canonicalAmbientResolutionMap_f]
  change moduleSpecΓFunctor.map
      ((closedImmersionRightAdjoint (Spec.map τ)).map
        ((affineOpenRestrictedInjectiveResolution φ J).cochainComplexXIso n n rfl).hom)
    (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map τ)).map
      ((J.cocomplex.mapExtendIso (restrictFunctor (Spec.map φ))
        ComplexShape.embeddingUpNat).hom.f (n : ℤ)))
      (closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h
        (J.cochainComplex.X (n : ℤ)) m)) = _
  erw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp, he]
  exact hn.symm

end Geometry
section Cycles
variable {R S : CommRingCat.{u}} (κ : R ⟶ S) [IsClosedImmersion (Spec.map κ)]
  {L : (Spec R).Modules} (J : InjectiveResolution L)

private def affineCycleTerm (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J κ).cycles (n : ℤ)) :
    moduleSpecΓFunctor.obj
      ((closedImmersionRightAdjoint (Spec.map κ)).obj (J.cocomplex.X n)) :=
  moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map κ)).map
    (J.cochainComplexXIso n n rfl).hom)
      ((closedImmersionSourceResolutionComplex J κ).iCycles (n : ℤ) z)

private theorem affineCycleTerm_d (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J κ).cycles (n : ℤ)) :
    moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map κ)).map
        (J.cocomplex.d n (n + 1))) (affineCycleTerm κ J n z) = 0 := by
  let G := closedImmersionRightAdjoint (Spec.map κ) ⋙ moduleSpecΓFunctor (R := S)
  let K := closedImmersionSourceResolutionComplex J κ
  apply (ConcreteCategory.bijective_of_isIso
    (G.map (J.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv)).1
  rw [map_zero]
  change G.map (J.cochainComplexXIso ((n + 1 : ℕ) : ℤ) (n + 1) rfl).inv
    (G.map (J.cocomplex.d n (n + 1))
      (G.map (J.cochainComplexXIso n n rfl).hom (K.iCycles (n : ℤ) z))) = 0
  have hz := ConcreteCategory.congr_hom (K.iCycles_d (n : ℤ) ((n + 1 : ℕ) : ℤ)) z
  change G.map (J.cochainComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ))
    (K.iCycles (n : ℤ) z) = 0 at hz
  rw [J.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl] at hz
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using hz

variable [L.IsQuasicoherent]

private theorem affineCycleTerm_cycle (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J κ).cycles (n : ℤ)) :
    ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars κ.hom).obj (ModuleCat.of S S))
        (Y := (moduleSpecΓFunctor (R := R)).obj (J.cocomplex.X n))
        (closedImmersionRightAdjointSectionsLinearEquiv κ (J.cocomplex.X n)
          (affineCycleTerm κ J n z)) ≫
      (AffineDerived.globalSectionsInjectiveResolution J).cocomplex.d n (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  have hh := ConcreteCategory.congr_hom
    ((closedImmersionRightAdjointAffineIso κ).hom.naturality (J.cocomplex.d n (n + 1)))
    (affineCycleTerm κ J n z)
  have hh' := congrArg (fun x => ModuleCat.CoextendScalars.equiv κ.hom _ x b) hh
  change closedImmersionRightAdjointSectionsLinearEquiv κ (J.cocomplex.X (n + 1))
      (moduleSpecΓFunctor.map ((closedImmersionRightAdjoint (Spec.map κ)).map
        (J.cocomplex.d n (n + 1))) (affineCycleTerm κ J n z)) b =
    moduleSpecΓFunctor.map (J.cocomplex.d n (n + 1))
      (closedImmersionRightAdjointSectionsLinearEquiv κ (J.cocomplex.X n)
        (affineCycleTerm κ J n z) b) at hh'
  rw [affineCycleTerm_d, map_zero] at hh'
  exact hh'.symm

private theorem affineCycleTerm_component (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J κ).cycles (n : ℤ)) :
    ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars κ.hom).obj (ModuleCat.of S S))
        (Y := (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex.X (n : ℤ))
        (ModuleCat.CoextendScalars.equiv κ.hom _
          ((affineClosedRightAdjointResolutionSectionsIso κ J).hom.f (n : ℤ)
            ((closedImmersionSourceResolutionComplex J κ).iCycles (n : ℤ) z))) ≫
      ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).hom =
    ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars κ.hom).obj (ModuleCat.of S S))
      (Y := (moduleSpecΓFunctor (R := R)).obj (J.cocomplex.X n))
      (closedImmersionRightAdjointSectionsLinearEquiv κ (J.cocomplex.X n)
        (affineCycleTerm κ J n z)) := by
  have h₁ := ConcreteCategory.congr_hom
    (affineClosedRightAdjointResolutionSectionsIso_hom_f κ J n)
    ((closedImmersionSourceResolutionComplex J κ).iCycles (n : ℤ) z)
  have h₂ := ConcreteCategory.congr_hom
    ((closedImmersionRightAdjointAffineIso κ).hom.naturality (J.cochainComplexXIso n n rfl).hom)
    ((closedImmersionSourceResolutionComplex J κ).iCycles (n : ℤ) z)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact congrArg (fun x => ModuleCat.CoextendScalars.equiv κ.hom
    ((AffineDerived.globalSectionsInjectiveResolution J).cocomplex.X n) x b)
      (h₁.trans h₂.symm)

variable [HasExt.{w} (ModuleCat.{u} R)]

private theorem affineCycleTerm_class (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J κ).cycles (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv κ J n
        ((closedImmersionSourceResolutionComplex J κ).homologyπ (n : ℤ) z) =
      (AffineDerived.globalSectionsInjectiveResolution J).extMk
        (ModuleCat.ofHom
          (X := (ModuleCat.restrictScalars κ.hom).obj (ModuleCat.of S S))
          (Y := (moduleSpecΓFunctor (R := R)).obj (J.cocomplex.X n))
          (closedImmersionRightAdjointSectionsLinearEquiv κ (J.cocomplex.X n)
            (affineCycleTerm κ J n z)))
        (n + 1) rfl (affineCycleTerm_cycle κ J n z) := by
  let I := AffineDerived.globalSectionsInjectiveResolution J
  let K := closedImmersionSourceResolutionComplex J κ
  let Q := ((ModuleCat.coextendScalars κ.hom).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := affineClosedRightAdjointResolutionSectionsIso κ J
  rw [affineClosedRightAdjointResolutionExtAddEquiv_homologyπ]
  change I.extEquivCohomologyClass.symm _ = I.extMk _ (n + 1) rfl _
  apply I.extEquivCohomologyClass.injective
  simp only [Equiv.apply_symm_apply, I.extEquivCohomologyClass_extMk]
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  rw [ModuleCat.coextendScalarsCyclesIso_coe,
    ModuleCat.coextendScalarsCochainEquiv_apply]
  have hi : Q.iCycles (n : ℤ) (cyclesMap E.hom (n : ℤ) z) =
      E.hom.f (n : ℤ) (K.iCycles (n : ℤ) z) :=
    ConcreteCategory.congr_hom (cyclesMap_i E.hom (n : ℤ)) z
  rw [hi]
  congr 1
  have ht := congrArg (fun f => f ≫ (I.cochainComplexXIso n n rfl).inv)
    (affineCycleTerm_component κ J n z)
  simpa only [I, E, K, Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht
end Cycles

section ExtTransport
variable {A A' B B' : CommRingCat.{u}}
  (φ : A ⟶ A') (σ : A ⟶ B) (τ : A' ⟶ B') (ψ : B ⟶ B')
  [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)]
  [IsClosedImmersion (Spec.map σ)] [IsClosedImmersion (Spec.map τ)]
  (h : IsPullback (Spec.map ψ) (Spec.map τ) (Spec.map σ) (Spec.map φ))
  {L : (Spec A).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

local instance : ((restrictFunctor (Spec.map φ)).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A').ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map φ)).symm.app L) (isQuasicoherent_pullback φ L)

omit [L.IsQuasicoherent] in
private theorem ambientCyclesMap_term (n : ℕ)
    (z : (closedImmersionSourceResolutionComplex J σ).cycles (n : ℤ)) :
    affineCycleTerm τ (affineOpenRestrictedInjectiveResolution φ J) n
        (ambientCyclesMap φ σ τ ψ h J (n : ℤ) z) =
      closedImmersionRightAdjointAffineOpenSections φ σ τ ψ h (J.cocomplex.X n)
        (affineCycleTerm σ J n z) := by
  dsimp only [affineCycleTerm]
  rw [ambientCyclesMap_i, canonicalAmbientResolutionMap_term]

/-- Native Ext of the actual affine-open model map is exact scalar extension,
with the original source and coefficient comparison maps. -/
theorem canonicalAmbientHomologyMap_ext
    (η : (ModuleCat.extendScalars φ.hom).obj
        ((ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B)) ≅
      (ModuleCat.restrictScalars τ.hom).obj (ModuleCat.of B' B'))
    (hη : ∀ b : B, η.hom
      ((1 : A') ⊗ₜ[A,φ.hom]
        (show (ModuleCat.restrictScalars σ.hom).obj (ModuleCat.of B B) from b)) = ψ b)
    (hφ : φ.hom.Flat) [HasExt.{w} (ModuleCat.{u} A)]
    [HasExt.{v} (ModuleCat.{u} A')] (n : ℕ)
    (x : (closedImmersionSourceResolutionComplex J σ).homology (n : ℤ)) :
    let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars φ.hom
    letI : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hφ
    letI : PreservesFiniteColimits F :=
      ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hφ
    affineClosedRightAdjointResolutionExtAddEquiv τ
        (affineOpenRestrictedInjectiveResolution φ J) n
        (canonicalAmbientHomologyMap φ σ τ ψ h J (n : ℤ) x) =
      ((Ext.mk₀ η.inv).comp
        ((affineClosedRightAdjointResolutionExtAddEquiv σ J n x).mapExactFunctor F)
        (zero_add n)).comp
        (Ext.mk₀ (affineRestrictGlobalSectionsIso φ L).hom) (add_zero n) := by
  let F : ModuleCat.{u} A ⥤ ModuleCat.{u} A' := ModuleCat.extendScalars φ.hom
  let : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hφ
  let : PreservesFiniteColimits F :=
    ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ hφ
  let K := closedImmersionSourceResolutionComplex J σ
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n : ℤ))).mp inferInstance x
  rw [ambientHomologyMap_π, affineCycleTerm_class, affineCycleTerm_class]
  have hm := ambientCyclesMap_term φ σ τ ψ h J n z
  have hh := (canonicalAmbientAffineOpenExtMk φ σ τ ψ h η hη J hφ n
    (affineCycleTerm σ J n z) (affineCycleTerm_cycle σ J n z)).symm
  simp only [canonicalAmbientAffineHom, canonicalAmbientLocalΓResolution, ← hm] at hh
  exact hh
end ExtTransport

end AlgebraicGeometry.Scheme.Modules
