/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Injective.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing
/-! # Actual sections of restricted injective resolutions

Open restriction sends the given ambient injective resolution to a genuine
injective resolution of the restricted sheaf. Its original additive section
complex is identified with sections on the image open using `restrictAppIso`.
For an affine open immersion and quasicoherent coefficients, positive-degree
exactness follows from the proved affine theorem over an arbitrary ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Open restriction of the given injective resolution, with its original terms. -/
def restrictInjectiveResolution (M : X.Modules) (I : InjectiveResolution M) :
    InjectiveResolution (M.restrict j) where
  cocomplex := ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).obj I.cocomplex
  ι := (singleMapHomologicalComplex (Scheme.Modules.restrictFunctor j) (.up ℕ) 0).inv.app M ≫
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).map I.ι
  injective n := by
    change Injective ((Scheme.Modules.restrictFunctor j).obj (I.cocomplex.X n))
    infer_instance

/-- Forgetting only scalar structure identifies affine global sections with
the original additive global sections. -/
def affineSectionsForgetIso (R : CommRingCat.{u}) :
    moduleSpecΓFunctor (R := R) ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      sectionsFunctor (Spec R) ⊤ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Homology of the original ambient resolution's sections on an affine open
is the actual affine right-derived global-section module, forgetting scalars.
No quasicoherence hypothesis is required for the comparison. -/
def affineOpenHomologyIsoRightDerived {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (I : InjectiveResolution M) (n : ℕ) :
    (((sectionsFunctor X j.opensRange).mapHomologicalComplex _).obj I.cocomplex).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((moduleSpecΓFunctor.rightDerived n).obj (M.restrict j)) := by
  let J := restrictInjectiveResolution j M I
  let L := (moduleSpecΓFunctor.mapHomologicalComplex _).obj J.cocomplex
  let F := forget₂ (ModuleCat R) AddCommGrpCat
  let e := (Functor.mapHomologicalComplexCompIso (affineSectionsForgetIso R) (.up ℕ)).app
    J.cocomplex ≪≫ restrictedSectionsComplexIso j I.cocomplex
  exact (homologyFunctor _ _ n).mapIso e.symm ≪≫ (L.sc n).mapHomologyIso F ≪≫
    F.mapIso (J.isoRightDerivedObj moduleSpecΓFunctor n).symm

/-- Every original injective-resolution section complex is acyclic in positive
degrees on an affine open, for quasicoherent coefficients. -/
theorem affineOpen_injectiveResolution_exact_succ {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) (n : ℕ) :
    (((sectionsFunctor X j.opensRange).mapHomologicalComplex _).obj I.cocomplex).ExactAt
      (n + 1) := by
  let J := restrictInjectiveResolution j M I
  have h := AffineDerived.globalSections_injectiveResolution_exact_succ (M.restrict j) J n
  have h' : (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex _).obj
      ((moduleSpecΓFunctor.mapHomologicalComplex _).obj J.cocomplex)).ExactAt (n + 1) :=
    h.map (forget₂ (ModuleCat R) AddCommGrpCat)
  have e := (Functor.mapHomologicalComplexCompIso (affineSectionsForgetIso R) (.up ℕ)).app
    J.cocomplex
  exact (h'.of_iso e).of_iso (restrictedSectionsComplexIso j I.cocomplex)

end AlgebraicGeometry.Scheme.Modules
