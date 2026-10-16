/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistExt
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Linear
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear

/-!
# Original structural linearity of the twist Ext comparison

The native linear Ext adjunction for the actual opposite-twist tensor
functor refines the existing additive comparison. The underlying additive
map, structural category action and original large sheaf cohomology are
unchanged. No field, Noetherianity or finiteness hypothesis is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Precomposition by the original tensor-unit isomorphism is linear on native Ext. -/
def twistingExtPrecomposeLinearEquiv (α : R →+* Γ(ProjectiveSpace R ι, ⊤))
    (a b : ℤ) (q : ℕ) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (twistingSheaf R ι a) (twistingSheaf R ι b) q ≃ₗ[R]
      Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        ((twistingTensorEquivalence R ι a).functor.obj
          (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf))
        (twistingSheaf R ι b) q := by
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  refine {
    __ := (((extFunctor (C := (ProjectiveSpace R ι).Modules) q).mapIso
      (twistingTensorUnitIso R ι a).op).app
        (twistingSheaf R ι b)).addCommGroupIsoToAddEquiv
    map_smul' := ?_ }
  intro r x
  change (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp (r • x) (Nat.zero_add q) =
    r • (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp x (Nat.zero_add q)
  exact Ext.comp_smul _ _ _ _

/-- The original opposite-twist adjunction is linear on native Ext for the chosen action. -/
def twistingExtAdjunctionLinearEquiv (α : R →+* Γ(ProjectiveSpace R ι, ⊤))
    (a b : ℤ) (q : ℕ) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        ((twistingTensorEquivalence R ι a).functor.obj
          (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf))
        (twistingSheaf R ι b) q ≃ₗ[R]
      Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf)
        ((twistingTensorEquivalence R ι a).inverse.obj (twistingSheaf R ι b)) q := by
  let X := ProjectiveSpace R ι
  letI := moduleCategoryLinearOfHom X α
  let T := twistingTensorEquivalence R ι a
  letI : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  letI : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  letI : Functor.Linear R T.inverse := inferInstanceAs
    (Functor.Linear R (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))))
  exact T.toAdjunction.extLinearEquiv R

/-- Postcomposition by original twist multiplication is linear on native Ext. -/
def twistingExtPostcomposeLinearEquiv (α : R →+* Γ(ProjectiveSpace R ι, ⊤))
    (a b : ℤ) (q : ℕ) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf)
        ((twistingTensorEquivalence R ι a).inverse.obj (twistingSheaf R ι b)) q ≃ₗ[R]
      Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
        (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf)
        (twistingSheaf R ι (-a + b)) q := by
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  refine {
    __ := ((extFunctorObj (C := (ProjectiveSpace R ι).Modules)
      (SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf) q).mapIso
        (twistingTensorIso R ι (-a) b)).addCommGroupIsoToAddEquiv
    map_smul' := ?_ }
  intro r x
  change (r • x).comp (Ext.mk₀ (twistingTensorIso R ι (-a) b).hom) (Nat.add_zero q) =
    r • x.comp (Ext.mk₀ (twistingTensorIso R ι (-a) b).hom) (Nat.add_zero q)
  exact Ext.smul_comp _ _ _ _

/-- The original twist Ext/cohomology comparison is linear over the actual structural ring.
Its underlying additive equivalence is literally the existing comparison. -/
def twistingExtCohomologyLinearEquiv (a b : ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-a + b)) q
    Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheaf R ι b) q ≃ₗ[R]
        Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
          (twistingSheaf R ι (-a + b))) q := by
  let X := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom X α
  letI := moduleCohomologyModuleOfHom X α (twistingSheaf R ι (-a + b)) q
  let e₁ := twistingExtPrecomposeLinearEquiv R ι α a b q
  let e₂ := twistingExtAdjunctionLinearEquiv R ι α a b q
  let e₃ := twistingExtPostcomposeLinearEquiv R ι α a b q
  let e₄ := moduleExtCohomologyLinearEquivOfCategory X α (twistingSheaf R ι (-a + b)) q
  refine { __ := twistingExtCohomologyAddEquiv R ι a b q, map_smul' := ?_ }
  intro r x
  change e₄ (e₃ (e₂ (e₁ (r • x)))) = r • e₄ (e₃ (e₂ (e₁ x)))
  rw [e₁.map_smul, e₂.map_smul, e₃.map_smul, e₄.map_smul]

/-- The linear refinement retains the existing original additive equivalence by definition. -/
theorem twistingExtCohomologyLinearEquiv_toAddEquiv (a b : ℤ) (q : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-a + b)) q
    (twistingExtCohomologyLinearEquiv R ι a b q).toAddEquiv =
      twistingExtCohomologyAddEquiv R ι a b q := rfl

/-- The existing additive twist comparison retains native coefficient functoriality. -/
theorem twistingExtCohomologyAddEquiv_naturality_right (a b c : ℤ)
    (φ : twistingSheaf R ι b ⟶ twistingSheaf R ι c) (q : ℕ)
    (x : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheaf R ι b) q) :
    twistingExtCohomologyAddEquiv R ι a c q (x.comp (Ext.mk₀ φ) (Nat.add_zero q)) =
      Sheaf.H.map ((SheafOfModules.toSheaf.{u} (ProjectiveSpace R ι).ringCatSheaf).map
        ((twistingTensorIso R ι (-a) b).inv ≫
          (twistingTensorEquivalence R ι a).inverse.map φ ≫
            (twistingTensorIso R ι (-a) c).hom)) q
        (twistingExtCohomologyAddEquiv R ι a b q x) := by
  let X := ProjectiveSpace R ι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let T := twistingTensorEquivalence R ι a
  let : T.functor.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι a)).Additive
  let : T.inverse.Additive := inferInstanceAs
    (moduleTensorLeftFunctor X (twistingSheaf R ι (-a))).Additive
  let δ : twistingSheaf R ι (-a + b) ⟶ twistingSheaf R ι (-a + c) :=
    (twistingTensorIso R ι (-a) b).inv ≫ T.inverse.map φ ≫
      (twistingTensorIso R ι (-a) c).hom
  let y := (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp x (Nat.zero_add q)
  change moduleExtCohomologyMap X (twistingSheaf R ι (-a + c)) q
      ((T.toAdjunction.extEquiv
        ((Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp
          (x.comp (Ext.mk₀ φ) (Nat.add_zero q)) (Nat.zero_add q))).comp
            (Ext.mk₀ (twistingTensorIso R ι (-a) c).hom) (Nat.add_zero q)) =
    Sheaf.H.map ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map δ) q
      (moduleExtCohomologyMap X (twistingSheaf R ι (-a + b)) q
        ((T.toAdjunction.extEquiv y).comp
          (Ext.mk₀ (twistingTensorIso R ι (-a) b).hom) (Nat.add_zero q)))
  rw [← moduleExtCohomologyMap_naturality]
  apply congrArg (moduleExtCohomologyMap X (twistingSheaf R ι (-a + c)) q)
  have hp : (Ext.mk₀ (twistingTensorUnitIso R ι a).hom).comp
        (x.comp (Ext.mk₀ φ) (Nat.add_zero q)) (Nat.zero_add q) =
      y.comp (Ext.mk₀ φ) (Nat.add_zero q) :=
    (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.zero_add q)).symm
  rw [hp, T.toAdjunction.extEquiv_naturality_right₀]
  dsimp only [δ]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_assoc]


/-- The linear refinement retains the original cohomology coefficient map. The coefficient
arrow is the original opposite-twist tensor map conjugated by the actual multiplication isos. -/
theorem twistingExtCohomologyLinearEquiv_naturality_right (a b c : ℤ)
    (φ : twistingSheaf R ι b ⟶ twistingSheaf R ι c) (q : ℕ)
    (x : Ext.{u + 1} (C := (ProjectiveSpace R ι).Modules)
      (twistingSheaf R ι a) (twistingSheaf R ι b) q) :
    twistingExtCohomologyLinearEquiv R ι a c q (x.comp (Ext.mk₀ φ) (Nat.add_zero q)) =
      moduleCohomologyMapOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        ((twistingTensorIso R ι (-a) b).inv ≫
          (twistingTensorEquivalence R ι a).inverse.map φ ≫
            (twistingTensorIso R ι (-a) c).hom) q
        (twistingExtCohomologyLinearEquiv R ι a b q x) :=
  twistingExtCohomologyAddEquiv_naturality_right R ι a b c φ q x

end AlgebraicGeometry.Scheme.Cohomology
