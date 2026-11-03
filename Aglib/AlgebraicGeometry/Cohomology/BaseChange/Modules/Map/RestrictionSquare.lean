/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.RestrictionData.OriginalMates
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Iso
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Open

/-! # Original coefficient data for tensor restriction

Construct the original scalar modules, tensor mates and comparison isomorphisms
before specializing the coefficient objects to geometric pullbacks. The native
consumer supplies its existing geometric compatibility to these shared original
data; no tensor-square hypothesis is added.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The full original tensor comparison data and its original unit-tensor laws. -/
def moduleCoefficientTensorLinearization
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (N : Y.Modules)
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : X.Opens)
    (P : (p ⁻¹ᵁ U).toScheme.Modules)
    (φb : M.restrict U.ι ⟶ (Scheme.Modules.pushforward (p ∣_ U)).obj P)
    (e : P ≅ N.restrict (p ⁻¹ᵁ U).ι) (n : ℕ) :
    ModuleCat.TensorRestrictionData.{u, u + 1} σ := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom Y β N n V
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
  let := moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n
  let := moduleCohomologyModuleOfHom V.toScheme βV P n
  let g := ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
    (moduleCoefficientPullback p (M := M) (N := N) φp) n).app (op U)).hom
  let r := moduleCohomologyMapAlong b φb n
  let eX := sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n
  let eY := sheafHPrimeOpenRestrictionAddEquiv Y V (moduleAddSheaf Y N) n
  let eε := (moduleCohomologyIsoOfHom V.toScheme βV e.symm n).toLinearEquiv.toAddEquiv
  let data := ModuleCat.TensorRestrictionData.ofAdditive.{u, u + 1} σ
    (AddCommGrpCat.of (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U))
    (AddCommGrpCat.of (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n))
    (AddCommGrpCat.of (Sheaf.H'.{u + 1} (moduleAddSheaf Y N) n V))
    (AddCommGrpCat.of (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme (N.restrict a)) n))
    (AddCommGrpCat.of (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme P) n))
    (moduleHPrimeModuleOfHom X α M n U)
    (moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n)
    (moduleHPrimeModuleOfHom Y β N n V)
    (moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n)
    (moduleCohomologyModuleOfHom V.toScheme βV P n)
    g r eX eY eε
    (moduleHPrimeGeometricMap_smul p σ α β hσ φp n (op U))
    (fun t x => (moduleCohomologyRestrictionMap b σ αU βV hs φb n).hom.map_smul t x)
    (fun t x => (moduleHPrimeOpenLinearEquiv X α M U n).map_smul t x)
    (fun t x => (moduleHPrimeOpenLinearEquiv Y β N V n).map_smul t x)
    (fun t x => (moduleCohomologyMapOfHom V.toScheme βV e.inv n).map_smul t x)
  exact data

/-- Retain the original scalar data and both literal native mates with their unit formulas. -/
def moduleCoefficientTensorRestrictionData
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (N : Y.Modules)
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N) (U : X.Opens)
    (P : (p ⁻¹ᵁ U).toScheme.Modules)
    (φb : M.restrict U.ι ⟶ (Scheme.Modules.pushforward (p ∣_ U)).obj P)
    (e : P ≅ N.restrict (p ⁻¹ᵁ U).ι) (n : ℕ) :
    ModuleCat.TensorRestrictionData.{u, u + 1} σ := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom Y β N n V
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
  let := moduleCohomologyModuleOfHom V.toScheme βV (N.restrict a) n
  let := moduleCohomologyModuleOfHom V.toScheme βV P n
  let q := (moduleHPrimeTensorMap p σ α β hσ φp n).app (op U)
  let δ := moduleCohomologyTensorMap b σ αU βV hs φb n
  exact ModuleCat.TensorRestrictionData.ofMaps.{u, u + 1} σ
    (ModuleCat.of R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U))
    (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n))
    (ModuleCat.of S (Sheaf.H'.{u + 1} (moduleAddSheaf Y N) n V))
    (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme (N.restrict a)) n))
    (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme P) n))
    q δ
    (moduleHPrimeOpenLinearEquiv X α M U n).toModuleIso
    (moduleHPrimeOpenLinearEquiv Y β N V n).toModuleIso
    (moduleCohomologyIsoOfHom V.toScheme βV e.symm n)
    ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p φp) n).app (op U)).hom
    (moduleCohomologyMapAlong b φb n)
    (moduleHPrimeTensorMap_one_tmul p σ α β hσ φp n (op U))
    (moduleCohomologyTensorMap_one_tmul b σ αU βV hs φb n)

end AlgebraicGeometry.Scheme.Cohomology
