/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars

/-!
# Original cohomology from scalar-linear section comparisons

A natural scalar-linear comparison of the original section presheaves induces
an actual additive sheaf map and hence the original `Sheaf.H` map. The resulting
linear equivalence preserves coefficient squares and its degree-zero map is
exactly the given map on global sections. No flatness or acyclicity is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] (X : Scheme.{u}) (α : A →+* Γ(X, ⊤))
  {M N P : X.Modules}

/-- Forgetting a scalar-linear section map gives a map of the original additive sheaves. -/
def moduleSectionsAddSheafMap
    (φ : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N) :
    moduleAddSheaf X M ⟶ moduleAddSheaf X N where
  hom := Functor.whiskerRight φ (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})

/-- Original module coefficient maps are unchanged by the scalar-section construction. -/
@[simp]
theorem moduleSectionsAddSheafMap_ofCoefficient (φ : M ⟶ N) :
    moduleSectionsAddSheafMap X α ((moduleSectionsPresheafFunctor X α).map φ) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ := rfl

/-- Sectionwise linearity is precisely compatibility with structural scalar maps. -/
theorem moduleSectionsAddSheafMap_scalar
    (φ : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N) (a : A) :
    moduleScalarOfGlobal X M (α a) ≫ moduleSectionsAddSheafMap X α φ =
      moduleSectionsAddSheafMap X α φ ≫ moduleScalarOfGlobal X N (α a) := by
  ext U x
  exact (φ.app U).hom.map_smul a x

/-- The original cohomology map of a scalar-linear section comparison. -/
def moduleSectionsCohomologyMap
    (φ : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M q
    letI := moduleCohomologyModuleOfHom X α N q
    Sheaf.H.{u + 1} (moduleAddSheaf X M) q →ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) q := by
  letI := moduleCohomologyModuleOfHom X α M q
  letI := moduleCohomologyModuleOfHom X α N q
  exact {
    __ := Sheaf.H.map (moduleSectionsAddSheafMap X α φ) q
    map_smul' := fun a x => by
      change Sheaf.H.map _ q (Sheaf.H.map (moduleScalarOfGlobal X M (α a)) q x) =
        Sheaf.H.map (moduleScalarOfGlobal X N (α a)) q (Sheaf.H.map _ q x)
      rw [← Sheaf.H.map_comp_apply, moduleSectionsAddSheafMap_scalar,
        Sheaf.H.map_comp_apply] }

/-- A section-presheaf isomorphism gives an isomorphism of the original additive sheaves. -/
def moduleSectionsAddSheafIso
    (e : moduleSectionsPresheaf X α M ≅ moduleSectionsPresheaf X α N) :
    moduleAddSheaf X M ≅ moduleAddSheaf X N where
  hom := moduleSectionsAddSheafMap X α e.hom
  inv := moduleSectionsAddSheafMap X α e.inv
  hom_inv_id := by
    ext U x
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app U) x
  inv_hom_id := by
    ext U x
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app U) x

/-- Canonical equivalence on actual cohomology, retaining the specified scalar action. -/
def moduleSectionsCohomologyEquiv
    (e : moduleSectionsPresheaf X α M ≅ moduleSectionsPresheaf X α N) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M q
    letI := moduleCohomologyModuleOfHom X α N q
    Sheaf.H.{u + 1} (moduleAddSheaf X M) q ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf X N) q := by
  letI := moduleCohomologyModuleOfHom X α M q
  letI := moduleCohomologyModuleOfHom X α N q
  let eH := (Sheaf.functorH _ q).mapIso (moduleSectionsAddSheafIso X α e)
  exact LinearEquiv.ofBijective (moduleSectionsCohomologyMap X α e.hom q)
    eH.addCommGroupIsoToAddEquiv.bijective

/-- The forward map is the original induced cohomology map, not a chosen equivalence. -/
theorem moduleSectionsCohomologyEquiv_apply
    (e : moduleSectionsPresheaf X α M ≅ moduleSectionsPresheaf X α N) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :
    moduleSectionsCohomologyEquiv X α e q x =
      Sheaf.H.map (moduleSectionsAddSheafMap X α e.hom) q x := rfl

/-- Degree zero is the unchanged given section map on the whole scheme. -/
theorem moduleSectionsCohomologyEquiv_equiv₀
    (e : moduleSectionsPresheaf X α M ≅ moduleSectionsPresheaf X α N)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf X N) isTerminalTop
      (moduleSectionsCohomologyEquiv X α e 0 x) =
    e.hom.app (op ⊤) (Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x) :=
  (Sheaf.H.equiv₀_naturality isTerminalTop
    (moduleSectionsAddSheafMap X α e.hom) x).symm

/-- A commuting square of actual section maps remains commuting on original cohomology.
In particular this transports homogeneous multiplication without replacing its map. -/
theorem moduleSectionsCohomologyMap_square
    {M' N' : X.Modules}
    (e : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α N)
    (e' : moduleSectionsPresheaf X α M' ⟶ moduleSectionsPresheaf X α N')
    (f : moduleSectionsPresheaf X α M ⟶ moduleSectionsPresheaf X α M')
    (g : moduleSectionsPresheaf X α N ⟶ moduleSectionsPresheaf X α N')
    (h : f ≫ e' = e ≫ g) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) q) :
    moduleSectionsCohomologyMap X α e' q (moduleSectionsCohomologyMap X α f q x) =
      moduleSectionsCohomologyMap X α g q (moduleSectionsCohomologyMap X α e q x) := by
  have h' : moduleSectionsAddSheafMap X α f ≫ moduleSectionsAddSheafMap X α e' =
      moduleSectionsAddSheafMap X α e ≫ moduleSectionsAddSheafMap X α g := by
    ext U x
    exact congrArg (fun k => (k.app U).hom x) h
  change Sheaf.H.map _ q (Sheaf.H.map _ q x) = Sheaf.H.map _ q (Sheaf.H.map _ q x)
  rw [← Sheaf.H.map_comp_apply, h', Sheaf.H.map_comp_apply]

end AlgebraicGeometry.Scheme.Cohomology
