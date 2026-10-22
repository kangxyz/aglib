/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineSystem

/-! # Recover original affine formal morphisms from their section maps

The native finite-type sheaf/module equivalence recovers every original stage
map. Naturality and uniqueness are checked by its faithfulness, without
introducing a replacement formal category.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]

/-- Recover a coherent affine map by the native finite-module equivalence. -/
def affineHomOfSections (M N : (Spec B).CoherentSheaf)
    (q : moduleSpecΓFunctor.obj M.obj ⟶ moduleSpecΓFunctor.obj N.obj) : M.obj ⟶ N.obj :=
  ((QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence B).functor.preimage
    (ObjectProperty.homMk q)).hom

/-- The recovered map induces exactly the specified original section map. -/
theorem affineHomOfSections_map (M N : (Spec B).CoherentSheaf)
    (q : moduleSpecΓFunctor.obj M.obj ⟶ moduleSpecΓFunctor.obj N.obj) :
    moduleSpecΓFunctor.map (affineHomOfSections M N q) = q :=
  congrArg (fun f => f.hom)
    ((QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence B).functor.map_preimage
      (ObjectProperty.homMk q))

/-- Original global sections detect equality of coherent affine morphisms. -/
theorem affineHom_ext (M N : (Spec B).CoherentSheaf) (a b : M.obj ⟶ N.obj)
    (h : moduleSpecΓFunctor.map a = moduleSpecΓFunctor.map b) : a = b := by
  have he : (ObjectProperty.homMk a : M ⟶ N) = ObjectProperty.homMk b := by
    apply (QuasiCoherent.finiteTypeSheavesSpecModuleEquivalence B).functor.map_injective
    exact ObjectProperty.hom_ext _ h
  exact congrArg (fun f => f.hom) he

namespace AdicSystem
variable {K : (Spec B).IdealSheafData} (F G : AdicSystem (Spec B) K)

/-- The original coherent coefficient at an arbitrary index. -/
abbrev affineCoefficient (j : ℕᵒᵖ) : (Spec B).CoherentSheaf :=
  ⟨F.obj.obj j, F.property.coherent j.unop⟩

/-- Lift an entire compatible family of original affine section maps. -/
def affineHomOfFamily
    (q : ∀ j, F.affineSectionsTower.obj j →ₗ[B] G.affineSectionsTower.obj j)
    (hq : ∀ {j k} (a : j ⟶ k) x,
      q k (F.affineSectionsTower.map a x) = G.affineSectionsTower.map a (q j x)) : F ⟶ G :=
  ObjectProperty.homMk
    { app j := affineHomOfSections (F.affineCoefficient j) (G.affineCoefficient j)
        (show F.affineSectionsTower.obj j ⟶ G.affineSectionsTower.obj j from
          ModuleCat.ofHom (X := F.affineSectionsTower.obj j)
            (Y := G.affineSectionsTower.obj j) (q j))
      naturality j k a := by
        apply affineHom_ext (F.affineCoefficient j) (G.affineCoefficient k)
        rw [Functor.map_comp, Functor.map_comp, affineHomOfSections_map,
          affineHomOfSections_map]
        apply ModuleCat.hom_ext
        ext x
        exact hq a x }

/-- No section map changes in passage back to the original sheaf category. -/
theorem affineHomOfFamily_map
    (q : ∀ j, F.affineSectionsTower.obj j →ₗ[B] G.affineSectionsTower.obj j)
    (hq : ∀ {j k} (a : j ⟶ k) x,
      q k (F.affineSectionsTower.map a x) = G.affineSectionsTower.map a (q j x))
    (j : ℕᵒᵖ) :
    moduleSpecΓFunctor.map ((F.affineHomOfFamily G q hq).hom.app j) =
      (show F.affineSectionsTower.obj j ⟶ G.affineSectionsTower.obj j from
        ModuleCat.ofHom (X := F.affineSectionsTower.obj j)
            (Y := G.affineSectionsTower.obj j) (q j)) :=
  affineHomOfSections_map _ _ _

/-- Equality of all original affine section maps detects equality of formal maps. -/
theorem affineHom_ext (α β : F ⟶ G)
    (h : ∀ j, moduleSpecΓFunctor.map (α.hom.app j) =
      moduleSpecΓFunctor.map (β.hom.app j)) : α = β := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext j
  exact Coherent.affineHom_ext (F.affineCoefficient j) (G.affineCoefficient j) _ _ (h j)

end AdicSystem
end AlgebraicGeometry.Scheme.Modules.Coherent
