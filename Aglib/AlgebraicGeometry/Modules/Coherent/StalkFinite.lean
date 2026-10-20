/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Locality
public import Mathlib.RingTheory.Localization.Finiteness
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators
public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic

/-!
# Finite generation of actual coherent stalk modules

Source-only extraction from `R5Lab.KTheory.Quillen.StalkModuleFiniteness` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/



/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.StalkFinite` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f14e74a1d469af614d6e99e63eb25e22df753a07581778c76ebb4966b496a4ce`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Stalk
universe u

/-- The tilde stalk's original structure-sheaf action makes it a finite module. -/
theorem tilde_stalk_finite (R : CommRingCat.{u}) (M : ModuleCat.{u} R) [Module.Finite R M]
    (x : Spec R) :
    Module.Finite ((Spec R).presheaf.stalk x)
      ((_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk (Spec R) x).obj (tilde M)) := by
  change Module.Finite ((structurePresheafInCommRingCat R).stalk x)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x)
  exact Module.Finite.of_isLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ R M x)

theorem finite_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} S)
    [Module.Finite S M] : Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  let : RingHomSurjective f := ⟨hf⟩
  let e : ((ModuleCat.restrictScalars f).obj M) →ₛₗ[f] M :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (e.finite_iff_of_bijective Function.bijective_id).mpr inferInstance

theorem coherent_affine_stalk_finite (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves (Spec R)) (x :
        Spec R) :
    Module.Finite ((Spec R).presheaf.stalk x)
      ((_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk (Spec R) x).obj M.obj) := by
  have hM :=
      (_root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff R
      M.obj).mp M.property
  let : M.obj.IsQuasicoherent := hM.1
  let : Module.Finite R ((modulesSpecToSheaf.obj M.obj).presheaf.obj (Opposite.op ⊤)) := hM.2
  let e := (_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk (Spec R) x).mapIso (asIso
      M.obj.fromTildeΓ)
  exact Module.Finite.of_surjective (hM := tilde_stalk_finite R _ x)
    e.hom.hom e.toLinearEquiv.surjective

/-- Finite generation is proved for the original stalk module and its original action. -/
theorem coherent_stalk_finite (X : Scheme.{u}) [IsNoetherian X]
    (M : _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves X) (x : X) :
    Module.Finite (X.presheaf.stalk x) ((_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk X
        x).obj M.obj) := by
  obtain ⟨i, y, rfl⟩ := X.affineOpenCover.openCover.exists_eq x
  let j := X.affineOpenCover.f i
  let : IsNoetherianRing (X.affineOpenCover.X i) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion j)
  let N := (_root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypeSheavesRestriction
      j).obj M
  let : Module.Finite (((Spec (X.affineOpenCover.X i)).presheaf.stalk y))
      ((_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk (Spec (X.affineOpenCover.X i))
          y).obj N.obj) :=
    coherent_affine_stalk_finite _ N y
  let P := (_root_.AlgebraicGeometry.Scheme.Modules.moduleStalk (Spec (X.affineOpenCover.X i))
      y).obj N.obj
  let : Module.Finite (X.presheaf.stalk (j y))
      ((ModuleCat.restrictScalars (j.stalkMap y).hom).obj P) :=
    finite_restrictScalars (j.stalkMap y).hom (ConcreteCategory.bijective_of_isIso _).2 P
  let e := (_root_.AlgebraicGeometry.Scheme.Modules.restrictModuleStalkIso j y).app M.obj
  exact Module.Finite.of_surjective
    (hM := finite_restrictScalars (j.stalkMap y).hom (ConcreteCategory.bijective_of_isIso _).2 P)
    e.hom.hom e.toLinearEquiv.surjective

end AlgebraicGeometry.Scheme.Modules.Stalk
