/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying

/-! Restriction detects endomorphisms of the original torsion coefficient unit. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

variable {X T : Scheme.{u}}
  [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
  [ConnectedSpace T] [CompactSpace T] [QuasiSeparatedSpace T] (f : T ⟶ X)

/-- The original inverse image detects maps from a constant source to a torsion
constant target between connected qcqs schemes. -/
theorem inverseImage_map_injective_of_constantIso
    {L M : AbelianSheaf.{u, u + 1} X} (A B : AddCommGrpCat.{u + 1}) (hB : IsAddTorsion B)
    (e : L ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (d : M ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B) :
    Function.Injective (fun (a : L ⟶ M) => (inverseImage f).map a) := by
  intro a b h
  apply (cancel_epi e.inv).mp
  apply ((constantAdjunction X).homEquiv A M).injective
  let : IsIso (globalSectionsPullback f M) :=
    globalSectionsPullback_isIso_of_torsionConstantIso f B hB M d
  apply (cancel_mono (globalSectionsPullback f M)).mp
  rw [← constantTransport_homEquiv f A (e.inv ≫ a),
    ← constantTransport_homEquiv f A (e.inv ≫ b)]
  simp only [Functor.map_comp, h]

/-- The original inverse image recovers every morphism between the given constant
source and torsion constant target on connected qcqs schemes. -/
theorem inverseImage_map_bijective_of_constantIso
    {L M : AbelianSheaf.{u, u + 1} X} (A B : AddCommGrpCat.{u + 1}) (hB : IsAddTorsion B)
    (e : L ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (d : M ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B) :
    Function.Bijective (fun (a : L ⟶ M) => (inverseImage f).map a) := by
  refine ⟨inverseImage_map_injective_of_constantIso f A B hB e d, ?_⟩
  intro q
  let F := inverseImage f
  let c := (inverseImageConstantIso f).app A
  let s := globalSectionsPullback f M
  let : IsIso s := globalSectionsPullback_isIso_of_torsionConstantIso f B hB M d
  let a := (constantAdjunction X).homEquiv A M
  let b := (constantAdjunction T).homEquiv A (F.obj M)
  let z := b ((c.inv ≫ F.map e.inv) ≫ q)
  let t := a.symm (z ≫ inv s)
  refine ⟨e.hom ≫ t, ?_⟩
  change F.map (e.hom ≫ t) = q
  apply (cancel_epi (c.inv ≫ F.map e.inv)).mp
  apply b.injective
  have hv : (c.inv ≫ F.map e.inv) ≫ F.map (e.hom ≫ t) = c.inv ≫ F.map t := by
    rw [Category.assoc, F.map_comp, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]
  have ht : a t ≫ s = z := by
    change a (a.symm (z ≫ inv s)) ≫ s = z
    rw [Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hv]
  exact (constantTransport_homEquiv f A t).trans ht

namespace Coefficients

/-- An endomorphism of the original torsion coefficient unit is detected by
its original inverse-image map. -/
theorem moduleInverseImage_map_injective_unit_end (Λ : Type (u + 1)) [Ring Λ]
    (hΛ : IsAddTorsion (AddCommGrpCat.of Λ)) :
    Function.Injective (fun (a : moduleUnit X Λ ⟶ moduleUnit X Λ) =>
      (moduleInverseImage f Λ).map a) := by
  let Q := SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)
  let R := SheafOfModules.toSheaf.{u + 1} (constantRing T Λ)
  let U := moduleUnit X Λ
  let A := AddCommGrpCat.of Λ
  let e := moduleUnitUnderlyingIso X Λ
  intro a b hab
  change (moduleInverseImage f Λ).map a = (moduleInverseImage f Λ).map b at hab
  apply Q.map_injective
  apply inverseImage_map_injective_of_constantIso f A A hΛ e.symm e.symm
  let α := (moduleInverseImageUnderlyingIso Λ f).hom
  have ha := α.naturality a
  have hb := α.naturality b
  change R.map ((moduleInverseImage f Λ).map a) ≫ α.app U =
    α.app U ≫ (inverseImage f).map (Q.map a) at ha
  change R.map ((moduleInverseImage f Λ).map b) ≫ α.app U =
    α.app U ≫ (inverseImage f).map (Q.map b) at hb
  apply (cancel_epi (α.app U)).mp
  rw [← ha, ← hb, hab]

end Coefficients

end AlgebraicGeometry.Scheme.EtaleCohomology
