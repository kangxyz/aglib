/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Integer-algebra maps factor through a filtered stage

The source ring is finitely presented over the integers. Lifted integers
keep the ring-colimit statement in its original universe. The chosen stage
can be required to lie above any specified index.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

/-- A map from a finitely presented integer algebra to an actual filtered
ring colimit factors through a stage above any prescribed index. -/
theorem CommRingCat.exists_factorization_of_finitePresentation_int_above
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : CommRingCat.{u}) [Algebra.FinitePresentation ℤ A]
    (φ : A ⟶ c.pt) (i₀ : I) :
    ∃ (i : I) (_ : i₀ ⟶ i) (ψ : A ⟶ F.obj i), ψ ≫ c.ι.app i = φ := by
  let Z := ULift.{u} ℤ
  let : Algebra Z A := ULift.algebra' ℤ A
  let : IsScalarTower ℤ Z A := ⟨fun r s x => by
    change (r * s.down) • x = r • (s.down • x)
    exact mul_smul r s.down x⟩
  let : IsNoetherianRing Z :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : Z ≃+* ℤ).symm
  let : Algebra.FiniteType Z A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ Z A
  let : Algebra.FinitePresentation Z A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let R := CommRingCat.of Z
  let α : (Functor.const I).obj R ⟶ F :=
    { app i := CommRingCat.ofHom
        ((Int.castRingHom (F.obj i)).comp (ULift.ringEquiv : Z ≃+* ℤ).toRingHom)
      naturality {i j} q := by
        ext ⟨r⟩
        change (r : F.obj j) = (F.map q).hom (r : F.obj i)
        exact (map_intCast (F.map q).hom r).symm }
  let a : R ⟶ A := CommRingCat.ofHom (algebraMap Z A)
  have ha : a.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, ψ, _, hψ⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    R F α a c hc ha φ (fun j => by
      ext ⟨r⟩
      change φ.hom (r : A) = (c.ι.app j).hom (r : F.obj j)
      exact (map_intCast φ.hom r).trans (map_intCast (c.ι.app j).hom r).symm)
  refine ⟨IsFiltered.max i₀ j, IsFiltered.leftToMax i₀ j,
    ψ ≫ F.map (IsFiltered.rightToMax i₀ j), ?_⟩
  rw [Category.assoc, c.w]
  exact hψ.symm
