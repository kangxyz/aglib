/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.ArtinSchreier
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Module.RingHom

/-! # Scalars on the original lifted additive ring coefficient

An actual natural cone of ring homomorphisms acts by multiplication on the
same single-lift additive sheaf. The induced cohomology action uses the
original additive cohomology functor and retains composition order.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf.RingAction

universe c h a r l e

variable {C : Type c} [Category.{h} C] (P : Cᵒᵖ ⥤ CommRingCat.{a})
  (J : GrothendieckTopology C)
  (hP : Presheaf.IsSheaf J (ArtinSchreier.additivePresheaf.{l} P))
  (R : Type r) [Ring R] (s : ∀ U : Cᵒᵖ, R →+* P.obj U)
  (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : R), (P.map f).hom (s U x) = s V x)

/-- Multiplication by an actual scalar-cone section on the original carrier. -/
def scalar (x : R) : ArtinSchreier.additiveSheaf.{l} P J hP ⟶
    ArtinSchreier.additiveSheaf.{l} P J hP where
  hom :=
    { app U := AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom
        { toFun := fun y : P.obj U => s U x * y
          map_zero' := mul_zero _
          map_add' := mul_add _ })
      naturality {U V} f := by
        ext y
        apply ULift.ext
        symm
        change (P.map f).hom (s U x * y.down) = s V x * (P.map f).hom y.down
        rw [map_mul, hs f x] }

/-- The original section value, with no new additive realization. -/
theorem scalar_apply (x : R) (U : Cᵒᵖ) (y : ULift.{l} (P.obj U)) :
    ((scalar P J hP R s hs x).hom.app U y).down = s U x * y.down := rfl

@[simp]
theorem scalar_zero : scalar P J hP R s hs 0 = 0 := by
  ext U y
  apply ULift.ext
  change s U 0 * y.down = 0
  simp

@[simp]
theorem scalar_one : scalar P J hP R s hs 1 = 𝟙 _ := by
  ext U y
  apply ULift.ext
  change s U 1 * y.down = y.down
  simp

@[simp]
theorem scalar_add (x y : R) :
    scalar P J hP R s hs (x + y) = scalar P J hP R s hs x + scalar P J hP R s hs y := by
  ext U z
  apply ULift.ext
  change s U (x + y) * z.down = s U x * z.down + s U y * z.down
  simp [add_mul]

/-- Categorical composition has exactly the original action order. -/
theorem scalar_mul (x y : R) :
    scalar P J hP R s hs (x * y) = scalar P J hP R s hs y ≫ scalar P J hP R s hs x := by
  ext U z
  apply ULift.ext
  change s U (x * y) * z.down = s U x * (s U y * z.down)
  simp [mul_assoc]

/-- The same literal multiplication endomorphisms satisfy the original
Frobenius square on this actual ring coefficient. -/
theorem scalar_frobenius (p : ℕ) (hp : p.Prime)
    (h : ∀ U : Cᵒᵖ, (p : P.obj U) = 0) (x : R) :
    scalar P J hP R s hs x ≫ ArtinSchreier.frobenius P J hP p hp h =
      ArtinSchreier.frobenius P J hP p hp h ≫ scalar P J hP R s hs (x ^ p) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro (y : ULift.{l} (P.obj U))
  apply ULift.ext
  change (s U x * (y.down : P.obj U)) ^ p =
    s U (x ^ p) * (y.down : P.obj U) ^ p
  simp [mul_pow]

variable [HasSheafify J AddCommGrpCat.{max a l}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max a l})]

/-- The original cohomology scalar action induced by those same sheaf maps. -/
def cohomologyScalars (q : ℕ) :
    R →+* AddMonoid.End (Sheaf.H.{e} (ArtinSchreier.additiveSheaf.{l} P J hP) q) where
  toFun x := Sheaf.H.map (scalar P J hP R s hs x) q
  map_zero' := by
    ext y
    rw [scalar_zero]
    change (Sheaf.functorH _ q).map 0 y = 0
    rw [CategoryTheory.Functor.map_zero]
    rfl
  map_one' := by
    ext y
    rw [scalar_one]
    exact Sheaf.H.map_id_apply y
  map_add' x y := by
    ext z
    rw [scalar_add]
    exact Sheaf.H.map_add_apply _ _ z
  map_mul' x y := by
    ext z
    rw [scalar_mul]
    exact Sheaf.H.map_comp_apply _ _ z

/-- The action uses the actual original cohomology map. -/
theorem cohomologyScalars_apply (q : ℕ) (x : R)
    (y : Sheaf.H.{e} (ArtinSchreier.additiveSheaf.{l} P J hP) q) :
    cohomologyScalars P J hP R s hs q x y = Sheaf.H.map (scalar P J hP R s hs x) q y := rfl

end CategoryTheory.Sheaf.RingAction
