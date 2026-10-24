/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono

/-! # The actual additive cokernel as a ZMod module

The categorical quotient by multiplication by `n` has its canonical ZMod
module structure. Its underlying additive object is the original cokernel.
Finiteness of the original group passes to this quotient, including modulus
zero; no condition on a geometric chart is involved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AddCommGrpCat

universe w

/-- Multiplication by `n` vanishes on its actual categorical cokernel. -/
theorem nsmul_id_cokernel (A : AddCommGrpCat.{w}) (n : ℕ) :
    n • 𝟙 (cokernel (n • 𝟙 A)) = 0 := by
  apply (cancel_epi (cokernel.π (n • 𝟙 A))).mp
  simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero,
    Preadditive.nsmul_comp, Category.id_comp] using cokernel.condition (n • 𝟙 A)

/-- The quotient's original elements are annihilated by the same integer. -/
theorem nsmul_cokernel_eq_zero (A : AddCommGrpCat.{w}) (n : ℕ)
    (x : (cokernel (n • 𝟙 A) : AddCommGrpCat.{w})) : n • x = 0 :=
  ConcreteCategory.congr_hom (nsmul_id_cokernel A n) x

/-- The native ZMod structure on the original additive categorical quotient. -/
def zmodQuotient (A : AddCommGrpCat.{w}) (n : ℕ) : ModuleCat.{w} (ZMod n) :=
  letI := AddCommGroup.zmodModule (nsmul_cokernel_eq_zero A n)
  ModuleCat.of (ZMod n) (cokernel (n • 𝟙 A) : AddCommGrpCat.{w})

/-- Forgetting the canonical quotient scalar structure retains the original cokernel. -/
def zmodQuotientUnderlyingIso (A : AddCommGrpCat.{w}) (n : ℕ) :
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).obj (zmodQuotient A n) ≅
      cokernel (n • 𝟙 A) := Iso.refl _

/-- The original quotient of a finite additive group is finite. -/
theorem finite_zmodQuotient (A : AddCommGrpCat.{w}) [Finite A] (n : ℕ) :
    Finite (zmodQuotient A n) := by
  change Finite (cokernel (n • 𝟙 A) : AddCommGrpCat.{w})
  exact Finite.of_surjective (cokernel.π (n • 𝟙 A))
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)

end AddCommGrpCat
