/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroKernelIso
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# The square-zero unit sequence in the actual abelian-sheaf category

The left term is the native additive kernel. Its inclusion is the original
one-plus map, and the right map is the original map on units. Local lifting
is used only for the epimorphism; no sectionwise surjectivity is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, w}]
variable {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)

/-- The original square-zero unit sequence, before asserting local surjectivity. -/
def squareZeroUnitsComplex
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) where
  X₁ := additiveKernel f
  X₂ := R.units
  X₃ := S.units
  f := oneAddUnits f hf
  g := unitsMap f
  zero := oneAddUnits_unitsMap f hf

/-- The unit sequence of a locally surjective square-zero ring-sheaf map is
short exact, with its native additive kernel and original quotient maps. -/
theorem squareZeroUnitsComplex_shortExact [HasSheafify J AddCommGrpCat.{w}]
    [Presheaf.IsLocallySurjective J f.hom]
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    (squareZeroUnitsComplex f hf).ShortExact := by
  let : IsIso (oneAddUnitsKernelMap f hf) := by
    change IsIso (oneAddUnitsKernelIso f hf).hom
    infer_instance
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (squareZeroUnitsComplex f hf).exact_iff_epi_kernel_lift.mpr
    change Epi (oneAddUnitsKernelMap f hf)
    infer_instance
  · change Mono (oneAddUnits f hf)
    rw [← oneAddUnitsKernelMap_ι f hf]
    infer_instance
  · let : Presheaf.IsLocallySurjective J (unitsMap f).hom :=
      unitsMap_isLocallySurjective f hf
    change Epi (unitsMap f)
    infer_instance

end CategoryTheory.Sheaf
