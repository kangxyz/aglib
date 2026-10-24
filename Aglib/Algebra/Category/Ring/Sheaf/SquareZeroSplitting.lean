/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroSequence
public import Aglib.CategoryTheory.Sites.SheafCohomology.Splitting

/-!
# Split square-zero unit sequences and their cohomology

A section `s : S ⟶ R` of a ring-sheaf map `f : R ⟶ S` makes `f` locally
surjective. If the section kernels of `f` are square-zero, the original
square-zero unit sequence `0 → I → R^* → S^* → 0` of
`squareZeroUnitsComplex_shortExact` is split by the units of `s`.

Every additive functor preserves the splitting. For Mathlib's sheaf cohomology
`Sheaf.H` the generic split-complex statements of
`Aglib.CategoryTheory.Sites.SheafCohomology.Splitting` give, in every degree `n`,
`H^n(R^*) ≃+ H^n(I) × H^n(S^*)`, and the kernel of the original map
`H^n(R^*) → H^n(S^*)` is identified with `H^n(I)` through the original
one-plus map. These are the cohomological statements behind the tangent space
of the Picard scheme (Kleiman, arXiv:math/0504020v1, Thm 5.11): there the site
is the Zariski site of `X`, `R` is the structure sheaf of `X[ε]` and `S = 𝒪_X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w z
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section SquareZero

variable {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (s : S ⟶ R)

/-- A ring-sheaf map with a section is surjective on all sections, hence locally
surjective. -/
theorem isLocallySurjective_of_section (hs : s ≫ f = 𝟙 S) :
    Presheaf.IsLocallySurjective J f.hom := by
  refine Presheaf.isLocallySurjective_of_surjective J f.hom fun U x => ⟨s.hom.app U x, ?_⟩
  have h := congrArg (fun g : S ⟶ S => g.hom.app U x) hs
  exact h

variable [UnivLE.{max u v, w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The original square-zero unit sequence is split by the original map on units of a
ring section. The section of the splitting is literally `unitsMap s`. -/
def squareZeroUnitsSplitting (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    (squareZeroUnitsComplex f hf).Splitting :=
  haveI := isLocallySurjective_of_section f s hs
  ShortComplex.Splitting.ofExactOfSection _ (squareZeroUnitsComplex_shortExact f hf).exact
    (unitsMap s) (by
      change unitsMap s ≫ unitsMap f = 𝟙 _
      rw [← unitsMap_comp, hs, unitsMap_id])
    (squareZeroUnitsComplex_shortExact f hf).mono_f

@[simp]
theorem squareZeroUnitsSplitting_s (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) :
    (squareZeroUnitsSplitting f s hs hf).s = unitsMap s := rfl

variable [HasExt.{z} (Sheaf J AddCommGrpCat.{w})]

/-- Cohomology of the units of a split square-zero ring-sheaf map:
`H^n(R^*) ≃+ H^n(I) × H^n(S^*)`, where `I` is the original additive kernel. The second
component is the original map `H.map (unitsMap f) n`. -/
def squareZeroUnitsCohomologyEquiv (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ) :
    H R.units n ≃+ H (additiveKernel f) n × H S.units n :=
  H.splittingAddEquiv (squareZeroUnitsSplitting f s hs hf) n

@[simp]
theorem squareZeroUnitsCohomologyEquiv_apply_snd (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ) (x : H R.units n) :
    (squareZeroUnitsCohomologyEquiv f s hs hf n x).2 = H.map (unitsMap f) n x := rfl

@[simp]
theorem squareZeroUnitsCohomologyEquiv_symm_apply (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ)
    (y : H (additiveKernel f) n × H S.units n) :
    (squareZeroUnitsCohomologyEquiv f s hs hf n).symm y =
      H.map (oneAddUnits f hf) n y.1 + H.map (unitsMap s) n y.2 := rfl

/-- The kernel of the original map `H^n(R^*) → H^n(S^*)` of a split square-zero
ring-sheaf map is `H^n` of the original additive kernel, through the one-plus map. -/
def squareZeroUnitsCohomologyKerEquiv (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ) :
    (H.map (unitsMap f) n).ker ≃+ H (additiveKernel f) n :=
  H.kerAddEquivOfSplitting (squareZeroUnitsSplitting f s hs hf) n

@[simp]
theorem squareZeroUnitsCohomologyKerEquiv_symm_apply_coe (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ)
    (a : H (additiveKernel f) n) :
    (((squareZeroUnitsCohomologyKerEquiv f s hs hf n).symm a :
        (H.map (unitsMap f) n).ker) : H R.units n) =
      H.map (oneAddUnits f hf) n a := rfl

/-- The one-plus map is injective on the cohomology of a split square-zero sequence. -/
theorem oneAddUnits_cohomology_injective (hs : s ≫ f = 𝟙 S)
    (hf : ∀ U : Cᵒᵖ, RingHom.ker (f.hom.app U).hom ^ 2 = ⊥) (n : ℕ) :
    Function.Injective (H.map (oneAddUnits f hf) n) :=
  H.map_f_injective_of_splitting (squareZeroUnitsSplitting f s hs hf) n

omit [UnivLE.{max u v, w}] in
/-- The original map on unit cohomology of a ring-sheaf map with a section is
surjective in every degree, without a vanishing hypothesis. -/
theorem unitsCohomology_map_surjective_of_section (hs : s ≫ f = 𝟙 S) (n : ℕ) :
    Function.Surjective (H.map (unitsMap f) n) := by
  intro y
  refine ⟨H.map (unitsMap s) n y, ?_⟩
  rw [← H.map_comp_apply, ← unitsMap_comp, hs, unitsMap_id, H.map_id_apply]

end SquareZero

end CategoryTheory.Sheaf
