/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RepresentedComparison
public import Aglib.AlgebraicGeometry.Picard.Scheme.Properties

/-! # Projective existence for the original relative Kummer comparison

The complete comparison on the supplied original representative is re-exported
from `RepresentedComparison`. This endpoint constructs its own representative.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w s e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard

attribute [local instance] hasSheafifyLarge

section Projective

open AlgebraicGeometry.ProjectiveSpace

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ι : Type u} {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι)
    [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)] [GeometricallyIntegral (i ≫ toSpec A ι)]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    [∀ U : (Spec (.of A)).Etale, HasExt.{s}
      (Sheaf ((Scheme.smallEtaleTopology Y).over
        ((siteBaseChange (i ≫ toSpec A ι)).obj U)) AddCommGrpCat.{u + 1})]
    [∀ Z : Scheme.{u}, HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)] in
/-- For an actual projective flat geometrically integral family with a section, the existing
Picard construction supplies the representer and its group law, and original `R¹ μ_n` is
its actual small étale torsion kernel. No representability or finite-kernel family is an input. -/
theorem exists_projective_rootsHigherDirectImage_picardTorsionIso
    [Finite ι] [Nonempty ι]
    (o : Spec (.of A) ⟶ Y) (ho : o ≫ (i ≫ toSpec A ι) = 𝟙 _)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : A)) :
    ∃ (P : LocallyNoetherianOver (Spec (.of A)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
        (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
          CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (hP : LocallyOfFiniteType P.obj.hom),
      letI := hP
      Nonempty ((higherDirectImage (i ≫ toSpec A ι) 1).obj (mu Y n) ≅
        kernel (n • 𝟙 (picardRepresenterEtaleSheaf (i ≫ toSpec A ι) P R))) := by
  let : Fintype ι := Fintype.ofFinite ι
  let N := Fintype.card ι - 1
  have hN : Fintype.card ι = N + 1 :=
    (Nat.sub_add_cancel (Fintype.card_pos (α := ι))).symm
  let d : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
  obtain ⟨P, R, hP, _⟩ := exists_representableBy_fppfPicardSheaf_basicProperties i d
  let := hP
  let : IsProper (i ≫ toSpec A ι) := isProper_comp_toSpec_of_isClosedImmersion i d
  have hS : IsUnit (n : Γ(Spec (.of A), ⊤)) := by
    simpa only [map_natCast] using hi.map (Scheme.ΓSpecIso (.of A)).inv.hom
  have hY := levelInvertible (i ≫ toSpec A ι) n hS
  exact ⟨P, R, hP, ⟨rootsHigherDirectImagePicardRepresenterTorsionIso
    (i ≫ toSpec A ι) n hn hY o ho P R⟩⟩

end Projective

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
