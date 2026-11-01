/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelDimension

/-!
# The actual image of divisors with a repeated point

Duplicate the first coordinate of the existing ordered curve parameter,
then use the original based Abel morphism. The whole family class acquires
one additional copy of that graph class. Its actual proper schematic image
has dimension at most the number of original coordinates.

For degree g at least two this image misses a nonempty open of the original
g-dimensional Jacobian. The further assertion that every repeated effective
degree-g divisor lands here uses its effective-divisor decomposition; it is
not built into this definition or assumed as a geometric hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

variable {k : Type u} [Field k]

/-- Duplicate the first coordinate using the existing finite-product lift. -/
def repeatedParameter (X : FScheme k) (n : ℕ) :
    parameter X.hom (n + 1) ⟶ parameter X.hom (n + 2) :=
  Over.homMk
    (parameterPoint X.hom (parameter X.hom (n + 1)).hom
      (Fin.cases (coordinate X.hom (n + 1) 0) (coordinate X.hom (n + 1)))
      (Fin.cases (coordinate_over X.hom (n + 1) 0) (coordinate_over X.hom (n + 1))))
    (parameterPoint_over X.hom _ _ _)

variable {X : FScheme k} [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom]
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole repeated family adds the first graph class to the original
family class, before specializing to any point. -/
theorem lineBundle_class_at_repeatedParameter (n : ℕ) :
    pullbackClass ((familyScheme X.hom).map (repeatedParameter X n))
      (classOf _ (lineBundle X.hom o ho (n + 2))) =
        Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho
          (parameter X.hom (n + 1)).hom (coordinate X.hom (n + 1) 0)
          (coordinate_over X.hom (n + 1) 0) + classOf _ (lineBundle X.hom o ho (n + 1)) := by
  have h := lineBundle_class_at_tuple X.hom o ho (parameter X.hom (n + 1)).hom
    (Fin.cases (coordinate X.hom (n + 1) 0) (coordinate X.hom (n + 1)))
    (Fin.cases (coordinate_over X.hom (n + 1) 0) (coordinate_over X.hom (n + 1)))
  refine h.trans ?_
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  exact congrArg (fun c => Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho
    (parameter X.hom (n + 1)).hom (coordinate X.hom (n + 1) 0)
      (coordinate_over X.hom (n + 1) 0) + c) (lineBundle_class X.hom o ho (n + 1)).symm

variable (hX : Properties X)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- The actual repeated-divisor map into the same original Jacobian. -/
def repeatedAbelMorphism (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    parameter X.hom (n + 1) ⟶ identityComponentOver P.obj :=
  repeatedParameter X n ≫ jacobianAbelMorphism hX o ho P R (n + 2)

omit [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The repeated map is proper, through properness of its existing ordered
source and separatedness of the original Jacobian. -/
theorem isProper_repeatedAbelMorphism (n : ℕ) :
    IsProper (repeatedAbelMorphism o ho hX P R n).left := by
  let := picardCommGrpObj X.hom P R
  let := hX.proper
  have : IsSeparated (identityComponentOver P.obj).hom := by
    rw [identityComponentOver_hom]
    infer_instance
  have : IsProper ((repeatedAbelMorphism o ho hX P R n).left ≫
      (identityComponentOver P.obj).hom) := by
    rw [Over.w]
    exact parameter_isProper X.hom (n + 1)
  exact IsProper.of_comp _ (identityComponentOver P.obj).hom

omit [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
/-- The actual repeated-divisor schematic image has the smaller source
dimension. No generically separable or finite-flat assertion is inferred. -/
theorem topologicalKrullDim_repeatedAbelImage_le (n : ℕ) :
    topologicalKrullDim (repeatedAbelMorphism o ho hX P R n).left.image ≤ (n + 1 : ℕ) := by
  have := isProper_repeatedAbelMorphism o ho hX P R n
  exact ((repeatedAbelMorphism o ho hX P R n).left.topologicalKrullDim_image_le).trans
    (topologicalKrullDim_parameter hX (n + 1)).le

omit [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] in
/-- A repeated degree-(n+2) divisor image cannot cover J when n+1<g. -/
theorem not_surjective_repeatedAbelMorphism (n : ℕ) (hn : n + 1 < coherentGenus k X) :
    ¬ Function.Surjective (repeatedAbelMorphism o ho hX P R n).left := by
  let := picardCommGrpObj X.hom P R
  intro hsurj
  have : Surjective (repeatedAbelMorphism o ho hX P R n).left := ⟨hsurj⟩
  have := isProper_repeatedAbelMorphism o ho hX P R n
  have hd := Scheme.Hom.topologicalKrullDim_le_of_isProper_of_surjective
    (repeatedAbelMorphism o ho hX P R n).left
  rw [topologicalKrullDim_identityComponentOver_eq_coherentGenus hX P R,
    topologicalKrullDim_parameter hX (n + 1)] at hd
  have hlt : ((n + 1 : ℕ) : WithBot ℕ∞) < (coherentGenus k X : WithBot ℕ∞) := by
    exact_mod_cast hn
  exact hlt.not_ge hd

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
