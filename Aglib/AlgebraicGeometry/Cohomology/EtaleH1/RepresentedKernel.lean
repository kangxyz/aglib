/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.RepresentedCoefficients
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# A represented categorical kernel from actual section lifts

The insertion is an actual monomorphism and the lift is supplied on
every over-category test object, with its factorization equation. These
data construct the represented sheaf kernel; quotient epimorphy and
application-specific exactness are separate questions.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.RepresentedKernel`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9b3c75f054cb56e898a9ef116d58b8518eb72c6c5d3f6fce7e47700fceb9643b`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open Opposite
open AlgebraicGeometry.Scheme.EtaleH1 CategoryTheory.Abelian
open CategoryTheory.Functor.LargePresheaf
attribute [local instance] hasSheafifyLarge

namespace AlgebraicGeometry.Scheme.EtaleH1.RepresentedKernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

section Represented
variable {S : Scheme.{u}} {A B C : Grp (Over S)}
variable [IsCommMonObj A.X] [IsCommMonObj B.X] [IsCommMonObj C.X]
variable (j : A ⟶ B) (q : B ⟶ C) [Mono j.hom.hom]

theorem represented_app_injective (U : S.Etaleᵒᵖ) :
    Function.Injective ((representedSheafMap j).hom.app U) := by
  intro x y h
  apply ULift.ext
  apply Additive.toMul.injective
  apply (cancel_mono j.hom.hom).mp
  exact congrArg (fun z => z.down.toMul) h

theorem represented_mono : Mono (representedSheafMap j) := by
  have : Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology S)
      (representedSheafMap j).hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (represented_app_injective j)
  exact Sheaf.mono_of_isLocallyInjective _

omit [Mono j.hom.hom] in
-- Retain monicity of the original kernel insertion in this public represented-kernel interface;
-- the zero-composition calculation itself uses only j ≫ q = 0.
@[nolint unusedArguments]
theorem represented_composition_zero [Mono j.hom.hom] (h : j ≫ q = 0) :
    representedSheafMap j ≫ representedSheafMap q = 0 := by
  rw [← representedSheafMap_comp, h]
  ext U x
  apply ULift.ext
  change Additive.ofMul (x.down.toMul ≫ (toUnit _ ≫ η[_])) = 0
  rw [← Category.assoc]
  have hx : x.down.toMul ≫ toUnit _ = toUnit _ := toUnit_unique _ _
  rw [hx]
  all_goals rfl

variable (liftOver : ∀ {V : Over S} (x : V ⟶ B.X), x ≫ q.hom.hom = 1 → (V ⟶ A.X))
variable (lift_fac : ∀ {V : Over S} (x : V ⟶ B.X) (h : x ≫ q.hom.hom = 1),
  liftOver x h ≫ j.hom.hom = x)

/-- Apply the supplied actual Over-section lift to a section in the represented kernel, on the
same test object. -/
def representedKernelSection (U : S.Etaleᵒᵖ) (a : (representedSheaf B).obj.obj U)
    (ha : (representedSheafMap q).hom.app U a = 0) : (representedSheaf A).obj.obj U :=
  ULift.up (Additive.ofMul (liftOver a.down.toMul (congrArg (fun z => z.down.toMul) ha)))

include lift_fac in
omit [Mono j.hom.hom] in
-- Retain the same monomorphic insertion as the public kernel-section lifting interface; this
-- factorization calculation uses the supplied lift_fac equation.
@[nolint unusedArguments]
theorem representedKernelSection_fac [Mono j.hom.hom] (U : S.Etaleᵒᵖ)
    (a : (representedSheaf B).obj.obj U) (ha : (representedSheafMap q).hom.app U a = 0) :
    (representedSheafMap j).hom.app U (representedKernelSection q liftOver U a ha) = a := by
  apply ULift.ext
  exact congrArg Additive.ofMul (lift_fac a.down.toMul (congrArg (fun z => z.down.toMul) ha))

omit [Mono j.hom.hom] in
-- Retain the original monomorphic kernel insertion shared by the represented-kernel API,
-- although this component equality follows from functorial naturality.
@[nolint unusedArguments]
theorem represented_insertion_naturality [Mono j.hom.hom]
    {U V : S.Etaleᵒᵖ} (f : U ⟶ V)
    (a : (representedSheaf A).obj.obj U) :
    (representedSheafMap j).hom.app V ((representedSheaf A).obj.map f a) =
      (representedSheaf B).obj.map f ((representedSheafMap j).hom.app U a) :=
  ConcreteCategory.congr_hom ((representedSheafMap j).hom.naturality f) a

theorem represented_kernel_condition {P : AbelianSheaf.{u, u + 1} S}
    (φ : P ⟶ representedSheaf B) (h : φ ≫ representedSheafMap q = 0)
    (U : S.Etaleᵒᵖ) (a : P.obj.obj U) :
    (representedSheafMap q).hom.app U (φ.hom.app U a) = 0 :=
  ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app U) h) a

/-- The sheaf map obtained by lifting kernel sections; the given monomorphic insertion and
factorization equation ensure additivity and naturality. -/
def representedKernelLift {P : AbelianSheaf.{u, u + 1} S}
    (φ : P ⟶ representedSheaf B) (h : φ ≫ representedSheafMap q = 0) :
    P ⟶ representedSheaf A where
  hom := {
    app U := AddCommGrpCat.ofHom {
      toFun a := representedKernelSection q liftOver U (φ.hom.app U a)
        (represented_kernel_condition q φ h U a)
      map_zero' := by
        apply represented_app_injective j U
        rw [representedKernelSection_fac j q liftOver lift_fac, map_zero, map_zero]
      map_add' a b := by
        apply represented_app_injective j U
        rw [representedKernelSection_fac j q liftOver lift_fac, map_add, map_add,
          representedKernelSection_fac j q liftOver lift_fac,
          representedKernelSection_fac j q liftOver lift_fac] }
    naturality {U V} f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      apply represented_app_injective j V
      change (representedSheafMap j).hom.app V
        (representedKernelSection q liftOver V _
          (represented_kernel_condition q φ h V (P.obj.map f a))) =
        (representedSheafMap j).hom.app V ((representedSheaf A).obj.map f
          (representedKernelSection q liftOver U _ (represented_kernel_condition q φ h U a)))
      rw [representedKernelSection_fac j q liftOver lift_fac,
        represented_insertion_naturality, representedKernelSection_fac j q liftOver lift_fac]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) a }

@[simp] theorem representedKernelLift_fac {P : AbelianSheaf.{u, u + 1} S}
    (φ : P ⟶ representedSheaf B) (h : φ ≫ representedSheafMap q = 0) :
    representedKernelLift j q liftOver lift_fac φ h ≫ representedSheafMap j = φ := by
  ext U a
  exact representedKernelSection_fac j q liftOver lift_fac U _
    (represented_kernel_condition q φ h U a)

/-- A supplied actual Over-section lifting operation gives the represented categorical kernel.
The native application below supplies this operation from the constructed literal kernel iso. -/
def representedKernelIsLimit (h : j ≫ q = 0) :
    IsLimit (KernelFork.ofι (representedSheafMap j) (represented_composition_zero j q h)) := by
  letI := represented_mono j
  exact KernelFork.IsLimit.ofι' _ _ (fun φ hφ =>
    ⟨representedKernelLift j q liftOver lift_fac φ hφ,
      representedKernelLift_fac j q liftOver lift_fac φ hφ⟩)
end Represented

end AlgebraicGeometry.Scheme.EtaleH1.RepresentedKernel
