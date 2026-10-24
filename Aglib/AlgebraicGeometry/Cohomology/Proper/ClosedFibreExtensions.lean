/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.CategoryTheory.Abelian.Ext1.Extension
public import Aglib.RingTheory.IntegralClosure.MaximalIdealDual

/-!
# Scalar correction for actual closed-fibre extensions

For a normal Noetherian local domain of dimension at least two, the original
maximal-ideal image in the structure module has only original scalar maps
back to the structure module whenever the structural coefficient map is
bijective. The proof tests maps on the actual ideal-image generators.

A concrete lift of the quotient then gives a splitting of its actual
extension after subtracting one original scalar. Proper birational geometry
supplies the coefficient-map condition. Producing the lift by punctured
cohomology is a separate geometric obligation; no vanishing is assumed here.

This is the corrected-lift part of Stacks Project, Lemma 54.7.6, tag 0AXC.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤))

/-- The actual ideal generators detect all maps out of their sheaf image. -/
private theorem idealMultiple_hom_ext (F N : X.Modules) (J : Ideal A)
    {c d : idealMultiple X α F J ⟶ N}
    (h : ∀ a : J, idealMultipleScalar X α F J a ≫ c =
      idealMultipleScalar X α F J a ≫ d) : c = d := by
  apply (cancel_epi (factorThruImage (idealEvaluation X α F J))).mp
  apply Sigma.hom_ext
  intro a
  simpa only [idealMultipleScalar, Category.assoc] using h a

/-- Original scalar generators are linear; equality is tested after the
actual monomorphism of the ideal image into the coefficient. -/
private def idealMultipleScalarLinearMap (F : X.Modules) (J : Ideal A) :
    letI := moduleCategoryLinearOfHom X α
    J →ₗ[A] (F ⟶ idealMultiple X α F J) := by
  letI := moduleCategoryLinearOfHom X α
  refine { toFun := idealMultipleScalar X α F J, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply (cancel_mono (idealMultipleι X α F J)).mp
    simp only [Preadditive.add_comp, idealMultipleScalar_ι,
      ← moduleCategoryLinearOfHom_smul_id X α]
    change ((a : A) + (b : A)) • 𝟙 F = (a : A) • 𝟙 F + (b : A) • 𝟙 F
    exact add_smul _ _ _
  · intro r a
    apply (cancel_mono (idealMultipleι X α F J)).mp
    simp only [Linear.smul_comp, idealMultipleScalar_ι,
      ← moduleCategoryLinearOfHom_smul_id X α]
    change (r * (a : A)) • 𝟙 F = r • ((a : A) • 𝟙 F)
    exact mul_smul _ _ _

local notation "O" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)
local notation "EndO" => @Quiver.Hom X.Modules _ O O

/-- Original scalar multiplication composes with the original ring product. -/
private theorem globalScalarEndomorphism_mul_comp (F : X.Modules) (a b : A) :
    globalScalarEndomorphism X F (α (a * b)) =
      globalScalarEndomorphism X F (α b) ≫ globalScalarEndomorphism X F (α a) := by
  let := moduleCategoryLinearOfHom X α
  rw [← moduleCategoryLinearOfHom_smul_id X α F (a * b),
    ← moduleCategoryLinearOfHom_smul_id X α F b,
    ← moduleCategoryLinearOfHom_smul_id X α F a,
    Linear.smul_comp, Category.id_comp, smul_smul, mul_comm a b]

/-- Original base scalars identify the endomorphisms of the structure module
through the native global-section comparison. -/
private def unitScalarEndLinearEquivOfBijective (hα : Function.Bijective α) :
    letI := moduleCategoryLinearOfHom X α
    A ≃ₗ[A] EndO := by
  letI := moduleCategoryLinearOfHom X α
  letI : Module A ((O).val.obj (op ⊤)) := Module.compHom _ α
  let c : A →ₗ[A] (O).val.obj (op ⊤) := {
    toFun := fun a => α a
    map_add' := fun a b => α.map_add a b
    map_smul' := fun a b => by
      change α (a * b) = α a * α b
      exact α.map_mul a b }
  exact (LinearEquiv.ofBijective c hα).trans
    (unitHomGlobalSectionsLinearEquivOfHom X α O).symm

private theorem unitScalarEndLinearEquivOfBijective_sections
    (hα : Function.Bijective α) (a : A) :
    unitHomGlobalSectionsLinearEquivOfHom X α O
      (unitScalarEndLinearEquivOfBijective X α hα a) = α a := by
  let L := unitHomGlobalSectionsLinearEquivOfHom X α O
  change L (L.symm (α a)) = α a
  exact L.apply_symm_apply _

private theorem unitScalarEndLinearEquivOfBijective_apply
    (hα : Function.Bijective α) (a : A) :
    unitScalarEndLinearEquivOfBijective X α hα a =
      globalScalarEndomorphism X O (α a) := by
  apply (unitHomGlobalSectionsLinearEquivOfHom X α O).injective
  rw [unitScalarEndLinearEquivOfBijective_sections,
    unitHomGlobalSectionsLinearEquivOfHom_apply, globalScalarEndomorphism_app]
  have htop : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
  rw [htop, X.presheaf.map_id]
  change α a = α a * 1
  exact (mul_one _).symm

variable [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

local notation "m" => IsLocalRing.maximalIdeal A
local notation "I" => idealMultiple X α O m
local notation "ι" => idealMultipleι X α O m
local notation "Q" => idealQuotient X α O m
local notation "q" => idealQuotientπ X α O m

/-- A morphism from the literal maximal-ideal image to the structure
module is multiplication by an original scalar, after the original inclusion.

The proof deliberately uses the actual generator maps. It does not assume
that global sections are faithful, or that pullback of m -> A is injective. -/
theorem maximalIdealMultipleHom_eq_scalar (hα : Function.Bijective α)
    (hdim : 2 ≤ ringKrullDim A) (c : I ⟶ O) :
    ∃ a : A, c = ι ≫ globalScalarEndomorphism X O (α a) := by
  let := moduleCategoryLinearOfHom X α
  let e := unitScalarEndLinearEquivOfBijective X α hα
  let t : m →ₗ[A] A := e.symm.toLinearMap.comp
    ((Linear.rightComp (C := X.Modules) A O c).comp (idealMultipleScalarLinearMap X α O m))
  obtain ⟨a, ha⟩ := (IsLocalRing.maximalIdeal_scalarToDual_bijective hdim).2 t
  refine ⟨a, idealMultiple_hom_ext X α O O m ?_⟩
  intro b
  have hb : t b = a * (b : A) := by
    simpa only [Ideal.scalarToDual_apply] using
      (congrArg (fun l : m →ₗ[A] A => l b) ha).symm
  have htb : idealMultipleScalar X α O m b ≫ c = e (t b) := by
    change _ = e (e.symm (idealMultipleScalar X α O m b ≫ c))
    exact (e.apply_symm_apply _).symm
  rw [htb, hb]
  change unitScalarEndLinearEquivOfBijective X α hα (a * (b : A)) =
    idealMultipleScalar X α O m b ≫ (ι ≫ globalScalarEndomorphism X O (α a))
  rw [unitScalarEndLinearEquivOfBijective_apply, ← Category.assoc, idealMultipleScalar_ι]
  exact globalScalarEndomorphism_mul_comp X α O a (b : A)


/-- Correcting a concrete lift of the quotient produces a section of the
original fibre extension. This is the last half of Stacks 0AXC. -/
theorem closedFibreExtension_section_of_lift
    (hα : Function.Bijective α) (hdim : 2 ≤ ringKrullDim A)
    (E : CategoryTheory.Abelian.Ext1.Extension Q O)
    (s : O ⟶ E.middle) (hs : s ≫ E.p = q) :
    ∃ r : Q ⟶ E.middle, r ≫ E.p = 𝟙 Q := by
  let : Mono E.i := E.shortExact.mono_f
  have hz : (ι ≫ s) ≫ E.p = 0 := by
    rw [Category.assoc, hs, idealMultipleι_quotientπ]
  let c : I ⟶ O := E.shortExact.exact.lift (ι ≫ s) hz
  have hc : c ≫ E.i = ι ≫ s := E.shortExact.exact.lift_f _ _
  obtain ⟨a, ha⟩ := maximalIdealMultipleHom_eq_scalar X α hα hdim c
  let t : O ⟶ E.middle := s - globalScalarEndomorphism X O (α a) ≫ E.i
  have hit : ι ≫ t = 0 := by
    dsimp only [t]
    rw [Preadditive.comp_sub, ← Category.assoc, ← ha, hc, sub_self]
  let r : Q ⟶ E.middle := cokernel.desc ι t hit
  have hqr : q ≫ r = t := cokernel.π_desc _ _ _
  refine ⟨r, (cancel_epi q).mp ?_⟩
  rw [← Category.assoc, hqr, Category.comp_id]
  dsimp only [t]
  rw [Preadditive.sub_comp, Category.assoc, E.zero, comp_zero, sub_zero, hs]

/-- A proper birational morphism supplies the exact coefficient-map
hypothesis of the corrected-lift constructor; no arbitrary A action is used. -/
theorem closedFibreExtension_section_of_proper_birational_lift
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hA : NormalStalks (Spec (.of A)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdim : 2 ≤ ringKrullDim A)
    (E : CategoryTheory.Abelian.Ext1.Extension
      (idealQuotient X (f.appTop.hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom) O m) O)
    (s : O ⟶ E.middle)
    (hs : s ≫ E.p = idealQuotientπ X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) O m) :
    ∃ r : idealQuotient X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) O m ⟶ E.middle,
      r ≫ E.p = 𝟙 _ :=
  closedFibreExtension_section_of_lift X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)
    (Hom.bijective_structuralCoefficients_of_isProper_birational A f hA hff)
    hdim E s hs

end AlgebraicGeometry.Scheme.Modules
