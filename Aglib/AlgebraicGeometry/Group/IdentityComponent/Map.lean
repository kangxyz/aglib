/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic

/-!
# The original map on identity components

A unit-preserving morphism of locally finite-type monoid schemes over a field
maps the original identity component into the original identity component.
Its restriction is the existing open-immersion lift. The whole inclusion
equation determines it uniquely and proves the identity and composition laws.
For group homomorphisms it preserves the original group laws, by cancellation
of the original monic inclusions. No properness or separatedness is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k]

section Pointed

variable {G H K : Over (Spec (.of k))} [MonObj G] [MonObj H] [MonObj K]
  [LocallyOfFiniteType G.hom] [LocallyOfFiniteType H.hom] [LocallyOfFiniteType K.hom]

/-- The original connected source component maps into the target component
under every morphism preserving the original unit section. -/
theorem range_identityComponent_comp_subset
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    Set.range (identityComponentι G ≫ f).left ⊆ identityComponent H :=
  range_subset_identityComponent_of_section H _ (identityComponentOne G)
    (by rw [identityComponentOne_ι_assoc, hf])

/-- Restriction of a unit-preserving morphism to the original components. -/
def identityComponentMap (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    identityComponentOver G ⟶ identityComponentOver H :=
  liftIdentityComponent H (identityComponentι G ≫ f)
    (range_identityComponent_comp_subset f hf)

/-- The defining whole-morphism equation uses the original inclusions. -/
@[reassoc (attr := simp)]
theorem identityComponentMap_ι (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    identityComponentMap f hf ≫ identityComponentι H = identityComponentι G ≫ f :=
  liftIdentityComponent_ι ..

/-- The original inclusion equation characterizes the component map. -/
theorem identityComponentMap_unique (f : G ⟶ H) (hf : η[G] ≫ f = η[H])
    (g : identityComponentOver G ⟶ identityComponentOver H)
    (hg : g ≫ identityComponentι H = identityComponentι G ≫ f) :
    g = identityComponentMap f hf := by
  apply (cancel_mono (identityComponentι H)).mp
  rw [identityComponentMap_ι]
  exact hg

/-- The original rational unit of the component is preserved. -/
@[reassoc (attr := simp)]
theorem identityComponentOne_comp_map (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    identityComponentOne G ≫ identityComponentMap f hf = identityComponentOne H := by
  apply (cancel_mono (identityComponentι H)).mp
  rw [Category.assoc, identityComponentMap_ι, identityComponentOne_ι_assoc,
    identityComponentOne_ι, hf]

/-- Identity coherence for the same component restriction. -/
@[simp]
theorem identityComponentMap_id :
    identityComponentMap (𝟙 G) (Category.comp_id η[G]) = 𝟙 (identityComponentOver G) := by
  apply (cancel_mono (identityComponentι G)).mp
  simp

/-- Composition coherence for arbitrary unit-preserving morphisms. -/
theorem identityComponentMap_comp (f : G ⟶ H) (g : H ⟶ K)
    (hf : η[G] ≫ f = η[H]) (hg : η[H] ≫ g = η[K]) :
    identityComponentMap (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      identityComponentMap f hf ≫ identityComponentMap g hg := by
  apply (cancel_mono (identityComponentι K)).mp
  simp only [identityComponentMap_ι, Category.assoc, identityComponentMap_ι_assoc]

end Pointed

section Group

variable {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]
  [LocallyOfFiniteType G.hom] [LocallyOfFiniteType H.hom]

/-- Restriction of an original group homomorphism preserves the original
component group law. The proof uses only the monic inclusion equations. -/
instance isMonHom_identityComponentMap (f : G ⟶ H) [IsMonHom f]
    (hf : η[G] ≫ f = η[H]) : IsMonHom (identityComponentMap f hf) where
  one_hom := by
    simpa only [one_identityComponentOver] using identityComponentOne_comp_map f hf
  mul_hom := by
    apply (cancel_mono (identityComponentι H)).mp
    calc
      (μ[identityComponentOver G] ≫ identityComponentMap f hf) ≫ identityComponentι H =
          μ[identityComponentOver G] ≫ identityComponentι G ≫ f := by
            rw [Category.assoc, identityComponentMap_ι]
      _ = (identityComponentι G ⊗ₘ identityComponentι G) ≫ μ[G] ≫ f := by
            rw [IsMonHom.mul_hom_assoc]
      _ = (identityComponentι G ⊗ₘ identityComponentι G) ≫ (f ⊗ₘ f) ≫ μ[H] := by
            rw [IsMonHom.mul_hom]
      _ = ((identityComponentι G ≫ f) ⊗ₘ (identityComponentι G ≫ f)) ≫ μ[H] := by
            rw [← tensorHom_comp_tensorHom_assoc]
      _ = ((identityComponentMap f hf ≫ identityComponentι H) ⊗ₘ
          (identityComponentMap f hf ≫ identityComponentι H)) ≫ μ[H] := by
            rw [identityComponentMap_ι]
      _ = ((identityComponentMap f hf ⊗ₘ identityComponentMap f hf) ≫
          μ[identityComponentOver H]) ≫ identityComponentι H := by
            rw [← tensorHom_comp_tensorHom_assoc, ← IsMonHom.mul_hom, Category.assoc]

/-- The same original component map, bundled for the existing group category. -/
def identityComponentGroupHom (f : G ⟶ H) [IsMonHom f] :
    Grp.mk (identityComponentOver G) ⟶ Grp.mk (identityComponentOver H) :=
  Grp.ofHom (identityComponentMap f (IsMonHom.one_hom f))

/-- Bundling leaves the original map unchanged. -/
@[simp]
theorem identityComponentGroupHom_hom_hom (f : G ⟶ H) [IsMonHom f] :
    (identityComponentGroupHom f).hom.hom =
      identityComponentMap f (IsMonHom.one_hom f) := rfl

/-- Bundled identity coherence retains the original component group object. -/
@[simp]
theorem identityComponentGroupHom_id :
    identityComponentGroupHom (𝟙 G) = 𝟙 (Grp.mk (identityComponentOver G)) := by
  apply Grp.hom_ext
  exact identityComponentMap_id

/-- Bundled composition is the same whole component-map composition law. -/
theorem identityComponentGroupHom_comp
    {K : Over (Spec (.of k))} [GrpObj K] [LocallyOfFiniteType K.hom]
    (f : G ⟶ H) (g : H ⟶ K) [IsMonHom f] [IsMonHom g] :
    identityComponentGroupHom (f ≫ g) =
      identityComponentGroupHom f ≫ identityComponentGroupHom g := by
  apply Grp.hom_ext
  exact identityComponentMap_comp f g (IsMonHom.one_hom f) (IsMonHom.one_hom g)

end Group

end AlgebraicGeometry.Scheme.Group
