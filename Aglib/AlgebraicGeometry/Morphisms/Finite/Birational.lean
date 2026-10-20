/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Finite birational morphisms to normal integral schemes

Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Birational`.
The current consumer identifies the finite rational-graph model of an actual
normal proper curve with the original curve. The statement is general: both
schemes are integral, the target has integrally closed actual stalks, the map
is finite, and its restriction over one nonempty open is an isomorphism.
There is no normality assumption on the source and no dimension assumption.

The inverse is constructed through the relative normalization of the literal
generic inclusion. The generic-normalization input is proved in Aglib revision
`197ca0728db3cdf1552a6bcefeeda901e3377862`, in
`Aglib.AlgebraicGeometry.FunctionField.Normalization`; the normalization and
separatedness APIs are from Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]

/-- A finite map to a normal integral scheme which is invertible over a
nonempty open admits an actual two-sided inverse. -/
theorem exists_inverse_of_isFinite_of_isIso_restrict
    (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] :
    ∃ s : X ⟶ Y, s ≫ p = 𝟙 X ∧ p ≫ s = 𝟙 Y := by
  let (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := (hN x).2
  let j := X.fromSpecStalk (genericPoint X)
  let V := p ⁻¹ᵁ U
  have hjU : Set.range j ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨genericPoint X, ?_⟩, ?_⟩
    · exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))
    · exact (fromSpecStalk_genericPoint_apply X z).symm
  let jU := IsOpenImmersion.lift U.ι j hjU
  have hjU_comp : jU ≫ U.ι = j := IsOpenImmersion.lift_fac U.ι j hjU
  have : IsDominant (jU ≫ U.ι) := by rw [hjU_comp]; infer_instance
  let : IsDominant jU := IsDominant.of_comp_of_isOpenImmersion jU U.ι
  let : Nonempty V.toScheme := Nonempty.map (inv (p ∣_ U)) inferInstance
  let : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let m : Spec X.functionField ⟶ Y := jU ≫ inv (p ∣_ U) ≫ V.ι
  let : IsDominant m := by dsimp [m]; infer_instance
  have hm : m ≫ p = j := by
    simp only [m, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    exact hjU_comp
  let s : X ⟶ Y := inv j.fromNormalization ≫ j.normalizationDesc m p hm.symm
  have hsp : s ≫ p = 𝟙 X := by
    simp only [s, Category.assoc, Hom.normalizationDesc_comp]
    exact IsIso.inv_hom_id _
  have hjs : j ≫ s = m := by
    have hj : j ≫ inv j.fromNormalization = j.toNormalization := by
      calc
        _ = (j.toNormalization ≫ j.fromNormalization) ≫ inv j.fromNormalization :=
          congrArg (fun f => f ≫ inv j.fromNormalization)
            j.toNormalization_fromNormalization.symm
        _ = _ := by simp
    simp only [s, ← Category.assoc, hj]
    exact j.toNormalization_normalizationDesc m p hm.symm
  refine ⟨s, hsp, ?_⟩
  exact ext_of_isDominant_of_isSeparated p (by simp [Category.assoc, hsp]) m
    (by simpa only [← Category.assoc, hm, Category.comp_id] using hjs)

/-- The actual normal-target identification, retaining the supplied map as
its forward morphism. -/
def finiteBirationalIso (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] : Y ≅ X where
  hom := p
  inv := Classical.choose (exists_inverse_of_isFinite_of_isIso_restrict p hN U)
  hom_inv_id := (Classical.choose_spec
    (exists_inverse_of_isFinite_of_isIso_restrict p hN U)).2
  inv_hom_id := (Classical.choose_spec
    (exists_inverse_of_isFinite_of_isIso_restrict p hN U)).1

@[simp] theorem finiteBirationalIso_hom
    (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] :
    (finiteBirationalIso p hN U).hom = p := rfl

/-- The constructed inverse is a section of the supplied finite map. -/
@[reassoc (attr := simp)] theorem finiteBirationalIso_inv_comp
    (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] :
    (finiteBirationalIso p hN U).inv ≫ p = 𝟙 X :=
  (finiteBirationalIso p hN U).inv_hom_id

/-- The constructed inverse is also a retraction of the supplied finite map. -/
@[reassoc (attr := simp)] theorem comp_finiteBirationalIso_inv
    (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] :
    p ≫ (finiteBirationalIso p hN U).inv = 𝟙 Y :=
  (finiteBirationalIso p hN U).hom_inv_id

/-- Finite birational maps to normal integral schemes are isomorphisms,
with birationality witnessed on a supplied nonempty open. -/
theorem isIso_of_isFinite_of_isIso_restrict
    (p : Y ⟶ X) [IsFinite p] (hN : NormalStalks X)
    (U : X.Opens) [Nonempty U] [IsIso (p ∣_ U)] : IsIso p :=
  (finiteBirationalIso p hN U).isIso_hom

end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/Birational.lean
SHA-256 442acab6d4486ef82440187da60f446da6c95b5bccbb9e14ca01a32e6197e7d4. -/
