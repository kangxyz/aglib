/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.Prefactor.Congruence

/-!
# Original top-differential pasting in the genuine chart degree

The original exterior restriction maps paste before and after the actual
rank equality. This supplies the coefficient and tangent comparisons used
when the original chart arrows are restricted to a common refinement.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem isoHomEqOfInvEq {C : Type*} [Category C] {X Y : C}
    (e f : X ≅ Y) (h : e.inv = f.inv) : e.hom = f.hom := by
  apply (cancel_mono f.inv).mp
  rw [← h, Iso.hom_inv_id, h, Iso.hom_inv_id]

section Pasting
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
  (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
  (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (k : X₂ ⟶ X₁) (l : Y₂ ⟶ Y₁)
  [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (h : i ≫ p₀ = p₁ ≫ j) (h' : k ≫ p₁ = p₂ ≫ l)
  (H : (k ≫ i) ≫ p₀ = p₂ ≫ (l ≫ j))

/-- The actual top-differential restrictions paste with the original composition map. -/
theorem canonicalTopDifferentialRestriction_comp (n : ℕ) :
    (restrictFunctorComp k i).hom.app
        (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≫
      (restrictFunctor k).map (relativeTopDifferentialRestrictionIso p₀ i p₁ j h n).hom ≫
        (relativeTopDifferentialRestrictionIso p₁ k p₂ l h' n).hom =
      (relativeTopDifferentialRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n).hom := by
  let e := relativeTopDifferentialRestrictionIso p₀ (k ≫ i) p₂ (l ≫ j) H n
  let f := (restrictFunctorComp k i).app
      (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≪≫
    (restrictFunctor k).mapIso (relativeTopDifferentialRestrictionIso p₀ i p₁ j h n) ≪≫
      relativeTopDifferentialRestrictionIso p₁ k p₂ l h' n
  have he : e.inv = f.inv :=
    relativeTopDifferentialRestrictionIso_comp_inv p₀ p₁ p₂ i j k l h h' H n
  exact (isoHomEqOfInvEq e f he).symm

end Pasting

/-- Equal actual source opens give the same original top-differential comparison. -/
theorem canonicalTopDifferentialRestriction_congr
    {X W Y Z : Scheme.{u}} (p : X ⟶ Y) (a a' : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion a'] (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion j] (h : a ≫ p = q ≫ j) (h' : a' ≫ p = q ≫ j)
    (ha : a = a') (n : ℕ) :
    (restrictFunctorCongr ha).hom.app
        (moduleExteriorPower X (relativeDifferentialSheaf p) n) ≫
      (relativeTopDifferentialRestrictionIso p a' q j h' n).hom =
    (relativeTopDifferentialRestrictionIso p a q j h n).hom := by
  subst a'
  rw [canonicalRestrictionCongr_refl, Category.id_comp]


/-- The original top maps paste on the actual equal source open with its native congruence. -/
theorem canonicalTopDifferentialRestriction_comp_congr
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (k : X₂ ⟶ X₁) (l : Y₂ ⟶ Y₁)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (h : i ≫ p₀ = p₁ ≫ j) (h' : k ≫ p₁ = p₂ ≫ l)
    (H : (k ≫ i) ≫ p₀ = p₂ ≫ (l ≫ j))
    (a : X₂ ⟶ X₀) [IsOpenImmersion a] (ha : a = k ≫ i)
    (Ha : a ≫ p₀ = p₂ ≫ (l ≫ j)) (n : ℕ) :
    (restrictFunctorCongr ha).hom.app
        (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≫
      (restrictFunctorComp k i).hom.app
        (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≫
      (restrictFunctor k).map (relativeTopDifferentialRestrictionIso p₀ i p₁ j h n).hom ≫
      (relativeTopDifferentialRestrictionIso p₁ k p₂ l h' n).hom =
    (relativeTopDifferentialRestrictionIso p₀ a p₂ (l ≫ j) Ha n).hom := by
  have hC := canonicalTopDifferentialRestriction_comp p₀ p₁ p₂ i j k l h h' H n
  have hA := canonicalTopDifferentialRestriction_congr p₀ a (k ≫ i) p₂ (l ≫ j) Ha H ha n
  have hC' := congrArg (fun t => (restrictFunctorCongr ha).hom.app
    (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≫ t) hC
  simpa only [Category.assoc] using hC'.trans hA


section Degree
variable {X Y W Z : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ p = q ≫ j)

/-- The same original restriction map commutes with a genuine exterior-degree equality. -/
theorem canonicalTopDifferentialRestriction_degree (n m : ℕ) (hnm : n = m) :
    (restrictFunctor i).map
        (eqToIso (congrArg (moduleExteriorPower X (relativeDifferentialSheaf p)) hnm)).hom ≫
      (relativeTopDifferentialRestrictionIso p i q j h m).hom =
    (relativeTopDifferentialRestrictionIso p i q j h n).hom ≫
      (eqToIso (congrArg (moduleExteriorPower W (relativeDifferentialSheaf q)) hnm)).hom := by
  subst m
  simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- Original top restriction followed only by its actual rank equality. -/
def canonicalTopDifferentialRestrictionInDegree (n m : ℕ) (hnm : n = m) :
    (moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict i ≅
      moduleExteriorPower W (relativeDifferentialSheaf q) m :=
  relativeTopDifferentialRestrictionIso p i q j h n ≪≫
    eqToIso (congrArg (moduleExteriorPower W (relativeDifferentialSheaf q)) hnm)

end Degree

section PastingInDegree
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
  (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
  (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (k : X₂ ⟶ X₁) (l : Y₂ ⟶ Y₁)
  [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
  (h : i ≫ p₀ = p₁ ≫ j) (h' : k ≫ p₁ = p₂ ≫ l)
  (H : (k ≫ i) ≫ p₀ = p₂ ≫ (l ≫ j))

/-- The original coefficient comparison pastes through the actual local rank equality. -/
theorem canonicalTopDifferentialRestrictionInDegree_comp (n m : ℕ) (hnm : n = m) :
    (restrictFunctorComp k i).hom.app
        (moduleExteriorPower X₀ (relativeDifferentialSheaf p₀) n) ≫
      (restrictFunctor k).map
        (canonicalTopDifferentialRestrictionInDegree p₀ i p₁ j h n m hnm).hom ≫
      (relativeTopDifferentialRestrictionIso p₁ k p₂ l h' m).hom =
    (canonicalTopDifferentialRestrictionInDegree p₀ (k ≫ i) p₂ (l ≫ j) H n m hnm).hom := by
  have hD := canonicalTopDifferentialRestriction_degree p₁ k p₂ l h' n m hnm
  have hC := canonicalTopDifferentialRestriction_comp p₀ p₁ p₂ i j k l h h' H n
  simp only [canonicalTopDifferentialRestrictionInDegree, Iso.trans_hom, Functor.map_comp,
    Category.assoc]
  rw [hD]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ (eqToIso (congrArg
      (moduleExteriorPower X₂ (relativeDifferentialSheaf p₂)) hnm)).hom) hC

end PastingInDegree
end AlgebraicGeometry.Scheme.Modules
