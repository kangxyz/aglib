/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Native coproducts in the homotopy category

Homotopies out of a coproduct are assembled degreewise from the original
coproduct inclusions. Consequently the actual quotient functor preserves
coproducts, and the native homotopy category has them. The family and complex
shape have independent universes. No exactness of coproducts is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v t s

open CategoryTheory CategoryTheory.Limits

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {κ : Type t} {ι : Type s} {c : ComplexShape ι}
  [HasColimitsOfShape (Discrete κ) C]
  (K : κ → HomologicalComplex C c) {L : HomologicalComplex C c}

/-- Component homotopies glue on the actual categorical coproduct of complexes. -/
def ofCoproductInclusions {f g : ∐ K ⟶ L}
    (h : ∀ a, Homotopy (Sigma.ι K a ≫ f) (Sigma.ι K a ≫ g)) : Homotopy f g := by
  let hc (i : ι) := isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval C c i) K
  let H (i j : ι) : (∐ K).X i ⟶ L.X j :=
    Cofan.IsColimit.desc (hc i) (fun a => (h a).hom i j)
  have hH (a : κ) (i j : ι) : (Sigma.ι K a).f i ≫ H i j = (h a).hom i j :=
    Cofan.IsColimit.fac (hc i) _ a
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro i j hij
    apply (hc i).hom_ext
    rintro ⟨a⟩
    change (Sigma.ι K a).f i ≫ H i j = (Sigma.ι K a).f i ≫ 0
    rw [hH, (h a).zero i j hij, comp_zero]
  · intro i
    apply (hc i).hom_ext
    rintro ⟨a⟩
    change (Sigma.ι K a).f i ≫ f.f i =
      (Sigma.ι K a).f i ≫
        ((∐ K).d i (c.next i) ≫ H (c.next i) i +
          H i (c.prev i) ≫ L.d (c.prev i) i + g.f i)
    simp only [Preadditive.comp_add, ← Category.assoc]
    rw [(Sigma.ι K a).comm i (c.next i), Category.assoc, hH, hH]
    exact (h a).comm i

end Homotopy

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {κ : Type t} {ι : Type s} (c : ComplexShape ι)
  [HasColimitsOfShape (Discrete κ) C]

/-- The original quotient images of coproduct inclusions form a colimit cofan. -/
def quotientCoproductCofanIsColimit (K : κ → HomologicalComplex C c) :
    IsColimit (Cofan.mk ((quotient C c).obj (∐ K))
      (fun a => (quotient C c).map (Sigma.ι K a))) := by
  refine Cofan.IsColimit.mk _
    (fun s => (quotient C c).map (Sigma.desc (fun a => (s.inj a).out))) ?_ ?_
  · intro s a
    change (quotient C c).map (Sigma.ι K a) ≫
      (quotient C c).map (Sigma.desc (fun a => (s.inj a).out)) = s.inj a
    rw [← Functor.map_comp, Sigma.ι_comp_desc]
    exact quotient_map_out _
  · intro s m hm
    rw [← quotient_map_out m]
    apply eq_of_homotopy
    apply Homotopy.ofCoproductInclusions K
    intro a
    apply homotopyOfEq
    rw [Functor.map_comp, quotient_map_out, Sigma.ι_comp_desc, quotient_map_out]
    exact hm a

instance quotientPreservesCoproduct (K : κ → HomologicalComplex C c) :
    PreservesColimit (Discrete.functor K) (quotient C c) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (quotientCoproductCofanIsColimit c K))

instance quotientPreservesCoproducts :
    PreservesColimitsOfShape (Discrete κ) (quotient C c) :=
  preservesColimitsOfShape_of_discrete _

instance hasCoproduct (K : κ → HomotopyCategory C c) : HasCoproduct K :=
  HasColimit.mk ⟨_, quotientCoproductCofanIsColimit c (fun a => (K a).as)⟩

instance hasCoproducts : HasColimitsOfShape (Discrete κ) (HomotopyCategory C c) where
  has_colimit F := hasColimit_of_iso (Discrete.natIsoFunctor (F := F))

end HomotopyCategory
