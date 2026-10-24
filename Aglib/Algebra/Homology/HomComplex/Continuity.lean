/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.HomComplex.Limit
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Surjectivity onto the entire native predecessor limit

The source comparison is a monomorphism from the colimit of the whole earlier
diagram. Termwise injectivity implies surjectivity onto its entire inverse Hom
limit, not only surjectivity of individual transition maps.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
  (F : J ⥤ CochainComplex C ℤ) (I : CochainComplex C ℤ)

instance hasLimit_inverseDiagram : HasLimit (inverseDiagram F I) :=
  ⟨⟨colimitCone F I, colimitConeIsLimit F I⟩⟩

/-- The comparison with the actual native limit, supplied by the actual limit proof. -/
def colimitIsoLimit : HomComplex (colimit F) I ≅ limit (inverseDiagram F I) :=
  (colimitConeIsLimit F I).conePointUniqueUpToIso (limit.isLimit _)

variable {K : CochainComplex C ℤ} (g : colimit F ⟶ K)

/-- The full inverse-limit comparison associated to a source cocone comparison. -/
def limitComparison : HomComplex K I ⟶ limit (inverseDiagram F I) :=
  precompMap g I ≫ (colimitIsoLimit F I).hom

/-- Monicity from the whole source colimit gives degreewise surjectivity to
all predecessors simultaneously. -/
lemma limitComparison_surjective [Mono g] [∀ n, Injective (I.X n)] (n : ℤ) :
    Function.Surjective ((limitComparison F I g).f n) := by
  have hi : Function.Surjective (((colimitIsoLimit F I).hom).f n) :=
    (ConcreteCategory.bijective_of_isIso _).surjective
  exact hi.comp (precompMap_surjective g I n)

end CochainComplex.HomComplex
