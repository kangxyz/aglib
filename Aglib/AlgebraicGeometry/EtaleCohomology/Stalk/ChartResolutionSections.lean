/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartHomSections
public import Aglib.CategoryTheory.Abelian.Injective.ExactFunctorPlus

/-! # Original chart sources on actual resolution terms

The original represented source map gives the literal section on the chart.
After an actual resolution lift, the same source gives the lifted term. These
are equalities of original cocycles, not cohomological comparison premises.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original constant-source chart comparison takes every represented
morphism to its original section, not only the represented identity. -/
theorem chartComparisonSource_sections_comp {X : Scheme.{u}} (V : X.Etale)
    {A : AbelianSheaf.{u, u + 1} X}
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) V ⟶ A) :
    (Continuity.pullbackSectionsEtaleEvaluationIso A V).hom
      ((constantIntegerHomGlobalSectionsIso V.left).hom.app _
        (chartComparisonSource V ≫ (inverseImage V.hom).map a)) =
      Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) V A a := by
  change chartHomSectionsEquiv V A
    (chartComparisonSource V ≫ (inverseImage V.hom).map a) = _
  rw [chartHomSectionsEquiv_naturality, chartHomSectionsEquiv_source]
  exact (Sheaf.Hypercohomology.sectionsEquiv_naturality.{u + 1}
    (Scheme.smallEtaleTopology X) V (𝟙 _) a).symm.trans
      (congrArg (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) V A) (Category.id_comp a))

/-- An actual lifted chart cocycle has the original represented section as its
term before applying the actual extended resolution lift. -/
theorem chartComparisonSource_sections_extendedLift {X : Scheme.{u}} (V : X.Etale)
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage V.hom).obj F))
    (φ : InjectiveResolution.ExactFunctor.mappedResolution (inverseImage V.hom) I ⟶
      J.cocomplex) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) V ⟶ I.cocomplex.X q) :
    (constantIntegerHomGlobalSectionsIso V.left).hom.app _
        ((chartComparisonSource V ≫ (inverseImage V.hom).map a ≫ φ.f q) ≫
          (J.cochainComplexXIso q q rfl).inv) =
      (globalSections V.left).map
        ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
          (q : ℤ))
        ((Continuity.pullbackSectionsEtaleEvaluationIso
          (I.cochainComplex.X (q : ℤ)) V).inv
          (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
            (Scheme.smallEtaleTopology X) V _ (a ≫ (I.cochainComplexXIso q q rfl).inv))) := by
  let a' := chartComparisonSource V ≫
    (inverseImage V.hom).map (a ≫ (I.cochainComplexXIso q q rfl).inv)
  let e := Continuity.pullbackSectionsEtaleEvaluationIso (I.cochainComplex.X (q : ℤ)) V
  have hp : (constantIntegerHomGlobalSectionsIso V.left).hom.app _ a' =
      e.inv (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) V _ (a ≫ (I.cochainComplexXIso q q rfl).inv)) := by
    have h := chartComparisonSource_sections_comp V (a ≫ (I.cochainComplexXIso q q rfl).inv)
    exact (ConcreteCategory.congr_hom e.hom_inv_id _).symm.trans (congrArg e.inv h)
  have hn := ConcreteCategory.congr_hom
    ((constantIntegerHomGlobalSectionsIso V.left).hom.naturality
      ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
        (q : ℤ))) a'
  change (constantIntegerHomGlobalSectionsIso V.left).hom.app _
      (a' ≫ (InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
        (q : ℤ)) =
    (globalSections V.left).map
      ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
        (q : ℤ)) ((constantIntegerHomGlobalSectionsIso V.left).hom.app _ a') at hn
  have hterm :
      ((chartComparisonSource V ≫ (inverseImage V.hom).map a ≫ φ.f q) ≫
        (J.cochainComplexXIso q q rfl).inv) =
      a' ≫ (InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
        (q : ℤ) := by
    dsimp only [a']
    rw [InjectiveResolution.ExactFunctor.extendedLift_f, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg ((constantIntegerHomGlobalSectionsIso V.left).hom.app
    (J.cochainComplex.X (q : ℤ))) hterm).trans (hn.trans (congrArg
      (fun z => (globalSections V.left).map
        ((InjectiveResolution.ExactFunctor.extendedLift (inverseImage V.hom) I J φ).f
          (q : ℤ)) z) hp))

end AlgebraicGeometry.Scheme.EtaleCohomology
