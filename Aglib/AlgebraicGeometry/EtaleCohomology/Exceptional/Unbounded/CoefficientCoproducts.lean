/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.HigherDirectImageColimits
public import Aglib.CategoryTheory.Limits.CoproductsFromFiltered

/-! # Arbitrary filtered coefficient colimits for the original higher direct image

The original marked-stalk comparison transports actual qcqs coefficient continuity,
not merely sequential continuity. This supplies the finite-subcoproduct diagrams
needed for arbitrary sums of coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

section Filtered

variable {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]

section MarkedChart

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η)
  (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)

include R j hη in
/-- Filtered continuity after an original geometric stalk, using a specified
actual affine chart and its original marked-point factorization. -/
theorem higherDirectImage_chartStalk_preservesFilteredColimits :
    PreservesColimitsOfShape I
      (higherDirectImage f q ⋙ (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) := by
  let Z := pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f
  let π : Z ⟶ X := pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f
  let : CompactSpace Z := inferInstance
  let : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)
  let : PreservesColimitsOfShape I (cohomologyFunctor.{u, u + 2} Z q) :=
    qcqsCohomologyFunctor_preservesColimitsOfShape Z q
  let L := higherDirectImage f q ⋙
    (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})
  let U := AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let V := AddCommGrpCat.uliftFunctor.{u + 1, u + 2}
  let : PreservesColimitsOfShape I ((inverseImage π ⋙ cohomologyFunctor.{u, u + 2} Z q) ⋙ V) :=
    inferInstance
  let : PreservesColimitsOfShape I (L ⋙ U) :=
    preservesColimitsOfShape_of_natIso (higherDirectImageChartStalkUliftIso R Ω j η hη f q).symm
  let : ReflectsColimitsOfShape I U := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves L U

end MarkedChart

/-- Every original geometric point admits an actual affine open chart with the
literal spectrum factorization used by the marked-stalk comparison. -/
private theorem higherDirectImage_geometricStalk_preservesFilteredColimits
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S) :
    PreservesColimitsOfShape I
      (higherDirectImage f q ⋙ (pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})) := by
  classical
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq (η default)
  let : IsOpenImmersion j := hj
  have hRange : Set.range η ⊆ Set.range j := by
    rintro z ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    subst x
    exact ⟨y, hy⟩
  let k := IsOpenImmersion.lift j η hRange
  let φ : R →+* Ω := (Spec.preimage k).hom
  let : Algebra R Ω := φ.toAlgebra
  have hk : Spec.algebraMap R Ω = k := Spec.map_preimage k
  have hη : Spec.algebraMap R Ω ≫ j = η :=
    (congrArg (fun l => l ≫ j) hk).trans (IsOpenImmersion.lift_fac j η hRange)
  exact higherDirectImage_chartStalk_preservesFilteredColimits R Ω j η hη f q

/-- The original sheaf-valued higher direct image of a qcqs morphism preserves
filtered coefficient colimits over an arbitrary target scheme. -/
theorem higherDirectImage_preservesFilteredColimits
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ) :
    PreservesColimitsOfShape I (higherDirectImage f q) := by
  let P (x : FibrewiseClosed.Index (𝟙 S)) :
      AbelianSheaf.{u, u + 1} S ⥤ AddCommGrpCat.{u + 1} :=
    (pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
  let (x : FibrewiseClosed.Index (𝟙 S)) : PreservesColimitsOfShape I (P x) :=
    inferInstanceAs (PreservesColimitsOfShape I
      ((pointSmallEtale (FibrewiseClosed.geometricPoint x.val)).sheafFiber
        (A := AddCommGrpCat.{u + 1})))
  let (x : FibrewiseClosed.Index (𝟙 S)) :
      PreservesColimitsOfShape I (higherDirectImage f q ⋙ P x) :=
    higherDirectImage_geometricStalk_preservesFilteredColimits f q
      (FibrewiseClosed.pointField x.val) (FibrewiseClosed.geometricPoint x.val)
  exact preservesColimitsOfShape_of_jointlyReflectIsomorphisms (higherDirectImage f q) P
    (StalkUniverse.originalStalks_jointlyReflectIsomorphisms (𝟙 S))

end Filtered

/-- The original higher direct image preserves arbitrary coproducts of the
coefficient universe, by the actual filtered diagram of finite subcoproducts. -/
theorem higherDirectImage_preservesCoproducts
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    (κ : Type (u + 1)) : PreservesColimitsOfShape (Discrete κ) (higherDirectImage f q) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let : (higherDirectImage f q).Additive :=
    Functor.additive_of_iso ((directImage f).rightDerivedSingleHomologyIso q).symm
  let : PreservesColimitsOfShape (Finset (Discrete κ)) (higherDirectImage f q) :=
    higherDirectImage_preservesFilteredColimits f q
  let : HasColimitsOfShape (Discrete κ) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := hasSheafifyLarge X
  let : HasColimitsOfShape (Discrete κ) (AbelianSheaf.{u, u + 1} X) := by
    change HasColimitsOfShape (Discrete κ) (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    exact ⟨fun _ => HasColimit.mk
      ⟨Sheaf.sheafifyCocone (colimit.cocone _),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
  constructor
  intro G
  let e : Discrete.functor (fun i => G.obj ⟨i⟩) ≅ G := Discrete.natIso (fun i => Iso.refl _)
  have : PreservesColimit (Discrete.functor (fun i => G.obj ⟨i⟩)) (higherDirectImage f q) :=
    preservesCoproduct_of_finiteSubcoproducts (higherDirectImage f q) (fun i : κ => G.obj ⟨i⟩)
  exact preservesColimit_of_iso_diagram (higherDirectImage f q) e

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
