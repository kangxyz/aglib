/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.PointedFixedCoefficientReturn
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.CanonicalFinitePointedStageLift
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointedTargetRestriction
public import Aglib.CategoryTheory.Limits.Shapes.PullbackPastingIso
public import Aglib.CategoryTheory.Limits.Shapes.CoproductMapFactor

/-! # Fixed-coefficient pointed return through an affine target chart

Global source charts and their actual transformed-class zeros are retained.
Their original residue marks lift to the literal restrictions over the chosen
affine target chart. The actual finite Henselian model and pointed stage lift
supply one whole-source factorization retaining every mark. Native pullback
pasting turns this into a factorization of the full original target stage,
and the same fixed finite coefficient detector returns the original class.

Only the target stage is localized. No global section is required to land in
the affine chart, no coefficient is reselected, and no class-zero producer or
induction hypothesis is hidden in this final gluing statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Coefficients GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Global marked source-chart zeros give a genuine pointed target stage over
the chosen affine chart and zero of the unchanged original class. The whole
local-stage map and every original residue mark are included in the output.
The chosen target map may be arbitrary; for an affine open chart, composing
its etale neighborhood with this map is an original etale neighborhood. -/
theorem exists_affine_stage_zero_of_fixed_coefficient
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X X' B B' Y : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    (j : Spec (.of R) ⟶ X)
    (g : B' ⟶ B) (b : Y ⟶ B) (a : Y ⟶ X)
    (p : pullback g b ⟶ X') (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) (J : ModuleSheaf B' Λ)
    (α : (moduleInverseImage g Λ).obj I ⟶ J)
    (hdetect : ∀ {Y₀ Y₁ : Scheme.{u}}
      (k : Y₁ ⟶ Y₀) (b₀ : Y₀ ⟶ B) (b₁ : Y₁ ⟶ B')
      (h : IsPullback b₁ k g b₀) (q : ℕ)
      (d : Sheaf.H.{u + 2} ((inverseImage b₀).obj
        ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q),
      Sheaf.H.map (moduleClosedPullbackCoefficientMap g k b₀ b₁ h.w.symm
        Λ I J α) q (cohomologyPullback.{u, u + 2, u + 2} k _ q d) = 0 → d = 0)
    (U : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f j)) → X'.Etale)
    (m : ∀ i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f j)),
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (hm : ∀ i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f j)),
      m i ≫ (U i).hom = limitResidueMap R Ω (pullback.snd f j) i ≫ pullback.fst f j)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : ∀ i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f j)),
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd (U i).hom p) _ q
        (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
          (pullback.condition (f := g) (g := b)).symm Λ I J α q c) = 0) :
    ∃ (V : GeometricEtaleNeighborhood R Ω)
      (w : ((baseChangedDiagram R Ω (pullback.snd f j)).obj (op V)).left ⟶
        (coproductEtale U).left),
      w ≫ (coproductEtale U).hom =
        ((baseChangedDiagram R Ω (pullback.snd f j)).obj (op V)).hom ≫ pullback.fst f j ∧
      (∀ i : MaximalSpectrum (limitSourceRing R Ω (pullback.snd f j)),
        (finiteSourceResiduePoint (limitSourceRing R Ω (pullback.snd f j)) i ≫
          (limitSourceIso R Ω (pullback.snd f j)).hom ≫
            ((baseChangedCone R Ω (pullback.snd f j)).π.app (op V)).left) ≫ w =
              m i ≫ Sigma.ι (fun i => (U i).left) i) ∧
      cohomologyPullback.{u, eY, u + 2} (X := Y)
        (S := pullback (Spec.algebraMap R V.algebra ≫ j) a)
        (pullback.snd (Spec.algebraMap R V.algebra ≫ j) a) _ q c = 0 := by
  let fO : pullback f j ⟶ Spec (.of R) := pullback.snd f j
  let rO : pullback f j ⟶ X' := pullback.fst f j
  let : IsFinite fO := inferInstanceAs (IsFinite (pullback.snd f j))
  let A : Type u := limitSourceRing R Ω fO
  let : Algebra (GeometricEtaleColimit R Ω) A := limitSourceAlgebra R Ω fO
  let : Module.Finite (GeometricEtaleColimit R Ω) A := limitSource_moduleFinite R Ω fO
  let : Finite (MaximalSpectrum A) :=
    Module.finiteAlgebra_maximalSpectrum_finite (GeometricEtaleColimit R Ω) A
  let UO : MaximalSpectrum A → (pullback f j).Etale :=
    fun i => Scheme.Etale.targetRestriction f j (U i)
  let mO (i : MaximalSpectrum A) :
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (UO i).left :=
    pullback.lift (m i) (limitResidueMap R Ω fO i) (hm i)
  have hmO (i : MaximalSpectrum A) :
      mO i ≫ (UO i).hom = limitResidueMap R Ω fO i := pullback.lift_snd ..
  let κ (i : MaximalSpectrum A) : (UO i).left ⟶ (U i).left :=
    pullback.fst (U i).hom rO
  have hκ (i : MaximalSpectrum A) : κ i ≫ (U i).hom = (UO i).hom ≫ rO :=
    pullback.condition (f := (U i).hom) (g := rO)
  have hmκ (i : MaximalSpectrum A) : mO i ≫ κ i = m i := pullback.lift_fst ..
  let forget : (coproductEtale UO).left ⟶ (coproductEtale U).left :=
    CategoryTheory.Limits.Sigma.map κ
  have hforgetι (i : MaximalSpectrum A) :
      Sigma.ι (fun i => (UO i).left) i ≫ forget =
        κ i ≫ Sigma.ι (fun i => (U i).left) i := Sigma.ι_map κ i
  have hforget : forget ≫ (coproductEtale U).hom = (coproductEtale UO).hom ≫ rO :=
    Sigma.map_desc_of_component_eq κ (fun i => (UO i).hom) (fun i => (U i).hom) rO hκ
  obtain ⟨V, v, hmarks, _⟩ := exists_finite_pointed_stage_lift_of_canonical_model
    R Ω fO UO mO hmO
  have hv : v.left ≫ (coproductEtale UO).hom =
      ((baseChangedDiagram R Ω fO).obj (op V)).hom := Over.w v
  let w : ((baseChangedDiagram R Ω fO).obj (op V)).left ⟶ (coproductEtale U).left :=
    v.left ≫ forget
  have hw : w ≫ (coproductEtale U).hom =
      ((baseChangedDiagram R Ω fO).obj (op V)).hom ≫ rO := by
    dsimp only [w]
    rw [Category.assoc, hforget, ← Category.assoc, hv]
  have hwhole := finiteCoproductPullback_cohomologyPullback_eq_zero
    (fun i => (U i).left) (fun i => (U i).hom) p _ q
    (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
      (pullback.condition (f := g) (g := b)).symm Λ I J α q c) hc
  let t : Spec (.of V.algebra) ⟶ Spec (.of R) := Spec.algebraMap R V.algebra
  let w' : pullback t fO ⟶ (coproductEtale U).left := w
  have hw' : w' ≫ (coproductEtale U).hom = pullback.snd t fO ≫ rO := hw
  let vglobal : pullback (t ≫ j) f ⟶ (coproductEtale U).left :=
    (pullbackSymmetry f (t ≫ j)).inv ≫
      (((IsPullback.of_hasPullback f j).flip).familyPullbackIso t).inv ≫ w'
  have hpaste : (((IsPullback.of_hasPullback f j).flip).familyPullbackIso t).inv ≫
      pullback.snd t fO ≫ rO = pullback.fst f (t ≫ j) :=
    ((IsPullback.of_hasPullback f j).flip).familyPullbackIso_inv_fst t
  have hsym : (pullbackSymmetry f (t ≫ j)).inv ≫ pullback.fst f (t ≫ j) =
      pullback.snd (t ≫ j) f := pullbackSymmetry_inv_comp_fst f (t ≫ j)
  have hvglobal : vglobal ≫ (coproductEtale U).hom = pullback.snd (t ≫ j) f := by
    simp only [vglobal, Category.assoc, hw', hpaste, hsym]
  have hzero := coefficientRefinement_zero_of_fixed_class_zero
    g b a (t ≫ j) f p hp (coproductEtale U).hom vglobal hvglobal
    Λ I J α hdetect q c hwhole
  refine ⟨V, w, hw, ?_, hzero⟩
  intro i
  let z : Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
      ((baseChangedDiagram R Ω fO).obj (op V)).left :=
    finiteSourceResiduePoint A i ≫ (limitSourceIso R Ω fO).hom ≫
      ((baseChangedCone R Ω fO).π.app (op V)).left
  have hi : z ≫ v.left = mO i ≫ Sigma.ι (fun i => (UO i).left) i := by
    simpa only [z, A, finiteSourceResiduePoint, Category.assoc] using hmarks i
  have hlast : (mO i ≫ Sigma.ι (fun i => (UO i).left) i) ≫ forget =
      m i ≫ Sigma.ι (fun i => (U i).left) i :=
    (Category.assoc (mO i) (Sigma.ι (fun i => (UO i).left) i) forget).trans
      ((congrArg (fun k : (UO i).left ⟶ (coproductEtale U).left => mO i ≫ k)
        (hforgetι i)).trans
          ((Category.assoc (mO i) (κ i) (Sigma.ι (fun i => (U i).left) i)).symm.trans
            (congrArg (fun k :
              Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
                (U i).left => k ≫ Sigma.ι (fun i => (U i).left) i) (hmκ i))))
  have hmarked : z ≫ w = m i ≫ Sigma.ι (fun i => (U i).left) i :=
    (Category.assoc z v.left forget).symm.trans
      ((congrArg (fun k :
        Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶
          (coproductEtale UO).left => k ≫ forget) hi).trans hlast)
  exact hmarked

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
