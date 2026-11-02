/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.LerayBound
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.PullbackIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.EtaleDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionPreservation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.InverseImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedPointLift
public import Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism

/-! # The actual unit cone for a morphism which is an isomorphism on an open

The first arrow is the original bounded-below adjunction unit, transported
only by the canonical exact-single comparison. Its distinguished cone has
torsion homology for a qcqs morphism and a torsion coefficient. A bound `N`
on the original higher direct images gives the actual cone window `[-1,N]`.
There is no monicity assumption on the original sheaf unit.

On an open where the actual base change of the morphism is an isomorphism,
the original unit restricts invertibly by ordinary etale derived base change
and the native mate unit equation. The cone's original homology stalks are
therefore supported on any displayed complementary closed subscheme.
No dimension bound, unbounded proper base change or replacement cone is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u dX dY dU dV

attribute [local instance] hasSheafifyLarge

variable {Y X : Scheme.{u}}
  [HasDerivedCategory.{dY} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]

/-- The original derived adjunction unit on a coefficient single, followed
by the canonical exact-single comparison inside the original direct image. -/
def derivedImageSingleUnit (b : Y ⟶ X) (F : AbelianSheaf.{u, u + 1} X) :
    (singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F ⟶
      (derivedDirectImage b).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj ((inverseImage b).obj F)) :=
  (derivedImageAdjunction b).unit.app
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F) ≫
    (derivedDirectImage b).map
      (((inverseImage b).rightDerivedFunctorPlusSingleIso 0).hom.app F)

private theorem isIso_openRestriction_derivedUnit
    (b : Y ⟶ X) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsIso (pullback.fst j b)]
    [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U)]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} (pullback j b))]
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    IsIso ((derivedInverseImage j).map ((derivedImageAdjunction b).unit.app K)) := by
  let : IsIso (derivedBaseChangeMap b (pullback.fst j b) j (pullback.snd j b)
      pullback.condition) := derivedBaseChangeMap_etale_isIso b j
  exact (derivedImageAdjunction b).isIso_map_unit_of_isIso_mate
    (derivedImageAdjunction (pullback.fst j b))
    (TwoSquare.mk _ _ _ _
      (derivedInverseImageSquareIso b (pullback.fst j b) j (pullback.snd j b)
        pullback.condition).hom)
    (derivedBaseChangeMap b (pullback.fst j b) j (pullback.snd j b) pullback.condition) rfl K

/-- The literal normalized derived unit restricts invertibly on any open
where the actual base change of the original morphism is an isomorphism. -/
theorem derivedImageSingleUnit_openRestriction_isIso
    (b : Y ⟶ X) {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsIso (pullback.fst j b)]
    [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U)]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} (pullback j b))]
    (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((derivedInverseImage j).map (derivedImageSingleUnit b F)) := by
  let := isIso_openRestriction_derivedUnit b j
    ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)
  dsimp only [derivedImageSingleUnit]
  rw [Functor.map_comp]
  infer_instance

private theorem single_homology_isTorsion (F : AbelianSheaf.{u, u + 1} X)
    (hF : IsTorsion X F) (n : ℤ) :
    IsTorsion X ((homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
      ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact ObjectProperty.prop_of_isZero (IsTorsion X) (isZero_homology_of_isGE _ 0 n hn)
  · exact hF.of_mono ((singleFunctorCompHomologyFunctorIso
      (C := AbelianSheaf.{u, u + 1} X) 0).hom.app F)
  · exact ObjectProperty.prop_of_isZero (IsTorsion X) (isZero_homology_of_isLE _ 0 n hn)

omit [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)] in
private theorem stalk_isZero_of_openRestriction
    {U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
    (G : AbelianSheaf.{u, u + 1} X) (hG : IsZero ((inverseImage j).obj G))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : ∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) : IsZero (coefficientFiber s G) := by
  have hsnot : s (default : Spec (.of Ω)) ∉ Set.range i := by
    intro h
    obtain ⟨z, hz⟩ := exists_closedImmersion_pointLift i s h
    exact hs z hz
  have hsrange : Set.range s ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [hcomp]
    change s x ∉ Set.range i
    simpa only [Subsingleton.elim x (default : Spec (.of Ω))] using hsnot
  let s' := IsOpenImmersion.lift j s hsrange
  have hs' : s' ≫ j = s := IsOpenImmersion.lift_fac j s hsrange
  have hz := ((pointSmallEtale s').sheafFiber (A := AddCommGrpCat.{u + 1})).map_isZero hG
  have h := hz.of_iso ((StalkInverseImage.stalkUnitNatIso j s').app G)
  simpa only [hs'] using h

/-- The original unit admits an actual distinguished cone in `[-1,N]`, with
torsion homology supported on the displayed closed complement of its
isomorphism open. The bound is on the original higher direct images of the
actual inverse-image coefficient, not on chosen resolution terms. -/
theorem exists_derivedImageSingleUnit_cone
    (b : Y ⟶ X) [QuasiCompact b] [QuasiSeparated b]
    {U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (i : Z ⟶ X) [IsClosedImmersion i] (hcomp : Set.range j = (Set.range i)ᶜ)
    [IsIso (pullback.fst j b)]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F) (N : ℕ)
    (hR : ∀ q : ℕ, N < q →
      IsZero ((higherDirectImage b q).obj ((inverseImage b).obj F))) :
    ∃ (Q : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
      (v : (derivedDirectImage b).obj
        ((singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj ((inverseImage b).obj F)) ⟶ Q)
      (w : Q ⟶ ((singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)⟦(1 : ℤ)⟧),
      Triangle.mk (derivedImageSingleUnit b F) v w ∈ distTriang _ ∧
      Q.IsGE (-1) ∧ Q.IsLE (N : ℤ) ∧
      (∀ n : ℤ, IsTorsion X ((homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj Q)) ∧
      (∀ n : ℤ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
        (∀ z : Spec (.of Ω) ⟶ Z, z ≫ i ≠ s) →
          IsZero (coefficientFiber s
            ((homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj Q))) := by
  let A := (singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
  let B := (singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj ((inverseImage b).obj F)
  let L := (derivedDirectImage b).obj B
  let : L.IsGE 0 := (directImage b).rightDerivedFunctorPlus_isGE B 0
  let : L.IsLE (N : ℤ) := isLE_derivedDirectImage_single_of_higher b _ N hR
  obtain ⟨Q, v, w, hT⟩ := distinguished_cocone_triangle (derivedImageSingleUnit b F)
  let T := Triangle.mk (derivedImageSingleUnit b F) v w
  have hQge : Q.IsGE (-1) := by
    apply TStructure.t.isGE₂ T.rotate (rot_of_distTriang T hT) (-1)
    · exact TStructure.t.isGE_of_ge L (-1) 0 (by omega)
    · exact TStructure.t.isGE_shift A 0 1 (-1) (by omega)
  have hQle : Q.IsLE (N : ℤ) := by
    apply TStructure.t.isLE₂ T.rotate (rot_of_distTriang T hT) (N : ℤ)
    · exact inferInstanceAs (L.IsLE (N : ℤ))
    · let : (A⟦(1 : ℤ)⟧).IsLE (-1) := TStructure.t.isLE_shift A 0 1 (-1) (by omega)
      exact TStructure.t.isLE_of_le (A⟦(1 : ℤ)⟧) (-1) (N : ℤ) (by omega)
  have hQtorsion (n : ℤ) :
      IsTorsion X ((homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj Q) := by
    exact ObjectProperty.prop_X₂_of_exact (IsTorsion X)
      ((homologyFunctor (AbelianSheaf.{u, u + 1} X) 0).homologySequence_exact₃
        T hT n (n + 1) rfl)
      (derivedDirectImage_isTorsion_homology b B
        (single_homology_isTorsion _ (hF.inverseImage b)) n)
      (single_homology_isTorsion F hF (n + 1))
  refine ⟨Q, v, w, hT, hQge, hQle, hQtorsion, ?_⟩
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} U)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} (pullback j b))
  have hzero : IsZero ((derivedInverseImage j).obj Q) :=
    ((derivedInverseImage j).mapTriangle.obj T).isZero₃_of_isIso₁
      ((derivedInverseImage j).map_distinguished T hT)
      (derivedImageSingleUnit_openRestriction_isIso b j F)
  intro n Ω _ _ s hs
  have hzeroH := (homologyFunctor (AbelianSheaf.{u, u + 1} U) n).map_isZero hzero
  have hzeroR : IsZero ((inverseImage j).obj
      ((homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj Q)) :=
    hzeroH.of_iso (((inverseImage j).rightDerivedFunctorPlusHomologyIso n).app Q).symm
  exact stalk_isZero_of_openRestriction j i hcomp _ hzeroR Ω s hs

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
