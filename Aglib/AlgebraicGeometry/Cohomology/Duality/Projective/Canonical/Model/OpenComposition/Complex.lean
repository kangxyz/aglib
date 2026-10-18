/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition

/-!
# Composition on the original fixed-resolution cochain models

The native direct-to-iterated restriction isomorphism is an actual lift on
the literal restrictions of one fixed resolution. Extending this same lift
by zero gives strict composition of the original closed-adjoint open maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

universe u v
namespace AlgebraicGeometry.Scheme.Modules

section Restriction
variable {V' V P : Scheme.{u}} (j : V ⟶ P) (k : V' ⟶ V)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The native direct-to-iterated restriction comparison on the original complex. -/
def canonicalRestrictionCompComplexIso {ι : Type v} (shape : ComplexShape ι)
    (K : HomologicalComplex P.Modules shape) :
    ((restrictFunctor (k ≫ j)).mapHomologicalComplex shape).obj K ≅
      ((restrictFunctor k).mapHomologicalComplex shape).obj
        (((restrictFunctor j).mapHomologicalComplex shape).obj K) :=
  ((Functor.mapHomologicalComplexCompIso (restrictFunctorComp k j).symm shape).app K).symm

/-- Its components are precisely the original ordinary restriction comparison. -/
theorem canonicalRestrictionCompComplexIso_hom_f {ι : Type v} (shape : ComplexShape ι)
    (K : HomologicalComplex P.Modules shape) (n : ι) :
    (canonicalRestrictionCompComplexIso j k shape K).hom.f n =
      (restrictFunctorComp k j).hom.app (K.X n) := by
  simp [canonicalRestrictionCompComplexIso]

variable {L : P.Modules} (J : InjectiveResolution L)

/-- The original restriction comparison on the literal fixed cocomplex. -/
def canonicalAmbientResolutionCompIso :
    (canonicalAmbientChartResolution J (k ≫ j)).cocomplex ≅
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J j) k).cocomplex :=
  canonicalRestrictionCompComplexIso j k (.up ℕ) J.cocomplex

/-- Every cocomplex component retains the original ordinary comparison. -/
theorem canonicalAmbientResolutionCompIso_hom_f (n : ℕ) :
    (canonicalAmbientResolutionCompIso j k J).hom.f n =
      (restrictFunctorComp k j).hom.app (J.cocomplex.X n) :=
  canonicalRestrictionCompComplexIso_hom_f j k (.up ℕ) J.cocomplex n

/-- The same native comparison is a lift over the original coefficient isomorphism. -/
def canonicalAmbientResolutionCompLift :
    InjectiveResolution.Hom (canonicalAmbientChartResolution J (k ≫ j))
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J j) k)
      ((restrictFunctorComp k j).hom.app L) where
  hom := (canonicalAmbientResolutionCompIso j k J).hom
  ι_f_zero_comp_hom_f_zero := by
    rw [canonicalAmbientResolutionCompIso_hom_f]
    change (restrictFunctor (k ≫ j)).map (J.ι.f 0) ≫
        (restrictFunctorComp k j).hom.app (J.cocomplex.X 0) =
      (restrictFunctorComp k j).hom.app L ≫
        (restrictFunctor k).map ((restrictFunctor j).map (J.ι.f 0))
    exact (restrictFunctorComp k j).hom.naturality (J.ι.f 0)

/-- Extending the actual cocomplex isomorphism gives the original cochain comparison. -/
def canonicalAmbientResolutionCompCochainIso :
    (canonicalAmbientChartResolution J (k ≫ j)).cochainComplex ≅
      (canonicalAmbientChartResolution (canonicalAmbientChartResolution J j) k).cochainComplex :=
  (ComplexShape.embeddingUpNat.extendFunctor V'.Modules).mapIso
    (canonicalAmbientResolutionCompIso j k J)

/-- Its forward map is exactly the original extension of the actual resolution lift. -/
theorem canonicalAmbientResolutionCompCochainIso_hom :
    (canonicalAmbientResolutionCompCochainIso j k J).hom =
      (canonicalAmbientResolutionCompLift j k J).hom' := rfl

/-- Retained cochain terms retain both original extension transports. -/
theorem canonicalAmbientResolutionCompLift_hom'_f (n : ℤ) (m : ℕ) (hm : (m : ℤ) = n) :
    (canonicalAmbientResolutionCompLift j k J).hom'.f n =
      ((canonicalAmbientChartResolution J (k ≫ j)).cochainComplexXIso n m hm).hom ≫
        (restrictFunctorComp k j).hom.app (J.cocomplex.X m) ≫
        ((canonicalAmbientChartResolution
          (canonicalAmbientChartResolution J j) k).cochainComplexXIso n m hm).inv := by
  rw [InjectiveResolution.Hom.hom'_f (canonicalAmbientResolutionCompLift j k J) n m hm]
  erw [canonicalAmbientResolutionCompIso_hom_f]

/-- The original extension comparisons compose with this same fixed-resolution lift. -/
theorem canonicalAmbientResolutionComp_mapExtend :
    (canonicalRestrictionCompComplexIso j k (.up ℤ) J.cochainComplex).hom ≫
        ((restrictFunctor k).mapHomologicalComplex (.up ℤ)).map
          (J.cocomplex.mapExtendIso (restrictFunctor j) ComplexShape.embeddingUpNat).hom ≫
        ((canonicalAmbientChartResolution J j).cocomplex.mapExtendIso
          (restrictFunctor k) ComplexShape.embeddingUpNat).hom =
      (J.cocomplex.mapExtendIso (restrictFunctor (k ≫ j)) ComplexShape.embeddingUpNat).hom ≫
        (canonicalAmbientResolutionCompLift j k J).hom' := by
  let J₁ := canonicalAmbientChartResolution J j
  let J₂ := canonicalAmbientChartResolution J₁ k
  let J₀ := canonicalAmbientChartResolution J (k ≫ j)
  let E₁ : ((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex ≅
      J₁.cochainComplex :=
    J.cocomplex.mapExtendIso (restrictFunctor j) ComplexShape.embeddingUpNat
  let E₂ : ((restrictFunctor k).mapHomologicalComplex (.up ℤ)).obj J₁.cochainComplex ≅
      J₂.cochainComplex :=
    J₁.cocomplex.mapExtendIso (restrictFunctor k) ComplexShape.embeddingUpNat
  let E₀ : ((restrictFunctor (k ≫ j)).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex ≅
      J₀.cochainComplex :=
    J.cocomplex.mapExtendIso (restrictFunctor (k ≫ j)) ComplexShape.embeddingUpNat
  let r := (canonicalAmbientResolutionCompLift j k J).hom'
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    canonicalRestrictionCompComplexIso_hom_f]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h₁ : E₁.hom.f (m : ℤ) ≫ (J₁.cochainComplexXIso (m : ℤ) m rfl).hom =
        (restrictFunctor j).map (J.cochainComplexXIso (m : ℤ) m rfl).hom :=
      J.cocomplex.mapExtendIso_hom_f_extendXIso (restrictFunctor j)
        ComplexShape.embeddingUpNat rfl
    have h₂ : E₂.hom.f (m : ℤ) ≫ (J₂.cochainComplexXIso (m : ℤ) m rfl).hom =
        (restrictFunctor k).map (J₁.cochainComplexXIso (m : ℤ) m rfl).hom :=
      J₁.cocomplex.mapExtendIso_hom_f_extendXIso (restrictFunctor k)
        ComplexShape.embeddingUpNat rfl
    have h₀ : E₀.hom.f (m : ℤ) ≫ (J₀.cochainComplexXIso (m : ℤ) m rfl).hom =
        (restrictFunctor (k ≫ j)).map (J.cochainComplexXIso (m : ℤ) m rfl).hom :=
      J.cocomplex.mapExtendIso_hom_f_extendXIso (restrictFunctor (k ≫ j))
        ComplexShape.embeddingUpNat rfl
    have hr : r.f (m : ℤ) ≫ (J₂.cochainComplexXIso (m : ℤ) m rfl).hom =
        (J₀.cochainComplexXIso (m : ℤ) m rfl).hom ≫
          (restrictFunctorComp k j).hom.app (J.cocomplex.X m) := by
      rw [canonicalAmbientResolutionCompLift_hom'_f j k J (m : ℤ) m rfl]
      simp only [J₂, J₁, J₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hα := (restrictFunctorComp k j).hom.naturality
      (J.cochainComplexXIso (m : ℤ) m rfl).hom
    change (restrictFunctor (k ≫ j)).map (J.cochainComplexXIso (m : ℤ) m rfl).hom ≫
        (restrictFunctorComp k j).hom.app (J.cocomplex.X m) =
      (restrictFunctorComp k j).hom.app (J.cochainComplex.X (m : ℤ)) ≫
        (restrictFunctor k).map ((restrictFunctor j).map
          (J.cochainComplexXIso (m : ℤ) m rfl).hom) at hα
    apply (cancel_mono (J₂.cochainComplexXIso (m : ℤ) m rfl).hom).mp
    change (restrictFunctorComp k j).hom.app (J.cochainComplex.X (m : ℤ)) ≫
        (restrictFunctor k).map (E₁.hom.f (m : ℤ)) ≫ E₂.hom.f (m : ℤ) ≫
          (J₂.cochainComplexXIso (m : ℤ) m rfl).hom =
      E₀.hom.f (m : ℤ) ≫ r.f (m : ℤ) ≫ (J₂.cochainComplexXIso (m : ℤ) m rfl).hom
    calc
      _ = (restrictFunctorComp k j).hom.app (J.cochainComplex.X (m : ℤ)) ≫
          (restrictFunctor k).map
            (E₁.hom.f (m : ℤ) ≫ (J₁.cochainComplexXIso (m : ℤ) m rfl).hom) := by
        rw [h₂, Functor.map_comp]
      _ = (restrictFunctorComp k j).hom.app (J.cochainComplex.X (m : ℤ)) ≫
          (restrictFunctor k).map ((restrictFunctor j).map
            (J.cochainComplexXIso (m : ℤ) m rfl).hom) := by rw [h₁]
      _ = (restrictFunctor (k ≫ j)).map (J.cochainComplexXIso (m : ℤ) m rfl).hom ≫
          (restrictFunctorComp k j).hom.app (J.cocomplex.X m) := hα.symm
      _ = E₀.hom.f (m : ℤ) ≫ r.f (m : ℤ) ≫
          (J₂.cochainComplexXIso (m : ℤ) m rfl).hom := by
        rw [hr, ← Category.assoc, h₀]
  · exact ((restrictFunctor (k ≫ j)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 n (by lia))).eq_of_src _ _

end Restriction

section Closed
variable {W' W U V' V P : Scheme.{u}} (f : U ⟶ P) [IsClosedImmersion f]
  {L : P.Modules} (J : InjectiveResolution L)
  (a : W ⟶ U) (j : V ⟶ P) (b : W ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsClosedImmersion b]
  (h : IsPullback a b f j)
  (c : W' ⟶ W) (k : V' ⟶ V) (d : W' ⟶ V')
  [IsOpenImmersion c] [IsOpenImmersion k] [IsClosedImmersion d]
  (h' : IsPullback c d b k)

/-- Each original model comparison retains its ordinary open arrow and extension map. -/
theorem closedImmersionModelOpenIso_hom_f (n : ℤ) :
    (closedImmersionModelOpenIso f J a j b h).hom.f n =
      (closedImmersionRightAdjointOpenIso a b f j h).hom.app (J.cochainComplex.X n) ≫
        (closedImmersionRightAdjoint b).map
          ((J.cocomplex.mapExtendIso (restrictFunctor j) ComplexShape.embeddingUpNat).hom.f n) :=
  rfl

/-- The actual direct and iterated open comparisons on one fixed ambient resolution
are strictly equal after the original restriction and resolution comparisons. -/
theorem closedImmersionModelOpenIso_comp :
    (canonicalRestrictionCompComplexIso a c (.up ℤ)
        (((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex)).hom ≫
        ((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map
          (closedImmersionModelOpenIso f J a j b h).hom ≫
        (closedImmersionModelOpenIso b (canonicalAmbientChartResolution J j) c k d h').hom =
      (closedImmersionModelOpenIso f J (c ≫ a) (k ≫ j) d (h'.paste_horiz h)).hom ≫
        ((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
          (canonicalAmbientResolutionCompLift j k J).hom' := by
  let J₁ := canonicalAmbientChartResolution J j
  let E₁ := J.cocomplex.mapExtendIso (restrictFunctor j) ComplexShape.embeddingUpNat
  let E₂ := J₁.cocomplex.mapExtendIso (restrictFunctor k) ComplexShape.embeddingUpNat
  let E₀ := J.cocomplex.mapExtendIso (restrictFunctor (k ≫ j)) ComplexShape.embeddingUpNat
  let O₁ := (closedImmersionRightAdjointOpenIso a b f j h).hom
  let O₂ := (closedImmersionRightAdjointOpenIso c d b k h').hom
  let O₀ := (closedImmersionRightAdjointOpenIso (c ≫ a) d f (k ≫ j)
    (h'.paste_horiz h)).hom
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    canonicalRestrictionCompComplexIso_hom_f, closedImmersionModelOpenIso_hom_f]
  simp only [Functor.map_comp, Category.assoc]
  have hN := O₂.naturality (E₁.hom.f n)
  change (restrictFunctor c).map ((closedImmersionRightAdjoint b).map (E₁.hom.f n)) ≫
      O₂.app (J₁.cochainComplex.X n) =
    O₂.app ((restrictFunctor j).obj (J.cochainComplex.X n)) ≫
      (closedImmersionRightAdjoint d).map ((restrictFunctor k).map (E₁.hom.f n)) at hN
  have hO := canonicalClosedRightAdjointOpenIso_comp a b f j c d k h h'
    (J.cochainComplex.X n)
  have hE := congrArg (fun t => t.f n) (canonicalAmbientResolutionComp_mapExtend j k J)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    canonicalRestrictionCompComplexIso_hom_f] at hE
  change (restrictFunctorComp k j).hom.app (J.cochainComplex.X n) ≫
      (restrictFunctor k).map (E₁.hom.f n) ≫ E₂.hom.f n =
    E₀.hom.f n ≫ (canonicalAmbientResolutionCompLift j k J).hom'.f n at hE
  change (restrictFunctorComp c a).hom.app
      ((closedImmersionRightAdjoint f).obj (J.cochainComplex.X n)) ≫
      (restrictFunctor c).map (O₁.app (J.cochainComplex.X n)) ≫
      (restrictFunctor c).map ((closedImmersionRightAdjoint b).map (E₁.hom.f n)) ≫
      O₂.app (J₁.cochainComplex.X n) ≫ (closedImmersionRightAdjoint d).map (E₂.hom.f n) =
    O₀.app (J.cochainComplex.X n) ≫ (closedImmersionRightAdjoint d).map (E₀.hom.f n) ≫
      (closedImmersionRightAdjoint d).map
        ((canonicalAmbientResolutionCompLift j k J).hom'.f n)
  calc
    _ = (restrictFunctorComp c a).hom.app
        ((closedImmersionRightAdjoint f).obj (J.cochainComplex.X n)) ≫
        (restrictFunctor c).map (O₁.app (J.cochainComplex.X n)) ≫
        O₂.app ((restrictFunctor j).obj (J.cochainComplex.X n)) ≫
        (closedImmersionRightAdjoint d).map ((restrictFunctor k).map (E₁.hom.f n)) ≫
        (closedImmersionRightAdjoint d).map (E₂.hom.f n) := by
      simpa only [Category.assoc] using congrArg
        (fun z => (restrictFunctorComp c a).hom.app
            ((closedImmersionRightAdjoint f).obj (J.cochainComplex.X n)) ≫
          (restrictFunctor c).map (O₁.app (J.cochainComplex.X n)) ≫ z ≫
            (closedImmersionRightAdjoint d).map (E₂.hom.f n)) hN
    _ = O₀.app (J.cochainComplex.X n) ≫
        (closedImmersionRightAdjoint d).map
          ((restrictFunctorComp k j).hom.app (J.cochainComplex.X n)) ≫
        (closedImmersionRightAdjoint d).map ((restrictFunctor k).map (E₁.hom.f n)) ≫
        (closedImmersionRightAdjoint d).map (E₂.hom.f n) := by
      simpa only [O₀, O₁, O₂, Category.assoc] using congrArg
        (fun z => z ≫ (closedImmersionRightAdjoint d).map
            ((restrictFunctor k).map (E₁.hom.f n)) ≫
          (closedImmersionRightAdjoint d).map (E₂.hom.f n)) hO
    _ = O₀.app (J.cochainComplex.X n) ≫ (closedImmersionRightAdjoint d).map
        ((restrictFunctorComp k j).hom.app (J.cochainComplex.X n) ≫
          (restrictFunctor k).map (E₁.hom.f n) ≫ E₂.hom.f n) := by
      simp only [Functor.map_comp]
    _ = O₀.app (J.cochainComplex.X n) ≫ (closedImmersionRightAdjoint d).map
        (E₀.hom.f n ≫ (canonicalAmbientResolutionCompLift j k J).hom'.f n) := by rw [hE]
    _ = _ := by simp only [Functor.map_comp]

/-- Taking native homology preserves the same strict fixed-resolution composition equation. -/
theorem closedImmersionModelOpenIso_comp_homology (n : ℤ) :
    homologyMap (canonicalRestrictionCompComplexIso a c (.up ℤ)
        (((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex)).hom n ≫
        homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map
          (closedImmersionModelOpenIso f J a j b h).hom) n ≫
        homologyMap (closedImmersionModelOpenIso b
          (canonicalAmbientChartResolution J j) c k d h').hom n =
      homologyMap (closedImmersionModelOpenIso f J (c ≫ a) (k ≫ j) d
        (h'.paste_horiz h)).hom n ≫
        homologyMap (((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
          (canonicalAmbientResolutionCompLift j k J).hom') n := by
  have ht := congrArg (fun t => homologyMap t n)
    (closedImmersionModelOpenIso_comp f J a j b h c k d h')
  simpa only [homologyMap_comp] using ht

end Closed
end AlgebraicGeometry.Scheme.Modules
