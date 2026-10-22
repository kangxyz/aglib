/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystem

/-! # Original projections of the actual global-cover restriction tower -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

/-- The original Over pullback-composition map retains the original first
projection. The proof uses its whole adjunction counit equation. -/
@[reassoc]
theorem pullbackComposition_projection {C : Type*} [Category C] [HasPullbacks C]
    {S T X : C} (f : T ⟶ S) (g : S ⟶ X) (P : Over X) :
    ((Over.pullbackComp f g).hom.app P).left ≫
      pullback.fst (pullback.snd P.hom g) f ≫ pullback.fst P.hom g =
        pullback.fst P.hom (f ≫ g) := by
  simp [Over.pullbackComp, conjugateIsoEquiv, Category.assoc]

/-- The native finite-etale base-change-composition iso retains its original
scheme projection, not just its isomorphism class. -/
@[reassoc]
theorem baseChangeComposition_projection {S T X : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ X) (C : FiniteEtale X) :
    (((baseChangeComp g f).app C).hom.hom.left) ≫
      pullback.fst (pullback.snd C.obj.hom g) f ≫ pullback.fst C.obj.hom g =
        pullback.fst C.obj.hom (f ≫ g) :=
  pullbackComposition_projection f g C.obj

/-- Equality transport in a reduction iso also retains the original projection. -/
@[reassoc]
theorem baseChangeReduction_projection {S T X : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ X) (j : T ⟶ X) (h : f ≫ g = j)
    (C : FiniteEtale X) :
    ((((baseChangeComp g f).app C).symm ≪≫
      eqToIso (congrArg (fun j => (baseChange j).obj C) h)).inv.hom.left) ≫
      pullback.fst (pullback.snd C.obj.hom g) f ≫ pullback.fst C.obj.hom g =
        pullback.fst C.obj.hom j := by
  subst j
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.symm_inv] using
    baseChangeComposition_projection f g C

variable {X : Scheme.{u}} (K : X.IdealSheafData) (C : FiniteEtale X)

/-- The original restriction transition commutes with the actual projection to
the given global cover. -/
@[reassoc (attr := simp)]
theorem restrictionCoverSystem_transition_fst (n : ℕ) :
    (restrictionCoverSystem K C).transition n ≫
      pullback.fst C.obj.hom (K ^ (n + 1)).subschemeι =
        pullback.fst C.obj.hom (K ^ n).subschemeι := by
  change (_ ≫ pullback.fst (pullback.snd C.obj.hom (K ^ (n + 1)).subschemeι)
    (stageMap K (Nat.le_succ n))) ≫ _ = _
  rw [Category.assoc]
  exact baseChangeReduction_projection (stageMap K (Nat.le_succ n))
    (K ^ (n + 1)).subschemeι (K ^ n).subschemeι (stageMap_ι K (Nat.le_succ n)) C

/-- Original global-cover projections as actual arrows over the ambient scheme. -/
def restrictionProjection (n : ℕ) :
    (restrictionCoverSystem K C).diagram.obj n ⟶ C.obj :=
  Over.homMk (pullback.fst C.obj.hom (K ^ n).subschemeι) pullback.condition

/-- A whole augmentation packet is assembled while its category and objects
remain abstract, before any actual pullback objects are substituted. -/
def sequenceToConstant {D : Type*} [Category D] {P : ℕ → D}
    (t : ∀ n, P n ⟶ P (n + 1)) (Q : D) (a : ∀ n, P n ⟶ Q)
    (ha : ∀ n, t n ≫ a (n + 1) = a n) :
    Functor.ofSequence t ⟶ (Functor.const ℕ).obj Q :=
  NatTrans.ofSequence a (fun n => by simpa using ha n)

/-- The original global-cover projections form a natural transformation on the
whole native forward tower. -/
def restrictionProjectionNatTrans :
    (restrictionCoverSystem K C).diagram ⟶ (Functor.const ℕ).obj C.obj :=
  sequenceToConstant
    (P := fun n => Over.mk ((restrictionCoverSystem K C).ambientMap n))
    (fun n => Over.homMk ((restrictionCoverSystem K C).transition n)
      ((restrictionCoverSystem K C).transition_ambientMap n))
    C.obj (restrictionProjection K C) (fun n => by
      apply Over.OverMorphism.ext
      exact restrictionCoverSystem_transition_fst K C n)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
