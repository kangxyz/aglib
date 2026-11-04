/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Bidual
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Poincare.Power
public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified.Symmetry

/-!
# The normalized swap of the original polarized Poincare bundle

The bundle is the original Poincare pair at the actual line-bundle morphism.
Its parameter-unit frame comes from the original rigidified unit comparison.
The swap is chosen once as a source-rigidified isomorphism, and restriction
at the common origin proves its other axis law and its diagonal law.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible Scheme.Group
open Scheme.Modules.Invertible.PowerPullback
open Scheme.Modules.Invertible.TrivializedPower
open Scheme.Modules.Invertible.TrivializedPowerTorsor

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

local notation "X₂" => pullback A.hom A.hom

/-- The original source-unit axis of the pair on `A × A`. -/
def polarizedSourceAxis : A.left ⟶ X₂ :=
  originSection A.hom η[A].left (by simp) A

/-- The original parameter-unit axis, using the native right unitor. -/
def polarizedParameterAxis : A.left ⟶ X₂ :=
  (ρ_ A).inv.left ≫ (familyScheme A.hom).map η[A]

/-- The native swap of the same fibre product. -/
def polarizedSwap : X₂ ⟶ X₂ := (β_ A A).hom.left

/-- The original diagonal. -/
def polarizedDiagonal : A.left ⟶ X₂ := (lift (𝟙 A) (𝟙 A)).left

/-- The common origin of the two axes. -/
def polarizedOrigin : (Spec (.of k)) ⟶ X₂ := η[A].left ≫ polarizedSourceAxis A

set_option backward.isDefEq.respectTransparency false in
/-- The actual parameter axis has coordinates `(id, 0)`. -/
theorem polarizedParameterAxis_eq_lift :
    polarizedParameterAxis A = (lift (𝟙 A) (1 : A ⟶ A)).left := by
  change ((ρ_ A).inv ≫ A ◁ η[A]).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, rightUnitor_inv_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, rightUnitor_inv_snd, lift_snd]
    rw [MonObj.one_eq_one, MonObj.comp_one]

private theorem origin_comp_rightUnitor_inv :
    η[A].left ≫ (ρ_ A).inv.left = originSection A.hom η[A].left (by simp) (𝟙_ (Over (Spec (.of
      k)))) := by
  rw [originSection_eq_unit_axis]
  change (η[A] ≫ (ρ_ A).inv).left = _
  apply congrArg (fun f : (𝟙_ (Over (Spec (.of k)))) ⟶ A ⊗ (𝟙_ (Over (Spec (.of k)))) => f.left)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, rightUnitor_inv_fst, Category.comp_id, lift_fst, MonObj.one_eq_one]
  · rw [Category.assoc, rightUnitor_inv_snd, lift_snd]
    exact toUnit_unique _ _

/-- The parameter axis has the same origin as the original source axis. -/
theorem origin_comp_polarizedParameterAxis :
    η[A].left ≫ polarizedParameterAxis A = polarizedOrigin A := by
  let f : pullback A.hom (𝟙_ (Over (Spec (.of k)))).hom ⟶ X₂ :=
    (familyScheme A.hom).map η[A]
  change η[A].left ≫ ((ρ_ A).inv.left ≫ f) = polarizedOrigin A
  have h1 := congrArg (fun t => t ≫ f) (origin_comp_rightUnitor_inv A)
  have h2 := RigidifiedPair.originSection_comp_familyScheme_map (p := A.hom)
    (o := η[A].left) (ho := by simp) η[A]
  exact (Category.assoc η[A].left (ρ_ A).inv.left f).symm.trans (h1.trans h2)

/-- The diagonal has that same origin. -/
theorem origin_comp_polarizedDiagonal : η[A].left ≫ polarizedDiagonal A = polarizedOrigin A := by
  unfold polarizedDiagonal polarizedOrigin polarizedSourceAxis
  rw [originSection_eq_unit_axis]
  change (η[A] ≫ lift (𝟙 A) (𝟙 A)).left = (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A)).left
  apply congrArg (fun f : (𝟙_ (Over (Spec (.of k)))) ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id, MonObj.comp_one, MonObj.one_eq_one]
  · simp only [Category.assoc, lift_snd, Category.comp_id]

/-- Swapping the source axis gives the actual parameter axis. -/
theorem polarizedSourceAxis_swap :
    polarizedSourceAxis A ≫ polarizedSwap A = polarizedParameterAxis A := by
  unfold polarizedSourceAxis polarizedSwap
  rw [originSection_eq_unit_axis, polarizedParameterAxis_eq_lift]
  change (lift (1 : A ⟶ A) (𝟙 A) ≫ (β_ A A).hom).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]

/-- Swapping the parameter axis gives the actual source axis. -/
theorem polarizedParameterAxis_swap :
    polarizedParameterAxis A ≫ polarizedSwap A = polarizedSourceAxis A := by
  unfold polarizedSourceAxis polarizedSwap
  rw [originSection_eq_unit_axis, polarizedParameterAxis_eq_lift]
  change (lift (𝟙 A) (1 : A ⟶ A) ≫ (β_ A A).hom).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]

omit [GrpObj A] in
/-- The actual swap fixes the whole diagonal map. -/
theorem polarizedDiagonal_swap : polarizedDiagonal A ≫ polarizedSwap A = polarizedDiagonal A := by
  change (lift (𝟙 A) (𝟙 A) ≫ (β_ A A).hom).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd, lift_fst, lift_snd]

/-- The actual swap fixes the common origin. -/
theorem polarizedOrigin_swap : polarizedOrigin A ≫ polarizedSwap A = polarizedOrigin A := by
  calc
    _ = η[A].left ≫ (polarizedSourceAxis A ≫ polarizedSwap A) := Category.assoc _ _ _
    _ = η[A].left ≫ polarizedParameterAxis A :=
      congrArg (fun f => η[A].left ≫ f) (polarizedSourceAxis_swap A)
    _ = _ := origin_comp_polarizedParameterAxis A

variable [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (L : LineBundle A.left)

local notation "D₀" => picardIdentityComponent A.hom P R
local notation "φ" => lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)

/-- The original polarized pair uses the actual Poincare pullback at `phi_L`. -/
def polarizedPoincarePair : RigidifiedPair A.hom η[A].left (by simp) A :=
  poincarePullback A P R φ

local notation "Q" => polarizedPoincarePair A P R L

/-- Restriction to the parameter unit uses the same rigidified Poincare unit. -/
def polarizedPoincareUnitIso :
    RigidifiedPair.Iso (RigidifiedPair.map η[A] Q)
      (trivialRigidifiedPair A.hom η[A].left (by simp) (𝟙_ (Over (Spec (.of k))))) := by
  have h : η[A] ≫ φ = (1 : (𝟙_ (Over (Spec (.of k)))) ⟶ D₀) := by
    rw [lineBundleClassMorphismIdentityComponent_pointed, MonObj.one_eq_one]
  exact (poincarePullbackCompIso A P R η[A] φ).symm.trans
    ((RigidifiedPair.mapCongrIso h (poincareRigidifiedPair A P R)).trans
      (poincareUnitIso A P R (𝟙_ (Over (Spec (.of k))))))

/-- The original parameter-axis frame, transported through the native
right-unitor comparison used by the Poincare parameter unit. -/
def polarizedParameterFrame :
    (Scheme.Modules.pullback (polarizedParameterAxis A)).obj (Q).bundle.val ≅
      SheafOfModules.unit A.left.ringCatSheaf :=
  nativePullFrame (Q).bundle ((familyScheme A.hom).map η[A]) (polarizedParameterAxis A)
    (ρ_ A).inv.left rfl
    ((polarizedPoincareUnitIso A P R L).iso ≪≫
      freeUnitIso (pullback A.hom ((𝟙_ (Over (Spec (.of k))))).hom))

/-- The source frame at the common origin. -/
def polarizedOriginFrame :
    (Scheme.Modules.pullback (polarizedOrigin A)).obj (Q).bundle.val ≅
      SheafOfModules.unit (Spec (.of k)).ringCatSheaf :=
  nativePullFrame (Q).bundle (polarizedSourceAxis A) (polarizedOrigin A) η[A].left rfl
    (Q).rigidification

private theorem nativePullFrame_congr_map {X Y Z : Scheme.{u}} (M : LineBundle X)
    (p : Y ⟶ X) (q : Z ⟶ X) {f g : Z ⟶ Y} (h : f = g) (hf : f ≫ p = q)
    (hg : g ≫ p = q)
    (v : (Scheme.Modules.pullback p).obj M.val ≅ SheafOfModules.unit Y.ringCatSheaf) :
    nativePullFrame M p q f hf v = nativePullFrame M p q g hg v := by
  subst g
  rfl

private theorem unitIso_origin {S X : Scheme.{u}} {p : X ⟶ S} {o : S ⟶ X}
    {ho : o ≫ p = 𝟙 S} {T T' : Over S} (f : T' ⟶ T) (B : RigidifiedPair p o ho T)
    (e : RigidifiedPair.Iso (RigidifiedPair.map f B) (trivialRigidifiedPair p o ho T'))
    (z : T'.left ⟶ pullback p T.hom)
    (hz : originSection p o ho T' ≫ (familyScheme p).map f = z) :
    nativePullFrame B.bundle ((familyScheme p).map f) z (originSection p o ho T') hz
        (e.iso ≪≫ freeUnitIso (pullback p T'.hom)) =
      nativePullFrame B.bundle (originSection p o ho T) z f.left
        ((RigidifiedPair.originSection_comp_familyScheme_map f).symm.trans hz) B.rigidification :=
          by
  subst z
  exact RigidifiedPair.mapToTrivial_originFrame f B e

set_option backward.isDefEq.respectTransparency false in
/-- The two original normalized frames agree at the common origin. -/
theorem polarizedParameterFrame_origin :
    nativePullFrame (Q).bundle (polarizedParameterAxis A) (polarizedOrigin A) η[A].left
      (origin_comp_polarizedParameterAxis A) (polarizedParameterFrame A P R L) =
    polarizedOriginFrame A P R L := by
  let F := (familyScheme A.hom).map η[A]
  let a := (ρ_ A).inv.left
  let s := originSection A.hom η[A].left (by simp) (𝟙_ (Over (Spec (.of k))))
  let v := (polarizedPoincareUnitIso A P R L).iso ≪≫ freeUnitIso (pullback A.hom ((𝟙_ (Over (Spec
    (.of k))))).hom)
  have hz : s ≫ F = polarizedOrigin A :=
    RigidifiedPair.originSection_comp_familyScheme_map η[A]
  calc
    _ = nativePullFrame (Q).bundle F (polarizedOrigin A) (η[A].left ≫ a)
        (by rw [Category.assoc]; exact origin_comp_polarizedParameterAxis A) v :=
      PowerBaseChange.nativePullFrame_comp (Q).bundle F (polarizedParameterAxis A)
        (polarizedOrigin A) a
        η[A].left rfl (origin_comp_polarizedParameterAxis A) v
    _ = nativePullFrame (Q).bundle F (polarizedOrigin A) s hz v :=
      nativePullFrame_congr_map (Q).bundle F (polarizedOrigin A)
        (origin_comp_rightUnitor_inv A) _ hz v
    _ = _ := unitIso_origin η[A] Q (polarizedPoincareUnitIso A P R L) (polarizedOrigin A) hz

/-- The actual transposed bundle rigidified by the original parameter frame. -/
def polarizedSwappedPair : RigidifiedPair A.hom η[A].left (by simp) A where
  bundle := pullbackLineBundle (polarizedSwap A) (Q).bundle
  rigidification := (pullbackTriangleIso (polarizedSourceAxis A) (polarizedSwap A)
    (polarizedParameterAxis A) (polarizedSourceAxis_swap A)).app (Q).bundle.val ≪≫
      polarizedParameterFrame A P R L

/-- The one actual normalized swap isomorphism of the polarized bundle. -/
def polarizedSwapIso : RigidifiedPair.Iso Q (polarizedSwappedPair A P R L) := by
  let : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have hB : classOf X₂ (Q).bundle = lineBundleDeltaClass A (classOf A.left L) :=
    poincareClass_lineBundleClassMorphism_pullback A P R L
  have h : classOf X₂ (Q).bundle = classOf X₂ (polarizedSwappedPair A P R L).bundle := by
    change classOf X₂ (Q).bundle = pullbackClass (polarizedSwap A) (classOf X₂ (Q).bundle)
    rw [hB]
    exact (lineBundleDeltaClass_swap A (classOf A.left L)).symm
  exact RigidifiedPair.isoOfBundleIso Q (polarizedSwappedPair A P R L)
    (Classical.choice (Quotient.exact h))

/-- Source rigidification makes this isomorphism unique. -/
theorem polarizedSwapIso_unique (e : RigidifiedPair.Iso Q (polarizedSwappedPair A P R L)) :
    e = polarizedSwapIso A P R L :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.hom η[A].left (by simp) _ _

/-- Restriction of the same actual swap through an indicated triangle. -/
def polarizedSwapAt {T : Scheme.{u}} (r t : T ⟶ X₂) (h : r ≫ polarizedSwap A = t) :
    (Scheme.Modules.pullback r).obj (Q).bundle.val ≅ (Scheme.Modules.pullback t).obj
      (Q).bundle.val :=
  restrictPullbackIso r (polarizedSwap A) t h (polarizedSwapIso A P R L).iso

set_option backward.isDefEq.respectTransparency false in
/-- On the source axis the swap carries the parameter frame to the source frame. -/
theorem polarizedSwap_sourceAxis :
    polarizedSwapAt A P R L (polarizedSourceAxis A) (polarizedParameterAxis A)
      (polarizedSourceAxis_swap A) ≪≫ polarizedParameterFrame A P R L = (Q).rigidification := by
  apply CategoryTheory.Iso.ext
  simpa only [polarizedSwapAt, restrictPullbackIso, polarizedSwappedPair, polarizedSourceAxis,
    CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.app_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc] using (polarizedSwapIso A P R L).comm

private theorem iso_eq_refl_of_trans_eq {C : Type*} [Category* C] {M N : C}
    (e : M ≅ M) (v : M ≅ N) (h : e ≪≫ v = v) : e = CategoryTheory.Iso.refl M := by
  apply CategoryTheory.Iso.ext
  apply (cancel_mono v.hom).mp
  simpa only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.refl_hom, Category.id_comp]
    using congrArg CategoryTheory.Iso.hom h

/-- The normalized swap is the identity at the original double origin. -/
theorem polarizedSwap_origin :
    polarizedSwapAt A P R L (polarizedOrigin A) (polarizedOrigin A) (polarizedOrigin_swap A) =
      CategoryTheory.Iso.refl _ := by
  let z := polarizedOrigin A
  let a := polarizedSourceAxis A
  let b := polarizedParameterAxis A
  let v := polarizedParameterFrame A P R L
  have h := congrArg (nativePullFrame (Q).bundle a z η[A].left rfl)
    (polarizedSwap_sourceAxis A P R L)
  have hs := nativePullFrame_restrictPullbackIso a (polarizedSwap A) b
    (polarizedSourceAxis_swap A) (Q).bundle (Q).bundle (polarizedSwapIso A P R L).iso v
    η[A].left z rfl z (origin_comp_polarizedParameterAxis A)
  have ht := hs.symm.trans h
  have hu := congrArg (fun w => polarizedSwapAt A P R L z z (polarizedOrigin_swap A) ≪≫ w)
    (polarizedParameterFrame_origin A P R L)
  exact iso_eq_refl_of_trans_eq _ (polarizedOriginFrame A P R L) (hu.symm.trans ht)

/-- The whole opposite-axis equation for the same normalized swap. -/
theorem polarizedSwap_parameterAxis :
    polarizedSwapAt A P R L (polarizedParameterAxis A) (polarizedSourceAxis A)
      (polarizedParameterAxis_swap A) ≪≫ (Q).rigidification = polarizedParameterFrame A P R L := by
  let z := polarizedOrigin A
  let a := polarizedSourceAxis A
  let b := polarizedParameterAxis A
  apply frame_eq_of_nativePullFrame_eq (Q).bundle b z η[A].left
    (origin_comp_polarizedParameterAxis A) (section_appTop_injective A.hom η[A].left (by simp))
  have h := nativePullFrame_restrictPullbackIso b (polarizedSwap A) a
    (polarizedParameterAxis_swap A) (Q).bundle (Q).bundle (polarizedSwapIso A P R L).iso
    (Q).rigidification η[A].left z (origin_comp_polarizedParameterAxis A) z rfl
  change _ = polarizedSwapAt A P R L z z (polarizedOrigin_swap A) ≪≫
    polarizedOriginFrame A P R L at h
  have hz := congrArg (fun e => e ≪≫ polarizedOriginFrame A P R L)
    (polarizedSwap_origin A P R L)
  exact h.trans (hz.trans ((CategoryTheory.Iso.refl_trans _).trans
    (polarizedParameterFrame_origin A P R L).symm))

/-- The swap restricts to the identity on the whole original diagonal. -/
theorem polarizedSwap_diagonal :
    polarizedSwapAt A P R L (polarizedDiagonal A) (polarizedDiagonal A)
      (polarizedDiagonal_swap A) = CategoryTheory.Iso.refl _ :=
  restrictPullbackIso_fixed_eq_refl_of_point (Q).bundle (polarizedSwap A)
    (polarizedSwapIso A P R L).iso (polarizedDiagonal A) (polarizedDiagonal_swap A)
    η[A].left (polarizedOrigin A) (origin_comp_polarizedDiagonal A)
    (polarizedOrigin_swap A) (section_appTop_injective A.hom η[A].left (by simp))
    (polarizedOriginFrame A P R L) (polarizedSwap_origin A P R L)

/-- The same diagonal identity on every test, by native pullback. -/
theorem polarizedSwap_diagonal_test {T : Scheme.{u}} (x : T ⟶ A.left) :
    polarizedSwapAt A P R L (x ≫ polarizedDiagonal A) (x ≫ polarizedDiagonal A)
      (by rw [Category.assoc, polarizedDiagonal_swap]) = CategoryTheory.Iso.refl _ :=
  restrictPullbackIso_fixed_eq_refl_pullback (polarizedSwap A) (polarizedSwapIso A P R L).iso
    (polarizedDiagonal A) (polarizedDiagonal_swap A) x (x ≫ polarizedDiagonal A) rfl _
    (polarizedSwap_diagonal A P R L)

section Powers

variable [IsSeparated P.obj.hom]

/-- The second-variable law is the pullback of the same universal Poincare
power, transported by the group law of the original `phi_L`. -/
def polarizedSecondPowerIso (n : ℕ) :
    RigidifiedPair.Iso ((Q).power n) (RigidifiedPair.map ((𝟙 A) ^ n) Q) := by
  letI := picardCommGrpObj A.hom P R
  let : IsMonHom φ := isMonHom_lineBundleClassMorphismIdentityComponent A P R
    (classOf A.left L)
  have h : φ ≫ ((𝟙 D₀) ^ n) = ((𝟙 A) ^ n) ≫ φ := by
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, Category.id_comp]
  exact (poincarePullbackPowerIso A P R φ n).trans
    ((RigidifiedPair.mapCongrIso h (poincareRigidifiedPair A P R)).trans
      (poincarePullbackCompIso A P R ((𝟙 A) ^ n) φ))

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
private theorem unit_comp_power (n : ℕ) : η[A] ≫ (𝟙 A) ^ n = η[A] := by
  rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- The original source axis commutes with parameter multiplication. -/
theorem sourceAxis_secondPower (n : ℕ) :
    polarizedSourceAxis A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) =
      ((𝟙 A) ^ n).left ≫ polarizedSourceAxis A :=
  RigidifiedPair.originSection_comp_familyScheme_map (p := A.hom) (o := η[A].left)
    (ho := by simp) ((𝟙 A) ^ n)

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
private theorem origin_secondPower (n : ℕ) :
    polarizedOrigin A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) = polarizedOrigin A := by
  have h := congrArg (fun g : (𝟙_ (Over (Spec (.of k)))) ⟶ A => g.left) (unit_comp_power A n)
  change η[A].left ≫ ((𝟙 A) ^ n).left = η[A].left at h
  let a := polarizedSourceAxis A
  let t : X₂ ⟶ X₂ := (familyScheme A.hom).map ((𝟙 A) ^ n)
  exact (Category.assoc η[A].left a t).trans
    ((congrArg (fun q => η[A].left ≫ q) (sourceAxis_secondPower A n)).trans
      ((Category.assoc η[A].left ((𝟙 A) ^ n).left a).symm.trans
        (congrArg (fun q => q ≫ a) h)))

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- Parameter multiplication fixes the original parameter axis. -/
theorem parameterAxis_secondPower (n : ℕ) :
    polarizedParameterAxis A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) =
      polarizedParameterAxis A := by
  rw [polarizedParameterAxis_eq_lift]
  change (lift (𝟙 A) (1 : A ⟶ A) ≫ (A ◁ ((𝟙 A) ^ n))).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, lift_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd,
      MonObj.comp_pow, Category.comp_id, one_pow]

set_option backward.isDefEq.respectTransparency false in
/-- The actual second power preserves the original source frame. -/
theorem polarizedSecondPowerIso_sourceAxis (n : ℕ) :
    restrictPullbackIso (polarizedSourceAxis A) ((familyScheme A.hom).map ((𝟙 A) ^ n))
        (polarizedSourceAxis A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n)) rfl
        (polarizedSecondPowerIso A P R L n).iso ≪≫
      nativePullFrame (Q).bundle (polarizedSourceAxis A)
        (polarizedSourceAxis A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n))
        ((𝟙 A) ^ n).left (sourceAxis_secondPower A n).symm (Q).rigidification =
    PowerDescent.powerFrame (Q).bundle (polarizedSourceAxis A) (Q).rigidification n := by
  let m := (𝟙 A) ^ n
  let a := polarizedSourceAxis A
  let t := (familyScheme A.hom).map m
  have h := (polarizedSecondPowerIso A P R L n).comm
  have hr := RigidifiedPair.map_rigidification_triangle m Q (a ≫ t) rfl
  rw [hr] at h
  apply CategoryTheory.Iso.ext
  simpa only [restrictPullbackIso, polarizedSourceAxis, a, t, m,
    RigidifiedPair.power_rigidification, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.app_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
private theorem polarizedSecondPowerIso_origin (n : ℕ) :
    restrictPullbackIso (polarizedOrigin A) ((familyScheme A.hom).map ((𝟙 A) ^ n))
        (polarizedOrigin A) (origin_secondPower A n) (polarizedSecondPowerIso A P R L n).iso ≪≫
      polarizedOriginFrame A P R L =
    PowerDescent.powerFrame (Q).bundle (polarizedOrigin A) (polarizedOriginFrame A P R L) n := by
  let m := (𝟙 A) ^ n
  let a := polarizedSourceAxis A
  let t := (familyScheme A.hom).map m
  let z := polarizedOrigin A
  let u := (Q).rigidification
  let e := (polarizedSecondPowerIso A P R L n).iso
  let v := nativePullFrame (Q).bundle a (a ≫ t) m.left (sourceAxis_secondPower A n).symm u
  have hη : η[A].left ≫ (a ≫ t) = z := (Category.assoc _ _ _).symm.trans
    (origin_secondPower A n)
  have hm := congrArg (fun g : (𝟙_ (Over (Spec (.of k)))) ⟶ A => g.left) (unit_comp_power A n)
  have hv : nativePullFrame (Q).bundle (a ≫ t) z η[A].left hη v =
      polarizedOriginFrame A P R L := by
    exact (PowerBaseChange.nativePullFrame_comp (Q).bundle a (a ≫ t) z m.left η[A].left
      (sourceAxis_secondPower A n).symm hη u).trans
        (nativePullFrame_congr_map (Q).bundle a z hm _ rfl u)
  have ha := nativePullFrame_restrictPullbackIso a t (a ≫ t) rfl
    (tensorPowerLineBundle X₂ (Q).bundle n) (Q).bundle e v η[A].left z rfl z hη
  have hh := congrArg (nativePullFrame (tensorPowerLineBundle X₂ (Q).bundle n) a z η[A].left rfl)
    (polarizedSecondPowerIso_sourceAxis A P R L n)
  have ht := PowerDescent.powerFrame_nativePullFrame (Q).bundle a z η[A].left rfl u n
  exact (congrArg (fun i => restrictPullbackIso z t z (origin_secondPower A n) e ≪≫ i)
    hv).symm.trans (ha.symm.trans (hh.trans ht))

set_option backward.isDefEq.respectTransparency false in
/-- The actual second power preserves the whole original parameter-axis frame. -/
theorem polarizedSecondPowerIso_parameterAxis (n : ℕ) :
    restrictPullbackIso (polarizedParameterAxis A) ((familyScheme A.hom).map ((𝟙 A) ^ n))
        (polarizedParameterAxis A) (parameterAxis_secondPower A n)
        (polarizedSecondPowerIso A P R L n).iso ≪≫ polarizedParameterFrame A P R L =
      PowerDescent.powerFrame (Q).bundle (polarizedParameterAxis A)
        (polarizedParameterFrame A P R L) n := by
  let t := (familyScheme A.hom).map ((𝟙 A) ^ n)
  let a := polarizedParameterAxis A
  let z := polarizedOrigin A
  let v := polarizedParameterFrame A P R L
  let e := (polarizedSecondPowerIso A P R L n).iso
  let h := origin_comp_polarizedParameterAxis A
  apply frame_eq_of_nativePullFrame_eq (tensorPowerLineBundle X₂ (Q).bundle n) a z η[A].left h
    (section_appTop_injective A.hom η[A].left (by simp))
  have h1 := nativePullFrame_restrictPullbackIso a t a (parameterAxis_secondPower A n)
    (tensorPowerLineBundle X₂ (Q).bundle n) (Q).bundle e v η[A].left z h z h
  have h2 := polarizedParameterFrame_origin A P R L
  have h3 := PowerDescent.powerFrame_nativePullFrame (Q).bundle a z η[A].left h v n
  exact h1.trans ((congrArg (fun i => restrictPullbackIso z t z (origin_secondPower A n) e ≪≫ i)
    h2).trans ((polarizedSecondPowerIso_origin A P R L n).trans
      ((congrArg (fun i => PowerDescent.powerFrame (Q).bundle z i n) h2).symm.trans h3.symm)))

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The original swap exchanges the two multiplication maps. -/
theorem swap_comp_secondMultiplication (n : ℕ) :
    polarizedSwap A ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) =
      familyMapOfHom ((𝟙 A) ^ n) A ≫ polarizedSwap A := by
  rw [familyMapOfHom_eq_tensorHom, tensorHom_id]
  exact congrArg (fun f : A ⊗ A ⟶ A ⊗ A => f.left)
    (BraidedCategory.braiding_naturality_left ((𝟙 A) ^ n) A).symm

/-- The first-variable law is obtained by transposing this same second-variable
law through the same normalized swap, with the native power comparison. -/
def polarizedFirstPowerIso (n : ℕ) :
    (tensorPowerLineBundle X₂ (Q).bundle n).val ≅
      (Scheme.Modules.pullback (familyMapOfHom ((𝟙 A) ^ n) A)).obj (Q).bundle.val := by
  let s := polarizedSwap A
  let m := familyMapOfHom ((𝟙 A) ^ n) A
  let t := (familyScheme A.hom).map ((𝟙 A) ^ n)
  let e := (polarizedSwapIso A P R L).iso
  exact powerIso X₂ (L := (Q).bundle) (M := pullbackLineBundle s (Q).bundle) e n ≪≫
    (pullbackPowerIso s (Q).bundle n).symm ≪≫
    (Scheme.Modules.pullback s).mapIso (polarizedSecondPowerIso A P R L n).iso ≪≫
    (pullbackTriangleIso s t (m ≫ s) (swap_comp_secondMultiplication A n)).app (Q).bundle.val ≪≫
    ((Scheme.Modules.pullbackComp m s).app (Q).bundle.val).symm ≪≫
    (Scheme.Modules.pullback m).mapIso e.symm

/-- The second-variable power preserves the original rigidified unit
trivialization after restricting the parameter to the base unit. -/
theorem polarizedSecondPowerIso_unit (n : ℕ) :
    ((RigidifiedPair.mapPowerIso η[A] Q n).symm.trans
        (RigidifiedPair.Iso.map η[A] (polarizedSecondPowerIso A P R L n))).trans
      (((RigidifiedPair.mapCompIso η[A] ((𝟙 A) ^ n) Q).symm).trans
        ((RigidifiedPair.mapCongrIso (show η[A] ≫ (𝟙 A) ^ n = η[A] by
          rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]) Q).trans
          (polarizedPoincareUnitIso A P R L))) =
    ((polarizedPoincareUnitIso A P R L).power n).trans (RigidifiedPair.trivialPowerIso (𝟙_ (Over
      (Spec (.of k)))) n) :=
  RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral
    A.hom η[A].left (by simp) _ _

set_option backward.isDefEq.respectTransparency false in
/-- On a test where the same swap fixes the bundle, the first power restricts
to the second power followed by the inverse swap at the target. -/
theorem polarizedFirstPowerIso_fixed {T : Scheme.{u}} (n : ℕ)
    (r u v : T ⟶ X₂) (hr : r ≫ polarizedSwap A = r)
    (hu : r ≫ familyMapOfHom ((𝟙 A) ^ n) A = u)
    (hv : r ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) = v)
    (hs : polarizedSwapAt A P R L r r hr = CategoryTheory.Iso.refl _) :
    restrictPullbackIso r (familyMapOfHom ((𝟙 A) ^ n) A) u hu
        (polarizedFirstPowerIso A P R L n) =
      restrictPullbackIso r ((familyScheme A.hom).map ((𝟙 A) ^ n)) v hv
        (polarizedSecondPowerIso A P R L n).iso ≪≫
      (polarizedSwapAt A P R L u v (by rw [← hu, Category.assoc,
        ← swap_comp_secondMultiplication, ← Category.assoc, hr, hv])).symm := by
  let s := polarizedSwap A
  let m := familyMapOfHom ((𝟙 A) ^ n) A
  let t := (familyScheme A.hom).map ((𝟙 A) ^ n)
  let e := (polarizedSwapIso A P R L).iso
  let B := (Q).bundle
  let b := (polarizedSecondPowerIso A P R L n).iso
  let a := powerIso X₂ (L := B) (M := pullbackLineBundle s B) e n ≪≫
    (pullbackPowerIso s B n).symm
  have hp : restrictPullbackIso r s r hr a = CategoryTheory.Iso.refl _ := by
    have h := restrictPullbackIso_power r s r hr B B e n
    change restrictPullbackIso r s r hr a =
      pullbackPowerIso r B n ≪≫ powerIso T (L := pullbackLineBundle r B)
        (M := pullbackLineBundle r B) (polarizedSwapAt A P R L r r hr) n ≪≫
        (pullbackPowerIso r B n).symm at h
    let p := pullbackPowerIso r B n
    let Br := pullbackLineBundle r B
    have h₁ := congrArg (fun z => p ≪≫ powerIso T (L := Br) (M := Br) z n ≪≫ p.symm) hs
    have h₂ := congrArg (fun z => p ≪≫ z ≪≫ p.symm) (UnitPower.powerIso_refl T Br n)
    have hc : p ≪≫ CategoryTheory.Iso.refl _ ≪≫ p.symm = CategoryTheory.Iso.refl _ :=
      (congrArg (fun z => p ≪≫ z) (CategoryTheory.Iso.refl_trans p.symm)).trans
        (CategoryTheory.Iso.self_symm_id p)
    exact h.trans (h₁.trans (h₂.trans hc))
  have hh : polarizedFirstPowerIso A P R L n =
      a ≪≫ restrictPullbackIso s t (m ≫ s) (swap_comp_secondMultiplication A n) b ≪≫
        ((pullbackComp m s).app B.val).symm ≪≫ (Scheme.Modules.pullback m).mapIso e.symm := by
    simp only [polarizedFirstPowerIso, a, b, e, s, m, t, B, restrictPullbackIso,
      CategoryTheory.Iso.trans_assoc]
  exact (congrArg (restrictPullbackIso r m u hu) hh).trans
    (restrictPullbackIso_transpose_fixed s m t (swap_comp_secondMultiplication A n)
      e b a r hr u v hu hv hp)

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- On the diagonal of a torsion test the first multiplication lands on the source axis. -/
theorem diagonal_firstPower_of_unit {T : Over (Spec (.of k))} (x : T ⟶ A) (n : ℕ)
    (hx : x ≫ (𝟙 A) ^ n = 1) :
    (x.left ≫ polarizedDiagonal A) ≫ familyMapOfHom ((𝟙 A) ^ n) A =
      x.left ≫ polarizedSourceAxis A := by
  unfold polarizedDiagonal polarizedSourceAxis
  rw [originSection_eq_unit_axis, familyMapOfHom_eq_tensorHom, tensorHom_id]
  change ((x ≫ lift (𝟙 A) (𝟙 A)) ≫ (((𝟙 A) ^ n) ▷ A)).left =
    (x ≫ lift (1 : A ⟶ A) (𝟙 A)).left
  apply congrArg (fun f : T ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;> simp [hx, MonObj.comp_one]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- On the diagonal of a torsion test the second multiplication lands on the parameter axis. -/
theorem diagonal_secondPower_of_unit {T : Over (Spec (.of k))} (x : T ⟶ A) (n : ℕ)
    (hx : x ≫ (𝟙 A) ^ n = 1) :
    (x.left ≫ polarizedDiagonal A) ≫ (familyScheme A.hom).map ((𝟙 A) ^ n) =
      x.left ≫ polarizedParameterAxis A := by
  rw [polarizedParameterAxis_eq_lift]
  change ((x ≫ lift (𝟙 A) (𝟙 A)) ≫ (A ◁ ((𝟙 A) ^ n))).left =
    (x ≫ lift (𝟙 A) (1 : A ⟶ A)).left
  apply congrArg (fun f : T ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;> simp [hx, MonObj.comp_one]

set_option backward.isDefEq.respectTransparency false in
/-- The two actual torsion trivializations agree on the original diagonal
on every test scheme. -/
theorem polarizedPower_diagonal_trivializations {T : Over (Spec (.of k))} (x : T ⟶ A) (n : ℕ)
    (hx : x ≫ (𝟙 A) ^ n = 1) :
    restrictPullbackIso (x.left ≫ polarizedDiagonal A) (familyMapOfHom ((𝟙 A) ^ n) A)
        (x.left ≫ polarizedSourceAxis A) (diagonal_firstPower_of_unit A x n hx)
        (polarizedFirstPowerIso A P R L n) ≪≫
      nativePullFrame (Q).bundle (polarizedSourceAxis A) (x.left ≫ polarizedSourceAxis A)
        x.left rfl (Q).rigidification =
    restrictPullbackIso (x.left ≫ polarizedDiagonal A) ((familyScheme A.hom).map ((𝟙 A) ^ n))
        (x.left ≫ polarizedParameterAxis A) (diagonal_secondPower_of_unit A x n hx)
        (polarizedSecondPowerIso A P R L n).iso ≪≫
      nativePullFrame (Q).bundle (polarizedParameterAxis A) (x.left ≫ polarizedParameterAxis A)
        x.left rfl (polarizedParameterFrame A P R L) := by
  let a := polarizedSourceAxis A
  let b := polarizedParameterAxis A
  let r := x.left ≫ polarizedDiagonal A
  let s := polarizedSwap A
  let u := x.left ≫ a
  let v := x.left ≫ b
  let e := (polarizedSwapIso A P R L).iso
  let w := polarizedParameterFrame A P R L
  have huv : u ≫ s = v := (Category.assoc x.left a s).trans
    (congrArg (fun f => x.left ≫ f) (polarizedSourceAxis_swap A))
  have hrs : r ≫ s = r := (Category.assoc x.left (polarizedDiagonal A) s).trans
    (congrArg (fun f => x.left ≫ f) (polarizedDiagonal_swap A))
  have h := polarizedFirstPowerIso_fixed A P R L n r u v hrs
    (diagonal_firstPower_of_unit A x n hx) (diagonal_secondPower_of_unit A x n hx)
    (polarizedSwap_diagonal_test A P R L x.left)
  have h1 := nativePullFrame_restrictPullbackIso a s b (polarizedSourceAxis_swap A)
    (Q).bundle (Q).bundle e w x.left u rfl v rfl
  have h2 := congrArg (nativePullFrame (Q).bundle a u x.left rfl)
    (polarizedSwap_sourceAxis A P R L)
  let d := polarizedSwapAt A P R L u v huv
  let u₁ := nativePullFrame (Q).bundle a u x.left rfl (Q).rigidification
  let v₁ := nativePullFrame (Q).bundle b v x.left rfl w
  have hframe : d ≪≫ v₁ = u₁ := h1.symm.trans h2
  have hcancel : d.symm ≪≫ u₁ = v₁ :=
    (congrArg (fun g => d.symm ≪≫ g) hframe.symm).trans
      ((CategoryTheory.Iso.trans_assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≪≫ v₁) (CategoryTheory.Iso.symm_self_id d)).trans
          (CategoryTheory.Iso.refl_trans v₁)))
  let g := restrictPullbackIso r ((familyScheme A.hom).map ((𝟙 A) ^ n)) v
    (diagonal_secondPower_of_unit A x n hx) (polarizedSecondPowerIso A P R L n).iso
  exact (congrArg (fun f => f ≪≫ u₁) h).trans
    ((CategoryTheory.Iso.trans_assoc g d.symm u₁).trans (congrArg (fun f => g ≪≫ f) hcancel))

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- Source multiplication fixes the original source axis. -/
theorem sourceAxis_firstPower (n : ℕ) :
    polarizedSourceAxis A ≫ familyMapOfHom ((𝟙 A) ^ n) A = polarizedSourceAxis A := by
  unfold polarizedSourceAxis
  rw [originSection_eq_unit_axis, familyMapOfHom_eq_tensorHom, tensorHom_id]
  change (lift (1 : A ⟶ A) (𝟙 A) ≫ (((𝟙 A) ^ n) ▷ A)).left = _
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst,
      MonObj.comp_pow, Category.comp_id, one_pow]
  · rw [Category.assoc, whiskerRight_snd, lift_snd]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- The original parameter axis commutes with source multiplication. -/
theorem parameterAxis_firstPower (n : ℕ) :
    polarizedParameterAxis A ≫ familyMapOfHom ((𝟙 A) ^ n) A =
      ((𝟙 A) ^ n).left ≫ polarizedParameterAxis A := by
  rw [polarizedParameterAxis_eq_lift, familyMapOfHom_eq_tensorHom, tensorHom_id]
  change (lift (𝟙 A) (1 : A ⟶ A) ≫ (((𝟙 A) ^ n) ▷ A)).left =
    (((𝟙 A) ^ n) ≫ lift (𝟙 A) (1 : A ⟶ A)).left
  apply congrArg (fun f : A ⟶ A ⊗ A => f.left)
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, lift_fst_assoc,
      lift_fst, lift_snd, Category.id_comp, Category.comp_id, MonObj.comp_one]

omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
private theorem origin_firstPower (n : ℕ) :
    polarizedOrigin A ≫ familyMapOfHom ((𝟙 A) ^ n) A = polarizedOrigin A := by
  let a := polarizedSourceAxis A
  let m := familyMapOfHom ((𝟙 A) ^ n) A
  exact (Category.assoc η[A].left a m).trans
    (congrArg (fun f => η[A].left ≫ f) (sourceAxis_firstPower A n))

set_option backward.isDefEq.respectTransparency false in
private theorem polarizedFirstPowerIso_origin (n : ℕ) :
    restrictPullbackIso (polarizedOrigin A) (familyMapOfHom ((𝟙 A) ^ n) A)
        (polarizedOrigin A) (origin_firstPower A n) (polarizedFirstPowerIso A P R L n) ≪≫
      polarizedOriginFrame A P R L =
    PowerDescent.powerFrame (Q).bundle (polarizedOrigin A) (polarizedOriginFrame A P R L) n := by
  let z := polarizedOrigin A
  have h := polarizedFirstPowerIso_fixed A P R L n z z z (polarizedOrigin_swap A)
    (origin_firstPower A n) (origin_secondPower A n) (polarizedSwap_origin A P R L)
  rw [polarizedSwap_origin] at h
  have he : (CategoryTheory.Iso.refl ((Scheme.Modules.pullback z).obj (Q).bundle.val)).symm =
      CategoryTheory.Iso.refl _ := rfl
  rw [he, CategoryTheory.Iso.trans_refl] at h
  exact (congrArg (fun f => f ≪≫ polarizedOriginFrame A P R L) h).trans
    (polarizedSecondPowerIso_origin A P R L n)

/-- The transposed first power preserves the whole original source-axis frame. -/
theorem polarizedFirstPowerIso_sourceAxis (n : ℕ) :
    restrictPullbackIso (polarizedSourceAxis A) (familyMapOfHom ((𝟙 A) ^ n) A)
        (polarizedSourceAxis A) (sourceAxis_firstPower A n)
        (polarizedFirstPowerIso A P R L n) ≪≫ (Q).rigidification =
    PowerDescent.powerFrame (Q).bundle (polarizedSourceAxis A) (Q).rigidification n :=
  powerFrame_axis_of_origin (Q).bundle _ _ _ (sourceAxis_firstPower A n) η[A].left
    (polarizedOrigin A) rfl rfl (origin_firstPower A n) (section_appTop_injective A.hom η[A].left
      (by simp)) n
    (Q).rigidification (Q).rigidification (polarizedFirstPowerIso A P R L n) rfl
    (polarizedFirstPowerIso_origin A P R L n)

set_option backward.isDefEq.respectTransparency false in
/-- The transposed first power preserves the whole original parameter-axis frame. -/
theorem polarizedFirstPowerIso_parameterAxis (n : ℕ) :
    restrictPullbackIso (polarizedParameterAxis A) (familyMapOfHom ((𝟙 A) ^ n) A)
        (polarizedParameterAxis A ≫ familyMapOfHom ((𝟙 A) ^ n) A) rfl
        (polarizedFirstPowerIso A P R L n) ≪≫
      nativePullFrame (Q).bundle (polarizedParameterAxis A)
        (polarizedParameterAxis A ≫ familyMapOfHom ((𝟙 A) ^ n) A) ((𝟙 A) ^ n).left
        (parameterAxis_firstPower A n).symm (polarizedParameterFrame A P R L) =
    PowerDescent.powerFrame (Q).bundle (polarizedParameterAxis A)
      (polarizedParameterFrame A P R L) n := by
  let m := (𝟙 A) ^ n
  let t := familyMapOfHom m A
  let a := polarizedParameterAxis A
  let z := polarizedOrigin A
  let v := polarizedParameterFrame A P R L
  let w := nativePullFrame (Q).bundle a (a ≫ t) m.left (parameterAxis_firstPower A n).symm v
  have ha := origin_comp_polarizedParameterAxis A
  have hb : η[A].left ≫ (a ≫ t) = z := (Category.assoc η[A].left a t).symm.trans
    ((congrArg (fun q => q ≫ t) ha).trans (origin_firstPower A n))
  have hm := congrArg (fun f : (𝟙_ (Over (Spec (.of k)))) ⟶ A => f.left) (unit_comp_power A n)
  have hv : nativePullFrame (Q).bundle (a ≫ t) z η[A].left hb w =
      nativePullFrame (Q).bundle a z η[A].left ha v :=
    (PowerBaseChange.nativePullFrame_comp (Q).bundle a (a ≫ t) z m.left η[A].left
      (parameterAxis_firstPower A n).symm hb v).trans
        (nativePullFrame_congr_map (Q).bundle a z hm _ ha v)
  apply powerFrame_axis_of_origin (Q).bundle t a (a ≫ t) rfl η[A].left z ha hb (origin_firstPower
    A n)
    (section_appTop_injective A.hom η[A].left (by simp)) n v w
    (polarizedFirstPowerIso A P R L n) hv
  have ho := polarizedParameterFrame_origin A P R L
  exact (congrArg (fun f => restrictPullbackIso z t z (origin_firstPower A n)
    (polarizedFirstPowerIso A P R L n) ≪≫ f) ho).trans
      ((polarizedFirstPowerIso_origin A P R L n).trans
        (congrArg (fun f => PowerDescent.powerFrame (Q).bundle z f n) ho.symm))

end Powers
end AlgebraicGeometry.Scheme.RelativePicard
