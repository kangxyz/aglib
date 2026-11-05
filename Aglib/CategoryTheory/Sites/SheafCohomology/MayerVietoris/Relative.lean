/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.MayerVietoris.Sections
public import Aglib.CategoryTheory.Abelian.RightDerived.BinarySum
public import Aglib.Algebra.Homology.RightDerived.Zero
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-! # Relative Mayer–Vietoris from the original continuous site functors

A square of continuous functors whose value on every target test is a native
Mayer–Vietoris square gives a short complex of the original sheaf pushforwards.
It is short exact on genuine injective sheaves. Its right-derived sequence is
therefore computed by the single-resolution construction, with no assertion
that any intermediate open direct image is acyclic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' w

namespace CategoryTheory.Sheaf.MayerVietoris

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v w}]
  [HasSheafify K AddCommGrpCat.{max v w}]
  (Q : Square (D ⥤ C))
  [Q.X₁.IsContinuous K J] [Q.X₂.IsContinuous K J]
  [Q.X₃.IsContinuous K J] [Q.X₄.IsContinuous K J]

/-- The original pushforward attached to a continuous test functor. -/
abbrev push (T : D ⥤ C) [T.IsContinuous K J] :
    Sheaf J AddCommGrpCat.{max v w} ⥤ Sheaf K AddCommGrpCat.{max v w} :=
  T.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J

instance push_additive (T : D ⥤ C) [T.IsContinuous K J] :
    (T.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J).Additive where
  map_add := by intros; rfl

/-- Original continuous pushforward preserves finite limits by presheaf evaluation. -/
instance push_preservesFiniteLimits (T : D ⥤ C) [T.IsContinuous K J] :
    PreservesFiniteLimits
      (T.sheafPushforwardContinuous AddCommGrpCat.{max v w} K J) := by
  let P : Sheaf J AddCommGrpCat.{max v w} ⥤ Sheaf K AddCommGrpCat.{max v w} :=
    push J K T
  let E : Sheaf K AddCommGrpCat.{max v w} ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{max v w} :=
    sheafToPresheaf K AddCommGrpCat.{max v w}
  let : PreservesFiniteLimits (P ⋙ E) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{max v w} ⋙
        (Functor.whiskeringLeft _ _ _).obj T.op))
  exact preservesFiniteLimits_of_reflects_of_preserves P E

/-- The original restriction induced contravariantly by a test-functor map. -/
abbrev restriction {T T' : D ⥤ C} [T.IsContinuous K J] [T'.IsContinuous K J]
    (a : T ⟶ T') : push J K T' ⟶ push J K T :=
  Functor.sheafPushforwardContinuousNatTrans a AddCommGrpCat.{max v w} K J

/-- The original sheaf square on a coefficient; arrows are literal restrictions. -/
def coefficientSquare (F : Sheaf J AddCommGrpCat.{max v w}) :
    Square (Sheaf K AddCommGrpCat.{max v w}) where
  f₁₂ := (restriction J K Q.f₂₄).app F
  f₁₃ := (restriction J K Q.f₃₄).app F
  f₂₄ := (restriction J K Q.f₁₂).app F
  f₃₄ := (restriction J K Q.f₁₃).app F
  fac := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map (Q.f₂₄.app V.unop).op ≫ F.obj.map (Q.f₁₂.app V.unop).op =
      F.obj.map (Q.f₃₄.app V.unop).op ≫ F.obj.map (Q.f₁₃.app V.unop).op
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun a => F.obj.map (a.app V.unop).op) Q.fac

variable
  [∀ V : D, Mono (Q.f₂₄.app V)] [∀ V : D, Mono (Q.f₃₄.app V)]
  (hQ : ∀ V : D, (Q.map ((evaluation D C).obj V)).IsPullback)
  (hcover : ∀ V : D, Sieve.ofTwoArrows (Q.f₂₄.app V) (Q.f₃₄.app V) ∈ J (Q.X₄.obj V))

include hQ hcover

omit [HasSheafify J AddCommGrpCat.{max v w}]
  [HasSheafify K AddCommGrpCat.{max v w}] in
/-- Actual sheaf gluing on every target test gives the relative pullback square. -/
theorem coefficientSquare_isPullback (F : Sheaf J AddCommGrpCat.{max v w}) :
    (coefficientSquare J K Q F).IsPullback := by
  let E := sheafToPresheaf K AddCommGrpCat.{max v w}
  apply IsPullback.of_map E (coefficientSquare J K Q F).fac
  apply IsPullback.of_forall_isPullback_app
  intro V
  let : Mono (Q.map ((evaluation D C).obj V.unop)).f₂₄ :=
    inferInstanceAs (Mono (Q.f₂₄.app V.unop))
  let : Mono (Q.map ((evaluation D C).obj V.unop)).f₃₄ :=
    inferInstanceAs (Mono (Q.f₃₄.app V.unop))
  exact TorsionFinitePresentation.FiniteCover.sheaf_isPullback J
    (Q.map ((evaluation D C).obj V.unop)) (hQ V.unop) (hcover V.unop) F

/-- The actual relative sum-and-difference section sequence. -/
def coefficientComplex (F : Sheaf J AddCommGrpCat.{max v w}) :
    ShortComplex (Sheaf K AddCommGrpCat.{max v w}) :=
  (coefficientSquare J K Q F).commSq.shortComplex'

omit [HasSheafify J AddCommGrpCat.{max v w}] in
/-- Original section restriction epis give the relative short exact sequence.
This also applies to genuine ringed injectives without forgotten injectivity. -/
theorem coefficientComplex_shortExact_of_restriction_epi
    (F : Sheaf J AddCommGrpCat.{max v w})
    (hrestriction : ∀ V : D, Epi (F.obj.map (Q.f₁₃.app V).op)) :
    (coefficientComplex J K Q F).ShortExact := by
  have hpb := coefficientSquare_isPullback J K Q hQ hcover F
  have : Epi ((restriction J K Q.f₁₃).app F) := by
    have : Epi (((restriction J K Q.f₁₃).app F).hom) := by
      let : ∀ V : Dᵒᵖ, Epi (((restriction J K Q.f₁₃).app F).hom.app V) :=
        fun V => hrestriction V.unop
      exact NatTrans.epi_of_epi_app _
    exact (sheafToPresheaf K AddCommGrpCat.{max v w}).epi_of_epi_map
      (inferInstanceAs (Epi (((restriction J K Q.f₁₃).app F).hom)))
  have : Epi (-((restriction J K Q.f₁₃).app F)) :=
    ⟨fun u v h => (cancel_epi ((restriction J K Q.f₁₃).app F)).mp
      (neg_injective (by simpa only [Preadditive.neg_comp] using h))⟩
  have : Epi (coefficientComplex J K Q F).g :=
    epi_of_epi_fac (biprod.inr_desc ((restriction J K Q.f₁₂).app F)
      (-((restriction J K Q.f₁₃).app F)))
  have : Mono (coefficientComplex J K Q F).f := hpb.mono_shortComplex'_f
  exact { exact := hpb.exact_shortComplex' }

/-- The relative difference is surjective on injectives, on every original test. -/
theorem coefficientComplex_shortExact (F : Sheaf J AddCommGrpCat.{max v w}) [Injective F] :
    (coefficientComplex J K Q F).ShortExact :=
  coefficientComplex_shortExact_of_restriction_epi J K Q hQ hcover F (fun V => by
    let : Mono (Q.map ((evaluation D C).obj V)).f₂₄ :=
      inferInstanceAs (Mono (Q.f₂₄.app V))
    have : Mono (Q.f₁₃.app V) := (hQ V).mono_f₁₃
    exact Sheaf.restriction_epi_of_injective J F (Q.f₁₃.app V))

/-- The functor sequence uses the native pointwise binary biproduct. -/
def functorComplex :
    ShortComplex (Sheaf J AddCommGrpCat.{max v w} ⥤ Sheaf K AddCommGrpCat.{max v w}) where
  X₁ := push J K Q.X₄
  X₂ := (pointwiseBinaryBicone (push J K Q.X₂) (push J K Q.X₃)).pt
  X₃ := push J K Q.X₁
  f :=
    { app F := biprod.lift ((restriction J K Q.f₂₄).app F)
        ((restriction J K Q.f₃₄).app F)
      naturality F G a := by
        apply biprod.hom_ext <;> simp [← NatTrans.naturality] }
  g :=
    { app F := biprod.desc ((restriction J K Q.f₁₂).app F)
        (-((restriction J K Q.f₁₃).app F))
      naturality F G a := by
        apply biprod.hom_ext' <;> simp [← NatTrans.naturality] }
  zero := by
    apply NatTrans.ext
    funext F
    exact (coefficientComplex J K Q F).zero

/-- The hypothesis of the native right-derived sequence is discharged by site gluing. -/
theorem functorComplex_injective_shortExact (F : Sheaf J AddCommGrpCat.{max v w}) [Injective F] :
    ((functorComplex J K Q).map
      ((evaluation (Sheaf J AddCommGrpCat.{max v w})
        (Sheaf K AddCommGrpCat.{max v w})).obj F)).ShortExact :=
  coefficientComplex_shortExact J K Q hQ hcover F

instance functorComplex_left_additive : (functorComplex J K Q).X₁.Additive :=
  push_additive J K Q.X₄

instance functorComplex_right_additive : (functorComplex J K Q).X₃.Additive :=
  push_additive J K Q.X₁

instance functorComplex_middle_additive : (functorComplex J K Q).X₂.Additive :=
  Functor.pointwiseBinaryBicone_additive _ _

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v w})]

/-- The relative native left higher image vanishes when the preceding difference
is epic and the middle higher image vanishes. Only site gluing is an input. -/
theorem rightDerived_isZero_left_succ_of_epi
    {F : Sheaf J AddCommGrpCat.{max v w}} (I : InjectiveResolution F) (n : ℕ)
    [Epi ((NatTrans.rightDerived (functorComplex J K Q).g n).app F)]
    (hzero : IsZero (((functorComplex J K Q).X₂.rightDerived (n + 1)).obj F)) :
    IsZero (((push J K Q.X₄).rightDerived (n + 1)).obj F) :=
  (functorComplex J K Q).rightDerived_isZero_left_succ_of_epi I
    (fun F _ => functorComplex_injective_shortExact J K Q hQ hcover F) n hzero

/-- Above degree one the preceding overlap and same-degree middle vanishings
alone suffice; no higher exchange hypothesis is hidden in the construction. -/
theorem rightDerived_isZero_left_succ
    {F : Sheaf J AddCommGrpCat.{max v w}} (I : InjectiveResolution F) (n : ℕ)
    (hprev : IsZero (((push J K Q.X₁).rightDerived n).obj F))
    (hzero : IsZero (((functorComplex J K Q).X₂.rightDerived (n + 1)).obj F)) :
    IsZero (((push J K Q.X₄).rightDerived (n + 1)).obj F) :=
  (functorComplex J K Q).rightDerived_isZero_left_succ I
    (fun F _ => functorComplex_injective_shortExact J K Q hQ hcover F) n hprev hzero

/-- Degree one needs only the original underived difference epi and the two
original degree-one chart vanishings. Native zero normalization retains that map. -/
theorem rightDerived_isZero_left_one_of_epi
    {F : Sheaf J AddCommGrpCat.{max v w}} (I : InjectiveResolution F)
    [Epi (coefficientComplex J K Q F).g]
    (hU : IsZero (((push J K Q.X₂).rightDerived 1).obj F))
    (hV : IsZero (((push J K Q.X₃).rightDerived 1).obj F)) :
    IsZero (((push J K Q.X₄).rightDerived 1).obj F) := by
  have hdiff : Epi ((functorComplex J K Q).g.app F) :=
    inferInstanceAs (Epi (coefficientComplex J K Q F).g)
  let G : Sheaf J AddCommGrpCat.{max v w} ⥤ Sheaf K AddCommGrpCat.{max v w} :=
    push J K Q.X₁
  let : PreservesFiniteLimits G := push_preservesFiniteLimits J K Q.X₁
  have : IsIso (G.toRightDerivedZero.app F) := inferInstance
  have : Epi ((NatTrans.rightDerived (functorComplex J K Q).g 0).app F) := by
    have : Epi ((functorComplex J K Q).g.app F ≫
        (functorComplex J K Q).X₃.toRightDerivedZero.app F) :=
      epi_comp' hdiff (IsIso.epi_of_iso (G.toRightDerivedZero.app F))
    exact epi_of_epi_fac
      (Functor.toRightDerivedZero_naturality (functorComplex J K Q).g F)
  exact rightDerived_isZero_left_succ_of_epi J K Q hQ hcover I 0
    (Functor.rightDerived_pointwiseBinaryBicone_isZero _ _ I 1 hU hV)

/-- Higher binary gluing uses the original two chart vanishings in the same
degree and the original overlap in the preceding degree. -/
theorem rightDerived_isZero_left_succ_of_vertices
    {F : Sheaf J AddCommGrpCat.{max v w}} (I : InjectiveResolution F) (n : ℕ)
    (hW : IsZero (((push J K Q.X₁).rightDerived n).obj F))
    (hU : IsZero (((push J K Q.X₂).rightDerived (n + 1)).obj F))
    (hV : IsZero (((push J K Q.X₃).rightDerived (n + 1)).obj F)) :
    IsZero (((push J K Q.X₄).rightDerived (n + 1)).obj F) :=
  rightDerived_isZero_left_succ J K Q hQ hcover I n hW
    (Functor.rightDerived_pointwiseBinaryBicone_isZero _ _ I (n + 1) hU hV)

end CategoryTheory.Sheaf.MayerVietoris
