/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExtTransport
public import Aglib.CategoryTheory.Shift.AdjunctValue
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdge
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeTrace
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.TopTrace
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Shift
public import Aglib.CategoryTheory.Adjunction.SectionTrace

/-! Generic original shifted traces and their original restriction laws. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Original bounded-below homology vanishing gives the native upper bound. -/
theorem isLE_of_original_homology (K : Plus C) (q : ℤ)
    (h : ∀ r : ℤ, q < r → IsZero ((homologyFunctor C r).obj K)) : K.IsLE q := by
  apply (isLE_ι_obj_iff K q).mp
  apply (DerivedCategory.isLE_iff _ _).mpr
  exact h

/-- The original top projection gives an ordinary trace through the original shift adjunction. -/
def ordinaryTraceFromTop (q : ℤ) (K : Plus C) [K.IsLE q] (U : C)
    (a : (homologyFunctor C q).obj K ⟶ U) :
    K⟦q⟧ ⟶ (singleFunctor C 0).obj U :=
  let I := (singleFunctor C 0).obj U
  let t := ((singleFunctors C).shiftIso (-q) q 0 (neg_add_cancel q)).app U
  let τ : K ⟶ I⟦-q⟧ := upperHomologyProjection K q ≫ (singleFunctor C q).map a ≫ t.inv
  let adj : shiftFunctor (Plus C) q ⊣ shiftFunctor (Plus C) (-q) :=
    (shiftEquiv' (Plus C) q (-q) (add_neg_cancel q)).toAdjunction
  (adj.homEquiv K I).symm τ

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- Transport the one supplied trace through the original shifted comparison and unit. -/
def shiftedTraceTransport (F : C ⥤ D) [F.CommShift ℤ] (q : ℤ)
    {K I : C} {L J : D} (e : F.obj K ≅ L) (u : F.obj I ≅ J) (a : K⟦q⟧ ⟶ I) :
    L⟦q⟧ ⟶ J :=
  ((F.commShiftIso q).app K ≪≫ (shiftFunctor D q).mapIso e).inv ≫ F.map a ≫ u.hom

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D E : Type*} [Category* D] [Category* E] [HasShift D ℤ]
  (F : DerivedCategory.Plus C ⥤ D) [F.CommShift ℤ] (R : E ⥤ D)
  (q : ℤ) {K : DerivedCategory.Plus C} (hK : K.IsLE q)
  {U : C} {J : D} {V W : E} {b : F.obj K ⟶ R.obj V}
  (hb : IsIso b) (a : V ≅ W)
  (u : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J)
  (t : (DerivedCategory.Plus.homologyFunctor C q).obj K ⟶ U)

/-- The original trace transported by its original proper exchange and original shifts. -/
def OriginalShiftedTraceValue (τ : (R.obj W)⟦q⟧ ⟶ J) : Prop :=
  letI := hK
  letI := hb
  τ = F.shiftedTraceTransport q (asIso b ≪≫ R.mapIso a) u
    (DerivedCategory.Plus.ordinaryTraceFromTop q K U t)

/-- Construct the unique transported map before specializing the actual proper witness. -/
theorem existsUnique_originalShiftedTrace :
    ∃! τ, F.OriginalShiftedTraceValue R q hK hb a u t τ := by
  let := hK
  let := hb
  exact ⟨F.shiftedTraceTransport q (asIso b ≪≫ R.mapIso a) u
    (DerivedCategory.Plus.ordinaryTraceFromTop q K U t), rfl, fun _ h => h⟩

end CategoryTheory.Functor

namespace DerivedCategory.Plus
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The original ordinary top trace keeps the complete original homogeneous value. -/
theorem ordinaryTraceFromTop_homology_value
    (q : ℤ) {U V : C} {K : Plus C} [K.IsLE q]
    (z : ShiftedHom ((singleFunctor C 0).obj U) K q)
    (a : (homologyFunctor C q).obj K ⟶ V) :
    let F := singleFunctor C 0
    let H := homologyFunctor C q
    let e := singleFunctorCompHomologyFunctorIso (C := C) q
    let η := (singleFunctors C).shiftIso (-q) q 0 (by omega)
    let adj : shiftFunctor (Plus C) (-q) ⊣ shiftFunctor (Plus C) q :=
      (shiftEquiv' (Plus C) (-q) q (by omega)).toAdjunction
    let x := η.inv.app U ≫ (adj.homEquiv (F.obj U) K).symm z
    z ≫ ordinaryTraceFromTop q K V a = F.map (e.inv.app U ≫ H.map x ≫ a) := by
  intro F H e η adj x
  let τ := upperHomologyProjection K q ≫ (singleFunctor C q).map a ≫ η.inv.app V
  let μ := shiftFunctorCompIsoId (Plus C) (-q) q (by omega)
  let adjOut : shiftFunctor (Plus C) q ⊣ shiftFunctor (Plus C) (-q) :=
    (shiftEquiv' (Plus C) q (-q) (by omega)).toAdjunction
  have ha : ordinaryTraceFromTop q K V a = τ⟦q⟧' ≫ μ.hom.app (F.obj V) :=
    adjOut.homEquiv_counit K (F.obj V) τ
  have hz : (adj.homEquiv (F.obj U) K) (η.hom.app U ≫ x) = z := by
    have hx : η.hom.app U ≫ x = (adj.homEquiv (F.obj U) K).symm z :=
      η.hom_inv_id_app_assoc _ _
    exact (congrArg (adj.homEquiv (F.obj U) K) hx).trans
      ((adj.homEquiv (F.obj U) K).apply_symm_apply z)
  have hval := singleShiftTrace_homology_value q x τ
  change (adj.homEquiv (F.obj U) K) (η.hom.app U ≫ x) ≫ τ⟦q⟧' ≫ μ.hom.app (F.obj V) =
    F.map (e.inv.app U ≫ H.map (x ≫ τ ≫ η.hom.app V) ≫ e.hom.app V) at hval
  rw [hz] at hval
  have hτ : τ ≫ η.hom.app V = upperHomologyProjection K q ≫ (singleFunctor C q).map a := by
    change (upperHomologyProjection K q ≫ (singleFunctor C q).map a ≫ η.inv.app V) ≫
      η.hom.app V = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (fun m => upperHomologyProjection K q ≫ m)
      (Category.comp_id ((singleFunctor C q).map a))
  have hnorm : H.map (τ ≫ η.hom.app V) ≫ e.hom.app V = a := by
    have hn := e.hom.naturality a
    change H.map ((singleFunctor C q).map a) ≫ e.hom.app V = e.hom.app (H.obj K) ≫ a at hn
    have hp : H.map (upperHomologyProjection K q) ≫ e.hom.app (H.obj K) = 𝟙 _ :=
      upperHomologyProjection_homology K q
    rw [hτ, Functor.map_comp, Category.assoc, hn, ← Category.assoc, hp, Category.id_comp]
  have hv : e.inv.app U ≫ H.map (x ≫ τ ≫ η.hom.app V) ≫ e.hom.app V =
      e.inv.app U ≫ H.map x ≫ a := by
    have hm : H.map (x ≫ τ ≫ η.hom.app V) = H.map x ≫ H.map (τ ≫ η.hom.app V) :=
      H.map_comp x _
    rw [hm]
    simp only [Category.assoc, hnorm]
  exact (congrArg (fun t => z ≫ t) ha).trans (hval.trans (congrArg F.map hv))

end DerivedCategory.Plus

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [HasShift D ℤ]

/-- The original point exchange followed by the same original absolute top trace. -/
def ShiftedTopTracePullbackValue
    (G : D ⥤ DerivedCategory.Plus C) [G.CommShift ℤ]
    (q : ℤ) {K : DerivedCategory.Plus C} (hK : K.IsLE q) {U : C} {J L : D}
    (v : G.obj J ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U)
    (k : G.obj L ⟶ K) (t : (DerivedCategory.Plus.homologyFunctor C q).obj K ⟶ U)
    (τ : L⟦q⟧ ⟶ J) : Prop :=
  letI := hK
  G.map τ ≫ v.hom = (G.commShiftIso q).hom.app L ≫ k⟦q⟧' ≫
    DerivedCategory.Plus.ordinaryTraceFromTop q K U t

variable {B E : Type*} [Category* B] [Category* E]
  {R₀ : B ⥤ DerivedCategory.Plus C} {R₁ : E ⥤ D}
  {F : DerivedCategory.Plus C ⥤ D} {G : D ⥤ DerivedCategory.Plus C}
  [F.CommShift ℤ] [G.CommShift ℤ]
  {H₁ : B ⥤ E} {H₂ : E ⥤ B} {G₀ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus C}

/-- Construct the original transported trace together with its original rational pullback. -/
theorem existsUnique_originalShiftedTrace_restriction_of_exists
    {β₁ : R₀ ⋙ F ⟶ H₁ ⋙ R₁} {β₂ : R₁ ⋙ G ⟶ H₂ ⋙ R₀}
    {γ : G₀ ≅ F ⋙ G} {eG : G₀ ≅ 𝟭 (DerivedCategory.Plus C)}
    {M : B} {N : E} {a : H₁.obj M ≅ N} {b : H₂.obj N ≅ M}
    {hb : IsIso (β₁.app M)} {q : ℤ} {hK : (R₀.obj M).IsLE q}
    {U : C} {J : D}
    {u : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J}
    {v : G.obj J ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U}
    {t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₀.obj M) ⟶ U}
    (hex : ∃! τ, F.OriginalShiftedTraceValue R₁ q hK hb a u t τ)
    (hx : CorrectedExchangeLoop β₁ β₂ γ eG M N a b)
    (hu : SectionCoefficientValue F G γ eG u v)
    (hη : NatTrans.CommShift (γ.symm ≪≫ eG).hom ℤ) :
    ∃! τ, F.OriginalShiftedTraceValue R₁ q hK hb a u t τ ∧
      ShiftedTopTracePullbackValue G q hK v (β₂.app N ≫ R₀.map b.hom) t τ := by
  let := hη
  let := hb
  let := hK
  let e := asIso (β₁.app M) ≪≫ R₁.mapIso a
  let η := γ.symm ≪≫ eG
  let k := β₂.app N ≫ R₀.map b.hom
  have he : G.map e.hom ≫ k = η.hom.app (R₀.obj M) := by
    apply (cancel_epi (γ.hom.app (R₀.obj M))).mp
    simpa only [CorrectedExchangeLoop, e, η, k, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc] using hx
  have hi : G.map u.hom ≫ v.hom = η.hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj U) := by
    apply (cancel_epi (γ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj U))).mp
    simpa only [SectionCoefficientValue, η, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_app_assoc] using hu
  let e₂ := (F.commShiftIso q).app (R₀.obj M) ≪≫ (shiftFunctor D q).mapIso e
  have hs := transported_loop_shift F G η e k he q
  obtain ⟨τ, hτ, huniq⟩ := hex
  refine ⟨τ, ⟨hτ, ?_⟩, fun τ' hτ' => huniq τ' hτ'.1⟩
  change G.map τ ≫ v.hom = _
  have ht : τ = F.shiftedTraceTransport q e u
      (DerivedCategory.Plus.ordinaryTraceFromTop q (R₀.obj M) U t) := hτ
  rw [ht]
  simpa only [Functor.shiftedTraceTransport, e₂, Category.assoc] using
    transported_trace_pullback F G η u v e₂
      ((G.commShiftIso q).hom.app (R₁.obj N) ≫ k⟦q⟧')
      (DerivedCategory.Plus.ordinaryTraceFromTop q (R₀.obj M) U t) hs hi

end CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : DerivedCategory.Plus C ⥤ D}
  {R₂ : D ⥤ DerivedCategory.Plus C} {G : A ⥤ DerivedCategory.Plus C} {H : B ⥤ D}
  [R₁.CommShift ℤ] [R₂.CommShift ℤ] [G.CommShift ℤ]

/-- Restriction of the original relative trace on a class is the original absolute trace. -/
def OriginalClassTraceRestrictionValue
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {U : C} {I : A} {J K : B} {J' K' : D}
    (e : L₁.obj I ≅ J)
    (e' : L₂.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J')
    (u : G.obj I ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U)
    {q : ℤ} (hK : (R₂.obj K').IsLE q)
    (t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₂.obj K') ⟶ U)
    (x : ShiftedHom J K q) (y : ShiftedHom J' K' q) (τ : (R₁.obj K)⟦q⟧ ⟶ I) : Prop :=
  letI := hK
  u.inv ≫ G.map ((adj₁.shiftedHomEquiv q I K (e.hom ≫ x)) ≫ τ) ≫ u.hom =
    (adj₂.shiftedHomEquiv q ((DerivedCategory.Plus.singleFunctor C 0).obj U) K'
      (e'.hom ≫ y)) ≫ DerivedCategory.Plus.ordinaryTraceFromTop q (R₂.obj K') U t

/-- A single original trace restriction evaluates every original shifted class. -/
theorem originalClassTraceRestrictionValue_of_shiftedMateValue
    {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂} {β : R₁ ⋙ G ⟶ H ⋙ R₂}
    {U : C} {I : A} {J K : B} {J' K' : D}
    {e : L₁.obj I ≅ J}
    {e' : L₂.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J'}
    {u : G.obj I ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U} {c : H.obj K ≅ K'}
    {q : ℤ} {hK : (R₂.obj K').IsLE q}
    {t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₂.obj K') ⟶ U}
    {x : ShiftedHom J K q} {y : ShiftedHom J' K' q} {τ : (R₁.obj K)⟦q⟧ ⟶ I}
    (hτ : ShiftedTopTracePullbackValue G q hK u (β.app K ≫ R₂.map c.hom) t τ)
    (hm : ShiftedMateValue adj₁ adj₂ β e e' u c x y) :
    OriginalClassTraceRestrictionValue adj₁ adj₂ e e' u hK t x y τ := by
  let := hK
  let a := DerivedCategory.Plus.ordinaryTraceFromTop q (R₂.obj K') U t
  let z := adj₁.shiftedHomEquiv q I K (e.hom ≫ x)
  let z₀ := adj₂.shiftedHomEquiv q ((DerivedCategory.Plus.singleFunctor C 0).obj U) K'
    (e'.hom ≫ y)
  have ht : G.map τ ≫ u.hom = (G.commShiftIso q).hom.app (R₁.obj K) ≫
      (β.app K ≫ R₂.map c.hom)⟦q⟧' ≫ a := hτ
  have hv : u.inv ≫ G.map z ≫ (G.commShiftIso q).hom.app (R₁.obj K) ≫
      (β.app K)⟦q⟧' ≫ (R₂.map c.hom)⟦q⟧' = z₀ := by
    simpa only [ShiftedMateValue, ShiftedHom.map, Category.assoc, z, z₀] using hm
  change u.inv ≫ G.map (z ≫ τ) ≫ u.hom = z₀ ≫ a
  rw [G.map_comp]
  simp only [Category.assoc]
  rw [ht, (shiftFunctor (DerivedCategory.Plus C) q).map_comp]
  simpa only [Category.assoc] using congrArg (fun m => m ≫ a) hv

/-- One original witness and restriction formula determine the traces of an entire class family. -/
theorem existsUnique_originalTrace_classRestriction
    {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂} {β : R₁ ⋙ G ⟶ H ⋙ R₂}
    {U : C} {I : A} {J K : B} {J' K' : D}
    {e : L₁.obj I ≅ J}
    {e' : L₂.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J'}
    {u : G.obj I ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U} {c : H.obj K ≅ K'}
    {q : ℤ} {hK : (R₂.obj K').IsLE q}
    {t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₂.obj K') ⟶ U}
    {P : ((R₁.obj K)⟦q⟧ ⟶ I) → Prop}
    (hex : ∃! τ, P τ ∧ ShiftedTopTracePullbackValue G q hK u (β.app K ≫ R₂.map c.hom) t τ)
    {W : Type*} {x : W → ShiftedHom J K q} {y : W → ShiftedHom J' K' q}
    (hm : ∀ w, ShiftedMateValue adj₁ adj₂ β e e' u c (x w) (y w)) :
    ∃! τ, (P τ ∧ ShiftedTopTracePullbackValue G q hK u (β.app K ≫ R₂.map c.hom) t τ) ∧
      ∀ w, OriginalClassTraceRestrictionValue adj₁ adj₂ e e' u hK t (x w) (y w) τ := by
  obtain ⟨τ, hτ, huniq⟩ := hex
  exact ⟨τ, ⟨hτ, fun w => originalClassTraceRestrictionValue_of_shiftedMateValue hτ.2 (hm w)⟩,
    fun τ' hτ' => huniq τ' hτ'.1⟩

end CategoryTheory

namespace CategoryTheory.ShiftedHom

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- The original shift adjunct of an ordinary trace retains its exact degree-zero composite. -/
theorem comp_shiftAdjunctionHomEquiv {I K : D} (q : ℤ)
    (z : ShiftedHom I K q) (a : K⟦q⟧ ⟶ I) :
    z.comp ((shiftEquiv' D q (-q) (add_neg_cancel q)).toAdjunction.homEquiv K I a)
        (neg_add_cancel q) = ShiftedHom.mk₀ 0 rfl (z ≫ a) := by
  let adj : shiftFunctor D q ⊣ shiftFunctor D (-q) :=
    (shiftEquiv' D q (-q) (add_neg_cancel q)).toAdjunction
  let τ : ShiftedHom K I (-q) := adj.homEquiv K I a
  have hτ : τ⟦q⟧' ≫ adj.counit.app I = a :=
    (adj.homEquiv_counit K I τ).symm.trans ((adj.homEquiv K I).symm_apply_apply a)
  have hc : adj.counit.app I =
      (shiftFunctorAdd' D (-q) q 0 (neg_add_cancel q)).inv.app I ≫
        (shiftFunctorZero D ℤ).hom.app I := rfl
  apply (cancel_mono ((shiftFunctorZero D ℤ).hom.app I)).mp
  change (z.comp τ (neg_add_cancel q)) ≫ _ = (ShiftedHom.mk₀ 0 rfl (z ≫ a)) ≫ _
  rw [ShiftedHom.comp, ShiftedHom.mk₀]
  simp only [shiftFunctorZero', eqToIso_refl, Iso.refl_trans, Category.assoc,
    Iso.inv_hom_id_app]
  rw [← hc, hτ]
  exact (congrArg (fun f => z ≫ f) (Category.comp_id a)).symm

end CategoryTheory.ShiftedHom

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : DerivedCategory.Plus C ⥤ D}
  {R₂ : D ⥤ DerivedCategory.Plus C} {G : A ⥤ DerivedCategory.Plus C} {H : B ⥤ D}
  [R₁.CommShift ℤ] [R₂.CommShift ℤ]

/-- The original rational restriction detects normalization of the same relative trace. -/
theorem OriginalClassTraceRestrictionValue.normalized
    {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂}
    {U : C} {I : A} {J K : B} {J' K' : D}
    {e : L₁.obj I ≅ J}
    {e' : L₂.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J'}
    {u : G.obj I ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U}
    {q : ℤ} {hK : (R₂.obj K').IsLE q}
    {t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₂.obj K') ⟶ U}
    {x : ShiftedHom J K q} {y : ShiftedHom J' K' q} {τ : (R₁.obj K)⟦q⟧ ⟶ I}
    (h : OriginalClassTraceRestrictionValue adj₁ adj₂ e e' u hK t x y τ)
    (hy : letI := hK
      (adj₂.shiftedHomEquiv q ((DerivedCategory.Plus.singleFunctor C 0).obj U) K'
        (e'.hom ≫ y)) ≫ DerivedCategory.Plus.ordinaryTraceFromTop q (R₂.obj K') U t = 𝟙 _)
    (hi : Function.Injective (fun f : I ⟶ I => G.map f)) :
    (adj₁.shiftedHomEquiv q I K (e.hom ≫ x)) ≫ τ = 𝟙 I := by
  let := hK
  have hc := h.trans hy
  apply hi
  apply (cancel_epi u.inv).mp
  apply (cancel_mono u.hom).mp
  simpa only [G.map_id, Category.assoc, Category.id_comp, Iso.inv_hom_id] using hc

/-- The same unique original trace is normalized by the given original class. -/
theorem existsUnique_originalTrace_normalized
    {adj₁ : L₁ ⊣ R₁} {adj₂ : L₂ ⊣ R₂}
    {U : C} {I : A} {J K : B} {J' K' : D}
    {e : L₁.obj I ≅ J}
    {e' : L₂.obj ((DerivedCategory.Plus.singleFunctor C 0).obj U) ≅ J'}
    {u : G.obj I ≅ (DerivedCategory.Plus.singleFunctor C 0).obj U}
    {q : ℤ} {hK : (R₂.obj K').IsLE q}
    {t : (DerivedCategory.Plus.homologyFunctor C q).obj (R₂.obj K') ⟶ U}
    {W : Type*} {x : W → ShiftedHom J K q} {y : W → ShiftedHom J' K' q}
    {P : ((R₁.obj K)⟦q⟧ ⟶ I) → Prop}
    (hex : ∃! τ, P τ ∧ ∀ w, OriginalClassTraceRestrictionValue adj₁ adj₂ e e' u hK t
      (x w) (y w) τ)
    (w : W)
    (hy : letI := hK
      (adj₂.shiftedHomEquiv q ((DerivedCategory.Plus.singleFunctor C 0).obj U) K'
        (e'.hom ≫ y w)) ≫ DerivedCategory.Plus.ordinaryTraceFromTop q (R₂.obj K') U t = 𝟙 _)
    (hi : Function.Injective (fun f : I ⟶ I => G.map f)) :
    ∃! τ, (P τ ∧ ∀ w, OriginalClassTraceRestrictionValue adj₁ adj₂ e e' u hK t (x w) (y w) τ) ∧
      (adj₁.shiftedHomEquiv q I K (e.hom ≫ x w)) ≫ τ = 𝟙 I := by
  obtain ⟨τ, hτ, huniq⟩ := hex
  exact ⟨τ, ⟨hτ, (hτ.2 w).normalized hy hi⟩, fun τ' hτ' => huniq τ' hτ'.1⟩

end CategoryTheory

namespace CategoryTheory.ShiftedHom

variable {D : Type*} [Category* D] [HasShift D ℤ]

/-- Convert a normalized original ordinary trace through its original shift adjunction. -/
theorem exists_originalShiftedTrace_normalized
    {I K : D} {q : ℤ} {z : ShiftedHom I K q} {P : (K⟦q⟧ ⟶ I) → Prop}
    (hex : ∃! a, P a ∧ z ≫ a = 𝟙 I) :
    ∃ τ : ShiftedHom K I (-q), ∃ a, P a ∧
      τ = (shiftEquiv' D q (-q) (add_neg_cancel q)).toAdjunction.homEquiv K I a ∧
      z.comp τ (neg_add_cancel q) = ShiftedHom.mk₀ 0 rfl (𝟙 I) := by
  obtain ⟨a, ha, _⟩ := hex
  refine ⟨_, a, ha.1, rfl, ?_⟩
  rw [comp_shiftAdjunctionHomEquiv, ha.2]

end CategoryTheory.ShiftedHom
