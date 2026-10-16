/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.CategoryTheory.NatTrans.Unit

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/OriginalUnitPostcomposition.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 102]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.NatTrans

namespace AlgebraicGeometry.Scheme.Modules.Plus

lemma plus_quasiIso_comp {X : Scheme.{u}} {A B C : CochainComplex.Plus X.Modules}
    (m : A ⟶ B) (n : B ⟶ C) [QuasiIso m.hom] [QuasiIso n.hom] :
    QuasiIso (m ≫ n).hom := by
  change QuasiIso (m.hom ≫ n.hom)
  infer_instance

lemma plus_iso_quasiIso {X : Scheme.{u}} {A B : CochainComplex.Plus X.Modules}
    (m : A ⟶ B) [IsIso m] : QuasiIso m.hom := by
  let : IsIso m.hom := Functor.map_isIso (CochainComplex.Plus.ι X.Modules) m
  infer_instance

variable {D : Type v} [Category.{w} D] {X : Scheme.{u}}
    {F G H : D ⥤ CochainComplex.Plus X.Modules}

lemma plus_nattrans_comp_quasiIso (a : F ⟶ G) (b : G ⟶ H)
    (ha : ∀ K, QuasiIso (a.app K).hom) (hb : ∀ K, QuasiIso (b.app K).hom) (K : D) :
    QuasiIso ((a ≫ b).app K).hom := by
  let := ha K
  let := hb K
  exact plus_quasiIso_comp (a.app K) (b.app K)

lemma plus_natIso_hom_quasiIso (e : F ≅ G) (K : D) : QuasiIso (e.hom.app K).hom :=
  plus_iso_quasiIso (e.hom.app K)

theorem unitTotalPostcompose_quasiIso {X : Scheme.{u}}
    (G F T : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (η : 𝟭 (CochainComplex.Plus X.Modules) ⟶ G)
    (hη : ∀ K, QuasiIso (η.app K).hom)
    (hF : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (F.map f).hom)
    (hT : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (T.map f).hom)
    (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((CategoryTheory.NatTrans.unitTotalPostcompose G F T η).app K).hom :=
  hT (F.map (η.app K)) (hF (η.app K) (hη K))

lemma plus_nattrans_precompose_quasiIso {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules}
    (α : F ⟶ G) (H : D ⥤ CochainComplex.Plus X.Modules)
    (hα : ∀ C, QuasiIso (α.app C).hom) (K : D) :
    QuasiIso ((Functor.whiskerLeft H α).app K).hom := hα (H.obj K)

lemma unitPrecompose_quasiIso {X : Scheme.{u}}
    (T F : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (η : 𝟭 (CochainComplex.Plus X.Modules) ⟶ T)
    (hη : ∀ C, QuasiIso (η.app C).hom) (K : CochainComplex.Plus X.Modules) :
    QuasiIso ((CategoryTheory.NatTrans.unitPrecompose T F η).app K).hom := hη (F.obj K)

lemma plus_nattrans_postcompose_quasiIso {X : Scheme.{u}} {D : Type*} [Category D]
    {F G : D ⥤ CochainComplex.Plus X.Modules} (α : F ⟶ G)
    (T : CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules)
    (hα : ∀ K, QuasiIso (α.app K).hom)
    (hT : ∀ {K C : CochainComplex.Plus X.Modules} (f : K ⟶ C),
      QuasiIso f.hom → QuasiIso (T.map f).hom) (K : D) :
    QuasiIso ((Functor.whiskerRight α T).app K).hom := hT (α.app K) (hα K)

end AlgebraicGeometry.Scheme.Modules.Plus
