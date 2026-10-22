/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientInterchange

/-! # Naturality of independent quotient interchange on original maps -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

private theorem interchange_naturality_aux {C : Type*} [Category C]
    (Q R : C ⥤ C) (η : 𝟭 C ⟶ Q) (θ : 𝟭 C ⟶ R)
    (e : ∀ F, R.obj (Q.obj F) ⟶ Q.obj (R.obj F))
    (he : ∀ F, η.app F ≫ θ.app (Q.obj F) ≫ e F = θ.app F ≫ η.app (R.obj F))
    {F G : C} (f : F ⟶ G) [Epi (η.app F)] [Epi (θ.app (Q.obj F))] :
    R.map (Q.map f) ≫ e G = e F ≫ Q.map (R.map f) := by
  apply (cancel_epi (η.app F ≫ θ.app (Q.obj F))).mp
  simp only [Category.assoc]
  rw [← θ.naturality_assoc]
  simp only [Functor.id_map]
  rw [← η.naturality_assoc]
  simp only [Functor.id_map]
  rw [he G, reassoc_of% (he F), ← η.naturality]
  simp only [Functor.id_map]
  rw [← θ.naturality_assoc]
  simp only [Functor.id_map]

private theorem interchange_ideal_naturality_aux {C : Type*} [Category C]
    (Q Q' R : C ⥤ C) (η : 𝟭 C ⟶ Q) (η' : 𝟭 C ⟶ Q') (θ : 𝟭 C ⟶ R)
    (a : Q ⟶ Q') (ha : ∀ F, η.app F ≫ a.app F = η'.app F)
    (e : ∀ F, R.obj (Q.obj F) ⟶ Q.obj (R.obj F))
    (e' : ∀ F, R.obj (Q'.obj F) ⟶ Q'.obj (R.obj F))
    (he : ∀ F, η.app F ≫ θ.app (Q.obj F) ≫ e F = θ.app F ≫ η.app (R.obj F))
    (he' : ∀ F, η'.app F ≫ θ.app (Q'.obj F) ≫ e' F = θ.app F ≫ η'.app (R.obj F))
    (F : C) [Epi (η.app F)] [Epi (θ.app (Q.obj F))] :
    R.map (a.app F) ≫ e' F = e F ≫ a.app (R.obj F) := by
  apply (cancel_epi (η.app F ≫ θ.app (Q.obj F))).mp
  simp only [Category.assoc]
  rw [← θ.naturality_assoc]
  simp only [Functor.id_map]
  rw [reassoc_of% (ha F), he' F, reassoc_of% (he F), ha (R.obj F)]

variable (X : Scheme.{u}) (I K : X.IdealSheafData)

/-- Independent quotient interchange is natural in the original coefficient. -/
@[reassoc]
theorem idealSheafQuotientInterchangeIso_naturality {F G : X.Modules} (f : F ⟶ G) :
    (idealSheafQuotientFunctor X K).map ((idealSheafQuotientFunctor X I).map f) ≫
        (idealSheafQuotientInterchangeIso X I K G).hom =
      (idealSheafQuotientInterchangeIso X I K F).hom ≫
        (idealSheafQuotientFunctor X I).map ((idealSheafQuotientFunctor X K).map f) := by
  exact interchange_naturality_aux
    (idealSheafQuotientFunctor X I) (idealSheafQuotientFunctor X K)
    (idealSheafQuotientUnit X I) (idealSheafQuotientUnit X K)
    (fun F => (idealSheafQuotientInterchangeIso X I K F).hom)
    (idealSheafQuotientUnit_interchangeIso_hom X I K) f

/-- The comparison of the two actual composite quotient functors. -/
def idealSheafQuotientInterchangeNatIso :
    idealSheafQuotientFunctor X I ⋙ idealSheafQuotientFunctor X K ≅
      idealSheafQuotientFunctor X K ⋙ idealSheafQuotientFunctor X I :=
  NatIso.ofComponents (idealSheafQuotientInterchangeIso X I K)
    (fun f => idealSheafQuotientInterchangeIso_naturality X I K f)

/-- Enlarging the first independent ideal commutes with original interchange. -/
@[reassoc]
theorem idealSheafQuotientInterchangeIso_ideal_naturality
    {J : X.IdealSheafData} (h : I ≤ J) (F : X.Modules) :
    (idealSheafQuotientFunctor X K).map (idealSheafQuotientMap X I h F) ≫
        (idealSheafQuotientInterchangeIso X J K F).hom =
      (idealSheafQuotientInterchangeIso X I K F).hom ≫
        idealSheafQuotientMap X I h ((idealSheafQuotientFunctor X K).obj F) := by
  let a : idealSheafQuotientFunctor X I ⟶ idealSheafQuotientFunctor X J := {
    app F := idealSheafQuotientMap X I h F
    naturality _ _ f := idealSheafQuotientMap_naturality X I h f }
  exact interchange_ideal_naturality_aux
    (idealSheafQuotientFunctor X I) (idealSheafQuotientFunctor X J)
    (idealSheafQuotientFunctor X K) (idealSheafQuotientUnit X I)
    (idealSheafQuotientUnit X J) (idealSheafQuotientUnit X K) a
    (idealSheafQuotientUnit_map X I h)
    (fun F => (idealSheafQuotientInterchangeIso X I K F).hom)
    (fun F => (idealSheafQuotientInterchangeIso X J K F).hom)
    (idealSheafQuotientUnit_interchangeIso_hom X I K)
    (idealSheafQuotientUnit_interchangeIso_hom X J K) F

end AlgebraicGeometry.Scheme.Modules.Coherent
