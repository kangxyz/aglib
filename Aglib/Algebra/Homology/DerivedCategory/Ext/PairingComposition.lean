/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.YonedaPairing
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Yoneda pairings under natural transformations, composition and adjunction

The original exact-functor Ext map intertwines every natural transformation.
Its whole biadditive pairing square is proved before the composite-functor and
adjunction specializations. A specified comparison `K ≅ P ⋙ Q` transports the
first Ext variable by its inverse; the corresponding output map uses that same
comparison followed by `Q` of the original adjunction counit. Restriction is
`adj.extEquiv` after precomposition with that counit, equivalently the Ext map
of the exact right adjoint. No geometric input occurs.

Sources: Mathlib `Ext/Map.lean`, `comp_mapExactFunctor` and
`mapExactFunctor_comp_mk₀_natTransApp`; `Ext/MapAdjunction.lean`, `extEquiv` and
its original unit/counit formulas. This generalizes the original etale
`Duality/LowerShriekComposition` and `Duality/PairingRestriction` proofs.
-/

@[expose] public noncomputable section

universe w w' w'' u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

section NaturalTransformation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {L M : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]

/-- The whole biadditive pairing square for a natural transformation of exact functors. -/
theorem extPairingHom_natTrans (τ : L ⟶ M) (A : D) (F G : C) (r s t : ℕ)
    (h : r + s = t) :
    (extPairingHom M A F G r s t h).comp
        ((Ext.mk₀ (τ.app F)).postcomp A (add_zero r)) =
      (extPairingHom L A F G r s t h).compr₂
        ((Ext.mk₀ (τ.app G)).postcomp A (add_zero t)) := by
  ext c e
  change ((c.comp (Ext.mk₀ (τ.app F)) (add_zero r)).comp (e.mapExactFunctor M) h) =
    (c.comp (e.mapExactFunctor L) h).comp (Ext.mk₀ (τ.app G)) (add_zero t)
  rw [Ext.comp_assoc_of_second_deg_zero, ← Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Ext.comp_assoc_of_third_deg_zero]

/-- Evaluating the whole natural-transformation square preserves the original maps. -/
theorem extPairing_natTrans (τ : L ⟶ M) {A : D} {F G : C} {r s t : ℕ}
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s) (h : r + s = t) :
    extPairing M A (c.comp (Ext.mk₀ (τ.app F)) (add_zero r)) e h =
      (extPairing L A c e h).comp (Ext.mk₀ (τ.app G)) (add_zero t) :=
  DFunLike.congr_fun (DFunLike.congr_fun (extPairingHom_natTrans τ A F G r s t h) c) e

end NaturalTransformation

section Comparison

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]
  (P : C ⥤ D) (Q : D ⥤ E) (K : C ⥤ E) (τ : K ≅ P ⋙ Q) (S : E)

/-- `Ext^r(S, Q(P A)) ≃+ Ext^r(S, K A)`: postcomposition with the inverse of the original
composition comparison `K ≅ Q ∘ P`. -/
def extPairingCompAddEquiv (A : C) (r : ℕ) :
    Ext.{w''} S
        (Q.obj (P.obj A)) r ≃+
      Ext.{w''} S (K.obj A) r :=
  ((extFunctorObj S r).mapIso
    (τ.app A).symm).addCommGroupIsoToAddEquiv

theorem extPairingCompAddEquiv_apply (A : C) (r : ℕ)
    (c : Ext.{w''} S
      (Q.obj (P.obj A)) r) :
    extPairingCompAddEquiv P Q K τ S A r c =
      c.comp (Ext.mk₀ (τ.inv.app A)) (add_zero r) :=
  rfl

theorem extPairingCompAddEquiv_symm_apply (A : C) (r : ℕ)
    (c : Ext.{w''} S (K.obj A) r) :
    (extPairingCompAddEquiv P Q K τ S A r).symm c =
      c.comp (Ext.mk₀ (τ.hom.app A)) (add_zero r) :=
  rfl

end Comparison

section Counit

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {P : C ⥤ D} {Q : D ⥤ E} {K : C ⥤ E}
  {τ : K ≅ P ⋙ Q} {R : D ⥤ C} (adj : P ⊣ R)

/-- The whole original counit comparison `R ⋙ K ⟶ Q`, before object evaluation. -/
def extPairingCounitNatTrans : R ⋙ K ⟶ Q :=
  whiskerLeft R τ.hom ≫ (Functor.associator R P Q).inv ≫
    whiskerRight adj.counit Q ≫ (Functor.leftUnitor Q).hom

/-- Evaluating the counit comparison gives the specified comparison followed by the counit. -/
theorem extPairingCounitNatTrans_app (B : D) :
    (extPairingCounitNatTrans (τ := τ) adj).app B =
      τ.hom.app (R.obj B) ≫ Q.map (adj.counit.app B) := by
  simp [extPairingCounitNatTrans]

/-- Changing a composite comparison respects composition of whole natural transformations. -/
theorem extPairingCounitNatTrans_trans {K' : C ⥤ E} (α : K' ≅ K) :
    extPairingCounitNatTrans (τ := α ≪≫ τ) adj =
      whiskerLeft R α.hom ≫ extPairingCounitNatTrans (τ := τ) adj := by
  ext B
  simp [extPairingCounitNatTrans, Category.assoc]

end Counit

section Composition

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]
  (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (Q : D ⥤ E) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  (K : C ⥤ E) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
  (τ : K ≅ P ⋙ Q) (S : E)

/-- The whole pairing for a composite functor is the iterated original Ext map. -/
theorem extPairingHom_comp (A B : C) (r s t : ℕ) (h : r + s = t) :
    (extPairingHom Q S (P.obj A) (P.obj B) r s t h).compl₂ (P.mapExtAddHom A B s) =
      extPairingHom (P ⋙ Q) S A B r s t h := by
  ext c e
  exact congrArg (fun x => c.comp x h) (Ext.comp_mapExactFunctor e P Q).symm

variable {P Q K τ S}

/-- The pairing through `Q` with `P` of a class through `K` is the pairing through `K`, followed
by the
original composition comparison `K B ⟶ Q P B`. -/
theorem extPairing_mapExt {A B : C} {r s t : ℕ}
    (c : Ext.{w''} S
      (Q.obj (P.obj A)) r)
    (e : Ext.{w} A B s) (h : r + s = t) :
    extPairing Q S c (e.mapExactFunctor P) h =
      (extPairing K S (extPairingCompAddEquiv P Q K τ S A r c) e
          h).comp
        (Ext.mk₀ (τ.hom.app B)) (add_zero t) := by
  have hτ := extPairing_natTrans τ.hom
    (extPairingCompAddEquiv P Q K τ S A r c) e h
  have hc : (extPairingCompAddEquiv P Q K τ S A r c).comp
      (Ext.mk₀ (τ.hom.app A)) (add_zero r) = c :=
    (extPairingCompAddEquiv P Q K τ S A r).symm_apply_apply c
  rw [hc] at hτ
  exact (DFunLike.congr_fun
    (DFunLike.congr_fun (extPairingHom_comp P Q S A B r s t h) c) e).trans hτ

variable {R : D ⥤ C} [R.Additive] [PreservesFiniteLimits R]
  [PreservesFiniteColimits R] (adj : P ⊣ R)

/-- Restriction defined by counit precomposition and the Ext adjunction is the right-adjoint map. -/
theorem extEquiv_mk₀_counit_comp {F G : D} {s : ℕ} (e : Ext.{w'} F G s) :
    adj.extEquiv ((Ext.mk₀ (adj.counit.app F)).comp e (zero_add s)) =
      e.mapExactFunctor R := by
  rw [adj.extEquiv_naturality_right]
  have h₀ : adj.extEquiv (Ext.mk₀ (adj.counit.app F)) = Ext.mk₀ (𝟙 (R.obj F)) :=
    adj.extEquiv_mk₀_counit_app F
  exact (congrArg (fun a => a.comp (e.mapExactFunctor R) (zero_add s)) h₀).trans
    (Ext.mk₀_id_comp _)

/-- The pairing through `Q` for `P A` is the pairing through `K` for `A`, followed by the map
induced by
the original composition comparison and `Q` of the original counit `P R B ⟶ B`:
`φ_Q(c, e) = φ_K(c', e') ∘ mk₀ (compIso.hom ≫ Q ε_B)`, where
`c' = extPairingCompAddEquiv c` and `e' = adj.extEquiv e`. -/
theorem extPairing_eq_comp_counit {A : C} {B : D}
    {r s t : ℕ}
    (c : Ext.{w''} S
      (Q.obj (P.obj A)) r)
    (e : Ext.{w'} (P.obj A) B s) (h : r + s = t) :
    extPairing Q S c e h =
      (extPairing K S (extPairingCompAddEquiv P Q K τ S A r c)
          (adj.extEquiv e) h).comp
        (Ext.mk₀ (τ.hom.app (R.obj B) ≫
          Q.map (adj.counit.app B)))
        (add_zero t) := by
  obtain ⟨e', rfl⟩ := (adj.extEquiv).symm.surjective e
  rw [AddEquiv.apply_symm_apply, Adjunction.extEquiv_symm_apply,
    extPairing_comp_mk₀, extPairing_mapExt (τ := τ),
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

variable (P Q K τ S)

/-- The square of the dual homomorphism for `P A` through `Q` against the one for `A` through `K`:
`φ_Q(c)` is `φ_K(c')` after `adj.extEquiv`, followed by postcomposition with
`mk₀ (compIso.hom ≫ Q ε_B)`, for `r ≤ d`. -/
theorem extPairingDualHom_eq_comp_counit (A : C)
    (B : D) (d r : ℕ) (hr : r ≤ d)
    (c : Ext.{w''} S
      (Q.obj (P.obj A)) r) :
    extPairingDualHom Q S (P.obj A) B d r hr c =
      ((Ext.mk₀ (τ.hom.app (R.obj B) ≫
          Q.map (adj.counit.app B))).postcomp
          S (add_zero d)).comp
        ((extPairingDualHom K S A (R.obj B) d r hr
          (extPairingCompAddEquiv P Q K τ S A r c)).comp
          (adj.extEquiv).toAddMonoidHom) := by
  ext e
  exact extPairing_eq_comp_counit adj c e (by lia)


variable {P Q K τ S adj}

/-- The transpose square for restriction along the exact right adjoint: counit extension
before pairing agrees with restriction of the Ext argument followed by counit extension. -/
theorem extPairingTransposeHom_restriction (F G : D) (d s : ℕ)
    (hs : s ≤ d) (e : Ext.{w'} F G s) :
    (extPairingTransposeHom Q S F G d s hs e).comp
        ((Ext.mk₀ (τ.hom.app (R.obj F) ≫
          Q.map (adj.counit.app F))).postcomp
          S (add_zero (d - s))) =
      ((Ext.mk₀ (τ.hom.app (R.obj G) ≫
          Q.map (adj.counit.app G))).postcomp
          S (add_zero d)).comp
        (extPairingTransposeHom K S (R.obj F)
          (R.obj G) d s hs
          (adj.extEquiv
            ((Ext.mk₀ (adj.counit.app F)).comp e
              (zero_add s)))) := by
  ext c
  change extPairing Q S (c.comp (Ext.mk₀ (τ.hom.app
        (R.obj F) ≫
          Q.map (adj.counit.app F)))
        (add_zero (d - s))) e (by lia) =
      (extPairing K S c
        (adj.extEquiv
          ((Ext.mk₀ (adj.counit.app F)).comp e (zero_add s)))
        (by lia)).comp
        (Ext.mk₀ (τ.hom.app (R.obj G) ≫
          Q.map (adj.counit.app G)))
        (add_zero d)
  rw [extEquiv_mk₀_counit_comp adj e]
  have hτ := extPairing_natTrans (t := d) (extPairingCounitNatTrans (τ := τ) adj) c e (by lia)
  simpa only [extPairingCounitNatTrans_app, extPairing, Ext.comp_mapExactFunctor] using hτ


end Composition

end CategoryTheory.Functor
