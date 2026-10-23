/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeSectionEquality
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSeeds
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackSectionsBase

/-! # Eventual equality through the original terminal coefficient chart -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Every original relative section at an étale chart is an identity representative. -/
theorem etaleRepresentativeSeed_surjective {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (U : X.Etale) :
    Function.Surjective (etaleRepresentativeSeed F U) := by
  intro s
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (pullbackSectionsEtaleEvaluationIso F U).inv).surjective s
  refine ⟨x, ?_⟩
  change (pullbackSectionsFunctor F).map (𝟙 (op ((Etale.forget X).obj U)))
    ((pullbackSectionsEtaleEvaluationIso F U).inv x) = s
  exact (ConcreteCategory.congr_hom
    ((pullbackSectionsFunctor F).map_id (op ((Etale.forget X).obj U)))
      ((pullbackSectionsEtaleEvaluationIso F U).inv x)).trans hx

private theorem natIso_image_eq_iff {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) (P : Dᵒᵖ ⥤ Ab.{u + 1}) (Q : Cᵒᵖ ⥤ Ab.{u + 1})
    (e : H.op ⋙ P ≅ Q) {B : D} {T Y : C}
    (a : Y ⟶ T) (b : H.obj T ⟶ B) (p : H.obj Y ⟶ B) (hp : H.map a ≫ b = p)
    (s t : P.obj (op B)) (x y : Q.obj (op T))
    (hx : x = e.hom.app (op T) (P.map b.op s))
    (hy : y = e.hom.app (op T) (P.map b.op t)) :
    (P.map p.op s = P.map p.op t) ↔ Q.map a.op x = Q.map a.op y := by
  have he (z : P.obj (op B)) :
      e.hom.app (op Y) (P.map p.op z) =
        Q.map a.op (e.hom.app (op T) (P.map b.op z)) := by
    have hc := ConcreteCategory.congr_hom (P.map_comp b.op (H.map a).op) z
    have hn := ConcreteCategory.congr_hom (e.hom.naturality a.op) (P.map b.op z)
    exact (congrArg (fun k : H.obj Y ⟶ B ↦ e.hom.app (op Y) (P.map k.op z)) hp).symm.trans
      ((congrArg (e.hom.app (op Y)) hc).trans hn)
  have hs := (he s).trans (congrArg (Q.map a.op) hx.symm)
  have ht := (he t).trans (congrArg (Q.map a.op) hy.symm)
  constructor
  · intro h
    exact hs.symm.trans ((congrArg (e.hom.app (op Y)) h).trans ht)
  · intro h
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (op Y))).injective
    exact hs.trans (h.trans ht.symm)

/-- The original arrow to the terminal étale coefficient object. -/
def terminalRepresentativeArrow {S T : Scheme.{u}} (τ : T ⟶ S) :
    Over.mk τ ⟶ (Etale.forget S).obj (etaleTerminal S) :=
  Over.homMk τ (Category.comp_id τ)

/-- The identity-stage relative arrow, before the change-of-base isomorphism. -/
def terminalBaseArrow {X S : Scheme.{u}} (r : S ⟶ X) :
    (Over.map r).obj ((Etale.forget S).obj (etaleTerminal S)) ⟶ Over.mk r :=
  Over.homMk (𝟙 S) rfl

private theorem terminalBaseArrow_triangle {X S T : Scheme.{u}}
    (r : S ⟶ X) (τ : T ⟶ S) :
    (Over.map r).map (terminalRepresentativeArrow τ) ≫ terminalBaseArrow r =
      Over.homMk τ (U := Over.mk (τ ≫ r)) (V := Over.mk r) := by
  apply Over.OverMorphism.ext
  exact Category.comp_id τ

/-- The native base-change isomorphism turns equality of original images into
terminal-coefficient representative equality, with the same original arrows. -/
theorem terminalRepresentative_image_eq_iff {X S T : Scheme.{u}}
    (r : S ⟶ X) (τ : T ⟶ S) (F : AbelianSheaf.{u, u + 1} X)
    (s t : (pullbackSectionsFunctor F).obj (op (Over.mk r)))
    (x y : ((inverseImage r).obj F).obj.obj (op (etaleTerminal S)))
    (hx : etaleRepresentativeSeed ((inverseImage r).obj F) (etaleTerminal S) x =
      (pullbackSectionsBaseIso r F).hom.app (op ((Etale.forget S).obj (etaleTerminal S)))
        ((pullbackSectionsFunctor F).map (terminalBaseArrow r).op s))
    (hy : etaleRepresentativeSeed ((inverseImage r).obj F) (etaleTerminal S) y =
      (pullbackSectionsBaseIso r F).hom.app (op ((Etale.forget S).obj (etaleTerminal S)))
        ((pullbackSectionsFunctor F).map (terminalBaseArrow r).op t)) :
    ((pullbackSectionsFunctor F).map
        (Over.homMk τ (U := Over.mk (τ ≫ r)) (V := Over.mk r)).op s =
      (pullbackSectionsFunctor F).map
        (Over.homMk τ (U := Over.mk (τ ≫ r)) (V := Over.mk r)).op t) ↔
    etaleRepresentativeSection ((inverseImage r).obj F) (Over.mk τ) (etaleTerminal S)
        (terminalRepresentativeArrow τ) x =
      etaleRepresentativeSection ((inverseImage r).obj F) (Over.mk τ) (etaleTerminal S)
        (terminalRepresentativeArrow τ) y := by
  exact (natIso_image_eq_iff (Over.map r) (pullbackSectionsFunctor F)
    (pullbackSectionsFunctor ((inverseImage r).obj F)) (pullbackSectionsBaseIso r F)
    (terminalRepresentativeArrow τ) (terminalBaseArrow r)
    (Over.homMk τ (U := Over.mk (τ ≫ r)) (V := Over.mk r))
    (terminalBaseArrow_triangle r τ) s t
    (etaleRepresentativeSeed ((inverseImage r).obj F) (etaleTerminal S) x)
    (etaleRepresentativeSeed ((inverseImage r).obj F) (etaleTerminal S) y) hx hy).trans
      (map_etaleRepresentativeSeed_eq_iff ((inverseImage r).obj F) (Over.mk τ)
        (etaleTerminal S) (etaleTerminal S)
        (terminalRepresentativeArrow τ) (terminalRepresentativeArrow τ) x y)

private theorem terminalRepresentative_eq_congr {S T : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} S) {τ σ : T ⟶ S} (e : τ = σ)
    (x y : F.obj.obj (op (etaleTerminal S)))
    (h : etaleRepresentativeSection F (Over.mk τ) (etaleTerminal S)
        (terminalRepresentativeArrow τ) x =
      etaleRepresentativeSection F (Over.mk τ) (etaleTerminal S)
        (terminalRepresentativeArrow τ) y) :
    etaleRepresentativeSection F (Over.mk σ) (etaleTerminal S)
        (terminalRepresentativeArrow σ) x =
      etaleRepresentativeSection F (Over.mk σ) (etaleTerminal S)
        (terminalRepresentativeArrow σ) y := by
  cases e
  exact h

/-- Terminal coefficient representative equality descends along an affine limit. -/
theorem exists_terminal_representatives_eventually_equal
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) (F : AbelianSheaf.{u, u + 1} (D.obj i))
    (x y : F.obj.obj (op (etaleTerminal (D.obj i))))
    (h : etaleRepresentativeSection F (Over.mk (c.π.app i)) (etaleTerminal (D.obj i))
        (terminalRepresentativeArrow (c.π.app i)) x =
      etaleRepresentativeSection F (Over.mk (c.π.app i)) (etaleTerminal (D.obj i))
        (terminalRepresentativeArrow (c.π.app i)) y) :
    ∃ (k : I) (q : k ⟶ i),
      etaleRepresentativeSection F (Over.mk (D.map q)) (etaleTerminal (D.obj i))
          (terminalRepresentativeArrow (D.map q)) x =
        etaleRepresentativeSection F (Over.mk (D.map q)) (etaleTerminal (D.obj i))
          (terminalRepresentativeArrow (D.map q)) y := by
  have h' : etaleRepresentativeSection F (Over.mk (c.π.app i ≫ 𝟙 _))
      (etaleTerminal (D.obj i)) (Over.homMk (c.π.app i ≫ 𝟙 _) (by simp)) x =
    etaleRepresentativeSection F (Over.mk (c.π.app i ≫ 𝟙 _))
      (etaleTerminal (D.obj i)) (Over.homMk (c.π.app i ≫ 𝟙 _) (by simp)) y := by
    exact terminalRepresentative_eq_congr F (Category.comp_id (c.π.app i)).symm x y h
  obtain ⟨k, q, hq⟩ := exists_affineScheme_representatives_eventually_equal D c hc i (𝟙 _) F
    (etaleTerminal (D.obj i)) (etaleTerminal (D.obj i)) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (Category.id_comp _) x y h'
  refine ⟨k, q, ?_⟩
  exact terminalRepresentative_eq_congr F (Category.comp_id (D.map q)) x y hq

/-- Two original sections at an affine stage with the same original limit image
have the same image at a later stage. No continuity hypothesis is assumed. -/
theorem exists_stage_sections_eventually_equal
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}}
    (r : D.obj i ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (s t : (pullbackSectionsFunctor F).obj (op (Over.mk r)))
    (h : (pullbackSectionsFunctor F).map
        (Over.homMk (c.π.app i) (U := Over.mk (c.π.app i ≫ r)) (V := Over.mk r)).op s =
      (pullbackSectionsFunctor F).map
        (Over.homMk (c.π.app i) (U := Over.mk (c.π.app i ≫ r)) (V := Over.mk r)).op t) :
    ∃ k : Over i,
      (pullbackSectionsFunctor F).map
        (Over.homMk (D.map k.hom) (U := Over.mk (D.map k.hom ≫ r))
          (V := Over.mk r)).op s =
      (pullbackSectionsFunctor F).map
        (Over.homMk (D.map k.hom) (U := Over.mk (D.map k.hom ≫ r))
          (V := Over.mk r)).op t := by
  obtain ⟨x, hx⟩ := etaleRepresentativeSeed_surjective ((inverseImage r).obj F)
    (etaleTerminal (D.obj i))
    ((pullbackSectionsBaseIso r F).hom.app (op ((Etale.forget (D.obj i)).obj
      (etaleTerminal (D.obj i)))) ((pullbackSectionsFunctor F).map (terminalBaseArrow r).op s))
  obtain ⟨y, hy⟩ := etaleRepresentativeSeed_surjective ((inverseImage r).obj F)
    (etaleTerminal (D.obj i))
    ((pullbackSectionsBaseIso r F).hom.app (op ((Etale.forget (D.obj i)).obj
      (etaleTerminal (D.obj i)))) ((pullbackSectionsFunctor F).map (terminalBaseArrow r).op t))
  have hlimit := (terminalRepresentative_image_eq_iff r (c.π.app i) F s t x y hx hy).mp h
  obtain ⟨k, q, hq⟩ := exists_terminal_representatives_eventually_equal D c hc i
    ((inverseImage r).obj F) x y hlimit
  exact ⟨Over.mk q, (terminalRepresentative_image_eq_iff r (D.map q) F s t x y hx hy).mpr hq⟩

end AlgebraicGeometry.Scheme.EtaleAffineBasis
