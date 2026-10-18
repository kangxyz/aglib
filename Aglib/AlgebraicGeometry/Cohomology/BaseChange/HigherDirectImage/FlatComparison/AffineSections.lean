/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit

/-!
# Native affine section classes after exact geometric pullback

The original geometric unit, exact-pullback cycle and homology comparisons,
and native affine counit mates define the actual forwarded section classes.
Only the geometric base map is flat. Global sections are used as the original
additive right adjoint, without preservation of homology or any quasicoherence
condition on the coefficient complex terms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Cohomology.FlatComparison



variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  [Flat (Spec.map φ)]

/-- The original geometric pullback unit on affine global sections, retaining
its native scalar comparison. -/
def sectionsUnit :
    moduleSpecΓFunctor (R := R) ⟶ Scheme.Modules.pullback (Spec.map φ) ⋙
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom where
  app M := (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
    (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom.app
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)
  naturality {M N} v := by
    let G := moduleSpecΓFunctor (R := R)
    let J := Scheme.Modules.pullback (Spec.map φ)
    let P := Scheme.Modules.pushforward (Spec.map φ)
    let e := (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom
    have hu := congrArg G.map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality v)
    simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hu
    have he := e.naturality (J.map v)
    change G.map (P.map (J.map v)) ≫ e.app (J.obj N) =
      e.app (J.obj M) ≫ (ModuleCat.restrictScalars φ.hom).map
        ((moduleSpecΓFunctor (R := S)).map (J.map v)) at he
    change G.map v ≫ G.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app N) ≫ e.app (J.obj N) =
      G.map ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        e.app (J.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((moduleSpecΓFunctor (R := S)).map (J.map v))
    rw [← Category.assoc, hu, Category.assoc, he]

omit [Flat (Spec.map φ)] in
/-- The native affine section unit is the original geometric unit on actual section values. -/
theorem sectionsUnit_apply (M : (Spec R).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj M) :
    (sectionsUnit φ).app M x =
      (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤) x := rfl

variable (K : CochainComplex (Spec R).Modules ℤ)
  (L : CochainComplex (Spec S).Modules ℤ)
  (ψ : ((Scheme.Modules.pullback (Spec.map φ)).mapHomologicalComplex (.up ℤ)).obj K ⟶ L)
  (n : ℤ)

/-- The native cycle map through exact pullback and the actual coefficient-complex arrow. -/
def cyclesForward
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (moduleSpecΓFunctor (R := S)).obj (L.cycles n) :=
  (moduleSpecΓFunctor (R := S)).map (HomologicalComplex.cyclesMap ψ n)
    ((moduleSpecΓFunctor (R := S)).map
      (((K.sc n).mapCyclesIso (Scheme.Modules.pullback (Spec.map φ))).inv)
      ((sectionsUnit φ).app (K.cycles n)
        ((tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c)))

/-- The forwarded cycle retains the literal geometric unit and coefficient component. -/
theorem cyclesForward_iCycles
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (moduleSpecΓFunctor (R := S)).map (L.iCycles n) (cyclesForward φ K L ψ n c) =
      (moduleSpecΓFunctor (R := S)).map (ψ.f n)
        ((sectionsUnit φ).app (K.X n)
          (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).iCycles n c)) := by
  let G := moduleSpecΓFunctor (R := S)
  let J := Scheme.Modules.pullback (Spec.map φ)
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let T := (J.mapHomologicalComplex (.up ℤ)).obj K
  let e := (K.sc n).mapCyclesIso J
  let s := (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c
  let z : G.obj (J.obj (K.cycles n)) := (sectionsUnit φ).app (K.cycles n) s
  let w : G.obj (T.cycles n) := G.map e.inv z
  have hh := congrArg G.map (HomologicalComplex.cyclesMap_i ψ n)
  simp only [Functor.map_comp] at hh
  have hψ := ConcreteCategory.congr_hom hh w
  change G.map (L.iCycles n) (G.map (HomologicalComplex.cyclesMap ψ n) w) =
    G.map (ψ.f n) (G.map (T.iCycles n) w) at hψ
  have he := congrArg G.map (ShortComplex.mapCyclesIso_inv_iCycles J (K.sc n))
  simp only [Functor.map_comp] at he
  have hex := ConcreteCategory.congr_hom he z
  change G.map (T.iCycles n) (G.map e.inv z) = G.map (J.map (K.iCycles n)) z at hex
  have hu := ConcreteCategory.congr_hom ((sectionsUnit φ).naturality (K.iCycles n)) s
  change (sectionsUnit φ).app (K.X n) ((moduleSpecΓFunctor (R := R)).map (K.iCycles n) s) =
    G.map (J.map (K.iCycles n)) z at hu
  have hc := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := R)).cyclesCounitMate_iCycles (K.sc n)) c
  change (moduleSpecΓFunctor (R := R)).map (K.iCycles n) s = C.iCycles n c at hc
  change G.map (L.iCycles n) (G.map (HomologicalComplex.cyclesMap ψ n) w) = _
  rw [hψ, hex, ← hu, hc]

/-- Homology of the actual coefficient arrow, after the original geometric unit
and native counit mate. -/
def homologyForward
    (x : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    (moduleSpecΓFunctor (R := S)).obj (L.homology n) :=
  (moduleSpecΓFunctor (R := S)).map (HomologicalComplex.homologyMap ψ n)
    ((moduleSpecΓFunctor (R := S)).map
      (((K.sc n).mapHomologyIso (Scheme.Modules.pullback (Spec.map φ))).inv)
      ((sectionsUnit φ).app (K.homology n)
        ((tilde.adjunction (R := R)).homologyCounitMate (K.sc n) x)))

/-- The forwarded homology class is the original target projection of the forwarded cycle. -/
theorem homologyForward_homologyπ
    (c : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    homologyForward φ K L ψ n
        (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K).homologyπ n c) =
      (moduleSpecΓFunctor (R := S)).map (L.homologyπ n) (cyclesForward φ K L ψ n c) := by
  let G := moduleSpecΓFunctor (R := S)
  let J := Scheme.Modules.pullback (Spec.map φ)
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let T := (J.mapHomologicalComplex (.up ℤ)).obj K
  let eH := (K.sc n).mapHomologyIso J
  let eC := (K.sc n).mapCyclesIso J
  let s := (tilde.adjunction (R := R)).cyclesCounitMate (K.sc n) c
  let z : G.obj (J.obj (K.cycles n)) := (sectionsUnit φ).app (K.cycles n) s
  let w : G.obj (T.cycles n) := G.map eC.inv z
  have hc := ConcreteCategory.congr_hom
    ((tilde.adjunction (R := R)).homologyCounitMate_homologyπ (K.sc n)) c
  change (tilde.adjunction (R := R)).homologyCounitMate (K.sc n) (C.homologyπ n c) =
    (moduleSpecΓFunctor (R := R)).map (K.homologyπ n) s at hc
  have hu := ConcreteCategory.congr_hom ((sectionsUnit φ).naturality (K.homologyπ n)) s
  change (sectionsUnit φ).app (K.homology n)
      ((moduleSpecΓFunctor (R := R)).map (K.homologyπ n) s) =
    G.map (J.map (K.homologyπ n)) z at hu
  have he := congrArg G.map (ShortComplex.map_homologyπ_mapHomologyIso_inv J (K.sc n))
  simp only [Functor.map_comp] at he
  have hex := ConcreteCategory.congr_hom he z
  change G.map eH.inv (G.map (J.map (K.homologyπ n)) z) = G.map (T.homologyπ n) w at hex
  have hh := congrArg G.map (HomologicalComplex.homologyπ_naturality ψ n)
  simp only [Functor.map_comp] at hh
  have hψ := ConcreteCategory.congr_hom hh w
  change G.map (HomologicalComplex.homologyMap ψ n) (G.map (T.homologyπ n) w) =
    G.map (L.homologyπ n) (G.map (HomologicalComplex.cyclesMap ψ n) w) at hψ
  change G.map (HomologicalComplex.homologyMap ψ n)
      (G.map eH.inv ((sectionsUnit φ).app (K.homology n)
        ((tilde.adjunction (R := R)).homologyCounitMate (K.sc n) (C.homologyπ n c)))) = _
  rw [hc, hu, hex, hψ]
  rfl



end AlgebraicGeometry.Scheme.Cohomology.FlatComparison
