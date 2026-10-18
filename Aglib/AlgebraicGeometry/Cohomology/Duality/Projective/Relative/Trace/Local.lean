/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.NatIso
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Sections
/-!
# Composition laws for the original local relative projective trace
The local comparison and trace compose over opaque coefficient and higher-image
functors. Their coefficient naturality and restriction refinement use the original
naturality, open-trace and restriction-composition equations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
/-- The local comparison and trace compose before specializing the five functors. -/
def traceLocalHomFactory
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ D) (L : D ⥤ F) (V : F ⥤ D)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (N : C)
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N) :
    J.obj (F1.obj (F0.obj N)) ⟶ J.obj N :=
  @CategoryStruct.comp D inferInstance
    (J.obj (F1.obj (F0.obj N))) (V.obj (L.obj (J.obj N))) (J.obj N)
    (η.hom.app N) t
/-- The defining equation of the same original local composition. -/
def traceLocalHomFactoryEquation
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ D) (L : D ⥤ F) (V : F ⥤ D)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (N : C)
    (z : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N)
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N) : Prop :=
  z = traceLocalHomFactory F0 F1 J L V η N t
/-- Coefficient naturality with both higher-image functors held opaque. -/
def traceLocalNaturalityEquation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ D) {N N' : C} (s : N ⟶ N')
    (t : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N)
    (t' : J.obj (F1.obj (F0.obj N')) ⟶ J.obj N') : Prop :=
  J.map (F1.map (F0.map s)) ≫ t' = t ≫ J.map s
/-- Naturality of the original local composition, before the geometric functors are supplied. -/
theorem traceLocalHomFactory_naturality
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ D) (L : D ⥤ F) (V : F ⥤ D)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) {N N' : C} (s : N ⟶ N')
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (t' : V.obj (L.obj (J.obj N')) ⟶ J.obj N')
    (ht : V.map (L.map (J.map s)) ≫ t' = t ≫ J.map s) :
    traceLocalNaturalityEquation F0 F1 J s
      (traceLocalHomFactory F0 F1 J L V η N t)
      (traceLocalHomFactory F0 F1 J L V η N' t') := by
  dsimp only [traceLocalNaturalityEquation]
  have hη := η.hom.naturality s
  change J.map (F1.map (F0.map s)) ≫ η.hom.app N' =
    η.hom.app N ≫ V.map (L.map (J.map s)) at hη
  dsimp only [traceLocalHomFactory]
  rw [← Category.assoc, hη, Category.assoc, ht]
  exact (Category.assoc _ _ _).symm
private theorem normalizeTraceRestrictionComp
    {C : Type*} [Category* C] {A A' B B' : C}
    (u : A ≅ A') (v : B ≅ B') (c : A ⟶ B) (d : A' ⟶ B')
    (h : u.inv ≫ c ≫ v.hom = d) : u.hom ≫ d ≫ v.inv = c := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original restriction-composition square and the two original affine trace laws
imply refinement; all module objects are held opaque in this calculation. -/
theorem traceLocalHomFactory_refine
    {C D D' E F F' : Type*}
    [Category* C] [Category* D] [Category* D'] [Category* E] [Category* F] [Category* F']
    (F0 : C ⥤ E) (F1 : E ⥤ C)
    (J : C ⥤ D) (K : D ⥤ D') (J' : C ⥤ D') (u : J' ≅ J ⋙ K)
    (L : D ⥤ F) (V : F ⥤ D) (L' : D' ⥤ F') (V' : F' ⥤ D')
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V))
    (β : (L ⋙ V) ⋙ K ≅ K ⋙ (L' ⋙ V'))
    (η' : (F0 ⋙ F1) ⋙ J' ≅ J' ⋙ (L' ⋙ V')) (N : C)
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (t' : V'.obj (L'.obj (J'.obj N)) ⟶ J'.obj N)
    (t'' : V'.obj (L'.obj (K.obj (J.obj N))) ⟶ K.obj (J.obj N))
    (hcomp : u.inv.app (F1.obj (F0.obj N)) ≫ η'.hom.app N ≫
      V'.map (L'.map (u.hom.app N)) = K.map (η.hom.app N) ≫ β.hom.app (J.obj N))
    (hopen : β.hom.app (J.obj N) ≫ t'' = K.map t)
    (hnat : V'.map (L'.map (u.inv.app N)) ≫ t' = t'' ≫ u.inv.app N) :
    u.hom.app (F1.obj (F0.obj N)) ≫
        K.map (traceLocalHomFactory F0 F1 J L V η N t) ≫ u.inv.app N =
      traceLocalHomFactory F0 F1 J' L' V' η' N t' := by
  dsimp only [traceLocalHomFactory]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← hopen]
  simp only [Category.assoc]
  rw [← hnat]
  have hc := normalizeTraceRestrictionComp (u.app (F1.obj (F0.obj N)))
    ((L' ⋙ V').mapIso (u.app N)) (η'.hom.app N)
    (K.map (η.hom.app N) ≫ β.hom.app (J.obj N)) hcomp
  have h := congrArg
    (fun z : J'.obj (F1.obj (F0.obj N)) ⟶ V'.obj (L'.obj (J'.obj N)) => z ≫ t') hc
  simpa only [Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.comp_map,
    Category.assoc] using h
/-- Producer equations preserve the original local morphisms during refinement. -/
theorem traceLocalHomFactory_refine_eq
    {C D D' E F F' : Type*}
    [Category* C] [Category* D] [Category* D'] [Category* E] [Category* F] [Category* F']
    (F0 : C ⥤ E) (F1 : E ⥤ C)
    (J : C ⥤ D) (K : D ⥤ D') (J' : C ⥤ D') (u : J' ≅ J ⋙ K)
    (L : D ⥤ F) (V : F ⥤ D) (L' : D' ⥤ F') (V' : F' ⥤ D')
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V))
    (η' : (F0 ⋙ F1) ⋙ J' ≅ J' ⋙ (L' ⋙ V')) (N : C)
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (t' : V'.obj (L'.obj (J'.obj N)) ⟶ J'.obj N)
    (z : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N)
    (z' : J'.obj (F1.obj (F0.obj N)) ⟶ J'.obj N)
    (hz : traceLocalHomFactoryEquation F0 F1 J L V η N z t)
    (hz' : traceLocalHomFactoryEquation F0 F1 J' L' V' η' N z' t')
    (h : u.hom.app (F1.obj (F0.obj N)) ≫
        K.map (traceLocalHomFactory F0 F1 J L V η N t) ≫ u.inv.app N =
      traceLocalHomFactory F0 F1 J' L' V' η' N t') :
    u.hom.app (F1.obj (F0.obj N)) ≫ K.map z ≫ u.inv.app N = z' := by
  dsimp only [traceLocalHomFactoryEquation] at hz hz'
  rw [hz, hz']
  exact h

/-- Comparison and trace compatibility transport the original factory equation. -/
theorem traceLocalHomFactoryEquation_compare
    {C D E F F' : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F] [Category* F']
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ D)
    (L : D ⥤ F) (V : F ⥤ D) (L' : D ⥤ F') (V' : F' ⥤ D)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V))
    (η' : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L' ⋙ V')) (N : C)
    (z : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N)
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (t' : V'.obj (L'.obj (J.obj N)) ⟶ J.obj N)
    (m : V'.obj (L'.obj (J.obj N)) ⟶ V.obj (L.obj (J.obj N)))
    (hz : traceLocalHomFactoryEquation F0 F1 J L V η N z t)
    (hc : η.hom.app N = η'.hom.app N ≫ m)
    (ht : m ≫ t = t') :
    traceLocalHomFactoryEquation F0 F1 J L' V' η' N z t' := by
  dsimp only [traceLocalHomFactoryEquation, traceLocalHomFactory] at hz ⊢
  rw [hz, hc, Category.assoc, ht]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

/-- The equation identifying the map on affine sections induced by `t` with `τ` under the affine
higher direct image comparison. -/
def affineTraceSectionsEquation
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [QuasiCompact p] [QuasiSeparated p]
    (M : X.Modules) [M.IsQuasicoherent] (N : (Spec (.of R)).Modules) (n : ℕ)
    (t : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf X M) n → moduleSpecΓFunctor.obj N) : Prop :=
  ∀ x, moduleSpecΓFunctor.map t x =
    τ (moduleHigherDirectImageAffineSectionsLinearEquiv p M (injectiveResolution M) n x)

/-- Compatibility of `tR` and `tA` with restriction along the given open pullback square. -/
def relativeHigherTraceSquare
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j) (n : ℕ)
    (N : Y.Modules)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N) : Prop :=
  @Eq ((Modules.restrictFunctor j).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
    (Modules.restrictFunctor j).obj N)
    (relativeHigherRestrictionHom p i q j H n N ≫ tA)
    ((Modules.restrictFunctor j).map
      (X := ((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) (Y := N) tR)

/-- The component of `m` followed by the supplied trace isomorphism `t`. -/
def compositeTraceIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (U : C ⥤ E) (V : E ⥤ D)
    (m : F ≅ U ⋙ V) (N : C) {Z : D} (t : V.obj (U.obj N) ≅ Z) :
    F.obj N ≅ Z := m.app N ≪≫ t
/-- The forward component of the functor comparison `m : F ≅ U ⋙ V`. -/
def compositeTraceRawModel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (U : C ⥤ E) (V : E ⥤ D) (m : F ≅ U ⋙ V) (N : C) :
    F.obj N ⟶ V.obj (U.obj N) := m.hom.app N
/-- The equation expressing `c` as the comparison component followed by `t.hom`. -/
def compositeTraceFactorization
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (U : C ⥤ E) (V : E ⥤ D)
    (m : F ≅ U ⋙ V) (N : C) {Z : D} (t : V.obj (U.obj N) ≅ Z)
    (c : F.obj N ⟶ Z) : Prop :=
  c = compositeTraceRawModel F U V m N ≫ t.hom
theorem compositeNatIso_hom_of_components
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (U : C ⥤ E) (V : E ⥤ D)
    (m : F ≅ U ⋙ V) (N : C) {Z : D} (t : V.obj (U.obj N) ≅ Z) :
    compositeTraceFactorization F U V m N t (compositeTraceIso F U V m N t).hom := by
  rfl
/-- The trace compatibility equation `s ≫ t' = J.map t`. -/
def compositeTraceRestrictionSquare
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (J : C ⥤ D) (U : C ⥤ E) (V : E ⥤ C) (U' : D ⥤ E') (V' : E' ⥤ D)
    (N : C) (s : J.obj ((U ⋙ V).obj N) ⟶ (U' ⋙ V').obj (J.obj N))
    (t : V.obj (U.obj N) ⟶ N) (t' : V'.obj (U'.obj (J.obj N)) ⟶ J.obj N) : Prop :=
  @Eq (J.obj (V.obj (U.obj N)) ⟶ J.obj N)
    (s ≫ t') (J.map (X := V.obj (U.obj N)) (Y := N) t)
/-- Compatibility of the composite trace isomorphisms with the comparison `ρ` under `J`. -/
def compositeTraceOpenSquare
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (J : C ⥤ D) (F : C ⥤ C) (U : C ⥤ E) (V : E ⥤ C) (η : F ≅ U ⋙ V)
    (F' : D ⥤ D) (U' : D ⥤ E') (V' : E' ⥤ D) (η' : F' ≅ U' ⋙ V')
    (N : C) (T : V.obj (U.obj N) ≅ N)
    (T' : V'.obj (U'.obj (J.obj N)) ≅ J.obj N) (ρ : F ⋙ J ≅ J ⋙ F') : Prop :=
  ρ.hom.app N ≫ (compositeTraceIso F' U' V' η' (J.obj N) T').hom =
    J.map (compositeTraceIso F U V η N T).hom
/-- The trace restriction equation using the component of the natural isomorphism `σ`. -/
def compositeTraceNatRestrictionSquare
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (J : C ⥤ D) (U : C ⥤ E) (V : E ⥤ C) (U' : D ⥤ E') (V' : E' ⥤ D)
    (N : C) (σ : (U ⋙ V) ⋙ J ≅ J ⋙ (U' ⋙ V'))
    (t : V.obj (U.obj N) ⟶ N) (t' : V'.obj (U'.obj (J.obj N)) ⟶ J.obj N) : Prop :=
  @Eq (J.obj (V.obj (U.obj N)) ⟶ J.obj N)
    (σ.hom.app N ≫ t') (J.map (X := V.obj (U.obj N)) (Y := N) t)
theorem compositeTrace_open_of_natSquare
    {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']
    (J : C ⥤ D) (F : C ⥤ C) (U : C ⥤ E) (V : E ⥤ C) (η : F ≅ U ⋙ V)
    (F' : D ⥤ D) (U' : D ⥤ E') (V' : E' ⥤ D) (η' : F' ≅ U' ⋙ V')
    (N : C) (T : V.obj (U.obj N) ≅ N)
    (T' : V'.obj (U'.obj (J.obj N)) ≅ J.obj N)
    (ρ : F ⋙ J ≅ J ⋙ F') (σ : (U ⋙ V) ⋙ J ≅ J ⋙ (U' ⋙ V'))
    (t : V.obj (U.obj N) ⟶ N) (t' : V'.obj (U'.obj (J.obj N)) ⟶ J.obj N)
    (hm : ρ ≪≫ Functor.isoWhiskerLeft J η' = Functor.isoWhiskerRight η J ≪≫ σ)
    (ht : compositeTraceNatRestrictionSquare J U V U' V' N σ t t')
    (ht₀ : t = T.hom) (ht₁ : t' = T'.hom) :
    compositeTraceOpenSquare J F U V η F' U' V' η' N T T' ρ := by
  have hmN := congrArg (fun e : F ⋙ J ≅ J ⋙ (U' ⋙ V') => e.hom.app N) hm
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at hmN
  change σ.hom.app N ≫ t' = J.map t at ht
  rw [ht₀, ht₁] at ht
  change ρ.hom.app N ≫ (η'.hom.app (J.obj N) ≫ T'.hom) =
    J.map (η.hom.app N ≫ T.hom)
  rw [← Category.assoc, hmN, Category.assoc, ht, J.map_comp]
theorem relativeHigherTraceSquare_generic
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j) (n : ℕ)
    (N : Y.Modules)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N)
    (ht : relativeHigherTraceSquare p i q j H n N tR tA) :
    compositeTraceRestrictionSquare (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n)
      N (relativeHigherRestrictionHom p i q j H n N) tR tA := ht
theorem relativeHigherTraceSquare_nat
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j) (n : ℕ)
    (N : Y.Modules)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N)
    (ht : relativeHigherTraceSquare p i q j H n N tR tA) :
    compositeTraceNatRestrictionSquare (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n) N
      (relativeHigherRestrictionIso p i q j H n) tR tA :=
  relativeHigherTraceSquare_generic p i q j H n N tR tA ht

/-- Model sections retain the original higher model map and the original trace. -/
def traceModelSectionsEquation
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    (F : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules) (n : ℕ)
    (μ : F ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : (Spec (.of A)).Modules) [(U.obj N).IsQuasicoherent]
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj N)) n → moduleSpecΓFunctor.obj N)
    (z : F.obj N ⟶ N) : Prop :=
  ∀ x, moduleSpecΓFunctor.map z x =
    τ (moduleHigherDirectImageAffineSectionsLinearEquiv r (U.obj N)
      (injectiveResolution (U.obj N)) n (moduleSpecΓFunctor.map (μ.hom.app N) x))
theorem traceModelSections_of_standard
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    (F : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules) (n : ℕ)
    (μ : F ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : (Spec (.of A)).Modules) [(U.obj N).IsQuasicoherent]
    (T : ((Scheme.Modules.pushforward r).rightDerived n).obj (U.obj N) ≅ N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj N)) n → moduleSpecΓFunctor.obj N)
    (hT : affineTraceSectionsEquation r (U.obj N) N n T.hom τ) :
    traceModelSectionsEquation r F U n μ N τ
      (compositeTraceIso F U ((Scheme.Modules.pushforward r).rightDerived n) μ N T).hom := by
  have h := compositeNatIso_hom_of_components F U
    ((Scheme.Modules.pushforward r).rightDerived n) μ N T
  dsimp only [compositeTraceFactorization, compositeTraceRawModel] at h
  intro x
  rw [h, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hT _
theorem identityHigherModelIso_trace
    {X W Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Y)
    [IsOpenImmersion i] (H : IsPullback i q p (𝟙 Y)) (n : ℕ) (N : Y.Modules)
    (t : (relativeHigherFunctor p n).obj N ⟶ N)
    (t' : (relativeHigherFunctor q n).obj N ⟶ N)
    (tK : (relativeHigherFunctor q n).obj (N.restrict (𝟙 Y)) ⟶ N.restrict (𝟙 Y))
    (hopen : (relativeHigherRestrictionIso p i q (𝟙 Y) H n).hom.app N ≫ tK =
      (Modules.restrictFunctor (𝟙 Y)).map t)
    (hnat : (relativeHigherFunctor q n).map ((restrictFunctorId (X := Y)).hom.app N) ≫ t' =
      tK ≫ (restrictFunctorId (X := Y)).hom.app N) :
    (identityHigherModelIso p i q H n).hom.app N ≫ t' = t := by
  rw [identityHigherModelIso_hom]
  exact traceIdentityNormalization (relativeHigherFunctor p n) (relativeHigherFunctor q n)
    (Modules.restrictFunctor (𝟙 Y)) (restrictFunctorId (X := Y))
    (relativeHigherRestrictionIso p i q (𝟙 Y) H n) N t t' tK hopen hnat

/-- The comparison `η` followed by the natural isomorphism `θ` whiskered on the left by `J`. -/
def affineHigherCompositeFactory {C C' : Type*} [Category C] [Category C']
    (F₀ : C ⥤ C) (F₁ F₂ : C' ⥤ C') (J : C ⥤ C')
    (η : F₀ ⋙ J ≅ J ⋙ F₁) (θ : F₁ ≅ F₂) : F₀ ⋙ J ≅ J ⋙ F₂ :=
  η ≪≫ Functor.isoWhiskerLeft J θ

theorem affineHigherCompositeFactory_hom
    {C C' : Type*} [Category C] [Category C']
    (F₀ : C ⥤ C) (F₁ F₂ : C' ⥤ C') (J : C ⥤ C')
    (η : F₀ ⋙ J ≅ J ⋙ F₁) (θ : F₁ ≅ F₂) (N : C) :
    (affineHigherCompositeFactory F₀ F₁ F₂ J η θ).hom.app N =
      η.hom.app N ≫ θ.hom.app (J.obj N) := rfl

/-- The section formula for a local restriction followed by the original affine trace. -/
def traceLocalSectionsEquation
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    {C E F : Type*} [Category* C] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ (Spec (.of A)).Modules)
    (L : (Spec (.of A)).Modules ⥤ F) (V : F ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (n : ℕ)
    (μ : L ⋙ V ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : C) [((U.obj (J.obj N))).IsQuasicoherent]
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj (J.obj N))) n →
      moduleSpecΓFunctor.obj (J.obj N))
    (z : J.obj (F1.obj (F0.obj N)) ⟶ J.obj N) : Prop :=
  ∀ x, moduleSpecΓFunctor.map z x =
    τ (moduleHigherDirectImageAffineSectionsLinearEquiv r (U.obj (J.obj N))
      (injectiveResolution (U.obj (J.obj N))) n
      (moduleSpecΓFunctor.map
        ((affineHigherCompositeFactory (F0 ⋙ F1) (L ⋙ V)
          (U ⋙ (Scheme.Modules.pushforward r).rightDerived n) J η μ).hom.app N) x))

theorem traceLocalSections_of_model
    {A : Type u} [CommRing A] {P : Scheme.{u}}
    (r : P ⟶ Spec (.of A)) [QuasiCompact r] [QuasiSeparated r]
    {C E F : Type*} [Category* C] [Category* E] [Category* F]
    (F0 : C ⥤ E) (F1 : E ⥤ C) (J : C ⥤ (Spec (.of A)).Modules)
    (L : (Spec (.of A)).Modules ⥤ F) (V : F ⥤ (Spec (.of A)).Modules)
    (U : (Spec (.of A)).Modules ⥤ P.Modules)
    (η : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (L ⋙ V)) (n : ℕ)
    (μ : L ⋙ V ≅ U ⋙ (Scheme.Modules.pushforward r).rightDerived n)
    (N : C) [((U.obj (J.obj N))).IsQuasicoherent]
    (t : V.obj (L.obj (J.obj N)) ⟶ J.obj N)
    (τ : Sheaf.H.{u + 1} (moduleAddSheaf P (U.obj (J.obj N))) n →
      moduleSpecΓFunctor.obj (J.obj N))
    (hT : traceModelSectionsEquation r (L ⋙ V) U n μ (J.obj N) τ t) :
    traceLocalSectionsEquation r F0 F1 J L V U η n μ N τ
      (traceLocalHomFactory F0 F1 J L V η N t) := by
  intro x
  dsimp only [traceLocalHomFactory]
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [affineHigherCompositeFactory_hom, Functor.map_comp, ConcreteCategory.comp_apply]
  exact hT _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem traceCanonicalLocalEquation
    {X W Y Z : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (n : ℕ) (N : Y.Modules)
    (z : (Modules.restrictFunctor j).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
      (Modules.restrictFunctor j).obj N)
    (t : ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N)
    (t' : ((Scheme.Modules.pushforward q).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N)
    (hz : traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
      ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
      (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
        (IsPullback.of_hasPullback p j) n) N z t)
    (ht : let E := H.isoPullback
      let q' := pullback.snd p j
      let HE : IsPullback E.inv q' q (𝟙 Z) :=
        IsPullback.of_horiz_isIso
          ⟨H.isoPullback_inv_snd.trans (Category.comp_id q').symm⟩
      (identityHigherModelIso q E.inv q' HE n).hom.app
        ((Modules.restrictFunctor j).obj N) ≫ t = t') :
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n)
      (relativeHigherRestrictionIso p i q j H n) N z t' := by
  dsimp only [traceLocalHomFactoryEquation, traceLocalHomFactory] at hz ⊢
  rw [hz, relativeHigherRestrictionIso_canonical p i q j H n N,
    Category.assoc, ht]

private theorem traceOpenOfChart
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ C) (G : D ⥤ D) (Q : E ⥤ E)
    (J : C ⥤ D) (K : D ⥤ E) (L : C ⥤ E) (u : L ≅ J ⋙ K)
    (α : F ⋙ J ≅ J ⋙ G) (β : G ⋙ K ≅ K ⋙ Q) (γ : F ⋙ L ≅ L ⋙ Q)
    (N : C) (t : F.obj N ⟶ N)
    (tL : Q.obj (L.obj N) ⟶ L.obj N)
    (tK : Q.obj (K.obj (J.obj N)) ⟶ K.obj (J.obj N))
    (hcomp : u.inv.app (F.obj N) ≫ γ.hom.app N ≫ Q.map (u.hom.app N) =
      K.map (α.hom.app N) ≫ β.hom.app (J.obj N))
    (hnat : Q.map (u.hom.app N) ≫ tK = tL ≫ u.hom.app N)
    (hlocal : γ.hom.app N ≫ tL = L.map t) :
    K.map (α.hom.app N) ≫ β.hom.app (J.obj N) ≫ tK = K.map (J.map t) := by
  rw [← Category.assoc, ← hcomp]
  simp only [Category.assoc]
  rw [hnat]
  have h := congrArg
    (fun z : L.obj (F.obj N) ⟶ L.obj N => u.inv.app (F.obj N) ≫ z ≫ u.hom.app N) hlocal
  have hu : K.map (J.map t) ≫ u.inv.app N = u.inv.app (F.obj N) ≫ L.map t :=
    u.inv.naturality (X := F.obj N) (Y := N) t
  calc
    _ = u.inv.app (F.obj N) ≫ L.map t ≫ u.hom.app N := by
      simpa only [Category.assoc] using h
    _ = K.map (J.map t) := by
      rw [← Category.assoc, ← hu, Category.assoc, Iso.inv_hom_id_app]
      dsimp only [Functor.comp_obj]
      exact Category.comp_id _

/-- The same chart calculation consumes the original unopened local
constructor equations, without comparing expanded trace values. -/
theorem traceOpenOfChartFactored
    {C D E A B B' : Type*}
    [Category* C] [Category* D] [Category* E]
    [Category* A] [Category* B] [Category* B']
    (F0 : C ⥤ A) (F1 : A ⥤ C)
    (G0 : D ⥤ B) (G1 : B ⥤ D) (Q0 : E ⥤ B') (Q1 : B' ⥤ E)
    (J : C ⥤ D) (K : D ⥤ E) (L : C ⥤ E) (u : L ≅ J ⋙ K)
    (α : (F0 ⋙ F1) ⋙ J ≅ J ⋙ (G0 ⋙ G1))
    (β : (G0 ⋙ G1) ⋙ K ≅ K ⋙ (Q0 ⋙ Q1))
    (γ : (F0 ⋙ F1) ⋙ L ≅ L ⋙ (Q0 ⋙ Q1))
    (N : C) (t : F1.obj (F0.obj N) ⟶ N)
    (zL : L.obj (F1.obj (F0.obj N)) ⟶ L.obj N)
    (zK : K.obj (G1.obj (G0.obj (J.obj N))) ⟶ K.obj (J.obj N))
    (tL : Q1.obj (Q0.obj (L.obj N)) ⟶ L.obj N)
    (tK : Q1.obj (Q0.obj (K.obj (J.obj N))) ⟶ K.obj (J.obj N))
    (hcomp : u.inv.app (F1.obj (F0.obj N)) ≫ γ.hom.app N ≫
        Q1.map (Q0.map (u.hom.app N)) =
      K.map (α.hom.app N) ≫ β.hom.app (J.obj N))
    (hnat : Q1.map (Q0.map (u.hom.app N)) ≫ tK = tL ≫ u.hom.app N)
    (hrestrict : L.map t = zL)
    (hzL : traceLocalHomFactoryEquation F0 F1 L Q0 Q1 γ N zL tL)
    (hzK : traceLocalHomFactoryEquation G0 G1 K Q0 Q1 β (J.obj N) zK tK) :
    K.map (α.hom.app N) ≫ zK = K.map (J.map t) := by
  dsimp only [traceLocalHomFactoryEquation, traceLocalHomFactory] at hzL hzK
  rw [hzK]
  exact traceOpenOfChart (F0 ⋙ F1) (G0 ⋙ G1) (Q0 ⋙ Q1) J K L u α β γ N t tL tK
    hcomp hnat (hzL.symm.trans hrestrict.symm)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Native restriction pasting proves the chart equation before the chart is an affine spectrum. -/
theorem traceOpenLocalEquation
    {X W V Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (b : V ⟶ W) (r : V ⟶ T) (k : T ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion k] (HB : IsPullback b r q k)
    (n : ℕ) (N : Y.Modules)
    (t : ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N)
    (zL : (Modules.restrictFunctor (k ≫ j)).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
      (Modules.restrictFunctor (k ≫ j)).obj N)
    (zK : (Modules.restrictFunctor k).obj
      (((Scheme.Modules.pushforward q).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor q n).obj
          ((Modules.restrictFunctor j).obj N))) ⟶
      (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
    (tL : ((Scheme.Modules.pushforward r).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor r n).obj
        ((Modules.restrictFunctor (k ≫ j)).obj N)) ⟶
      (Modules.restrictFunctor (k ≫ j)).obj N)
    (tK : ((Scheme.Modules.pushforward r).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor r n).obj
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))) ⟶
      (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
    (hnat : ((Scheme.Modules.pushforward r).rightDerived n).map
      ((relativeTopDifferentialCoefficientsFunctor r n).map
        ((restrictFunctorComp k j).hom.app N)) ≫ tK =
      tL ≫ (restrictFunctorComp k j).hom.app N)
    (hrestrict : (Modules.restrictFunctor (k ≫ j)).map t = zL)
    (hzL : traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor (k ≫ j))
      (relativeTopDifferentialCoefficientsFunctor r n)
      ((Scheme.Modules.pushforward r).rightDerived n)
      (relativeHigherRestrictionIso p (b ≫ i) r (k ≫ j) (HB.paste_horiz H) n) N zL tL)
    (hzK : traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n) (Modules.restrictFunctor k)
      (relativeTopDifferentialCoefficientsFunctor r n)
      ((Scheme.Modules.pushforward r).rightDerived n)
      (relativeHigherRestrictionIso q b r k HB n) ((Modules.restrictFunctor j).obj N) zK tK) :
    (Modules.restrictFunctor k).map
      ((relativeHigherRestrictionIso p i q j H n).hom.app N) ≫ zK =
    (Modules.restrictFunctor k).map ((Modules.restrictFunctor j).map t) := by
  have hc := relativeHigherRestrictionIso_comp p q r i j b k H HB (HB.paste_horiz H) n N
  dsimp -proj only [relativeHigherFunctor, Functor.comp_map] at hc
  exact traceOpenOfChartFactored
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n)
    (relativeTopDifferentialCoefficientsFunctor q n)
    ((Scheme.Modules.pushforward q).rightDerived n)
    (relativeTopDifferentialCoefficientsFunctor r n)
    ((Scheme.Modules.pushforward r).rightDerived n)
    (Modules.restrictFunctor j) (Modules.restrictFunctor k)
    (Modules.restrictFunctor (k ≫ j)) (restrictFunctorComp k j)
    (relativeHigherRestrictionIso p i q j H n)
    (relativeHigherRestrictionIso q b r k HB n)
    (relativeHigherRestrictionIso p (b ≫ i) r (k ≫ j) (HB.paste_horiz H) n)
    N t zL zK tL tK hc hnat hrestrict hzL hzK

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
