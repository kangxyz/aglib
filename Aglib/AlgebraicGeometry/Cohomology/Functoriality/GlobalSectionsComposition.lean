/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.SingleComparison

/-!
# Actual structural global sections and native derived pushforward

Global sections of the original pushforward agree with the original source
sections for the induced structural ring map. The comparison is the identity
on section values. A bounded-below complex of flasque module sheaves computes
its installed derived global sections; the private proof uses the actual
flasque differential kernels and the original mapping cone.

The native composite-derived unit therefore derives pushforward followed by
structural sections for every scheme morphism. For a closed immersion, exact
pushforward gives an actual comparison on every original bounded-below complex
and native module single. Original units, coefficient maps and native single
comparisons are retained. No quasicoherence, Noetherianity or flatness is
assumed, and preservation of injectives by pushforward is not asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R]

/-- The standard derived-category model for modules on `X`, used locally. -/
local instance globalSectionsCompositionStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance globalSectionsCompositionTargetDerived :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

private theorem globalSections_exactAt_of_acyclic_flasque (X : Scheme.{u})
    (α : R →+* Γ(X, ⊤)) (K : CochainComplex X.Modules ℤ)
    (a : ℤ) (hl : ∀ n, n < a → IsZero (K.X n)) (hA : ∀ n, K.ExactAt n)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf) (n : ℤ) :
    (((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).obj K).ExactAt
      (n + 1) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let k := kernel.lift (K.d (n + 1) (n + 2)) (K.d n (n + 1))
    (K.d_comp_d n (n + 1) (n + 2))
  let : TopCat.Presheaf.IsFlasque
      (CochainComplex.kernelSequence K n).X₁.presheaf :=
    acyclicComplex_kernel_isFlasque K a hl hA hK n
  have hk : Function.Surjective (F.map k) :=
    sections_surjective_of_flasque_kernel
      (CochainComplex.kernelSequence_shortExact K n (hA (n + 1))) ⊤
  have he : Epi (F.map k) := (ModuleCat.epi_iff_surjective _).mpr hk
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; omega),
    ShortComplex.exact_iff_epi_kernel_lift]
  have h : kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1)))
      (by rw [← F.map_comp, K.d_comp_d, F.map_zero]) =
      F.map k ≫ kernelComparison (K.d (n + 1) (n + 2)) F := by
    apply (cancel_mono (kernel.ι (F.map (K.d (n + 1) (n + 2))))).mp
    simp only [kernel.lift_ι, Category.assoc, kernelComparison_comp_ι, ← F.map_comp]
    rw [kernel.lift_ι]
  change Epi (kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1))) _)
  rw [h]
  infer_instance

private theorem quasiIso_globalSections_of_flasque (X : Scheme.{u})
    (α : R →+* Γ(X, ⊤))
    {K L : CochainComplex X.Modules ℤ} (s : K ⟶ L) [QuasiIso s]
    (a b : ℤ) (hKa : ∀ n, n < a → IsZero (K.X n))
    (hLb : ∀ n, n < b → IsZero (L.X n))
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).presheaf)
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.X n).presheaf) :
    QuasiIso (((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)).map s) := by
  have hlow (n : ℤ) (hn : n < min a b - 1) : IsZero ((CochainComplex.mappingCone s).X n) := by
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hKa (n + 1) (by omega), hLb n (by omega)⟩
  have hA := CochainComplex.mappingCone_acyclic_of_quasiIso s
  have hF := mappingCone_isFlasque s hK hL
  apply CochainComplex.quasiIso_of_mappingCone_acyclic
  intro n
  have h := globalSections_exactAt_of_acyclic_flasque X α (CochainComplex.mappingCone s)
    (min a b - 1) hlow hA hF (n - 1)
  rw [sub_add_cancel] at h
  exact h.of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso s (moduleGlobalSectionsFunctorOfHom X α))

/-- The original installed structural global-sections derived unit is invertible on every
bounded-below complex with flasque terms. -/
theorem isIso_moduleGlobalSectionsRightDerivedFunctorPlusUnit_of_flasque
    (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (K : CochainComplex.Plus X.Modules)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf) :
    IsIso ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨a, ha⟩ := K.property
  let := ha
  obtain ⟨J, hJ, q, hq⟩ := CochainComplex.Plus.exists_quasiIso_injective K a
  let L := (InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J
  let F := moduleGlobalSectionsFunctorOfHom X α
  let : QuasiIso q.hom := hq
  have hL (n : ℤ) : TopCat.Presheaf.IsFlasque (L.obj.X n).presheaf := by
    let : Injective (L.obj.X n) := inferInstanceAs (Injective (J.obj.X n).obj)
    infer_instance
  obtain ⟨b, hb⟩ := L.property
  let := hb
  have hFq : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map q.hom) :=
    quasiIso_globalSections_of_flasque X α q.hom a b
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)
      (fun n hn => CochainComplex.isZero_of_isStrictlyGE L.obj b n hn) hK hL
  have hQq : IsIso (DerivedCategory.Plus.Q.map q) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) q hq
  have hFQq : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (ModuleCat.{u} R)) _ hFq
  have hI : IsIso (F.rightDerivedFunctorPlusUnit.app L) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)))
  have hRq : IsIso ((DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus).map q) :=
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map q)))
  have hcomp : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      (DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus).map q) := by
    rw [← F.rightDerivedFunctorPlusUnit.naturality q]
    exact inferInstanceAs
      (IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map q) ≫
        F.rightDerivedFunctorPlusUnit.app L))
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus).map q)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (α : R →+* Γ(Y, ⊤))

/-- Original pushforward global sections are the actual source global sections for the induced
structural ring map. -/
def modulePushforwardGlobalSectionsIso :
    Scheme.Modules.pushforward f ⋙ moduleGlobalSectionsFunctorOfHom Y α ≅
      moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α) :=
  NatIso.ofComponents
    (fun M => (moduleTopSectionsIso Y α ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
      (modulePushforwardSectionsPresheafIso f α M).app (op ⊤) ≪≫
      moduleTopSectionsIso X (f.appTop.hom.comp α) M)
    (by intro M N φ; ext x; rfl)

/-- The original forward comparison is the literal identity on section values. -/
theorem modulePushforwardGlobalSectionsIso_hom_app_apply (M : X.Modules)
    (x : (moduleGlobalSectionsFunctorOfHom Y α).obj ((Scheme.Modules.pushforward f).obj M)) :
    (modulePushforwardGlobalSectionsIso f α).hom.app M x = x := rfl

/-- The original inverse comparison is the literal identity on section values. -/
theorem modulePushforwardGlobalSectionsIso_inv_app_apply (M : X.Modules)
    (x : (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).obj M) :
    (modulePushforwardGlobalSectionsIso f α).inv.app M x = x := rfl

/-- The original composite unit computes right derivation, since actual pushforward of each
injective complex has flasque terms. -/
theorem moduleGlobalSectionsPushforwardComp_isRightDerived :
    ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (moduleGlobalSectionsFunctorOfHom Y α))
      (CochainComplex.Plus.quasiIso X.Modules) := by
  let F := Scheme.Modules.pushforward f
  let G := moduleGlobalSectionsFunctorOfHom Y α
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (F ⋙ G)).isRightDerivedFunctor_of_isIso
  intro J
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  change IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
    ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)) ≫
    G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J)))
  have : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj
      ((InjectiveObject.ι X.Modules).mapCochainComplexPlus.obj J))) := by
    apply isIso_moduleGlobalSectionsRightDerivedFunctorPlusUnit_of_flasque
    intro n
    change TopCat.Presheaf.IsFlasque
      ((Scheme.Modules.pushforward f).obj (J.obj.X n).obj).presheaf
    infer_instance
  infer_instance

/-- The native composite of pushforward and structural sections has its actual right-derived
comparison. -/
def moduleGlobalSectionsPushforwardFunctorCompIso :
    (Scheme.Modules.pushforward f ⋙ moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus := by
  let := moduleGlobalSectionsPushforwardComp_isRightDerived f α
  exact rightDerivedUnique _ _
    (Scheme.Modules.pushforward f ⋙ moduleGlobalSectionsFunctorOfHom Y
      α).rightDerivedFunctorPlusUnit
    (Functor.rightDerivedFunctorPlusCompUnit
      (Scheme.Modules.pushforward f) (moduleGlobalSectionsFunctorOfHom Y α))
    (CochainComplex.Plus.quasiIso X.Modules)

/-- The derived comparison retains both original derived units in their original order. -/
theorem moduleGlobalSectionsPushforwardFunctorCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pushforward f ⋙
      moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.app K ≫
        (moduleGlobalSectionsPushforwardFunctorCompIso f α).hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (moduleGlobalSectionsFunctorOfHom Y α)).app K := by
  let := moduleGlobalSectionsPushforwardComp_isRightDerived f α
  simpa only [moduleGlobalSectionsPushforwardFunctorCompIso, rightDerivedUnique,
    rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    rightDerivedNatTrans_app
      (Scheme.Modules.pushforward f ⋙ moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus)
      (Scheme.Modules.pushforward f ⋙ moduleGlobalSectionsFunctorOfHom Y
        α).rightDerivedFunctorPlusUnit
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (moduleGlobalSectionsFunctorOfHom Y α))
      (CochainComplex.Plus.quasiIso X.Modules) (𝟙 _) K

/-- Original source derived global sections agree with derived pushforward followed by
original target derived global sections. -/
def moduleDerivedGlobalSectionsPushforwardCompIso :
    (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus :=
  (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlusIso
      (modulePushforwardGlobalSectionsIso f α).symm ≪≫
    moduleGlobalSectionsPushforwardFunctorCompIso f α

/-- The geometric comparison retains the same original section isomorphism and native
composite unit. -/
theorem moduleDerivedGlobalSectionsPushforwardCompIso_unit
    (K : CochainComplex.Plus X.Modules) :
    (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlusUnit.app K ≫
        (moduleDerivedGlobalSectionsPushforwardCompIso f α).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso f α)).inv.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit
        (Scheme.Modules.pushforward f) (moduleGlobalSectionsFunctorOfHom Y α)).app K := by
  have hM := (moduleGlobalSectionsFunctorOfHom X
    (f.appTop.hom.comp α)).rightDerivedFunctorPlusIso_hom_app
      (modulePushforwardGlobalSectionsIso f α).symm K
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc]
  erw [hM]
  rw [Category.assoc, moduleGlobalSectionsPushforwardFunctorCompIso_unit]
  rfl

variable [IsClosedImmersion f]

/-- Exact closed pushforward gives the actual derived global-sections comparison on each
original bounded-below complex. -/
def moduleDerivedGlobalSectionsClosedImmersionComplexIso
    (K : CochainComplex.Plus X.Modules) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K)) ≅
      (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K) := by
  let := (Scheme.Modules.pushforward f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.mapIso
      (asIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app K)) ≪≫
    (moduleDerivedGlobalSectionsPushforwardCompIso f α).symm.app (DerivedCategory.Plus.Q.obj K)

/-- The forward comparison is exactly the image of the original exact-pushforward unit
followed by the native composite inverse. -/
theorem moduleDerivedGlobalSectionsClosedImmersionComplexIso_hom
    (K : CochainComplex.Plus X.Modules) :
    (moduleDerivedGlobalSectionsClosedImmersionComplexIso f α K).hom =
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.app (DerivedCategory.Plus.Q.obj K) :=
  rfl

/-- The exact-closed comparison preserves the original global-sections derived unit and the
original section comparison. -/
theorem moduleDerivedGlobalSectionsClosedImmersionComplexIso_unit
    (K : CochainComplex.Plus X.Modules) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K) ≫
        (moduleDerivedGlobalSectionsClosedImmersionComplexIso f α K).hom =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso f α)).hom.app K) ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlusUnit.app
          K := by
  apply (cancel_mono
    ((moduleDerivedGlobalSectionsPushforwardCompIso f α).hom.app
      (DerivedCategory.Plus.Q.obj K))).mp
  rw [moduleDerivedGlobalSectionsClosedImmersionComplexIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [moduleDerivedGlobalSectionsPushforwardCompIso_unit]
  conv_rhs =>
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
  simp only [Functor.rightDerivedFunctorPlusCompUnit_app]
  erw [Category.comp_id]

/-- Every native coefficient-complex morphism is preserved by the exact-closed comparison. -/
theorem moduleDerivedGlobalSectionsClosedImmersionComplexIso_naturality
    {K L : CochainComplex.Plus X.Modules} (p : K ⟶ L) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map p)) ≫
        (moduleDerivedGlobalSectionsClosedImmersionComplexIso f α L).hom =
      (moduleDerivedGlobalSectionsClosedImmersionComplexIso f α K).hom ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map p) := by
  have hF := congrArg (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
    ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.naturality p)
  simp only [Functor.map_comp, Functor.comp_map] at hF
  have hC := (moduleDerivedGlobalSectionsPushforwardCompIso f α).inv.naturality
    (DerivedCategory.Plus.Q.map p)
  simp only [Functor.comp_map] at hC
  rw [moduleDerivedGlobalSectionsClosedImmersionComplexIso_hom,
    moduleDerivedGlobalSectionsClosedImmersionComplexIso_hom]
  rw [← Category.assoc, hF, Category.assoc, hC, Category.assoc]

/-- Derived global sections of the original exact closed pushforward single are actual source
derived global sections. -/
def moduleDerivedGlobalSectionsClosedImmersionSingleIso (M : X.Modules) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj
          M)) ≅
      (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.mapIso
      (DerivedCategory.Plus.Q.mapIso ((exactSingleComplexNatIso (Scheme.Modules.pushforward
        f)).app M).symm) ≪≫
    moduleDerivedGlobalSectionsClosedImmersionComplexIso f α
      ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)

/-- The forward single comparison retains the native original single-complex comparison and
exact-closed model. -/
theorem moduleDerivedGlobalSectionsClosedImmersionSingleIso_hom (M : X.Modules) :
    (moduleDerivedGlobalSectionsClosedImmersionSingleIso f α M).hom =
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)) ≫
        (moduleDerivedGlobalSectionsClosedImmersionComplexIso f α
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)).hom := rfl

/-- The native single comparison retains both original global-sections units and the original
pushforward-section isomorphism. -/
theorem moduleDerivedGlobalSectionsClosedImmersionSingleIso_unit (M : X.Modules) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj
          M)) ≫
        (moduleDerivedGlobalSectionsClosedImmersionSingleIso f α M).hom =
      DerivedCategory.Plus.Q.map
          ((moduleGlobalSectionsFunctorOfHom Y α).mapCochainComplexPlus.map
            ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)) ≫
        DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (modulePushforwardGlobalSectionsIso f α)).hom.app
            ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlusUnit.app
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) := by
  have h := (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.naturality
    ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)
  simp only [Functor.comp_map] at h
  change DerivedCategory.Plus.Q.map
      ((moduleGlobalSectionsFunctorOfHom Y α).mapCochainComplexPlus.map
        ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)) ≫
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) =
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj
          M)) ≫
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)) at h
  rw [moduleDerivedGlobalSectionsClosedImmersionSingleIso_hom]
  rw [← Category.assoc, ← h, Category.assoc,
    moduleDerivedGlobalSectionsClosedImmersionComplexIso_unit]

/-- Every original module morphism commutes with the exact-closed single comparison. -/
theorem moduleDerivedGlobalSectionsClosedImmersionSingleIso_naturality
    {M N : X.Modules} (g : M ⟶ N) :
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((Scheme.Modules.pushforward f).map
          g)) ≫
        (moduleDerivedGlobalSectionsClosedImmersionSingleIso f α N).hom =
      (moduleDerivedGlobalSectionsClosedImmersionSingleIso f α M).hom ≫
        (moduleGlobalSectionsFunctorOfHom X (f.appTop.hom.comp α)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).map g) := by
  have h := congrArg (fun q =>
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map q))
    ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.naturality g)
  simp only [Functor.map_comp, Functor.comp_map] at h
  change (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).map ((Scheme.Modules.pushforward f).map
        g)) ≫
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app N)) =
    (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((exactSingleComplexNatIso (Scheme.Modules.pushforward f)).inv.app M)) ≫
      (moduleGlobalSectionsFunctorOfHom Y α).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward f).mapCochainComplexPlus.map
          ((CochainComplex.singleFunctorPlus X.Modules 0).map g))) at h
  rw [moduleDerivedGlobalSectionsClosedImmersionSingleIso_hom,
    moduleDerivedGlobalSectionsClosedImmersionSingleIso_hom]
  rw [← Category.assoc, h, Category.assoc,
    moduleDerivedGlobalSectionsClosedImmersionComplexIso_naturality, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
