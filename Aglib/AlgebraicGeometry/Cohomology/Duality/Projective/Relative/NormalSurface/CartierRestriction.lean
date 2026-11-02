/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CartierRegularity
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.CartierRestriction.Transport
public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity.Global
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.CohenMacaulayCurve.Coefficients.Serre
public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Residue.Coinduction.HomComparison
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.RegularQuotient
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Blowup.Exceptional.Geometry
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The original normal-surface canonical restriction

The positive original Cartier row, own canonical reconstructions and native
finite-local coinduction comparison identify the actual twisted quotient with
the coefficient-valued curve canonical module. Coherent Hom Yoneda supplies the
same isomorphism in every Ext degree. Original structural units and the native
counit normalize its trace. The literal rational-blowup specialization derives
normality and the required closed-stalk parameters from its geometric producers.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Functor
open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Opposite IsLocalRing
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open RelativeCanonicalReindex
open scoped TensorProduct ModuleCat.Algebra

private theorem restriction_regularParameter_of_principal_surjection
    {S B : Type u} [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [IsIntegrallyClosed S] [CommRing B] [IsLocalRing B]
    (φ : S →+* B) (hφ : Function.Surjective φ)
    (hdim : ringKrullDim S = 2) (t : S) (ht0 : t ≠ 0)
    (ht : t ∈ maximalIdeal S) (hker : RingHom.ker φ = Ideal.span {t}) :
    ∃ b ∈ maximalIdeal B, IsSMulRegular B b ∧
      (Ideal.span {b}).radical = maximalIdeal B := by
  let : Ring.KrullDimLE 2 S := Ring.krullDimLE_iff.mpr hdim.le
  let : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  obtain ⟨s, hs, hrad⟩ := exists_parameter_pair_containing S t ht0 ht
  have havoid : ∀ P : Ideal S, P.IsPrime → P.height = 1 → t ∈ P → s ∉ P := by
    intro P hP hheight htP hsP
    let : P.IsPrime := hP
    have hle : Ideal.span {t} ⊔ Ideal.span {s} ≤ P :=
      sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htP))
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsP))
    have hmle : maximalIdeal S ≤ P := by
      rw [← hrad]
      exact hP.radical_le_iff.mpr hle
    have he : maximalIdeal S = P :=
      le_antisymm hmle (le_maximalIdeal_of_isPrime P)
    have hd : 2 ≤ ringKrullDim S := hdim.ge
    rw [← maximalIdeal_height_eq_ringKrullDim, he, hheight] at hd
    norm_num at hd
  let Q := S ⧸ Ideal.span {t}
  let q : S →+* Q := Ideal.Quotient.mk (Ideal.span {t})
  have hreg : IsSMulRegular Q s :=
    IsIntegrallyClosed.isSMulRegular_quotient_of_pair_avoids_height_one t s ht0 havoid
  let e : Q ≃+* B := (Ideal.quotEquivOfEq hker.symm).trans
    (φ.quotientKerEquivOfSurjective hφ)
  have he (a : S) : e (q a) = φ a := by
    change (φ.quotientKerEquivOfSurjective hφ)
      ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk (Ideal.span {t}) a)) = φ a
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ a
  refine ⟨φ s, map_nonunit φ s hs, ?_, ?_⟩
  · intro x y hxy
    change φ s * x = φ s * y at hxy
    apply e.symm.injective
    apply hreg
    apply e.injective
    change e (q s * e.symm x) = e (q s * e.symm y)
    simpa only [map_mul, he, e.apply_symm_apply] using hxy
  · have hkerle : RingHom.ker φ ≤ Ideal.span {t} ⊔ Ideal.span {s} := by
      rw [hker]
      exact le_sup_left
    have h := congrArg (Ideal.map φ) hrad
    rw [Ideal.map_radical_of_surjective hφ hkerle,
      map_maximalIdeal_of_surjective φ hφ] at h
    have htker : t ∈ RingHom.ker φ := by
      rw [hker]
      exact Ideal.mem_span_singleton_self t
    have hφt : φ t = 0 := htker
    simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hφt,
      Ideal.span_singleton_zero, bot_sup_eq] using h

private theorem restriction_closedStalk_parameter
    {E X : Scheme.{u}} [IsLocallyNoetherian X] (i : E ⟶ X) [IsClosedImmersion i]
    (hX : Scheme.NormalStalks X) (hI : IsLocallyRankOne X (idealModule i))
    (x : E) (hdim : ringKrullDim (X.presheaf.stalk (i x)) = 2) :
    ∃ b ∈ maximalIdeal (E.presheaf.stalk x), IsSMulRegular (E.presheaf.stalk x) b ∧
      (Ideal.span {b}).radical = maximalIdeal (E.presheaf.stalk x) := by
  let S := X.presheaf.stalk (i x)
  let B := E.presheaf.stalk x
  let φ : S →+* B := (i.stalkMap x).hom
  let : IsDomain S := (hX (i x)).1
  let : IsIntegrallyClosed S := (hX (i x)).2
  let L : LineBundle (Spec S) :=
    ⟨(Scheme.Modules.pullback (X.fromSpecStalk (i x))).obj (idealModule i),
      pullback_locallyRankOne _ _ hI⟩
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing S L
  let eM : (moduleStalk X (i x)).obj (idealModule i) ≅ ModuleCat.of S S :=
    stalkFromSpecStalkSectionsIso X (i x) (idealModule i) ≪≫
      moduleSpecΓFunctor.mapIso e ≪≫ (tilde.isoTop (ModuleCat.of S S)).symm
  let eK : RingHom.ker φ ≃ₗ[S] S :=
    (LinearEquiv.ofEq _ _ (i.ker_stalkIdeal_eq_ker_stalkMap x).symm).trans
      ((idealModuleStalkEquiv i (i x)).symm.trans eM.toLinearEquiv)
  obtain ⟨t, htreg, hker⟩ := Ideal.ideal_exists_regular_generator (RingHom.ker φ) eK
  have ht0 : t ≠ 0 := by
    intro h
    have h10 : (1 : S) = 0 := htreg (by simp only [h, zero_smul])
    exact one_ne_zero h10
  have htker : t ∈ RingHom.ker φ := by
    rw [hker]
    exact Ideal.mem_span_singleton_self t
  have ht : t ∈ maximalIdeal S := by
    intro hu
    exact (hu.map φ).ne_zero (show φ t = 0 from htker)
  exact restriction_regularParameter_of_principal_surjection φ (i.stalkMap_surjective x)
    hdim t ht0 ht hker

namespace AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The standard module derived model used by the original affine comparisons. -/
public local instance restrictionModuleDerived (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- The structure coefficient is finitely presented via its original singleton
free-module presentation. -/
public local instance restrictionUnit_finitePresentation (E : Scheme.{u}) :
    (SheafOfModules.unit E.ringCatSheaf).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation E.ringCatSheaf).prop_of_iso
    (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit E.ringCatSheaf))
    (lineBundle_isFinitePresentation E (trivialLineBundle E))

/-- Original restrictionHomIsoAddEquiv comparison, retained for the exposed restriction maps. -/
public def restrictionHomIsoAddEquiv {C : Type*} [Category* C] [Preadditive C]
    {K K' L L' : C} (e : K ≅ K') (d : L ≅ L') : (K ⟶ L) ≃+ (K' ⟶ L') where
  toFun f := e.inv ≫ f ≫ d.hom
  invFun g := e.hom ≫ g ≫ d.inv
  left_inv f := by simp only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]
  right_inv g := by simp only [Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]
  map_add' f g := by simp only [Preadditive.comp_add, Preadditive.add_comp]

private theorem restriction_cancel_iso_of_eq
    {C : Type*} [Category C] {A B D E Z : C}
    (e : D ≅ E) (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ Z)
    (f : A ⟶ D) (g : D ⟶ Z)
    (hf : f = a ≫ b ≫ e.inv) (hg : g = e.hom ≫ c) :
    f ≫ g = a ≫ b ≫ c := by
  rw [hf, hg]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem restriction_paste
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ F)
    (e : F ⟶ E) (f : E ⟶ G) (g : G ⟶ H) (h : F ⟶ H)
    (hn : b ≫ c = d ≫ e) (hc : e ≫ f ≫ g = h) :
    (a ≫ b ≫ c ≫ f) ≫ g = a ≫ d ≫ h := by
  calc
    (a ≫ b ≫ c ≫ f) ≫ g = a ≫ (b ≫ c) ≫ f ≫ g := by simp only [Category.assoc]
    _ = a ≫ (d ≫ e) ≫ f ≫ g := by rw [hn]
    _ = a ≫ d ≫ h := by rw [← hc]; simp only [Category.assoc]

private theorem restriction_map_comp_under
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {A B E : C} {X Y : D} (a : A ⟶ B) (b : B ⟶ E)
    (l : X ⟶ H.obj A) (r : H.obj E ⟶ Y) :
    l ≫ H.map a ≫ H.map b ≫ r = l ≫ H.map (a ≫ b) ≫ r := by
  rw [H.map_comp]
  simp only [Category.assoc]

section CartierExt

variable {E X : Scheme.{u}} (i : E ⟶ X) [IsClosedImmersion i]
  (hI : IsLocallyRankOne X (idealModule i))
  (M : X.Modules) [Mono ((cartierTensorSection i).app M)]

/-- The actual twisted pullback quotient of the original Cartier row. -/
public abbrev cartierRestrictionQuotient : E.Modules :=
  (Scheme.Modules.pullback i).obj (tensorSheaf X (dualSheaf X (idealModule i)) M)

/-- The native pushforward of an Ext class followed by the positive original
Cartier row class. No derived comparison replaces this displayed map. -/
public def cartierRestrictionExtMap (F : E.Modules) (r : ℕ) :
    Ext.{u + 1} F (cartierRestrictionQuotient i M) r →+
      Ext.{u + 1} ((Scheme.Modules.pushforward i).obj F) M (r + 1) :=
  ((cartierCoefficientSequence_shortExact i hI M).extClass.postcomp
    ((Scheme.Modules.pushforward i).obj F) rfl).comp
      ((Scheme.Modules.pushforward i).mapExtAddHom F (cartierRestrictionQuotient i M) r)

/-- The degree-zero identity has exactly the original positive extension class. -/
public theorem cartierRestrictionExtMap_identity :
    cartierRestrictionExtMap i hI M (cartierRestrictionQuotient i M) 0
        (Ext.mk₀ (𝟙 _)) = (cartierCoefficientSequence_shortExact i hI M).extClass := by
  change ((Ext.mk₀ (𝟙 _)).mapExactFunctor (Scheme.Modules.pushforward i)).comp
    _ (Nat.zero_add 1) = _
  erw [Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id, Ext.mk₀_id_comp]

/-- Its source Yoneda law retains the actual native pushforward and positive row. -/
public theorem cartierRestrictionExtMap_comp {F F' : E.Modules} {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' (cartierRestrictionQuotient i M) b)
    (hab : a + b = r) :
    cartierRestrictionExtMap i hI M F r (α.comp x hab) =
      (α.mapExactFunctor (Scheme.Modules.pushforward i)).comp
        (cartierRestrictionExtMap i hI M F' b x) (by omega) := by
  change ((α.comp x hab).mapExactFunctor (Scheme.Modules.pushforward i)).comp _ rfl = _
  rw [Ext.mapExactFunctor_comp]
  exact Ext.comp_assoc _ _ (cartierCoefficientSequence_shortExact i hI M).extClass
    hab rfl (by omega)

/-- The actual positive mate proves bijectivity of the displayed Cartier Ext map. -/
public theorem cartierRestrictionExtMap_bijective [IsLocallyNoetherian X]
    [M.IsQuasicoherent] (F : E.Modules) (r : ℕ) :
    Function.Bijective (cartierRestrictionExtMap i hI M F r) := by
  let Q := cartierRestrictionQuotient i M
  let D := DerivedCategory.Plus.ι.obj (globalCartierDerivedObject i M)
  let η := cartierCoefficientExtensionMate i hI M
  let : IsIso η := cartierCoefficientExtensionMate_isIso i hI M
  let eQ : ((DerivedCategory.singleFunctor E.Modules 0).obj Q)⟦(r : ℤ)⟧ ≅
      D⟦((r + 1 : ℕ) : ℤ)⟧ :=
    (shiftFunctor (DerivedCategory E.Modules) (r : ℤ)).mapIso (asIso η) ≪≫
      ((shiftFunctorAdd' (DerivedCategory E.Modules) 1 (r : ℤ) ((r + 1 : ℕ) : ℤ)
        (by omega)).app D).symm
  let adj := Scheme.Modules.closedImmersionRightAdjunction i
  let J := injectiveResolution M
  let B : Ext.{u + 1} F Q r ≃+
      Ext.{u + 1} ((Scheme.Modules.pushforward i).obj F) M (r + 1) :=
    (Ext.homAddEquiv (X := F) (Y := Q) (n := r)).trans
      ((restrictionHomIsoAddEquiv
        (Iso.refl ((DerivedCategory.singleFunctor E.Modules 0).obj F)) eQ).trans
          ((adj.singleDerivedHomEquivOfInjectiveResolution F J ((r + 1 : ℕ) : ℤ)).symm.trans
            Ext.homAddEquiv.symm))
  have hη : (adj.singleDerivedHomEquivOfInjectiveResolution Q J 1).symm η =
      (cartierCoefficientSequence_shortExact i hI M).extClass.hom :=
    (adj.singleDerivedHomEquivOfInjectiveResolution Q J 1).symm_apply_apply _
  have hB (x : Ext.{u + 1} F Q r) : B x = cartierRestrictionExtMap i hI M F r x := by
    apply Ext.ext
    change Ext.homAddEquiv (Ext.homAddEquiv.symm
      ((adj.singleDerivedHomEquivOfInjectiveResolution F J ((r + 1 : ℕ) : ℤ)).symm
        ((𝟙 _) ≫ x.hom ≫ eQ.hom))) = _
    rw [AddEquiv.apply_symm_apply, Category.id_comp]
    change (adj.singleDerivedHomEquivOfInjectiveResolution F J ((r + 1 : ℕ) : ℤ)).symm
      (x.hom.comp η (by omega)) = _
    erw [Adjunction.singleDerivedHomEquivOfInjectiveResolution_symm_comp_ext, hη]
    exact (Ext.comp_hom (x.mapExactFunctor (Scheme.Modules.pushforward i))
      (cartierCoefficientSequence_shortExact i hI M).extClass rfl).symm
  have heq : (cartierRestrictionExtMap i hI M F r : _ → _) = B := by
    funext x
    exact (hB x).symm
  rw [heq]
  exact B.bijective

end CartierExt

section FiniteSections

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]
  [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k]
  (hdR : ringKrullDim R = (2 : ℕ))
  (E : Scheme.{u}) (αk : k →+* Γ(E, ⊤)) (αR : R →+* Γ(E, ⊤))
  (hα : αR = RingHom.comp αk (algebraMap R k))

/-- Original restrictionSectionsR comparison, retained for the exposed restriction maps. -/
public abbrev restrictionSectionsR :=
  (moduleGlobalSectionsFunctorOfHom E αR).rightDerivedFunctorPlus

/-- Original restrictionSectionsK comparison, retained for the exposed restriction maps. -/
public abbrev restrictionSectionsK :=
  (moduleGlobalSectionsFunctorOfHom E αk).rightDerivedFunctorPlus

/-- Original restrictionScalarSectionsIso comparison, retained for the exposed restriction maps. -/
public def restrictionScalarSectionsIso :
    restrictionSectionsR R E αR ≅ restrictionSectionsK k E αk ⋙
      (ModuleCat.restrictScalars (algebraMap R k)).rightDerivedFunctorPlus :=
  moduleDerivedGlobalSectionsRestrictIso E (algebraMap R k) αk αR hα

omit [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k] in
private theorem restrictionScalarSectionsIso_commShift :
    (restrictionScalarSectionsIso R k E αk αR hα).hom.CommShift ℤ := by
  let F := moduleGlobalSectionsFunctorOfHom E αR
  let G := moduleGlobalSectionsFunctorOfHom E αk
  let U := ModuleCat.restrictScalars (algebraMap R k)
  let e := moduleGlobalSectionsRestrictIso E (algebraMap R k) αk αR hα
  let : (F.rightDerivedFunctorPlusIso e).hom.CommShift ℤ :=
    restriction_derivedIso_commShift F (G ⋙ U) e
  let : (rightDerivedFunctorPlusCompIsoOfPreservesHomology G U).hom.CommShift ℤ :=
    restriction_derivedComp_commShift G U
  change NatTrans.CommShift ((F.rightDerivedFunctorPlusIso e).hom ≫
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology G U).hom) ℤ
  infer_instance

/-- Original restrictionFiniteHomEquiv comparison, retained for the exposed restriction maps. -/
public def restrictionFiniteHomEquiv (M : DerivedCategory.Plus E.Modules) (r : ℤ) :
    ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionSectionsR R E αR).obj M))
      (ModuleCat.residueBaseSingle R) (r + 1) ≃+
    ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionSectionsK k E αk).obj M))
      (ModuleCat.residueLineSingle R k) (r - 1) :=
  (restrictionHomIsoAddEquiv
    (DerivedCategory.Plus.ι.mapIso ((restrictionScalarSectionsIso R k E αk αR hα).app M))
    (Iso.refl ((ModuleCat.residueBaseSingle R)⟦r + 1⟧))) |>.trans
      (ModuleCat.residueLineHomEquivPlus R k hdR ((restrictionSectionsK k E αk).obj M) r)

private theorem restrictionFiniteHomEquiv_symm_apply
    (M : DerivedCategory.Plus E.Modules) (r : ℤ)
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionSectionsK k E αk).obj M))
      (ModuleCat.residueLineSingle R k) (r - 1)) :
    (restrictionFiniteHomEquiv R k hdR E αk αR hα M r).symm g =
      DerivedCategory.Plus.ι.map
        ((restrictionScalarSectionsIso R k E αk αR hα).hom.app M) ≫
      (ModuleCat.residueLineHomEquivPlus R k hdR
        ((restrictionSectionsK k E αk).obj M) r).symm g := by
  simp only [restrictionFiniteHomEquiv, AddEquiv.symm_trans_apply,
    restrictionHomIsoAddEquiv, Iso.refl_inv, Category.comp_id]
  rfl

private theorem restrictionFiniteHomEquiv_symm_comp
    {M M' : DerivedCategory.Plus E.Modules} {a r t : ℤ}
    (β : ShiftedHom M M' a)
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionSectionsK k E αk).obj M'))
      (ModuleCat.residueLineSingle R k) (r - 1)) (h : r + a = t) :
    (restrictionFiniteHomEquiv R k hdR E αk αR hα M t).symm
        ((β.map (restrictionSectionsK k E αk ⋙ DerivedCategory.Plus.ι)).comp g (by omega)) =
      (β.map (restrictionSectionsR R E αR ⋙ DerivedCategory.Plus.ι)).comp
        ((restrictionFiniteHomEquiv R k hdR E αk αR hα M' r).symm g) (by omega) := by
  let U := (ModuleCat.restrictScalars (algebraMap R k)).rightDerivedFunctorPlus
  let J : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let C : restrictionSectionsR R E αR ⋙ J ≅ restrictionSectionsK k E αk ⋙ U ⋙ J :=
    Functor.isoWhiskerRight (restrictionScalarSectionsIso R k E αk αR hα) J ≪≫
      Functor.associator _ _ _
  let : (restrictionScalarSectionsIso R k E αk αR hα).hom.CommShift ℤ :=
    restrictionScalarSectionsIso_commShift R k E αk αR hα
  let : C.hom.CommShift ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight (restrictionScalarSectionsIso R k E αk αR hα).hom J ≫
        (Functor.associator _ _ _).hom) ℤ
    infer_instance
  have hC (T : DerivedCategory.Plus E.Modules) :
      C.hom.app T = J.map ((restrictionScalarSectionsIso R k E αk αR hα).hom.app T) :=
    Category.comp_id _
  have hβ := ShiftedHom.map_naturality β C.hom
  rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, hC, hC] at hβ
  rw [restrictionFiniteHomEquiv_symm_apply, restrictionFiniteHomEquiv_symm_apply]
  rw [ShiftedHom.comp_map,
    ModuleCat.residueLineHomEquivPlus_symm_comp R k hdR _ g h]
  simpa only [ShiftedHom.comp, ShiftedHom.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun q => q ≫
      ((ModuleCat.residueLineHomEquivPlus R k hdR
        ((restrictionSectionsK k E αk).obj M') r).symm g)⟦a⟧' ≫
        (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) (r + 1) a (t + 1)
          (by omega)).inv.app (ModuleCat.residueBaseSingle R)) hβ.symm

private theorem restrictionFiniteHomEquiv_comp
    {M M' : DerivedCategory.Plus E.Modules} {a r t : ℤ}
    (β : ShiftedHom M M' a)
    (f : ShiftedHom (DerivedCategory.Plus.ι.obj ((restrictionSectionsR R E αR).obj M'))
      (ModuleCat.residueBaseSingle R) (r + 1)) (h : r + a = t) :
    restrictionFiniteHomEquiv R k hdR E αk αR hα M t
        ((β.map (restrictionSectionsR R E αR ⋙ DerivedCategory.Plus.ι)).comp f (by omega)) =
      (β.map (restrictionSectionsK k E αk ⋙ DerivedCategory.Plus.ι)).comp
        (restrictionFiniteHomEquiv R k hdR E αk αR hα M' r f) (by omega) := by
  apply (restrictionFiniteHomEquiv R k hdR E αk αR hα M t).symm.injective
  rw [AddEquiv.symm_apply_apply, restrictionFiniteHomEquiv_symm_comp,
    AddEquiv.symm_apply_apply]
  exact h

private theorem restrictionFiniteHomEquiv_unit
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj (moduleDerivedStructure E αk))
      (ModuleCat.residueLineSingle R k) (1 - 1)) :
    let O : E.Modules := SheafOfModules.unit E.ringCatSheaf
    let M := (DerivedCategory.Plus.singleFunctor E.Modules 0).obj O
    let U := ModuleCat.restrictScalars (algebraMap R k)
    DerivedCategory.Plus.ι.map
        (moduleRestrictedDerivedStructureUnit E (algebraMap R k) αk αR hα) ≫
      (restrictionFiniteHomEquiv R k hdR E αk αR hα M 1).symm g =
    (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of k k) ≫
      (ModuleCat.residueLineHomEquiv R k hdR
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) 1).symm
          (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E αk) ≫ g) := by
  dsimp only
  let O : E.Modules := SheafOfModules.unit E.ringCatSheaf
  let M := (DerivedCategory.Plus.singleFunctor E.Modules 0).obj O
  let D := moduleDerivedStructureRestrictionIso E (algebraMap R k) αk αR hα
  have hA : (restrictionFiniteHomEquiv R k hdR E αk αR hα M 1).symm g =
      D.hom ≫ (ModuleCat.residueLineHomEquiv R k hdR
        (DerivedCategory.Plus.ι.obj (moduleDerivedStructure E αk)) 1).symm g := by
    erw [restrictionFiniteHomEquiv_symm_apply, ModuleCat.residueLineHomEquivPlus_symm_apply]
    exact (Category.assoc _ _ _).symm
  let U := ModuleCat.restrictScalars (algebraMap R k)
  let a := (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of k k)
  let b := U.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E αk))
  let c := (ModuleCat.residueLineHomEquiv R k hdR
    (DerivedCategory.Plus.ι.obj (moduleDerivedStructure E αk)) 1).symm g
  have hc := restriction_cancel_iso_of_eq D a b c _ _
    (moduleRestrictedDerivedStructureUnit_full E (algebraMap R k) αk αR hα) hA
  have hn := ModuleCat.residueLineHomEquiv_symm_naturality R k hdR
    (DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E αk)) 1 g
  exact hc.trans (congrArg (fun z => a ≫ z) hn.symm)

end FiniteSections

private theorem restriction_tensor_finitePresentation
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (tensorSheaf X M N).IsFinitePresentation := by
  apply QuasiCoherent.affineLocallyFiniteType_finitePresentation
  intro A j _
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let M' := M.restrict j
  let N' := N.restrict j
  have : M'.IsFinitePresentation := finitePresentation_restrict j M
  have : N'.IsFinitePresentation := finitePresentation_restrict j N
  let P := moduleSpecΓFunctor.obj M'
  let Q := moduleSpecΓFunctor.obj N'
  have : Module.Finite A P := finite_globalSections_of_finitePresentation A M'
  have : Module.Finite A Q := finite_globalSections_of_finitePresentation A N'
  let T : ModuleCat.{u} A := ModuleCat.of A (TensorProduct A P Q)
  have : Module.Finite A T := inferInstanceAs (Module.Finite A (TensorProduct A P Q))
  have : (tilde T).IsFinitePresentation := finitePresentation_tilde A T
  let e : tensorSheaf (Spec A) M' N' ≅ tilde T :=
    tensorSheafIso (Spec A) (asIso M'.fromTildeΓ).symm
      (asIso N'.fromTildeΓ).symm ≪≫ tildeTensorIso P Q
  have h : QuasiCoherent.affineFiniteSheaf A (tilde T) :=
    ⟨inferInstance, finite_globalSections_of_finitePresentation A _⟩
  exact (QuasiCoherent.affineFiniteSheaf A).prop_of_iso
    ((tensorRestrictionIso j M N).symm ≪≫ e).symm h

private theorem restriction_quotient_finitePresentation
    {E X : Scheme.{u}} [IsLocallyNoetherian X] (i : E ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules) [M.IsFinitePresentation] :
    (cartierRestrictionQuotient i M).IsFinitePresentation := by
  let L : LineBundle X := ⟨dualSheaf X (idealModule i), dualSheaf_locallyRankOne X _ hI⟩
  let : L.val.IsFinitePresentation := lineBundle_isFinitePresentation X L
  let : (tensorSheaf X L.val M).IsFinitePresentation := restriction_tensor_finitePresentation _ _
  exact finitePresentation_pullback i (tensorSheaf X L.val M)

section SurfaceSerre

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X E : Scheme.{u}} [IsIntegral X]
  (j : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion j]
  [IsDominant (j ≫ toSpec R ι)]
  (hX : Scheme.NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (en : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι j).Finite)
  (i : E ⟶ X) [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i))

/-- Original surface reconstruction retained for the exposed restriction maps. -/
public def restrictionSurfaceReconstruction :
    restrictionSerreObject R ι j n (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) ≅
      (DerivedCategory.singleFunctor X.Modules ((n : ℤ) - 0)).obj
        (normalSurfaceCanonicalModule R ι j n) := by
  simpa only [sub_zero] using
    DerivedCategory.Plus.ι.mapIso (normalSurfaceCanonicalIso R ι j hX hXdim n en hfin) ≪≫
      (DerivedCategory.Plus.singleFunctorιIso X.Modules (n : ℤ)).app
        (normalSurfaceCanonicalModule R ι j n)

/-- Original restrictionSurfaceSerreMap comparison, retained for the exposed restriction maps. -/
public def restrictionSurfaceSerreMap (F : E.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} F (cartierRestrictionQuotient i (normalSurfaceCanonicalModule R ι j n)) r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (i ≫ (j ≫ toSpec R ι))).obj
          ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F)))
        (ModuleCat.residueBaseSingle R) ((r : ℤ) + 1) := by
  let : Mono ((cartierTensorSection i).app (normalSurfaceCanonicalModule R ι j n)) :=
    normalSurfaceCanonical_cartierSection_mono R ι j hX hXdim n en hfin i hI
  exact (restrictionClosedSerreMap R ι j n en
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) (ModuleCat.of R R)
    (restrictionSpecUnitSectionsIso (.of R)) (normalSurfaceCanonicalModule R ι j n)
    0 n (by omega) (restrictionSurfaceReconstruction R ι j hX hXdim n en hfin)
    i F (r + 1)).comp
      (cartierRestrictionExtMap i hI (normalSurfaceCanonicalModule R ι j n) F r)

private theorem restrictionSurfaceSerreMap_bijective
    (F : E.Modules) [F.IsQuasicoherent]
    (hF : QuasiCoherent.affineLocallyFiniteType E F) (r : ℕ) :
    Function.Bijective (restrictionSurfaceSerreMap R ι j hX hXdim n en hfin i hI F r) := by
  let : Finite ι := Finite.of_equiv _ en.symm
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian j
  let ω := normalSurfaceCanonicalModule R ι j n
  let : (ω).IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι j n en n
  let : (ω).IsQuasicoherent := inferInstance
  let : Mono ((cartierTensorSection i).app ω) :=
    normalSurfaceCanonical_cartierSection_mono R ι j hX hXdim n en hfin i hI
  exact (restrictionClosedSerreMap_bijective R ι j n en
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) (ModuleCat.of R R)
    (restrictionSpecUnitSectionsIso (.of R)) ω 0 n (by omega)
    (restrictionSurfaceReconstruction R ι j hX hXdim n en hfin) i F hF (r + 1)).comp
      (cartierRestrictionExtMap_bijective i hI ω F r)

private theorem restrictionSurfaceSerreMap_comp
    {F F' : E.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a)
    (x : Ext.{u + 1} F' (cartierRestrictionQuotient i (normalSurfaceCanonicalModule R ι j n)) b)
    (hab : a + b = r) :
    restrictionSurfaceSerreMap R ι j hX hXdim n en hfin i hI F r (α.comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (i ≫ (j ≫ toSpec R ι)) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionSurfaceSerreMap R ι j hX hXdim n en hfin i hI F' b x) (by omega) := by
  let : Mono ((cartierTensorSection i).app (normalSurfaceCanonicalModule R ι j n)) :=
    normalSurfaceCanonical_cartierSection_mono R ι j hX hXdim n en hfin i hI
  change restrictionClosedSerreMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (cartierRestrictionExtMap i hI _ F r (α.comp x hab)) = _
  rw [cartierRestrictionExtMap_comp]
  erw [restrictionClosedSerreMap_comp]
  rfl

end SurfaceSerre

section CurveSerre

variable (k : Type u) [Field k] (ι : Type u) {E : Scheme.{u}}
  (j : E ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
  (m : ℕ) (em : ι ≃ Fin (m + 1)) (hm : 1 ≤ m)
  (V : ModuleCat.{u} k) [Module.Finite k V] (hV : Module.finrank k V = 1)
  (hCM : ∀ x : E, IsClosed ({x} : Set E) →
    ∃ b ∈ maximalIdeal (E.presheaf.stalk x), IsSMulRegular (E.presheaf.stalk x) b ∧
      (Ideal.span {b}).radical = maximalIdeal (E.presheaf.stalk x))

/-- Original curve reconstruction retained for the exposed restriction maps. -/
public def restrictionCurveReconstruction :
    restrictionSerreObject k ι j m (tilde V) ≅
      (DerivedCategory.singleFunctor E.Modules ((m : ℤ) - 1)).obj
        (cmCurveCoefficientCanonicalModule k ι j m V) :=
  DerivedCategory.Plus.ι.mapIso (cmCurveCoefficientCanonicalIso k ι j m em V hV hCM) ≪≫
    (DerivedCategory.Plus.singleFunctorιIso E.Modules ((m : ℤ) - 1)).app
      (cmCurveCoefficientCanonicalModule k ι j m V)

/-- Original restrictionCurveSerreMap comparison, retained for the exposed restriction maps. -/
public def restrictionCurveSerreMap (F : E.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} F (cmCurveCoefficientCanonicalModule k ι j m V) r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (j ≫ toSpec k ι)).obj
          ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj V) ((r : ℤ) - 1) :=
  restrictionModuleSerreMap k ι j m em (tilde V) V (cmCurveCoefficientSerreSpecSectionsIso k V)
    (cmCurveCoefficientCanonicalModule k ι j m V) 1 (m - 1) (by omega)
    (restrictionCurveReconstruction k ι j m em V hV hCM) F r

private theorem restrictionCurveSerreMap_bijective (F : E.Modules) [F.IsQuasicoherent]
    (hF : QuasiCoherent.affineLocallyFiniteType E F) (r : ℕ) :
    Function.Bijective (restrictionCurveSerreMap k ι j m em hm V hV hCM F r) :=
  restrictionModuleSerreMap_bijective k ι j m em (tilde V) V
    (cmCurveCoefficientSerreSpecSectionsIso k V)
    (cmCurveCoefficientCanonicalModule k ι j m V) 1 (m - 1) (by omega)
    (restrictionCurveReconstruction k ι j m em V hV hCM) F hF r

private theorem restrictionCurveSerreMap_comp
    {F F' : E.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' (cmCurveCoefficientCanonicalModule k ι j m V) b)
    (hab : a + b = r) :
    restrictionCurveSerreMap k ι j m em hm V hV hCM F r (α.comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (j ≫ toSpec k ι) ⋙
        DerivedCategory.Plus.ι)).comp
        (restrictionCurveSerreMap k ι j m em hm V hV hCM F' b x) (by omega) :=
  restrictionModuleSerreMap_comp k ι j m em (tilde V) V (cmCurveCoefficientSerreSpecSectionsIso k V)
    (cmCurveCoefficientCanonicalModule k ι j m V) 1 (m - 1) (by omega)
    (restrictionCurveReconstruction k ι j m em V hV hCM) α x hab

omit [Module.Finite k V] in
/-- The actual affine transport agrees with the coefficient parent's original
module-valued arrow, including its original coefficient isomorphism. -/
private theorem restrictionCurveAffineHom_eq_coefficient
    (F : E.Modules) [F.IsQuasicoherent] (s : ℤ)
    (φ : cmCurveSerreDirectImage k ι j F ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V))⟦s⟧) :
    letI : Finite ι := Finite.of_equiv _ em.symm
    restrictionAffineHomEquiv (j ≫ toSpec k ι) F (tilde V) s φ ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧' =
      cmCurveCoefficientSerreModuleHom k ι j V F s φ := by
  let : Finite ι := Finite.of_equiv _ em.symm
  dsimp only
  let p := j ≫ toSpec k ι
  let O : (Spec (.of k)).Modules := tilde V
  let S := DerivedCategory.Plus.singleFunctor E.Modules 0
  let SY := DerivedCategory.Plus.singleFunctor (Spec (.of k)).Modules 0
  let SM := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} k) 0
  let IY := DerivedCategory.Plus.ι (C := (Spec (.of k)).Modules)
  let IM := DerivedCategory.Plus.ι (C := ModuleCat.{u} k)
  let D := derivedPushforwardPlus p
  let G := moduleGlobalSectionsFunctorOfHom (Spec (.of k)) (ΓSpecIso (.of k)).inv.hom
  let U := moduleSpecΓFunctor (R := .of k)
  let : U.Additive := moduleSpecΓFunctor_additive (.of k)
  let : PreservesFiniteLimits U :=
    preservesFiniteLimits_of_natIso (moduleAffineGlobalSectionsIso (.of k)).symm
  let ρ := (moduleAffineGlobalSectionsIso (.of k)).symm
  let R := G.rightDerivedFunctorPlusIso ρ
  let : R.hom.CommShift ℤ := G.cmCurveRightDerivedPlusIso_commShift U ρ
  let Rfull := Functor.isoWhiskerRight R IM
  let : Rfull.hom.CommShift ℤ := by
    dsimp only [Rfull, Functor.isoWhiskerRight_hom]
    infer_instance
  let A := U.rightDerivedFunctorPlusSingleIsoOfAcyclic O
    (AffineDerived.isZero_rightDerived_globalSections_succ O)
  let Cmp := moduleDerivedGlobalSectionsPushforwardCompIso p (ΓSpecIso (.of k)).inv.hom
  let v : ShiftedHom (D.obj (S.obj F)) (SY.obj O) s :=
    IY.preimage (φ ≫ (IY.commShiftIso s).inv.app (SY.obj O))
  have hnat : IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) =
      v.map (G.rightDerivedFunctorPlus ⋙ IM) ≫
        (IM.map (R.hom.app (SY.obj O)))⟦s⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
      Rfull, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using
      (ShiftedHom.map_naturality v Rfull.hom).symm
  have hcoef₀ : IM.map (R.hom.app (SY.obj O)) ≫ IM.map A.hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
        (cmCurveCoefficientSerreSpecSectionsIso k V).hom =
      IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom := by
    have h := congrArg IM.map (cmCurveCoefficientSerreAffineDerived_coefficient k V)
    erw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hcoef : (IM.map (R.hom.app (SY.obj O)))⟦s⟧' ≫
        (IM.map A.hom)⟦s⟧' ≫
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).map
            (cmCurveCoefficientSerreSpecSectionsIso k V).hom)⟦s⟧' =
      (IM.map (cmCurveCoefficientSerreAffineTargetIso k V).hom)⟦s⟧' := by
    have h := congrArg
      (fun f => (shiftFunctor (DerivedCategory (ModuleCat.{u} k)) s).map f) hcoef₀
    erw [Functor.map_comp, Functor.map_comp] at h
    exact h
  have hSections : (restrictionAffineFullSectionsIso p).hom.app (S.obj F) =
      IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) := by
    change IM.map (Cmp.hom.app (S.obj F) ≫ R.hom.app (D.obj (S.obj F))) ≫ 𝟙 _ = _
    exact (Category.comp_id _).trans (IM.map_comp _ _)
  have hCoefficient : (restrictionAffineFullCoefficientIso O).hom = IM.map A.hom := by
    change IM.map A.hom ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hAffine : restrictionAffineHomEquiv p F O s φ =
      IM.map (Cmp.hom.app (S.obj F)) ≫ IM.map (R.hom.app (D.obj (S.obj F))) ≫
        v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫ (IM.map A.hom)⟦s⟧' := by
    unfold restrictionAffineHomEquiv
    erw [restrictionHomTransportEquiv_apply]
    change (restrictionAffineFullSectionsIso p).hom.app (S.obj F) ≫
      v.map (U.rightDerivedFunctorPlus ⋙ IM) ≫
        (restrictionAffineFullCoefficientIso O).hom⟦s⟧' = _
    rw [hSections, hCoefficient]
    exact Category.assoc _ _ _
  rw [hAffine, cmCurveCoefficientSerreModuleHom_apply]
  exact restriction_paste _ _ _ _ _ _ _ _ hnat hcoef

/-- Reindexing in either order gives the same original coefficient Serre map. -/
private theorem restrictionCurveSerreMap_eq_coefficient
    (F : E.Modules) [F.IsQuasicoherent] (r : ℕ)
    (β : Ext.{u + 1} F (cmCurveCoefficientCanonicalModule k ι j m V) r) :
    restrictionCurveSerreMap k ι j m em hm V hV hCM F r β =
      cmCurveCoefficientSerreModuleHom k ι j V F ((r : ℤ) - 1)
        (cmCurveCoefficientSerreDerivedLinearMap k ι j m em V hV hCM F r hm β) := by
  let : Finite ι := Finite.of_equiv _ em.symm
  let := moduleCategoryLinearOfHom E (cmCurveSerreScalar k ι j)
  let := moduleCategoryLinearOfHom (Spec (.of k)) (ΓSpecIso (.of k)).inv.hom
  have hSerre : restrictionSerreMap k ι j m em (tilde V)
        (cmCurveCoefficientCanonicalModule k ι j m V) 1 (m - 1) (by omega)
        (restrictionCurveReconstruction k ι j m em V hV hCM) F r β =
      cmCurveCoefficientSerreDerivedLinearMap k ι j m em V hV hCM F r hm β := by
    have hRec : restrictionCurveReconstruction k ι j m em V hV hCM =
        cmCurveCoefficientSerreCanonicalIso k ι j m em V hV hCM := by
      unfold restrictionCurveReconstruction cmCurveCoefficientSerreCanonicalIso
      change _ ≪≫ Iso.refl _ = _
      exact Iso.trans_refl _
    let G (q : {q : ℕ // (q : ℤ) - r = (m : ℤ) - 1}) :=
      serreLinearMapOfPurity F (cmCurveCoefficientCanonicalModule k ι j m V)
        (DerivedCategory.Plus.ι.obj (cmCurveCoefficientDualizingObject k ι j m V))
        (cmCurveSerreDirectImage k ι j F) (tilde V) m 1 q.val r q.property
        (cmCurveCoefficientSerreCanonicalIso k ι j m em V hV hCM)
        (relativeClosedEmbeddingSerreLinearMap j (toSpec k ι) k ι (𝟙 _) (𝟙 _)
          (IsPullback.id_horiz (toSpec k ι)) (ΓSpecIso (.of k)).inv.hom
          m em (tilde V) F q.val) β
    have hleft : restrictionSerreMap k ι j m em (tilde V)
        (cmCurveCoefficientCanonicalModule k ι j m V) 1 (m - 1) (by omega)
        (restrictionCurveReconstruction k ι j m em V hV hCM) F r β =
        G ⟨m - 1 + r, by omega⟩ := by
      unfold restrictionSerreMap
      rw [hRec]
      rfl
    rw [hleft]
    change G ⟨m - 1 + r, by omega⟩ = G ⟨r + (m - 1), by omega⟩
    apply congrArg G
    apply Subtype.ext
    exact Nat.add_comm _ _
  unfold restrictionCurveSerreMap
  rw [restrictionModuleSerreMap_apply, hSerre]
  exact restrictionCurveAffineHom_eq_coefficient k ι j m em V F ((r : ℤ) - 1) _

omit [IsClosedImmersion j] [Module.Finite k V] in
/-- Native single preimage evaluation of the module arrow is the very same
coefficient Serre structural-unit evaluator. -/
private theorem restrictionCoefficientModuleTrace_eq_evaluation
    (φ : cmCurveSerreDirectImage k ι j (cmCurveSerreUnit E) ⟶
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj (tilde V))⟦(0 : ℤ)⟧) :
    let S := DerivedCategory.singleFunctor (ModuleCat.{u} k) 0
    let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E (cmCurveSerreScalar k ι j))
    (S.preimage (u ≫ cmCurveCoefficientSerreModuleHom k ι j V (cmCurveSerreUnit E) 0 φ ≫
      (shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).hom.app (S.obj V))) (1 : k) =
      cmCurveCoefficientSerreUnitEvaluationLinearMap k ι j V φ := by
  dsimp only
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} k) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0
  let E₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app
    (ModuleCat.of k k)
  let E₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app V
  let u := DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E (cmCurveSerreScalar k ι j))
  let χ := cmCurveCoefficientSerreModuleHom k ι j V (cmCurveSerreUnit E) 0 φ
  let Z := (shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app (S.obj V)
  have hχ : χ = ShiftedHom.mk₀ (0 : ℤ) rfl (χ ≫ Z.hom) :=
    cmCurveEqMk₀_of_postZero χ (χ ≫ Z.hom) rfl
  have hH : H.shiftMap χ 0 0 (by omega) = H.map (χ ≫ Z.hom) :=
    (congrArg (fun f => H.shiftMap f 0 0 (by omega)) hχ).trans
      (DerivedCategory.cmCurve_homology_shiftMap_mk₀ (χ ≫ Z.hom))
  have hpre : E₀.inv ≫ H.map u ≫ H.shiftMap χ 0 0 (by omega) ≫ E₁.hom =
      S.preimage (u ≫ χ ≫ Z.hom) := by
    rw [hH]
    exact (restriction_map_comp_under H u (χ ≫ Z.hom) E₀.inv E₁.hom).trans
      (DerivedCategory.cmCurveSinglePreimage_homology
        (A := ModuleCat.{u} k) (M := ModuleCat.of k k) (N := V) 0 (u ≫ χ ≫ Z.hom))
  exact (congrArg (fun f : ModuleCat.of k k ⟶ V => f (1 : k)) hpre).symm.trans
    (cmCurveCoefficientSerreModuleHom_unit k ι j V φ)

end CurveSerre

private theorem restriction_inverse_of_ext_zero
    {D : Type*} [Category D] [Abelian D] [HasExt.{u + 1} D] {Q W : D}
    (TQ : Ext.{u + 1} Q Q 0 ≃+ Ext.{u + 1} Q W 0)
    (TW : Ext.{u + 1} W Q 0 ≃+ Ext.{u + 1} W W 0)
    (f : Q ⟶ W) (g : W ⟶ Q)
    (hf : Ext.mk₀ f = TQ (Ext.mk₀ (𝟙 Q)))
    (hg : Ext.mk₀ g = TW.symm (Ext.mk₀ (𝟙 W)))
    (hQ : ∀ (a : Q ⟶ W) (x : Ext.{u + 1} W Q 0),
      TQ ((Ext.mk₀ a).comp x rfl) = (Ext.mk₀ a).comp (TW x) rfl)
    (hW : ∀ (a : W ⟶ Q) (x : Ext.{u + 1} Q Q 0),
      TW ((Ext.mk₀ a).comp x rfl) = (Ext.mk₀ a).comp (TQ x) rfl) :
    f ≫ g = 𝟙 Q ∧ g ≫ f = 𝟙 W := by
  constructor
  · apply Ext.addEquiv₀.symm.injective
    change Ext.mk₀ (f ≫ g) = Ext.mk₀ (𝟙 Q)
    apply TQ.injective
    rw [← Ext.mk₀_comp_mk₀, hQ, hg, AddEquiv.apply_symm_apply, Ext.comp_mk₀_id, hf]
  · apply Ext.addEquiv₀.symm.injective
    change Ext.mk₀ (g ≫ f) = Ext.mk₀ (𝟙 W)
    rw [← Ext.mk₀_comp_mk₀, hf, ← hW, Ext.comp_mk₀_id, hg, AddEquiv.apply_symm_apply]

section OriginalRestriction

variable (R k : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  [Field k] [Algebra R k] [IsLocalHom (algebraMap R k)] [Module.Finite R k]
  (hdR : ringKrullDim R = (2 : ℕ))
  (ιX ιE : Type u) {X E : Scheme.{u}} [IsIntegral X]
  (jX : X ⟶ ProjectiveSpace R ιX) [IsClosedImmersion jX]
  [IsDominant (jX ≫ toSpec R ιX)]
  (hX : Scheme.NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (eX : ιX ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ιX jX).Finite)
  (i : E ⟶ X) [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i))
  (jE : E ⟶ ProjectiveSpace k ιE) [IsClosedImmersion jE]
  (m : ℕ) (eE : ιE ≃ Fin (m + 1)) (hm : 1 ≤ m)
  (hbase : (jE ≫ toSpec k ιE) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
    i ≫ (jX ≫ toSpec R ιX))
  (hclosedDim : ∀ x : E, IsClosed ({x} : Set E) →
    ringKrullDim (X.presheaf.stalk (i x)) = 2)

local notation "ω" => normalSurfaceCanonicalModule R ιX jX n
local notation "Q" => cartierRestrictionQuotient i ω
local notation "V" => ModuleCat.derivedResidueCoefficientLine R k
local notation "Ω" => cmCurveCoefficientCanonicalModule k ιE jE m V
local notation "αR" => RingHom.comp (α := R)
  (CommRingCat.Hom.hom (Scheme.Hom.appTop (i ≫ (jX ≫ toSpec R ιX))))
  (CommRingCat.Hom.hom (CategoryTheory.Iso.inv (ΓSpecIso (CommRingCat.of R))))
local notation "αk" => RingHom.comp (α := k)
  (CommRingCat.Hom.hom (Scheme.Hom.appTop (jE ≫ toSpec k ιE)))
  (CommRingCat.Hom.hom (CategoryTheory.Iso.inv (ΓSpecIso (CommRingCat.of k))))

omit [IsDomain R] [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k]
  [IsIntegral X] [IsClosedImmersion jX] [IsDominant (jX ≫ toSpec R ιX)]
  [IsClosedImmersion i] [IsClosedImmersion jE] in
include hbase in
/-- The actual structural triangle derives the equality of the original scalar maps. -/
public theorem normalSurfaceCartierScalar_compatibility : αR = RingHom.comp αk (algebraMap R k) :=
  chosenEmbeddingBaseScalar_eq_of_triangle R i (jX ≫ toSpec R ιX)
    (algebraMap R k) (jE ≫ toSpec k ιE) hbase.symm

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
include R jX hX eX i hI hclosedDim in
public theorem restrictionOriginalCurveCM : ∀ x : E, IsClosed ({x} : Set E) →
    ∃ b ∈ maximalIdeal (E.presheaf.stalk x), IsSMulRegular (E.presheaf.stalk x) b ∧
      (Ideal.span {b}).radical = maximalIdeal (E.presheaf.stalk x) := by
  let : Finite ιX := Finite.of_equiv _ eX.symm
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian jX
  intro x hx
  exact restriction_closedStalk_parameter i hX hI x (hclosedDim x hx)

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
include eX hI in
/-- Coherence of the actual Cartier quotient follows from the own canonical
homology, the actual invertible ideal and ordinary geometric pullback. -/
public theorem normalSurfaceCartierQuotient_finitePresentation : (Q).IsFinitePresentation := by
  let : Finite ιX := Finite.of_equiv _ eX.symm
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian jX
  let : (ω).IsFinitePresentation := normalSurfaceHomology_finitePresentation R ιX jX n eX n
  exact restriction_quotient_finitePresentation i hI ω

omit [IsDomain R] in
include hdR eE in
/-- Coherence of the curve canonical object uses the intrinsic finite coefficient
line and does not choose an orientation of that line. -/
public theorem normalSurfaceCartierCurveCanonical_finitePresentation :
    (Ω).IsFinitePresentation := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  exact cmCurveCoefficientCanonicalModule_finitePresentation k ιE jE m eE V

/-- The surface functional uses the original positive Cartier row and the own
normal-surface canonical reconstruction. Its target has degree `r+1`. -/
public def normalSurfaceCartierSurfaceSerreMap (F : E.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} F Q r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (i ≫ (jX ≫ toSpec R ιX))).obj
          ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F)))
        (ModuleCat.residueBaseSingle R) ((r : ℤ) + 1) :=
  restrictionSurfaceSerreMap R ιX jX hX hXdim n eX hfin i hI F r

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
/-- The curve functional uses the original coefficient-valued right adjoint,
with its own homology and the un-oriented intrinsic coefficient line. -/
public def normalSurfaceCartierCurveSerreMap (F : E.Modules) [F.IsQuasicoherent] (r : ℕ) :
    Ext.{u + 1} F Ω r →+
      ShiftedHom (DerivedCategory.Plus.ι.obj
        ((restrictionDerivedSections (jE ≫ toSpec k ιE)).obj
          ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F)))
        (ModuleCat.residueLineSingle R k) ((r : ℤ) - 1) := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  exact restrictionCurveSerreMap k ιE jE m eE hm V
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
    (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) F r

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
/-- The transported curve arrow is exactly the coefficient parent's original
Serre arrow followed by its original affine module comparison. -/
public theorem normalSurfaceCartierCurveSerreMap_eq_coefficient
    (F : E.Modules) [F.IsQuasicoherent] (r : ℕ) (β : Ext.{u + 1} F Ω r) :
    letI : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
    normalSurfaceCartierCurveSerreMap R k hdR ιX ιE jX hX n eX i hI
        jE m eE hm hclosedDim F r β =
      cmCurveCoefficientSerreModuleHom k ιE jE V F ((r : ℤ) - 1)
        (cmCurveCoefficientSerreDerivedLinearMap k ιE jE m eE V
          (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
          (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) F r hm β) := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  exact restrictionCurveSerreMap_eq_coefficient k ιE jE m eE hm V
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
    (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) F r β

local notation "S" => normalSurfaceCartierSurfaceSerreMap R ιX jX hX hXdim n eX hfin i hI
local notation "C" => normalSurfaceCartierCurveSerreMap R k hdR ιX ιE jX hX n eX i hI
  jE m eE hm hclosedDim

omit [IsDomain R] [IsIntegral X] [IsClosedImmersion jX]
  [IsDominant (jX ≫ toSpec R ιX)] [IsClosedImmersion i] [IsClosedImmersion jE] in
/-- Original derived scalar restriction along the structural triangle, followed
by the installed finite-local adjunction and its own degree-two residue line. -/
public def normalSurfaceCartierFiniteHomEquiv (M : DerivedCategory.Plus E.Modules) (r : ℤ) :
    ShiftedHom (DerivedCategory.Plus.ι.obj
      ((restrictionDerivedSections (i ≫ (jX ≫ toSpec R ιX))).obj M))
      (ModuleCat.residueBaseSingle R) (r + 1) ≃+
    ShiftedHom (DerivedCategory.Plus.ι.obj
      ((restrictionDerivedSections (jE ≫ toSpec k ιE)).obj M))
      (ModuleCat.residueLineSingle R k) (r - 1) :=
  restrictionFiniteHomEquiv R k hdR E αk αR
    (normalSurfaceCartierScalar_compatibility R k ιX ιE jX i jE hbase) M r

local notation "A" => normalSurfaceCartierFiniteHomEquiv R k hdR ιX ιE jX i jE hbase

omit [IsDomain R] [IsIntegral X] [IsClosedImmersion jX]
  [IsDominant (jX ≫ toSpec R ιX)] [IsClosedImmersion i] [IsClosedImmersion jE] in
private theorem restrictionOriginalFinite_comp
    {M M' : DerivedCategory.Plus E.Modules} {a r t : ℤ}
    (β : ShiftedHom M M' a)
    (f : ShiftedHom (DerivedCategory.Plus.ι.obj
      ((restrictionDerivedSections (i ≫ (jX ≫ toSpec R ιX))).obj M'))
      (ModuleCat.residueBaseSingle R) (r + 1)) (h : r + a = t) :
    A M t ((β.map (restrictionDerivedSections (i ≫ (jX ≫ toSpec R ιX)) ⋙
        DerivedCategory.Plus.ι)).comp f (by omega)) =
      (β.map (restrictionDerivedSections (jE ≫ toSpec k ιE) ⋙ DerivedCategory.Plus.ι)).comp
        (A M' r f) (by omega) :=
  restrictionFiniteHomEquiv_comp R k hdR E αk αR
    (normalSurfaceCartierScalar_compatibility R k ιX ιE jX i jE hbase) β f h

/-- Bijectivity of the original surface Serre map on the actual Cartier quotient. -/
public theorem restrictionOriginalSurface_bijective (F : E.Modules) [F.IsFinitePresentation]
    (r : ℕ) : Function.Bijective (S F r) :=
  restrictionSurfaceSerreMap_bijective R ιX jX hX hXdim n eX hfin i hI F
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation F) r

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
/-- Bijectivity of the original coefficient curve map on the full closed curve. -/
public theorem restrictionOriginalCurve_bijective (F : E.Modules) [F.IsFinitePresentation]
    (r : ℕ) : Function.Bijective (C F r) := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  exact restrictionCurveSerreMap_bijective k ιE jE m eE hm V
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
    (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) F
    (QuasiCoherent.affineLocallyFiniteType_of_finitePresentation F) r

private theorem restrictionOriginalSurface_comp
    {F F' : E.Modules} [F.IsFinitePresentation] [F'.IsFinitePresentation] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' Q b) (hab : a + b = r) :
    S F r (α.comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (i ≫ (jX ≫ toSpec R ιX)) ⋙
        DerivedCategory.Plus.ι)).comp (S F' b x) (by omega) :=
  restrictionSurfaceSerreMap_comp R ιX jX hX hXdim n eX hfin i hI α x hab

omit [IsDomain R] [IsIntegral X] [IsDominant (jX ≫ toSpec R ιX)] in
private theorem restrictionOriginalCurve_comp
    {F F' : E.Modules} [F.IsFinitePresentation] [F'.IsFinitePresentation] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' Ω b) (hab : a + b = r) :
    C F r (α.comp x hab) =
      (α.homPlus.map (restrictionDerivedSections (jE ≫ toSpec k ιE) ⋙
        DerivedCategory.Plus.ι)).comp (C F' b x) (by omega) := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  exact restrictionCurveSerreMap_comp k ιE jE m eE hm V
    (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
    (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) α x hab

/-- The original positive Cartier row, surface Serre map, finite-local
restriction/coinduction adjunction and curve Serre map give this actual Ext
equivalence. Both canonical objects are their original chosen homology. -/
public def normalSurfaceCartierExtEquiv (F : E.Modules) [F.IsFinitePresentation] (r : ℕ) :
    Ext.{u + 1} F Q r ≃+ Ext.{u + 1} F Ω r :=
  (AddEquiv.ofBijective (S F r)
    (restrictionOriginalSurface_bijective R ιX jX hX hXdim n eX hfin i hI F r)).trans
    ((A ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F) (r : ℤ)).trans
      (AddEquiv.ofBijective (C F r)
        (restrictionOriginalCurve_bijective R k hdR ιX ιE jX hX n eX i hI
          jE m eE hm hclosedDim F r)).symm)

local notation "T" => normalSurfaceCartierExtEquiv R k hdR ιX ιE jX hX hXdim n eX hfin
  i hI jE m eE hm hbase hclosedDim

/-- The comparison is normalized by the same original two Serre maps and the
native finite-local coinduction counit; this identity defines no extra premise. -/
public theorem normalSurfaceCartierExtEquiv_serre
    (F : E.Modules) [F.IsFinitePresentation] (r : ℕ) (x : Ext.{u + 1} F Q r) :
    C F r (T F r x) =
      A ((DerivedCategory.Plus.singleFunctor E.Modules 0).obj F) (r : ℤ) (S F r x) := by
  exact (AddEquiv.ofBijective (C F r)
    (restrictionOriginalCurve_bijective R k hdR ιX ιE jX hX n eX i hI
      jE m eE hm hclosedDim F r)).apply_symm_apply _

/-- Arbitrary source Yoneda composition is retained, with the actual native
actions on both Ext groups. -/
public theorem normalSurfaceCartierExtEquiv_comp
    {F F' : E.Modules} [F.IsFinitePresentation] [F'.IsFinitePresentation] {a b r : ℕ}
    (α : Ext.{u + 1} F F' a) (x : Ext.{u + 1} F' Q b) (hab : a + b = r) :
    T F r (α.comp x hab) = α.comp (T F' b x) hab := by
  apply (restrictionOriginalCurve_bijective R k hdR ιX ιE jX hX n eX i hI
    jE m eE hm hclosedDim F r).injective
  rw [normalSurfaceCartierExtEquiv_serre R k hdR ιX ιE jX hX hXdim n eX hfin
    i hI jE m eE hm hbase hclosedDim F r,
    restrictionOriginalSurface_comp (R := R) (ιX := ιX) (jX := jX)
      (hX := hX) (hXdim := hXdim) (n := n) (eX := eX) (hfin := hfin)
      (i := i) (hI := hI) (m := m) (α := α) (x := x) hab,
    restrictionOriginalFinite_comp (R := R) (k := k) (hdR := hdR)
      (ιX := ιX) (ιE := ιE) (jX := jX) (i := i) (jE := jE) (m := m)
      (hbase := hbase) α.homPlus (S F' b x) (by omega),
    restrictionOriginalCurve_comp R k hdR ιX ιE jX hX n eX i hI
      jE m eE hm hclosedDim α (T F' b x) hab,
    normalSurfaceCartierExtEquiv_serre R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim F' b]

/-- Original degree-zero precomposition, as an opaque proof input to canonical Yoneda. -/
public theorem normalSurfaceCartierExtEquiv_precomp_zero
    (F F' : E.Modules) [F.IsFinitePresentation] [F'.IsFinitePresentation] :
    ∀ (f : F ⟶ F') (x : Ext.{u + 1} F' Q 0),
      T F 0 ((Ext.mk₀ («C» := E.Modules) f).comp x rfl) =
        (Ext.mk₀ («C» := E.Modules) f).comp (T F' 0 x) rfl := by
  intro f x
  exact normalSurfaceCartierExtEquiv_comp R k hdR ιX ιE jX hX hXdim n eX hfin
    i hI jE m eE hm hbase hclosedDim (F := F) (F' := F')
    (a := 0) (b := 0) (r := 0) (Ext.mk₀ («C» := E.Modules) f) x rfl

/-- The original forward Yoneda map, evaluated by the native Ext-zero inverse. -/
public def normalSurfaceCartierQuotientHom : Q ⟶ Ω := by
  let : (Q).IsFinitePresentation :=
    normalSurfaceCartierQuotient_finitePresentation R ιX jX n eX i hI
  exact Ext.addEquiv₀ (T Q 0 (Ext.mk₀ («C» := E.Modules) (𝟙 Q)))

/-- The original inverse Yoneda map from the inverse of the same Ext equivalence. -/
public def normalSurfaceCartierQuotientInv : Ω ⟶ Q := by
  let : (Ω).IsFinitePresentation :=
    normalSurfaceCartierCurveCanonical_finitePresentation R k hdR ιE jE m eE
  exact Ext.addEquiv₀ ((T Ω 0).symm (Ext.mk₀ («C» := E.Modules) (𝟙 Ω)))

local notation "θhom" => normalSurfaceCartierQuotientHom R k hdR ιX ιE jX hX hXdim n eX hfin
  i hI jE m eE hm hbase hclosedDim
local notation "θinv" => normalSurfaceCartierQuotientInv R k hdR ιX ιE jX hX hXdim n eX hfin
  i hI jE m eE hm hbase hclosedDim

private theorem restrictionQuotientHom_mk₀ :
    letI : (Q).IsFinitePresentation :=
      normalSurfaceCartierQuotient_finitePresentation R ιX jX n eX i hI
    Ext.mk₀ («C» := E.Modules) θhom = T Q 0 (Ext.mk₀ (𝟙 Q)) := by
  exact Ext.mk₀_addEquiv₀_apply _

private theorem restrictionQuotientInv_mk₀ :
    letI : (Ω).IsFinitePresentation :=
      normalSurfaceCartierCurveCanonical_finitePresentation R k hdR ιE jE m eE
    Ext.mk₀ («C» := E.Modules) θinv = (T Ω 0).symm (Ext.mk₀ (𝟙 Ω)) := by
  exact Ext.mk₀_addEquiv₀_apply _

/-- Both inverse laws are proved for the same original forward and inverse maps. -/
public theorem normalSurfaceCartierQuotient_inverse :
    θhom ≫ θinv = 𝟙 Q ∧ θinv ≫ θhom = 𝟙 Ω := by
  let : (Q).IsFinitePresentation :=
    normalSurfaceCartierQuotient_finitePresentation R ιX jX n eX i hI
  let : (Ω).IsFinitePresentation :=
    normalSurfaceCartierCurveCanonical_finitePresentation R k hdR ιE jE m eE
  exact restriction_inverse_of_ext_zero (D := E.Modules) («Q» := Q) (W := Ω)
    (T Q 0) (T Ω 0) θhom θinv
    (restrictionQuotientHom_mk₀ R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim)
    (restrictionQuotientInv_mk₀ R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim)
    (normalSurfaceCartierExtEquiv_precomp_zero R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim Q Ω)
    (normalSurfaceCartierExtEquiv_precomp_zero R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim Ω Q)

/-- The canonical quotient isomorphism consists of the original two Yoneda
maps and their proved inverse laws; no isomorphism is chosen independently. -/
public def normalSurfaceCartierQuotientIso : Q ≅ Ω :=
  ⟨θhom, θinv, (normalSurfaceCartierQuotient_inverse R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim).1,
    (normalSurfaceCartierQuotient_inverse R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim).2⟩

local notation "θ" => normalSurfaceCartierQuotientIso R k hdR ιX ιE jX hX hXdim n eX hfin
  i hI jE m eE hm hbase hclosedDim

private theorem restrictionQuotientIso_hom :
    letI : (Q).IsFinitePresentation :=
      normalSurfaceCartierQuotient_finitePresentation R ιX jX n eX i hI
    Ext.mk₀ (θ).hom = T Q 0 (Ext.mk₀ (𝟙 Q)) := by
  exact restrictionQuotientHom_mk₀ R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim

/-- The whole Ext comparison is postcomposition by this SAME canonical
isomorphism, rather than a separately chosen degree-zero isomorphism. -/
public theorem normalSurfaceCartierExtEquiv_eq_comp
    (F : E.Modules) [F.IsFinitePresentation] (r : ℕ) (x : Ext.{u + 1} F Q r) :
    T F r x = x.comp (Ext.mk₀ (θ).hom) (Nat.add_zero r) := by
  let : (Q).IsFinitePresentation :=
    normalSurfaceCartierQuotient_finitePresentation R ιX jX n eX i hI
  rw [restrictionQuotientIso_hom]
  simpa only [Ext.comp_mk₀_id] using
    normalSurfaceCartierExtEquiv_comp R k hdR ιX ιE jX hX hXdim n eX hfin
      i hI jE m eE hm hbase hclosedDim x (Ext.mk₀ (𝟙 Q)) (Nat.add_zero r)

/-- Evaluate the original curve Serre functional on the original structural
field unit. The target is the literal intrinsic coefficient line in degree zero. -/
public def normalSurfaceCartierCurveUnitPairing
    (β : Ext.{u + 1} («C» := E.Modules) (SheafOfModules.unit E.ringCatSheaf) Q 1) :
    ShiftedHom ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))
      (ModuleCat.residueLineSingle R k) ((1 : ℤ) - 1) :=
  DerivedCategory.Plus.ι.map (moduleDerivedStructureUnit E αk) ≫
    C (SheafOfModules.unit E.ringCatSheaf) 1 (β.comp (Ext.mk₀ (θ).hom) (Nat.add_zero 1))

local notation "P" => normalSurfaceCartierCurveUnitPairing R k hdR ιX ιE jX hX hXdim
  n eX hfin i hI jE m eE hm hbase hclosedDim

set_option backward.isDefEq.respectTransparency false in
/-- The same Yoneda isomorphism retains the original restricted field unit and
the installed finite-local coinduction adjunction. The field unit is not replaced
by its precomposition with the regular-base unit. -/
public theorem normalSurfaceCartierUnitTrace
    (β : Ext.{u + 1} («C» := E.Modules) (SheafOfModules.unit E.ringCatSheaf) Q 1) :
    let U := ModuleCat.restrictScalars (algebraMap R k)
    DerivedCategory.Plus.ι.map
        (moduleRestrictedDerivedStructureUnit E (algebraMap R k) αk αR
          (normalSurfaceCartierScalar_compatibility R k ιX ιE jX i jE hbase)) ≫
      S (SheafOfModules.unit E.ringCatSheaf) 1 β =
    (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of k k) ≫
      (ModuleCat.residueLineHomEquiv R k hdR
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) 1).symm
          (P β) := by
  dsimp only
  let O : E.Modules := SheafOfModules.unit E.ringCatSheaf
  let M := (DerivedCategory.Plus.singleFunctor E.Modules 0).obj O
  let g : ShiftedHom (DerivedCategory.Plus.ι.obj (moduleDerivedStructure E αk))
      (ModuleCat.residueLineSingle R k) ((1 : ℤ) - 1) :=
    C O 1 (β.comp (Ext.mk₀ (θ).hom) (Nat.add_zero 1))
  have hs : S O 1 β = (A M 1).symm g := by
    dsimp only [g]
    rw [← normalSurfaceCartierExtEquiv_eq_comp R k hdR ιX ιE jX hX hXdim n eX hfin
        i hI jE m eE hm hbase hclosedDim O 1 β,
      normalSurfaceCartierExtEquiv_serre R k hdR ιX ιE jX hX hXdim n eX hfin
        i hI jE m eE hm hbase hclosedDim O 1 β]
    exact ((A M 1).symm_apply_apply (S O 1 β)).symm
  rw [hs]
  dsimp only [normalSurfaceCartierFiniteHomEquiv, normalSurfaceCartierCurveUnitPairing]
  have hu := restrictionFiniteHomEquiv_unit R k hdR E αk αR
    (normalSurfaceCartierScalar_compatibility R k ιX ιE jX i jE hbase) g
  conv_rhs => rw [← show g = C O 1 (β.comp (Ext.mk₀ (θ).hom) (Nat.add_zero 1)) from rfl]
  dsimp only at hu
  exact hu

/-- The original finite-local counit gives the trace normalization explicitly;
the retained degree-two residue trace is its own-homology-normalized form. -/
public theorem normalSurfaceCartierUnitTrace_counit
    (β : Ext.{u + 1} («C» := E.Modules) (SheafOfModules.unit E.ringCatSheaf) Q 1) :
    let U := ModuleCat.restrictScalars (algebraMap R k)
    DerivedCategory.Plus.ι.map
        (moduleRestrictedDerivedStructureUnit E (algebraMap R k) αk αR
          (normalSurfaceCartierScalar_compatibility R k ιX ιE jX i jE hbase)) ≫
      S (SheafOfModules.unit E.ringCatSheaf) 1 β =
    (U.mapDerivedCategorySingleFunctor 0).inv.app (ModuleCat.of k k) ≫
      ((P β).map (ModuleCat.residueDerivedRestriction R k)).comp
        (ModuleCat.residueLineTrace R k hdR) (by omega) := by
  rw [normalSurfaceCartierUnitTrace, ModuleCat.residueLineHomEquiv_symm_eq_trace]

/-- The intrinsic coefficient-valued trace is evaluation at one after the native
single functor and the original zero-shift comparison. No `V ≅ k` is chosen. -/
public def normalSurfaceCartierCurveTrace
    (β : Ext.{u + 1} («C» := E.Modules) (SheafOfModules.unit E.ringCatSheaf) Q 1) : V :=
  ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).preimage
    (P β ≫ (shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).hom.app
      (ModuleCat.residueLineSingle R k))) (1 : k)

set_option backward.isDefEq.respectTransparency false in
/-- The Cartier trace equals the coefficient parent's original trace after
the same quotient isomorphism and the original Ext/cohomology map. -/
public theorem normalSurfaceCartierCurveTrace_eq_coefficient
    (β : Ext.{u + 1} («C» := E.Modules) (SheafOfModules.unit E.ringCatSheaf) Q 1) :
    letI : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
    normalSurfaceCartierCurveTrace R k hdR ιX ιE jX hX hXdim n eX hfin
        i hI jE m eE hm hbase hclosedDim β =
      cmCurveCoefficientSerreTrace k ιE jE m eE V
        (ModuleCat.derivedResidueCoefficientLine_finrank R k hdR)
        (restrictionOriginalCurveCM R ιX jX hX n eX i hI hclosedDim) hm
          (moduleExtCohomologyMap E Ω 1 (β.comp (Ext.mk₀ (θ).hom) (Nat.add_zero 1))) := by
  let : Module.Finite k V := ModuleCat.derivedResidueCoefficientLine_finite R k hdR
  rw [cmCurveCoefficientSerreTrace_apply_ext]
  unfold normalSurfaceCartierCurveTrace normalSurfaceCartierCurveUnitPairing
  rw [normalSurfaceCartierCurveSerreMap_eq_coefficient R k hdR ιX ιE jX hX n eX i hI
    jE m eE hm hclosedDim (cmCurveSerreUnit E) 1]
  rw [Category.assoc]
  exact restrictionCoefficientModuleTrace_eq_evaluation k ιE jE V _

/-- The original Cartier ideal occurs with the positive twist. The cancellation
and pullback tensor maps are the installed actual maps. -/
public def normalSurfaceCartierRestrictionIso :
    (Scheme.Modules.pullback i).obj ω ≅
      tensorSheaf E Ω ((Scheme.Modules.pullback i).obj (idealModule i)) := by
  let N := tensorSheaf X (dualSheaf X (idealModule i)) ω
  let : IsIso (pullbackTensorMap i N (idealModule i)) :=
    Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso i N (idealModule i)
  exact (Scheme.Modules.pullback i).mapIso (cartierCoefficientCancellationIso i hI ω).symm ≪≫
    asIso (pullbackTensorMap i N (idealModule i)) ≪≫
      tensorSheafIso E θ (Iso.refl ((Scheme.Modules.pullback i).obj (idealModule i)))

end OriginalRestriction

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

open AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
  restrictionModuleDerived restrictionUnit_finitePresentation

variable (R A : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Algebra R A] [Module.Finite R A] [IsLocalHom (algebraMap R A)]
  (hdR : ringKrullDim R = (2 : ℕ)) (hdA : ringKrullDim A = 2)
  (hNagata : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
  (ιX : Type u) (jX : source A hdA ⟶ ProjectiveSpace R ιX) [IsClosedImmersion jX]
  [IsDominant (jX ≫ toSpec R ιX)]
  (n : ℕ) (eX : ιX ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ιX jX).Finite)
  (hjX : jX ≫ toSpec R ιX = map A hdA ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The native quotient residue-field operations. -/
local instance restrictionResidueField : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
  Ideal.Quotient.field _

local notation "κ" => A ⧸ IsLocalRing.maximalIdeal A

/-- Canonical restriction on the literal full exceptional curve. Its normality,
ambient dimension, Cartier ideal and closed-stalk dimensions are supplied by
the original rational-blowup producers, not new canonical-module hypotheses. -/
public def exceptionalCanonicalRestrictionIso
    (ιE : Type u) (jE : exceptionalCurve A hdA ⟶ ProjectiveSpace κ ιE)
    [IsClosedImmersion jE] (m : ℕ) (eE : ιE ≃ Fin (m + 1)) (hm : 1 ≤ m)
    (hjE : jE ≫ toSpec κ ιE = exceptionalStructureMap A hdA) :
    (Modules.pullback (exceptionalCurveInclusion A hdA)).obj
      (normalSurfaceCanonicalModule R ιX jX n) ≅
    tensorSheaf (exceptionalCurve A hdA)
      (cmCurveCoefficientCanonicalModule κ ιE jE m
        (ModuleCat.derivedResidueCoefficientLine R κ)) (exceptionalLine A hdA).val := by
  let : Module.Finite R κ := Module.Finite.trans A κ
  let : IsLocalHom (algebraMap A κ) :=
    IsLocalHom.of_surjective (algebraMap A κ) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R κ) := by
    rw [IsScalarTower.algebraMap_eq R A κ]
    infer_instance
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap R κ)) =
      residueSpectrumInclusion A ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [IsScalarTower.algebraMap_eq R A κ]
    change Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) = _
    exact Spec.map_comp _ _
  have hbase : (jE ≫ toSpec κ ιE) ≫ Spec.map (CommRingCat.ofHom (algebraMap R κ)) =
      exceptionalCurveInclusion A hdA ≫ (jX ≫ toSpec R ιX) := by
    rw [hjE, hρ, ← Category.assoc, exceptionalStructureMap_triangle, Category.assoc, ← hjX]
  exact normalSurfaceCartierRestrictionIso R κ hdR ιX ιE jX
    (ordinary_normalStalks A hdA hNagata hRat)
    (ordinary_dimension_le_two A hdA hNagata hRat) n eX hfin
    (exceptionalCurveInclusion A hdA) (datum A).cartier jE m eE hm hbase
    (exceptionalCurve_closedPoint_stalk_dimension A hdA hNagata hRat)

include hdR hNagata hRat eX hfin hjX in
/-- The actual padded tautological row supplies a matched curve embedding of
positive ambient dimension and positive `O(1)`, together with the same original
canonical restriction. The exceptional scheme is never reduced. -/
public theorem exists_exceptionalCanonicalRestriction :
    ∃ (m : ℕ) (jE : exceptionalCurve A hdA ⟶ ProjectiveSpace κ (ULift.{u} (Fin (m + 1)))),
      ∃ hjE : IsClosedImmersion jE, letI := hjE
      1 ≤ m ∧
        jE ≫ toSpec κ (ULift.{u} (Fin (m + 1))) = exceptionalStructureMap A hdA ∧
        Nonempty ((Modules.pullback jE).obj
          (ProjectiveSpace.twistingSheaf κ (ULift.{u} (Fin (m + 1))) 1) ≅
            (exceptionalLine A hdA).val) ∧
        Nonempty ((Modules.pullback (exceptionalCurveInclusion A hdA)).obj
          (normalSurfaceCanonicalModule R ιX jX n) ≅
          tensorSheaf (exceptionalCurve A hdA)
            (cmCurveCoefficientCanonicalModule κ (ULift.{u} (Fin (m + 1))) jE m
              (ModuleCat.derivedResidueCoefficientLine R κ)) (exceptionalLine A hdA).val) := by
  obtain ⟨m, jE, hm, hjE, hstruct, hL⟩ := exists_exceptionalTautologicalEmbedding A hdA
  let : IsClosedImmersion jE := hjE
  refine ⟨m, jE, hjE, hm, hstruct, hL, ?_⟩
  exact ⟨exceptionalCanonicalRestrictionIso R A hdR hdA hNagata hRat ιX jX n eX hfin hjX
    (ULift.{u} (Fin (m + 1))) jE m Equiv.ulift hm hstruct⟩

end AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup
