/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.ClosedFibreExtensions
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.Mixed
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.Algebra.Homology.ModuleCat.IdealPresentation
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward.Spec
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Functor
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.Thickening
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.ExtensionGraph.Construction

/-!
# The original residue-field obstruction for a normal surface

For a proper birational map from an integral normal scheme to a normal
Noetherian Nagata local surface, the actual closed-fibre quotient has
vanishing degree-one Ext into the structure module. The original quotient
restricts to zero on the punctured inverse image. The original Ext/H1
comparison and punctured H1 injectivity construct a lift of that quotient,
and the scalar correction splits the same original extension.

The finite three-term presentation and the original tilde/pullback
adjunction then identify the needed residue-Hom calculation. The actual
negative homology is annihilated by an original nonzero base scalar, and
the canonical truncation triangle reduces to the split extension class.
The final target is the original right-derived structural global sections.
This is Stacks Project, Lemma 54.7.6, tag 0AXC.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The original maximal-ideal quotient vanishes on the actual punctured inverse image. -/
theorem closedFibreQuotient_restrict_isZero :
    IsZero ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ localPuncturedSpectrum A).ι).obj
      (idealQuotient X (idealThickeningBaseScalar f)
        (SheafOfModules.unit X.ringCatSheaf) (IsLocalRing.maximalIdeal A))) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsQuasicoherent := isQuasicoherent_unit X
  let m := IsLocalRing.maximalIdeal A
  let Q := idealQuotient X (idealThickeningBaseScalar f) O m
  let V := f ⁻¹ᵁ localPuncturedSpectrum A
  let i := idealThickeningι f m
  let N := idealThickeningCoefficient f O m
  have hi (x : V) : (x : X) ∉ Set.range i := by
    rintro ⟨z, hz⟩
    have hc := congrArg (fun k : idealThickeningSpace f m ⟶ Spec (.of A) => k z)
      (Limits.pullback.condition (f := f)
        (g := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m))))
    change f (i z) =
      PrimeSpectrum.comap (Ideal.Quotient.mk m) (idealThickeningStructure f m z) at hc
    have hp : f (i z) = IsLocalRing.closedPoint A :=
      hc.trans (IsLocalRing.PrimeSpectrum.comap_residue A _)
    exact x.property (hz ▸ hp)
  apply (isZero_iff_stalks _).mpr
  intro x
  have hP : IsZero ((moduleStalk X (V.ι x)).obj ((Scheme.Modules.pushforward i).obj N)) :=
    isZero_closedImmersion_moduleStalk_of_not_mem i (V.ι x) (hi x) N
  have hQ : IsZero ((moduleStalk X (V.ι x)).obj Q) :=
    hP.of_iso ((moduleStalk X (V.ι x)).mapIso (idealQuotientThickeningIso f O m))
  have hA := (forget₂ (ModuleCat (X.presheaf.stalk (V.ι x))) AddCommGrpCat.{u}).map_isZero hQ
  have hS : IsZero ((stalkFunctor X (V.ι x)).obj Q) :=
    hA.of_iso ((moduleStalkForgetIso X (V.ι x)).app Q).symm
  exact hS.of_iso ((restrictStalkNatIso V.ι x).app Q)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

local instance (X : Scheme.{u}) : HasExt.{u + 1} X.Modules := HasExt.standard _

variable {X : Scheme.{u}}

/-- Injectivity of the original structural H1 restriction detects an original
degree-one structure-module Ext class after exact open restriction. -/
private theorem structureExt_one_eq_zero_of_restrict
    (U : X.Opens)
    (hinj : Function.Injective (moduleCohomologyMapAlong U.ι
      (Scheme.Hom.structureModuleMap U.ι) 1))
    (xi : Ext.{u + 1} (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1)
    (hxi : xi.mapExactFunctor (Scheme.Modules.restrictFunctor U.ι) = 0) : xi = 0 := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e := restrictUnitIso U.ι
  let unit := (Scheme.Modules.restrictAdjunction U.ι).unit.app O
  have hunit : unit ≫ (Scheme.Modules.pushforward U.ι).map e.hom =
      Scheme.Hom.structureModuleMap U.ι := by
    have h := (Scheme.Modules.restrictAdjunction U.ι).homEquiv_unit O
      (SheafOfModules.unit U.toScheme.ringCatSheaf) e.hom
    exact h.symm.trans (restrictUnitIso_hom_adjoint U.ι)
  have hR : moduleCohomologyMapAlong U.ι unit 1
      (moduleExtCohomologyMap X O 1 xi) = 0 := by
    have h := moduleExtCohomologyMap_restrict U.ι O 1 xi
    rw [hxi, Ext.comp_zero, map_zero] at h
    exact h
  apply (moduleExtCohomologyMap_bijective X O 1).injective
  rw [map_zero]
  apply hinj
  rw [map_zero]
  have h := moduleCohomologyMapAlong_postcomp U.ι unit e.hom 1
    (moduleExtCohomologyMap X O 1 xi)
  rw [hunit, hR, map_zero] at h
  exact h

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsNoetherianRing A] [IsIntegrallyClosed A] [IsIntegral X]
  (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
  (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
  (hdim : ringKrullDim A = 2) (hX : Scheme.NormalStalks X)
  (hA : IsNagataRing.{u, 0} A)

local notation "O" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)
local notation "α" => idealThickeningBaseScalar f
local notation "Q" => idealQuotient X α O (IsLocalRing.maximalIdeal A)
local notation "q" => idealQuotientπ X α O (IsLocalRing.maximalIdeal A)

include hff hdim hX hA

/-- Punctured H1 injectivity constructs a lift of the original closed-fibre
quotient into every actual extension, with the literal quotient equation. -/
theorem closedFibreExtension_quotient_lift_of_isNagata (E : Ext1.Extension Q O) :
    ∃ s : O ⟶ E.middle, s ≫ E.p = q := by
  let V := f ⁻¹ᵁ localPuncturedSpectrum A
  let xi : Ext.{u + 1} O O 1 := (Ext.mk₀ q).comp E.extClass (Nat.zero_add 1)
  have hQ := closedFibreQuotient_restrict_isZero f
  have hq : (Scheme.Modules.restrictFunctor V.ι).map q = 0 := hQ.eq_of_tgt _ _
  have hxi : xi.mapExactFunctor (Scheme.Modules.restrictFunctor V.ι) = 0 := by
    simp only [xi, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      hq, Ext.mk₀_zero, Ext.zero_comp]
  have hz : xi = 0 := structureExt_one_eq_zero_of_restrict V
    (structureH1_puncturedRestriction_injective_of_isNagata f hff hdim hX hA) xi hxi
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ O E.shortExact
    (Ext.mk₀ q) (show 0 + 1 = 1 from rfl) hz
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective O E.middle).surjective x
  refine ⟨s, (Ext.mk₀_bijective O Q).injective ?_⟩
  simpa only [Ext.mk₀_comp_mk₀] using hx

/-- The original closed-fibre extension splits using the actual H1-produced
lift and the already constructed original scalar correction. -/
theorem closedFibreExtension_section_of_isNagata (E : Ext1.Extension Q O) :
    ∃ r : Q ⟶ E.middle, r ≫ E.p = 𝟙 Q := by
  obtain ⟨s, hs⟩ := closedFibreExtension_quotient_lift_of_isNagata f hff hdim hX hA E
  have hbase : NormalStalks (Spec (.of A)) :=
    fun y => (isIntegrallyClosed_and_isDomain_stalk_Spec A y).symm
  exact closedFibreExtension_section_of_proper_birational_lift X f hbase hff
    hdim.ge E s hs

/-- Every original degree-one class of the actual closed-fibre quotient into
the structure module is zero over a normal Nagata local surface. -/
theorem closedFibreExt_one_eq_zero_of_isNagata (xi : Ext.{u + 1} Q O 1) : xi = 0 := by
  obtain ⟨E, hE⟩ := Ext1.exists_extension xi
  obtain ⟨r, hr⟩ := closedFibreExtension_section_of_isNagata f hff hdim hX hA E
  have hs : Nonempty E.toShortComplex.Splitting :=
    ⟨ShortComplex.Splitting.ofExactOfSection E.toShortComplex E.shortExact.exact
      r hr E.shortExact.mono_f⟩
  have hz : E.extClass = 0 :=
    (ShortComplex.ShortExact.extClass_eq_zero_iff_splitting E.shortExact).mpr hs
  exact hE.symm.trans hz

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem structureScalar_mono {X : Scheme.{u}} [IsIntegral X]
    (a : Γ(X, ⊤)) (ha : a ≠ 0) :
    Mono (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a) := by
  constructor
  intro M g h hgh
  apply Scheme.Modules.hom_ext
  intro U
  by_cases hU : Nonempty U
  · let := hU
    have hres : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a ≠ 0 := by
      intro hz
      apply ha
      apply map_injective_of_isIntegral X (homOfLE (le_top : U ≤ ⊤))
      simpa only [map_zero] using hz
    ext s
    have he := congrArg (fun k => k.val.app (Opposite.op U) s) hgh
    change (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val.app
        (Opposite.op U) (g.val.app (Opposite.op U) s) =
      (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val.app
        (Opposite.op U) (h.val.app (Opposite.op U) s) at he
    simp only [globalScalarEndomorphism_app] at he
    let gs : Γ(X, U) := g.val.app (Opposite.op U) s
    let hs : Γ(X, U) := h.val.app (Opposite.op U) s
    change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a * gs =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a * hs at he
    change gs = hs
    exact mul_left_cancel₀ hres he
  · have hbot : U = ⊥ := by
      apply bot_unique
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    let : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    ext s
    exact Subsingleton.elim (show Γ(X, U) from g.val.app (Opposite.op U) s)
      (show Γ(X, U) from h.val.app (Opposite.op U) s)

section LowTruncation

universe v w t

variable {C : Type v} [Category.{w} C] [Abelian C]
  [HasDerivedCategory.{t} C]

private theorem lowerTruncation_homology_mono (Z : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C (-1)).map
      ((DerivedCategory.TStructure.t.truncLTι 0).app Z)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE 0).obj Z
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished 0 Z
  have h₀ := DerivedCategory.isZero_of_isGE T.obj₃ 0 (-1) (by norm_num)
  have hprev := DerivedCategory.isZero_of_isGE T.obj₃ 0 (-2) (by norm_num)
  change IsIso (((DerivedCategory.homologyFunctor C 0).shift (-1)).map T.mor₁)
  let : Epi (((DerivedCategory.homologyFunctor C 0).shift (-1)).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff
      T hT (-1)).mpr (h₀.eq_of_tgt _ _)
  let : Mono (((DerivedCategory.homologyFunctor C 0).shift (-1)).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (-2) (-1) (by norm_num)).mpr (hprev.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

variable [HasExt.{t} C]

/-- The canonical truncation triangle reduces this particular Hom group to
the original Ext1 class once the actual negative homology has no maps to
the coefficient. No higher negative homology vanishing is assumed. -/
private theorem hom_to_single_shift_eq_zero (Z : DerivedCategory C) [Z.IsLE 0] (N : C)
    (hneg : ∀ a : (DerivedCategory.homologyFunctor C (-1)).obj Z ⟶ N, a = 0)
    (hext : ∀ xi : Ext.{t} ((DerivedCategory.homologyFunctor C 0).obj Z) N 1, xi = 0)
    (φ : Z ⟶ ((DerivedCategory.singleFunctor C 0).obj N)⟦(1 : ℤ)⟧) : φ = 0 := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE 0).obj Z
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished 0 Z
  let : T.obj₁.IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj Z 0 (-1) (by norm_num)
  let : IsIso ((DerivedCategory.homologyFunctor C (-1)).map T.mor₁) := by
    change IsIso ((DerivedCategory.homologyFunctor C (-1)).map
      ((DerivedCategory.TStructure.t.truncLTι 0).app Z))
    exact lowerTruncation_homology_mono Z
  let eNeg := asIso ((DerivedCategory.homologyFunctor C (-1)).map T.mor₁)
  have hlow (a : (DerivedCategory.homologyFunctor C (-1)).obj T.obj₁ ⟶ N) : a = 0 := by
    apply (cancel_epi eNeg.inv).mp
    simpa only [comp_zero] using hneg (eNeg.inv ≫ a)
  let es := ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app N
  have hιφ : T.mor₁ ≫ φ = 0 := by
    apply (cancel_mono es.hom).mp
    rw [zero_comp]
    apply (DerivedCategory.homToSingleAddEquiv T.obj₁ (-1) N).injective
    rw [map_zero]
    exact hlow _
  obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT φ hιφ
  let : T.obj₃.IsGE 0 := by
    change ((DerivedCategory.TStructure.t.truncGE 0).obj Z).IsGE 0
    infer_instance
  let : T.obj₃.IsLE 0 := by
    change ((DerivedCategory.TStructure.t.truncGE 0).obj Z).IsLE 0
    infer_instance
  let : IsIso ((DerivedCategory.homologyFunctor C 0).map T.mor₂) := by
    change IsIso ((DerivedCategory.homologyFunctor C 0).map
      ((DerivedCategory.TStructure.t.truncGEπ 0).app Z))
    exact DerivedCategory.isIso_homology_truncGEπ Z 0 0 (le_refl 0)
  let e₀ : T.obj₃ ≅ (DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C 0).obj Z) :=
    DerivedCategory.isoSingleHomology T.obj₃ 0 ≪≫
    (DerivedCategory.singleFunctor C 0).mapIso
      (asIso ((DerivedCategory.homologyFunctor C 0).map T.mor₂)).symm
  have hg₀ : e₀.inv ≫ g = 0 := by
    let xi : Ext.{t} ((DerivedCategory.homologyFunctor C 0).obj Z) N 1 :=
      Ext.homEquiv.symm (e₀.inv ≫ g)
    calc
      e₀.inv ≫ g = xi.hom := (Ext.homEquiv.apply_symm_apply _).symm
      _ = 0 := by rw [hext xi, Ext.zero_hom]
  have hgzero : g = 0 := (cancel_epi e₀.inv).mp (by simpa only [comp_zero] using hg₀)
  rw [hg, hgzero, comp_zero]

end LowTruncation

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A))

/-- The actual affine tilde functor followed by the original geometric pullback. -/
abbrev structuralPullbackFunctor : ModuleCat.{u} A ⥤ X.Modules :=
  tilde.functor (.of A) ⋙ Scheme.Modules.pullback f

/-- The original ordinary adjunction, transported by the actual structural
global-section comparison. No exactness premise is imposed on pullback. -/
def structuralPullbackGlobalSectionsAdjunction :
    structuralPullbackFunctor f ⊣
      moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f) :=
  ((tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)).ofNatIsoRight
      (moduleSpecPushforwardGlobalSectionsIso f)

instance structuralPullbackFunctor_additive : (structuralPullbackFunctor f).Additive :=
  (structuralPullbackGlobalSectionsAdjunction f).left_adjoint_additive

instance structuralPullbackFunctor_isLeftAdjoint :
    (structuralPullbackFunctor f).IsLeftAdjoint :=
  (structuralPullbackGlobalSectionsAdjunction f).isLeftAdjoint

/-- The original structure-module comparison on the literal free rank-one term. -/
def structuralPullbackUnitIso :
    (structuralPullbackFunctor f).obj (ModuleCat.of A A) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).mapIso (tildeSelf (R := CommRingCat.of A)) ≪≫
    Scheme.Modules.pullbackUnitIso f

private theorem structuralGlobalSectionsLinear :
    letI := moduleCategoryLinearOfHom X (idealThickeningBaseScalar f)
    Functor.Linear A (moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)) := by
  let := moduleCategoryLinearOfHom X (idealThickeningBaseScalar f)
  constructor
  intro M N φ a
  ext x
  change (a • φ).val.app (Opposite.op ⊤) x =
    (idealThickeningBaseScalar f) a • φ.val.app (Opposite.op ⊤) x
  rw [moduleCategoryLinearOfHom_smul_app]
  have htop : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op ⊤) := rfl
  rw [htop, X.presheaf.map_id]
  rfl

/-- The actual left adjoint is linear for the original structural action.
This follows from the original unit equation and linearity of global sections. -/
theorem structuralPullbackLinear :
    letI := moduleCategoryLinearOfHom X (idealThickeningBaseScalar f)
    Functor.Linear A (structuralPullbackFunctor f) := by
  let := moduleCategoryLinearOfHom X (idealThickeningBaseScalar f)
  let := structuralGlobalSectionsLinear f
  let adj := structuralPullbackGlobalSectionsAdjunction f
  apply (Functor.linear_iff A (structuralPullbackFunctor f)).mpr
  intro M a
  apply (adj.homEquiv M ((structuralPullbackFunctor f).obj M)).injective
  change adj.unit.app M ≫
      (moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)).map
        ((structuralPullbackFunctor f).map (a • 𝟙 M)) =
    adj.unit.app M ≫
      (moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)).map
        (a • 𝟙 ((structuralPullbackFunctor f).obj M))
  have hG := ((moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)).map_smul a
      (𝟙 ((structuralPullbackFunctor f).obj M))).trans
    (congrArg (fun z => a • z)
      ((moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)).map_id
        ((structuralPullbackFunctor f).obj M)))
  rw [hG]
  calc
    adj.unit.app M ≫
        (moduleGlobalSectionsFunctorOfHom X (idealThickeningBaseScalar f)).map
          ((structuralPullbackFunctor f).map (a • 𝟙 M)) =
      (a • 𝟙 M) ≫ adj.unit.app M := (adj.unit.naturality (a • 𝟙 M)).symm
    _ = adj.unit.app M ≫ (a • 𝟙 _) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (adj.unit.app M).hom (a • x) = a • (adj.unit.app M).hom x
      exact (adj.unit.app M).hom.map_smul a x

private theorem mapIdealSubtype_comp_eq_zero_iff (I : Ideal A) {M : X.Modules}
    (t : (structuralPullbackFunctor f).obj (ModuleCat.of A A) ⟶ M) :
    (structuralPullbackFunctor f).map (ModuleCat.ofHom I.subtype) ≫ t = 0 ↔
      ∀ b : I, (structuralPullbackFunctor f).map
        ((b : A) • 𝟙 (ModuleCat.of A A)) ≫ t = 0 := by
  let adj := structuralPullbackGlobalSectionsAdjunction f
  constructor
  · intro ht b
    let v : ModuleCat.of A A ⟶ ModuleCat.of A I :=
      ModuleCat.ofHom (LinearMap.toSpanSingleton A I b)
    have hv : v ≫ ModuleCat.ofHom I.subtype = (b : A) • 𝟙 (ModuleCat.of A A) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change r * (b : A) = (b : A) * r
      exact mul_comm _ _
    rw [← hv, Functor.map_comp, Category.assoc, ht, comp_zero]
  · intro ht
    apply (adj.homEquiv (ModuleCat.of A I) M).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homAddEquiv_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    have hb := congrArg (adj.homEquiv (ModuleCat.of A A) M) (ht b)
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homAddEquiv_zero] at hb
    have h := congrArg (fun k : ModuleCat.of A A ⟶ _ => k (1 : A)) hb
    change (adj.homEquiv (ModuleCat.of A A) M t).hom ((b : A) * 1) = 0 at h
    change (adj.homEquiv (ModuleCat.of A A) M t).hom (b : A) = 0
    simpa only [mul_one] using h

/-- The original pulled-back ideal inclusion detects exactly the original ideal scalars. -/
theorem structuralQuotient_scalar_condition (I : Ideal A) {M : X.Modules}
    (t : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    (structuralPullbackFunctor f).map (ModuleCat.ofHom I.subtype) ≫
        (structuralPullbackUnitIso f).hom ≫ t = 0 ↔
      ∀ b : I, globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf)
        ((idealThickeningBaseScalar f) b) ≫ t = 0 := by
  let := moduleCategoryLinearOfHom X (idealThickeningBaseScalar f)
  let := structuralPullbackLinear f
  rw [mapIdealSubtype_comp_eq_zero_iff f I]
  apply forall_congr'
  intro b
  rw [Functor.map_smul, (structuralPullbackFunctor f).map_id,
    ← moduleCategoryLinearOfHom_smul_id X (idealThickeningBaseScalar f)]
  simp only [Linear.smul_comp, Category.id_comp]
  rw [← Linear.comp_smul]
  constructor
  · intro h
    apply (cancel_epi (structuralPullbackUnitIso f).hom).mp
    simpa only [comp_zero] using h
  · intro h
    rw [h, comp_zero]

/-- The original structure quotient as a cofork for the pulled-back ideal inclusion. -/
def structuralQuotientCofork (I : Ideal A) :
    CokernelCofork ((structuralPullbackFunctor f).map (ModuleCat.ofHom I.subtype)) :=
  CokernelCofork.ofπ
    ((structuralPullbackUnitIso f).hom ≫ idealQuotientπ X (idealThickeningBaseScalar f)
      (SheafOfModules.unit X.ringCatSheaf) I)
    ((structuralQuotient_scalar_condition f I _).mpr (fun b => by
      rw [← idealMultipleScalar_ι X (idealThickeningBaseScalar f)
        (SheafOfModules.unit X.ringCatSheaf) I b, Category.assoc,
        idealMultipleι_quotientπ, comp_zero]))

/-- The original structure quotient has the required cokernel universal property. -/
def structuralQuotientCoforkIsColimit (I : Ideal A) :
    IsColimit (structuralQuotientCofork f I) := by
  let u := structuralPullbackUnitIso f
  let q := idealQuotientπ X (idealThickeningBaseScalar f)
    (SheafOfModules.unit X.ringCatSheaf) I
  refine CokernelCofork.IsColimit.ofπ (u.hom ≫ q)
    (structuralQuotientCofork f I).condition
    (fun {M} t ht => idealQuotientDesc X (idealThickeningBaseScalar f) I
      (u.inv ≫ t) ((structuralQuotient_scalar_condition f I _).mp (by
        change (structuralPullbackFunctor f).map (ModuleCat.ofHom I.subtype) ≫
          u.hom ≫ u.inv ≫ t = 0
        rw [u.hom_inv_id_assoc]
        exact ht))) ?_ ?_
  · intro M t ht
    rw [Category.assoc, idealQuotientπ_desc, Iso.hom_inv_id_assoc]
  · intro M t ht r hr
    apply (cancel_epi (u.hom ≫ q)).mp
    rw [hr, Category.assoc, idealQuotientπ_desc, Iso.hom_inv_id_assoc]

/-- The original inclusion and projection defining the base ideal quotient. -/
def idealQuotientSequence (I : Ideal A) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom I.mkQ) (by
    ext x
    exact (Submodule.Quotient.mk_eq_zero I).mpr x.property)

/-- Exactness of the original ideal inclusion and quotient projection. -/
theorem idealQuotientSequence_exact (I : Ideal A) :
    (idealQuotientSequence I).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  exact ⟨⟨a, (Submodule.Quotient.mk_eq_zero I).mp ha⟩, rfl⟩

instance idealQuotientSequence_epi (I : Ideal A) : Epi (idealQuotientSequence I).g :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective I)

/-- The actual geometric pullback of the original quotient module is the
original ideal-image quotient. The isomorphism is constructed from their
original cokernel universal properties. -/
def structuralPullbackQuotientIso (I : Ideal A) :
    (structuralPullbackFunctor f).obj (ModuleCat.of A (A ⧸ I)) ≅
      idealQuotient X (idealThickeningBaseScalar f)
        (SheafOfModules.unit X.ringCatSheaf) I := by
  let hS := idealQuotientSequence_exact I
  let hL := CokernelCofork.mapIsColimit _ hS.gIsCokernel (structuralPullbackFunctor f)
  exact hL.coconePointUniqueUpToIso (structuralQuotientCoforkIsColimit f I)

/-- The quotient comparison retains the original quotient and structure-unit arrows. -/
@[reassoc]
theorem structuralPullbackQuotientIso_hom (I : Ideal A) :
    (structuralPullbackFunctor f).map (ModuleCat.ofHom I.mkQ) ≫
        (structuralPullbackQuotientIso f I).hom =
      (structuralPullbackUnitIso f).hom ≫
        idealQuotientπ X (idealThickeningBaseScalar f)
          (SheafOfModules.unit X.ringCatSheaf) I := by
  exact (CokernelCofork.mapIsColimit _ (idealQuotientSequence_exact I).gIsCokernel
    (structuralPullbackFunctor f)).comp_coconePointUniqueUpToIso_hom
      (structuralQuotientCoforkIsColimit f I) WalkingParallelPair.one

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]
  {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
  (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
  (hdim : ringKrullDim A = 2)

local notation "O" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)
local notation "α" => idealThickeningBaseScalar f
local notation "m" => IsLocalRing.maximalIdeal A

include hff hdim in
omit [IsNoetherianRing A] in
/-- The actual negative homology of the finite pulled-back presentation has
no maps to the structure module. One nonzero original ideal scalar both
annihilates that homology and acts injectively on the original structure sheaf. -/
theorem structuralPresentation_negativeHomology_hom_eq_zero
    (P : ModuleCat.IdealPresentation m)
    (t : (((structuralPullbackFunctor f).mapHomologicalComplex (.up ℤ)).obj
      P.cochain).homology (-1) ⟶ O) : t = 0 := by
  let := moduleCategoryLinearOfHom X α
  let := structuralPullbackLinear f
  have hm : m ≠ ⊥ := by
    intro hm
    have hd := hdim
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm, Ideal.height_bot] at hd
    norm_num at hd
  obtain ⟨a, ha, ha₀⟩ := (Submodule.ne_bot_iff _).mp hm
  have hbase : NormalStalks (Spec (.of A)) :=
    fun y => (isIntegrallyClosed_and_isDomain_stalk_Spec A y).symm
  have hα := Hom.bijective_structuralCoefficients_of_isProper_birational A f hbase hff
  have hαa : α a ≠ 0 := by
    intro h
    exact ha₀ (hα.injective (by simpa only [map_zero] using h))
  let H : X.Modules :=
    (((structuralPullbackFunctor f).mapHomologicalComplex (.up ℤ)).obj P.cochain).homology (-1)
  let s : O ⟶ O := globalScalarEndomorphism X O (α a)
  let : Mono s := structureScalar_mono (α a) hαa
  have hann : globalScalarEndomorphism X H (α a) = 0 :=
    (moduleCategoryLinearOfHom_smul_id X α H a).symm.trans
      (P.mappedHomology_neg_one_scalar_eq_zero (structuralPullbackFunctor f) a ha)
  have hn : globalScalarEndomorphism X H (α a) ≫ t = t ≫ s :=
    ((globalScalarCenter X (α a)).naturality t).symm
  apply (cancel_mono s).mp
  rw [zero_comp, ← hn, hann, zero_comp]

/-- The standard derived category of the original structure-module category. -/
local instance residueVanishingModuleDerivedCategory :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The standard derived category of the original coefficient-module category. -/
local instance residueVanishingCoefficientDerivedCategory :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
local instance : HasExt.{u + 1} X.Modules := HasExt.standard _

include hff hdim in
/-- The actual pulled-back finite presentation has no degree-one derived
maps into the structure module. The proof uses its actual H0 quotient,
its actual annihilated H-minus-one and the original truncation triangle. -/
theorem structuralPresentation_hom_shift_eq_zero_of_isNagata
    (hX : Scheme.NormalStalks X) (hA : IsNagataRing.{u, 0} A)
    (P : ModuleCat.IdealPresentation m)
    (φ : DerivedCategory.Q.obj
        (((structuralPullbackFunctor f).mapHomologicalComplex (.up ℤ)).obj P.cochain) ⟶
      ((DerivedCategory.singleFunctor X.Modules 0).obj O)⟦(1 : ℤ)⟧) : φ = 0 := by
  let L := structuralPullbackFunctor f
  let F : CochainComplex X.Modules ℤ := (L.mapHomologicalComplex (.up ℤ)).obj P.cochain
  let Z : DerivedCategory X.Modules := DerivedCategory.Q.obj F
  let : CochainComplex.IsStrictlyLE F 0 := inferInstance
  let : Z.IsLE 0 := inferInstance
  let eNeg := (DerivedCategory.homologyFunctorFactors X.Modules (-1)).app F
  let e₀ := (DerivedCategory.homologyFunctorFactors X.Modules 0).app F ≪≫
    P.mappedHomologyZeroIso L ≪≫ structuralPullbackQuotientIso f m
  apply hom_to_single_shift_eq_zero Z O ?_ ?_ φ
  · intro t
    apply (cancel_epi eNeg.inv).mp
    simpa only [comp_zero] using
      structuralPresentation_negativeHomology_hom_eq_zero f hff hdim P (eNeg.inv ≫ t)
  · intro xi
    have hz := closedFibreExt_one_eq_zero_of_isNagata f hff hdim hX hA
      ((Ext.mk₀ e₀.inv).comp xi (Nat.zero_add 1))
    have h := congrArg (fun z => (Ext.mk₀ e₀.hom).comp z (Nat.zero_add 1)) hz
    simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

include hff hdim in
/-- The original residue field in degree one has no maps to the original
right-derived global sections of the structure module. This is the native
form of Stacks 0AXC used by the residue obstruction, with the original base
ring, original structural action and original right-derived object.

The finite presentation only computes this Hom group. It is not asserted
to resolve the residue field, and higher negative Tor is not assumed zero. -/
theorem residueField_hom_derivedGlobalSections_eq_zero_of_isNagata
    (hX : Scheme.NormalStalks X) (hA : IsNagataRing.{u, 0} A)
    (φ : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 1).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶
      DerivedCategory.Plus.ι.obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj O))) : φ = 0 := by
  let P := ModuleCat.IdealPresentation.ofNoetherian m
  let G := moduleGlobalSectionsFunctorOfHom X α
  let I : InjectiveResolution (C := X.Modules) O := injectiveResolution O
  let J : CochainComplex X.Modules ℤ := I.cochainComplex
  let Kplus := G.rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj O)
  let K := DerivedCategory.Plus.ι.obj Kplus
  let : Kplus.IsGE 0 := G.rightDerivedFunctorPlus_isGE _ 0
  let : K.IsGE 0 := inferInstance
  let : (K⟦(1 : ℤ)⟧).IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_shift K 0 1 (-1) (by norm_num)
  let eG : DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj J) ≅ K :=
    ((DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).app
      (G.mapCochainComplexPlus.obj I.cochainComplexPlus)).symm ≪≫
        DerivedCategory.Plus.ι.mapIso (I.rightDerivedFunctorPlusIso G)
  let eG₁ : DerivedCategory.Q.obj
      ((G.mapHomologicalComplex (.up ℤ)).obj (J⟦(1 : ℤ)⟧)) ≅ K⟦(1 : ℤ)⟧ :=
    DerivedCategory.Q.mapIso
      (((G.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app J) ≪≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).app
        ((G.mapHomologicalComplex (.up ℤ)).obj J) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).mapIso eG
  let eO : DerivedCategory.Q.obj J ≅ (DerivedCategory.singleFunctor X.Modules 0).obj O :=
    (asIso ((DerivedCategory.Q (C := X.Modules)).map I.ι')).symm
  let eO₁ : DerivedCategory.Q.obj (J⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj O)⟦(1 : ℤ)⟧ :=
    ((DerivedCategory.Q (C := X.Modules)).commShiftIso (1 : ℤ)).app J ≪≫
      (shiftFunctor (DerivedCategory X.Modules) (1 : ℤ)).mapIso eO
  let eκ := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
    1 0 1 (by norm_num)).app (ModuleCat.of A (IsLocalRing.ResidueField A))
  let g : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ K⟦(1 : ℤ)⟧ :=
    eκ.inv ≫ φ⟦(1 : ℤ)⟧'
  let a := DerivedCategory.Q.map P.augmentation ≫ g ≫ eG₁.inv
  let adj := structuralPullbackGlobalSectionsAdjunction f
  let e := adj.cochainDerivedHomEquivOfMixed P.cochain (J⟦(1 : ℤ)⟧)
  have hb : e.symm a = 0 := by
    apply (cancel_mono eO₁.hom).mp
    rw [zero_comp]
    exact structuralPresentation_hom_shift_eq_zero_of_isNagata f hff hdim hX hA P
      (e.symm a ≫ eO₁.hom)
  have ha : a = 0 := by
    have h := congrArg e hb
    simpa only [AddEquiv.apply_symm_apply, map_zero] using h
  have hag : DerivedCategory.Q.map P.augmentation ≫ g = 0 := by
    apply (cancel_mono eG₁.inv).mp
    simpa only [Category.assoc, zero_comp] using ha
  have hg : g = 0 := (P.augmentation_precomp_bijective (K⟦(1 : ℤ)⟧)).injective
    (by simpa only [comp_zero] using hag)
  apply (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map_injective
  rw [Functor.map_zero]
  apply (cancel_epi eκ.inv).mp
  simpa only [comp_zero] using hg

end AlgebraicGeometry.Scheme.Cohomology
