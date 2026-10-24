/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GaloisInvariantSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConstantPullbackSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CoverConservativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Trivial subobjects on an actual Galois trivialization

A linear map into the fixed vectors of the original literal module action
descends through invariant sections and the original constant/sections
adjunction. Its original inverse image is exactly the original constant map.
For an injection, actual cover faithfulness gives a monomorphism, and its
actual cokernel is trivialized by the constant module cokernel on the same
cover. This realizes trivial left-hand subobjects, not arbitrary object descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}}

local instance galoisTrivialSubobjectHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, r}

local instance {S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint := (moduleImageAdjunction R f).isLeftAdjoint

local instance galoisTrivialSubobjectHasSheafify (S : Scheme.{u}) :
    (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)).IsLeftAdjoint :=
  (moduleConstantAdjunction R S).isLeftAdjoint

/-- Original pullback sections are original sections on the actual cover object. -/
def finiteEtalePullbackSectionsIso (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X) :
    (moduleGlobalSections R Y.obj.left).obj ((moduleInverseImage R Y.obj.hom).obj F) ≅
      finiteEtaleSections F Y :=
  (moduleGlobalSections R Y.obj.left).mapIso ((moduleInverseImageEtaleIso R Y.obj.hom).app F) ≪≫
    (F.obj.mapIso (finiteEtalePostcomposeTerminalIso Y).op).symm

/-- The original pullback unit restricts along the original structural arrow. -/
@[reassoc]
theorem finiteEtalePullbackSectionsIso_restriction (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) :
    moduleGlobalSectionsPullback R Y.obj.hom F ≫
      (finiteEtalePullbackSectionsIso F Y).hom = finiteEtaleGlobalRestriction F Y := by
  change moduleGlobalSectionsPullback R Y.obj.hom F ≫
    ((moduleGlobalSections R Y.obj.left).map
      ((moduleInverseImageEtaleIso R Y.obj.hom).hom.app F) ≫
        F.obj.map (finiteEtalePostcomposeTerminalIso Y).inv.op) = _
  rw [← Category.assoc, moduleGlobalSectionsPullback_etale,
    ← Functor.map_comp, ← op_comp]
  exact congrArg (fun a => F.obj.map a.op) ((etaleTerminalIsTerminal X).hom_ext _ _)

variable (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X)
  [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
  (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
  (e : (moduleInverseImage R Y.obj.hom).obj F ≅
    (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)

/-- The prescribed trivialization retains the original constant unit and pullback sections. -/
theorem trivializedFiniteEtaleSectionsIso_hom :
    (trivializedFiniteEtaleSectionsIso F Y M hM e).hom =
      (moduleConstantAdjunction R Y.obj.left).unit.app M ≫
        (moduleGlobalSections R Y.obj.left).map e.inv ≫
          (finiteEtalePullbackSectionsIso F Y).hom := by
  simp only [trivializedFiniteEtaleSectionsIso, moduleConstantSectionsIso,
    finiteEtalePullbackSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Functor.map_comp, Category.assoc]

variable {N : ModuleCat.{u + 1} R} (i : N ⟶ M)
  (hi : ∀ (σ : Aut Y) (n : N), trivializedDeckRepresentation F Y M hM e σ (i n) = i n)

include hi in
/-- A fixed-image linear map gives a genuinely invariant original cover-section map. -/
theorem trivializedLinearMap_invariant (σ : Aut Y) :
    (i ≫ (trivializedFiniteEtaleSectionsIso F Y M hM e).hom) ≫
      F.obj.map ((Scheme.FiniteEtale.toEtale X).map σ.hom).op =
    i ≫ (trivializedFiniteEtaleSectionsIso F Y M hM e).hom := by
  ext n
  have h := trivializedDeckRepresentation_restriction F Y M hM e σ⁻¹ (i n)
  rw [hi] at h
  exact h.symm

variable [ConnectedSpace X] [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]

/-- The actual constant-source map obtained by native invariant-section descent. -/
def galoisTrivialSubobjectMap :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj N ⟶ F :=
  ((moduleConstantAdjunction R X).homEquiv N F).symm
    (invariantLinearSectionDescend Y F
      (i ≫ (trivializedFiniteEtaleSectionsIso F Y M hM e).hom)
      (trivializedLinearMap_invariant F Y M hM e i hi))

/-- Its original adjoint is the native amalgamation, without replacing global sections. -/
theorem galoisTrivialSubobjectMap_homEquiv :
    (moduleConstantAdjunction R X).homEquiv N F
      (galoisTrivialSubobjectMap F Y M hM e i hi) =
    invariantLinearSectionDescend Y F
      (i ≫ (trivializedFiniteEtaleSectionsIso F Y M hM e).hom)
      (trivializedLinearMap_invariant F Y M hM e i hi) :=
  Equiv.apply_symm_apply _ _

/-- The original inverse image, through the original constant and F trivializations,
is literally the constant map of the supplied linear map. -/
@[reassoc]
theorem galoisTrivialSubobjectMap_pullback :
    (moduleInverseImage R Y.obj.hom).map (galoisTrivialSubobjectMap F Y M hM e i hi) ≫
      e.hom =
    (moduleInverseImageConstantIso R Y.obj.hom).hom.app N ≫
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).map i := by
  let d := invariantLinearSectionDescend Y F
    (i ≫ (trivializedFiniteEtaleSectionsIso F Y M hM e).hom)
    (trivializedLinearMap_invariant F Y M hM e i hi)
  let b := finiteEtalePullbackSectionsIso F Y
  let G := moduleGlobalSections R Y.obj.left
  have hd : d ≫ moduleGlobalSectionsPullback R Y.obj.hom F =
      i ≫ (moduleConstantAdjunction R Y.obj.left).unit.app M ≫ G.map e.inv := by
    apply (cancel_mono b.hom).mp
    rw [Category.assoc, finiteEtalePullbackSectionsIso_restriction,
      invariantLinearSectionDescend_restriction, trivializedFiniteEtaleSectionsIso_hom]
    simp only [Category.assoc, b, G]
  apply (cancel_epi ((moduleInverseImageConstantIso R Y.obj.hom).inv.app N)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply ((moduleConstantAdjunction R Y.obj.left).homEquiv N _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  have ht : (moduleConstantAdjunction R Y.obj.left).homEquiv N _
      ((moduleInverseImageConstantIso R Y.obj.hom).inv.app N ≫
        (moduleInverseImage R Y.obj.hom).map (galoisTrivialSubobjectMap F Y M hM e i hi)) =
      d ≫ moduleGlobalSectionsPullback R Y.obj.hom F :=
    (moduleConstantTransport_homEquiv R Y.obj.hom N
      (galoisTrivialSubobjectMap F Y M hM e i hi)).trans
        (congrArg (fun t => t ≫ moduleGlobalSectionsPullback R Y.obj.hom F)
          (galoisTrivialSubobjectMap_homEquiv F Y M hM e i hi))
  rw [ht]
  change (d ≫ moduleGlobalSectionsPullback R Y.obj.hom F) ≫ G.map e.hom = _
  rw [hd]
  simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, Adjunction.homEquiv_unit]
  rw [G.map_id]
  exact (congrArg
    (fun z : M ⟶ G.obj
      ((constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) => i ≫ z)
    (Category.comp_id ((moduleConstantAdjunction R Y.obj.left).unit.app M))).trans
      ((moduleConstantAdjunction R Y.obj.left).unit.naturality i)

/-- Injectivity of the supplied original module map gives a monomorphism downstairs. -/
theorem galoisTrivialSubobjectMap_mono (hinj : Function.Injective i) :
    Mono (galoisTrivialSubobjectMap F Y M hM e i hi) := by
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr hinj
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  have : PreservesFiniteLimits C := by
    dsimp [C, constantSheaf]
    infer_instance
  have hm : Mono ((moduleInverseImage R Y.obj.hom).map
      (galoisTrivialSubobjectMap F Y M hM e i hi) ≫ e.hom) := by
    rw [galoisTrivialSubobjectMap_pullback]
    infer_instance
  have : Mono ((moduleInverseImage R Y.obj.hom).map
      (galoisTrivialSubobjectMap F Y M hM e i hi)) := mono_of_mono _ e.hom
  exact (moduleInverseImage R Y.obj.hom).mono_of_mono_map this

/-- The actual cokernel gives the native short exact sequence with trivial left term. -/
theorem galoisTrivialSubobjectMap_shortExact (hinj : Function.Injective i) :
    (ShortComplex.cokernelSequence (galoisTrivialSubobjectMap F Y M hM e i hi)).ShortExact := by
  refine { exact := ShortComplex.cokernelSequence_exact _, mono_f := ?_ }
  change Mono (galoisTrivialSubobjectMap F Y M hM e i hi)
  exact galoisTrivialSubobjectMap_mono F Y M hM e i hi hinj

/-- The actual cokernel remains constant on the original cover, with literal module cokernel. -/
def galoisTrivialSubobjectCokernelIso :
    (moduleInverseImage R Y.obj.hom).obj
      (cokernel (galoisTrivialSubobjectMap F Y M hM e i hi)) ≅
    (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (cokernel i) := by
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : PreservesFiniteColimits C := by
    dsimp [C, constantSheaf]
    infer_instance
  exact PreservesCokernel.iso (moduleInverseImage R Y.obj.hom) _ ≪≫
    cokernel.mapIso _ (C.map i) ((moduleInverseImageConstantIso R Y.obj.hom).app N) e
      (galoisTrivialSubobjectMap_pullback F Y M hM e i hi) ≪≫
    (PreservesCokernel.iso C i).symm

/-- The quotient trivialization retains the original cokernel projection exactly. -/
@[reassoc]
theorem galoisTrivialSubobjectCokernelIso_projection :
    (moduleInverseImage R Y.obj.hom).map
        (cokernel.π (galoisTrivialSubobjectMap F Y M hM e i hi)) ≫
      (galoisTrivialSubobjectCokernelIso F Y M hM e i hi).hom =
    e.hom ≫ (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).map
      (cokernel.π i) := by
  simp [galoisTrivialSubobjectCokernelIso, PreservesCokernel.iso_inv]

/-- Quotients of finitely generated original modules remain finitely generated over R. -/
theorem moduleCokernel_finite [Module.Finite R M] :
    Module.Finite R ↥(cokernel i : ModuleCat.{u + 1} R) :=
  Module.Finite.of_surjective (cokernel.π i).hom
    ((ModuleCat.epi_iff_surjective (cokernel.π i)).mp inferInstance)

include hM in
/-- The actual module cokernel retains additive torsion, even for infinite underlying groups. -/
theorem moduleCokernel_isAddTorsion : IsAddTorsion ↥(cokernel i : ModuleCat.{u + 1} R) :=
  IsAddTorsion.of_surjective (f := (cokernel.π i).hom.toAddMonoidHom)
    ((ModuleCat.epi_iff_surjective (cokernel.π i)).mp inferInstance) hM

/-- Finite generation is needed only here: the actual quotient is finite-type locally constant. -/
def galoisTrivialSubobjectCokernelTrivialization [Module.Finite R M] :
    FiniteTypeLocalTrivialization (cokernel (galoisTrivialSubobjectMap F Y M hM e i hi)) where
  index := PUnit.{u + 1}
  chart _ := (Scheme.FiniteEtale.toEtale X).obj Y
  covers x := by
    obtain ⟨y, hy⟩ := Y.obj.hom.surjective x
    exact ⟨PUnit.unit, y, hy⟩
  value _ := cokernel i
  finite_value _ := moduleCokernel_finite M i
  trivialization _ := galoisTrivialSubobjectCokernelIso F Y M hM e i hi

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
