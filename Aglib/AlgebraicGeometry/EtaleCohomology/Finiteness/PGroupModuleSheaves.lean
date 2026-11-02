/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GaloisActionMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.ConstantModuleSheaves
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FiniteExact
public import Aglib.CategoryTheory.Sites.FiniteGroupAction.ModulePropertyDevissage

/-! # Proper cohomology of modules trivialized by a p-group cover

Finite prime-killed representations are built from finite trivial left-hand
subobjects. Actual invariant sections descend those subobjects; their actual
sheaf cokernels, not a representation-to-sheaf equivalence, supply the
induction step. Original-map naturality identifies the quotient action after
the native module cokernel isomorphism.

The literal supplied coefficient module is explicitly killed by the prime.
It need not have a finite underlying additive group. The coefficient-ring
universe is independent. Noetherianity enters only the finite-middle
cohomology argument, not the representation or sheaf induction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u r e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}} [ConnectedSpace X]
  (Y : Scheme.FiniteEtale X) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
  [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]

local instance pGroupModuleHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, r}

/-- The original Galois cover, image adjunction and constant-unit section data. -/
def pGroupModuleCoverData :
    CategoryTheory.FiniteGroupAction.ModuleCoverData X.smallEtaleTopology R (Aut Y)
      (ModuleSheaf R Y.obj.left) where
  terminal := etaleTerminal X
  cover := (Scheme.FiniteEtale.toEtale X).obj Y
  overlap := (Scheme.FiniteEtale.toEtale X).obj
    (Scheme.FiniteEtale.ProperResidue.productCover Y Y)
  isTerminal := etaleTerminalIsTerminal X
  action := Functor.mapAut Y (Scheme.FiniteEtale.toEtale X)
  arrow := finiteEtaleTerminalMap Y
  arrow_covering := finiteEtaleTerminalMap_covering Y
  first := (Scheme.FiniteEtale.toEtale X).map
    (Scheme.FiniteEtale.ProperResidue.productFirst Y Y)
  second := (Scheme.FiniteEtale.toEtale X).map
    (Scheme.FiniteEtale.ProperResidue.productSecond Y Y)
  isPullback := finiteEtaleOverlap_isPullback Y
  graph := fun σ => (Scheme.FiniteEtale.toEtale X).map
    (Scheme.FiniteEtale.galoisOverlapGraph Y σ)
  graph_covering := galoisOverlapGraph_covering Y
  graph_first := by
    intro σ
    rw [← Functor.map_comp, Scheme.FiniteEtale.galoisOverlapGraph_fst,
      CategoryTheory.Functor.map_id]
  graph_second := by
    intro σ
    rw [← Functor.map_comp, Scheme.FiniteEtale.galoisOverlapGraph_snd]
    rfl
  image := moduleInverseImage R Y.obj.hom
  directImage := moduleDirectImage R Y.obj.hom
  «constant» := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  sections := moduleGlobalSections R Y.obj.left
  imageAdjunction := moduleImageAdjunction R Y.obj.hom
  constantAdjunction := moduleConstantAdjunction R Y.obj.left
  rightSectionsIso := moduleDirectImageGlobalSectionsIso R Y.obj.hom
  constantIso := moduleInverseImageConstantIso R Y.obj.hom
  constantIso_eq := (moduleInverseImageConstantCanonicalIso_eq R Y.obj.hom).symm
  sectionComparison := fun F => finiteEtalePullbackSectionsIso F Y
  sectionComparison_naturality := fun f => finiteEtalePullbackSectionsIso_naturality Y f
  sectionIso := fun F M hM t => trivializedFiniteEtaleSectionsIso F Y M hM t
  sectionIso_hom := fun F M hM t => trivializedFiniteEtaleSectionsIso_hom F Y M hM t
  restriction := fun F => finiteEtalePullbackSectionsIso_restriction F Y

local instance pGroupModuleCoverData_image_preservesZeroMorphisms :
    (pGroupModuleCoverData (R := R) Y).image.PreservesZeroMorphisms :=
  inferInstanceAs ((moduleInverseImage R Y.obj.hom).PreservesZeroMorphisms)

local instance pGroupModuleCoverData_constant_preservesZeroMorphisms :
    (pGroupModuleCoverData (R := R) Y).constant.PreservesZeroMorphisms :=
  inferInstanceAs ((constantSheaf Y.obj.left.smallEtaleTopology
    (ModuleCat.{u + 1} R)).PreservesZeroMorphisms)

/-- This operational record constructs exactly the original descended map. -/
theorem pGroupModuleCoverData_subobjectMap (F : ModuleSheaf R X)
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    {N : ModuleCat.{u + 1} R} (i : N ⟶ M)
    (hi : ∀ (σ : Aut Y) (x : N), trivializedDeckRepresentation F Y M hM t σ (i x) = i x) :
    (pGroupModuleCoverData (R := R) Y).subobjectMap F M hM t i hi =
      galoisTrivialSubobjectMap F Y M hM t i hi := rfl

/-- The quotient comparison is the original image/cokernel/constant comparison. -/
theorem pGroupModuleCoverData_subobjectCokernelIso (F : ModuleSheaf R X)
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    {N : ModuleCat.{u + 1} R} (i : N ⟶ M)
    (hi : ∀ (σ : Aut Y) (x : N), trivializedDeckRepresentation F Y M hM t σ (i x) = i x) :
    (pGroupModuleCoverData (R := R) Y).subobjectCokernelIso F M hM t i hi =
      galoisTrivialSubobjectCokernelIso F Y M hM t i hi := rfl

/-- A trivial actual deck action descends the original chosen constant module.
This is the identity-map case of invariant-section descent. -/
def galoisTrivialActionIso (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R)
    (hM : IsAddTorsion M)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (htriv : ∀ (σ : Aut Y) (m : M), trivializedDeckRepresentation F Y M hM e σ m = m) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ≅ F := by
  let d := pGroupModuleCoverData (R := R) Y
  let : d.image.Faithful :=
    inferInstanceAs ((moduleInverseImage R Y.obj.hom).Faithful)
  exact d.trivialActionIso F M hM e htriv

/-- The complete actual-sheaf induction on the original Galois cover. -/
theorem property_of_pGroup_trivialization (p : ℕ) [Fact p.Prime]
    (hY : IsPGroup p (Aut Y)) (P : ModuleSheaf R X → Prop)
    (hconstant : ∀ (M : ModuleCat.{u + 1} R), ∀ [Module.Finite R M],
      (∀ m : M, p • m = 0) →
        P ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))
    (hiso : ∀ {F G : ModuleSheaf R X}, (F ≅ G) → P F → P G)
    (hstep : ∀ S : ShortComplex (ModuleSheaf R X), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (F : ModuleSheaf R X) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) : P F := by
  let d := pGroupModuleCoverData (R := R) Y
  let K := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : PreservesFiniteLimits K := by
    dsimp [K, constantSheaf]
    infer_instance
  let : d.image.Faithful :=
    inferInstanceAs ((moduleInverseImage R Y.obj.hom).Faithful)
  let : d.constant.PreservesMonomorphisms := by
    change K.PreservesMonomorphisms
    infer_instance
  let : d.image.PreservesZeroMorphisms :=
    inferInstanceAs ((moduleInverseImage R Y.obj.hom).PreservesZeroMorphisms)
  let : d.constant.PreservesZeroMorphisms :=
    inferInstanceAs (K.PreservesZeroMorphisms)
  exact d.property_of_pGroup_trivialization p hY P hconstant hiso hstep F M hM e

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open AlgebraicGeometry.Scheme.OverField Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {k : Type u} [Field k] [IsSepClosed k] (X : FScheme k) [IsProper X.hom]
  [ConnectedSpace X.left]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X.left)]
  [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{e}]
  (p : ℕ) [Fact p.Prime] [CharP k p]
  (R : Type r) [CommRing R] [IsNoetherianRing R]

/-- An actual p-group Galois trivialization by a finite prime-killed original
module gives finite original module cohomology in every degree on a proper
scheme over a separably closed field of characteristic p.

The connected qcqs cover hypotheses are explicit. No finite underlying group,
small coefficient ring, general effective descent, or torsion-detection premise
is substituted for the literal chosen module and actual trivialization. -/
theorem moduleSheaf_cohomology_finite_of_pGroup_trivialization
    (Y : Scheme.FiniteEtale X.left) [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (hY : IsPGroup p (Aut Y)) (q : ℕ)
    (F : ModuleSheaf R X.left) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Module.Finite R ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj F) := by
  apply property_of_pGroup_trivialization Y p hY
    (fun E => Module.Finite R
      ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).obj E))
    (fun N _ hp => constantModuleSheaf_cohomology_finite_of_prime_nsmul X p R q N hp)
    ?_ ?_ F M hM e
  · intro E E' i hE
    let := hE
    exact Module.Finite.equiv
      ((ModuleCat.Sheaf.cohomology X.left.smallEtaleTopology R q).mapIso i).toLinearEquiv
  · intro S hS h₁ h₃
    let := h₁
    let := h₃
    exact ModuleCat.Sheaf.finite_cohomology_of_shortExact X.left.smallEtaleTopology R S hS q

end AlgebraicGeometry.Scheme.EtaleCohomology
