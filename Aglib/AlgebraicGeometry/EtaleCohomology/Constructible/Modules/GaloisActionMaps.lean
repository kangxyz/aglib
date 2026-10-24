/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.GaloisTrivialSubobject

/-! # Original maps and transported deck actions

Naturality of an actual sheaf morphism along inverse deck maps gives
intertwining maps on original sections. A commutative original pullback square
transports this equation to the literal coefficient modules. In particular,
the actual cokernel projection intertwines the actual quotient action.
No representation-to-sheaf descent or finite underlying-set assumption is used.
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
  {F F' : ModuleSheaf R X} (Y : Scheme.FiniteEtale X)

/-- An actual original sheaf map intertwines restriction along inverse deck maps. -/
theorem finiteEtaleSectionsRepresentation_naturality (a : F ⟶ F')
    (σ : Aut Y) (s : finiteEtaleSections F Y) :
    a.hom.app (op ((Scheme.FiniteEtale.toEtale X).obj Y))
        (finiteEtaleSectionsRepresentation F Y σ s) =
      finiteEtaleSectionsRepresentation F' Y σ
        (a.hom.app (op ((Scheme.FiniteEtale.toEtale X).obj Y)) s) := by
  exact congrArg (fun b => b s)
    (a.hom.naturality ((Scheme.FiniteEtale.toEtale X).map σ.inv).op)

/-- The original pullback-section comparison is natural in the original sheaf. -/
@[reassoc]
theorem finiteEtalePullbackSectionsIso_naturality (a : F ⟶ F') :
    (moduleGlobalSections R Y.obj.left).map ((moduleInverseImage R Y.obj.hom).map a) ≫
      (finiteEtalePullbackSectionsIso F' Y).hom =
    (finiteEtalePullbackSectionsIso F Y).hom ≫
      a.hom.app (op ((Scheme.FiniteEtale.toEtale X).obj Y)) := by
  let G := moduleGlobalSections R Y.obj.left
  have h := congrArg G.map ((moduleInverseImageEtaleIso R Y.obj.hom).hom.naturality a)
  change G.map ((moduleInverseImage R Y.obj.hom).map a) ≫
      G.map ((moduleInverseImageEtaleIso R Y.obj.hom).hom.app F') =
    G.map ((moduleInverseImageEtaleIso R Y.obj.hom).hom.app F) ≫
      a.hom.app (op ((siteEtalePostcompose Y.obj.hom).obj
        (etaleTerminal Y.obj.left))) at h
  change G.map ((moduleInverseImage R Y.obj.hom).map a) ≫
      (G.map ((moduleInverseImageEtaleIso R Y.obj.hom).hom.app F') ≫
        F'.obj.map (finiteEtalePostcomposeTerminalIso Y).inv.op) =
    (G.map ((moduleInverseImageEtaleIso R Y.obj.hom).hom.app F) ≫
      F.obj.map (finiteEtalePostcomposeTerminalIso Y).inv.op) ≫ _
  rw [← Category.assoc, h, Category.assoc,
    ← a.hom.naturality (finiteEtalePostcomposeTerminalIso Y).inv.op,
    ← Category.assoc]

variable [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left]
  [QuasiSeparatedSpace Y.obj.left]
  (M M' : ModuleCat.{u + 1} R) (hM : IsAddTorsion M) (hM' : IsAddTorsion M')
  (e : (moduleInverseImage R Y.obj.hom).obj F ≅
    (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
  (e' : (moduleInverseImage R Y.obj.hom).obj F' ≅
    (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M')
  (a : F ⟶ F') (j : M ⟶ M')
  (ha : (moduleInverseImage R Y.obj.hom).map a ≫ e'.hom =
    e.hom ≫ (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).map j)

include ha in
/-- A literal inverse-image square gives the corresponding original section square,
retaining the native constant unit and the supplied trivializations. -/
@[reassoc]
theorem trivializedFiniteEtaleSectionsIso_naturality :
    j ≫ (trivializedFiniteEtaleSectionsIso F' Y M' hM' e').hom =
    (trivializedFiniteEtaleSectionsIso F Y M hM e).hom ≫
      a.hom.app (op ((Scheme.FiniteEtale.toEtale X).obj Y)) := by
  let G := moduleGlobalSections R Y.obj.left
  let C := constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)
  have he : e.inv ≫ (moduleInverseImage R Y.obj.hom).map a = C.map j ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ha, Iso.inv_hom_id_assoc]
  rw [trivializedFiniteEtaleSectionsIso_hom,
    trivializedFiniteEtaleSectionsIso_hom]
  change j ≫ (moduleConstantAdjunction R Y.obj.left).unit.app M' ≫
      G.map e'.inv ≫ (finiteEtalePullbackSectionsIso F' Y).hom =
    ((moduleConstantAdjunction R Y.obj.left).unit.app M ≫
      G.map e.inv ≫ (finiteEtalePullbackSectionsIso F Y).hom) ≫ _
  have hu : j ≫ (moduleConstantAdjunction R Y.obj.left).unit.app M' =
      (moduleConstantAdjunction R Y.obj.left).unit.app M ≫ G.map (C.map j) :=
    (moduleConstantAdjunction R Y.obj.left).unit.naturality j
  rw [← Category.assoc j, hu]
  change ((moduleConstantAdjunction R Y.obj.left).unit.app M ≫ G.map (C.map j)) ≫ _ = _
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, ← he, G.map_comp]
  simp only [Category.assoc]
  rw [finiteEtalePullbackSectionsIso_naturality]

include ha in
/-- The original coefficient map intertwines the two actual transported deck actions. -/
theorem trivializedDeckRepresentation_naturality (σ : Aut Y) (m : M) :
    j (trivializedDeckRepresentation F Y M hM e σ m) =
      trivializedDeckRepresentation F' Y M' hM' e' σ (j m) := by
  let b := trivializedFiniteEtaleSectionsIso F Y M hM e
  let b' := trivializedFiniteEtaleSectionsIso F' Y M' hM' e'
  let aY := a.hom.app (op ((Scheme.FiniteEtale.toEtale X).obj Y))
  have hnat (x : M) : b'.hom (j x) = aY (b.hom x) :=
    congrArg (fun f => f x)
      (trivializedFiniteEtaleSectionsIso_naturality Y M M' hM hM' e e' a j ha)
  apply b'.toLinearEquiv.injective
  change b'.hom (j (trivializedDeckRepresentation F Y M hM e σ m)) =
    b'.hom (trivializedDeckRepresentation F' Y M' hM' e' σ (j m))
  rw [hnat, trivializedDeckRepresentation_restriction,
    trivializedDeckRepresentation_restriction]
  change aY (finiteEtaleSectionsRepresentation F Y σ (b.hom m)) =
    finiteEtaleSectionsRepresentation F' Y σ (b'.hom (j m))
  rw [hnat]
  exact finiteEtaleSectionsRepresentation_naturality Y a σ (b.hom m)

include ha in
/-- The same original coefficient map, bundled in the native representation category. -/
def trivializedDeckRepMap :
    Rep.of (trivializedDeckRepresentation F Y M hM e) ⟶
      Rep.of (trivializedDeckRepresentation F' Y M' hM' e') :=
  Rep.ofHom (j.hom.intertwiningMap_of_isIntertwiningMap _ _
    (trivializedDeckRepresentation_naturality Y M M' hM hM' e e' a j ha))

/-- Changing a supplied trivialization by an actual module isomorphism transports
its deck action by that same original isomorphism. -/
theorem trivializedDeckRepresentation_change_trivialization
    (j : M ≅ M') (σ : Aut Y) (m : M) :
    j.hom (trivializedDeckRepresentation F Y M hM e σ m) =
      trivializedDeckRepresentation F Y M' hM'
        (e ≪≫ (constantSheaf Y.obj.left.smallEtaleTopology
          (ModuleCat.{u + 1} R)).mapIso j) σ (j.hom m) := by
  apply trivializedDeckRepresentation_naturality Y M M' hM hM' e
    (e ≪≫ (constantSheaf Y.obj.left.smallEtaleTopology
      (ModuleCat.{u + 1} R)).mapIso j) (𝟙 F) j.hom
  simp

variable [ConnectedSpace X] [PreGaloisCategory.IsGalois Y] [Surjective Y.obj.hom]
  {N : ModuleCat.{u + 1} R} (i : N ⟶ M)
  (hi : ∀ (σ : Aut Y) (n : N), trivializedDeckRepresentation F Y M hM e σ (i n) = i n)

/-- The actual original cokernel projection intertwines the actual quotient action. -/
theorem galoisTrivialSubobjectCokernel_projection_intertwines
    (σ : Aut Y) (m : M) :
    (cokernel.π i) (trivializedDeckRepresentation F Y M hM e σ m) =
      trivializedDeckRepresentation
        (cokernel (galoisTrivialSubobjectMap F Y M hM e i hi)) Y
        (cokernel i) (moduleCokernel_isAddTorsion M hM i)
        (galoisTrivialSubobjectCokernelIso F Y M hM e i hi) σ ((cokernel.π i) m) :=
  trivializedDeckRepresentation_naturality Y M (cokernel i) hM
    (moduleCokernel_isAddTorsion M hM i) e
    (galoisTrivialSubobjectCokernelIso F Y M hM e i hi)
    (cokernel.π (galoisTrivialSubobjectMap F Y M hM e i hi)) (cokernel.π i)
    (galoisTrivialSubobjectCokernelIso_projection F Y M hM e i hi) σ m

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
