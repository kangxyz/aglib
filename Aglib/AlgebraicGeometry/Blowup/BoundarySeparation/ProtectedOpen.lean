/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.BoundarySeparation.IdealChoice
public import Aglib.AlgebraicGeometry.Blowup.Extension

/-!
# The complementary open in two-open boundary control

The complement of the closure of the inverse image of `V \ U` meets the
inverse image of `V` in exactly the inverse image of `U`. Boundary separation
makes the actual closed schematic image factor through this open. A subsequent
centre on the complementary open can therefore extend while avoiding all of
`V`, not just `U`. No global schematic-density assertion is made.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- The open remaining after removing the closure of the unwanted protected
boundary on the modified base. -/
def boundaryComplement {X B : Scheme.{u}} (q : B ⟶ X) (U V : X.Opens) : B.Opens :=
  ⟨(closure (q ⁻¹' ((V : Set X) \ (U : Set X))))ᶜ, isClosed_closure.isOpen_compl⟩

/-- The whole inverse image of `U` lies in the complementary open. -/
lemma preimage_le_boundaryComplement {X B : Scheme.{u}} (q : B ⟶ X)
    (U V : X.Opens) : q ⁻¹ᵁ U ≤ boundaryComplement q U V := by
  intro x hx
  change x ∉ closure (q ⁻¹' ((V : Set X) \ (U : Set X)))
  intro hcl
  have hbound : closure (q ⁻¹' ((V : Set X) \ (U : Set X))) ⊆
      ((q ⁻¹ᵁ U : B.Opens) : Set B)ᶜ :=
    closure_minimal (fun _ hy => hy.2) (q ⁻¹ᵁ U).isOpen.isClosed_compl
  exact hbound hcl hx

/-- The two protected opens remain distinct: only `U`, not all of `V`, meets
the complementary open. This identity requires no density or reducedness. -/
lemma boundaryComplement_inf_preimage {X B : Scheme.{u}} (q : B ⟶ X)
    (U V : X.Opens) (hUV : U ≤ V) :
    boundaryComplement q U V ⊓ q ⁻¹ᵁ V = q ⁻¹ᵁ U := by
  apply le_antisymm
  · intro x hx
    by_contra hxU
    exact hx.1 (subset_closure ⟨hx.2, hxU⟩)
  · intro x hx
    exact ⟨preimage_le_boundaryComplement q U V hx, hUV hx⟩

/-- On the complementary open, restriction to the larger protected open is
literally restriction to the smaller one. -/
lemma boundaryComplement_preimage_protected {X B : Scheme.{u}} (q : B ⟶ X)
    (U V : X.Opens) (hUV : U ≤ V) :
    (boundaryComplement q U V).ι ⁻¹ᵁ (q ⁻¹ᵁ V) =
      (boundaryComplement q U V).ι ⁻¹ᵁ (q ⁻¹ᵁ U) := by
  ext x
  constructor
  · intro hx
    exact (boundaryComplement_inf_preimage q U V hUV).le ⟨x.property, hx⟩
  · intro hx
    exact hUV hx

/-- If the modification is unchanged over `U`, the original open itself maps
to the complementary open by the inverse of the literal restricted morphism. -/
def originalOpenToBoundaryComplement {X B : Scheme.{u}} (q : B ⟶ X)
    (U V : X.Opens) [IsIso (q ∣_ U)] :
    U.toScheme ⟶ (boundaryComplement q U V).toScheme :=
  inv (q ∣_ U) ≫ B.homOfLE (preimage_le_boundaryComplement q U V)

/-- The original-open lift preserves its given map to the original base. -/
@[reassoc (attr := simp)]
lemma originalOpenToBoundaryComplement_ι {X B : Scheme.{u}} (q : B ⟶ X)
    (U V : X.Opens) [IsIso (q ∣_ U)] :
    originalOpenToBoundaryComplement q U V ≫ (boundaryComplement q U V).ι ≫ q = U.ι := by
  rw [originalOpenToBoundaryComplement, Category.assoc, ← Category.assoc _ _ q,
    Scheme.homOfLE_ι, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- Separation places the actual closed schematic image inside the
complementary open on the base. -/
lemma image_range_subset_boundaryComplement {X B Z Y : Scheme.{u}}
    (q : B ⟶ X) (p : Z ⟶ B) (f : Y ⟶ Z) [QuasiCompact f]
    (U V : X.Opens)
    (hsep : Disjoint (closure (Set.range f))
      (p ⁻¹' closure (q ⁻¹' ((V : Set X) \ (U : Set X))))) :
    Set.range (f.imageι ≫ p) ⊆ boundaryComplement q U V := by
  rintro _ ⟨x, rfl⟩
  change p (f.imageι x) ∉ closure (q ⁻¹' ((V : Set X) \ (U : Set X)))
  have hx : f.imageι x ∈ closure (Set.range f) := by
    rw [← f.support_ker]
    exact (Scheme.IdealSheafData.range_subschemeι f.ker).le ⟨x, rfl⟩
  exact Set.disjoint_left.mp hsep hx

/-- The native scheme morphism from the actual schematic image to the
complementary open, supplied by the universal property of an open immersion. -/
def imageToBoundaryComplement {X B Z Y : Scheme.{u}}
    (q : B ⟶ X) (p : Z ⟶ B) (f : Y ⟶ Z) [QuasiCompact f]
    (U V : X.Opens)
    (hsep : Disjoint (closure (Set.range f))
      (p ⁻¹' closure (q ⁻¹' ((V : Set X) \ (U : Set X))))) :
    f.image ⟶ (boundaryComplement q U V).toScheme :=
  IsOpenImmersion.lift (boundaryComplement q U V).ι (f.imageι ≫ p) (by
    rw [Scheme.Opens.range_ι]
    exact image_range_subset_boundaryComplement q p f U V hsep)

@[reassoc (attr := simp)]
lemma imageToBoundaryComplement_ι {X B Z Y : Scheme.{u}}
    (q : B ⟶ X) (p : Z ⟶ B) (f : Y ⟶ Z) [QuasiCompact f]
    (U V : X.Opens)
    (hsep : Disjoint (closure (Set.range f))
      (p ⁻¹' closure (q ⁻¹' ((V : Set X) \ (U : Set X))))) :
    imageToBoundaryComplement q p f U V hsep ≫ (boundaryComplement q U V).ι =
      f.imageι ≫ p :=
  IsOpenImmersion.lift_fac _ _ _

/-- Actual ideal choice produces the initial proper modification and the
closed-image factor needed for the two-open argument. The displayed image is
that of the literal base-changed original immersion. -/
theorem exists_boundaryComplement_image_factor {X Z Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNoetherian Z]
    (p : Z ⟶ X) (f : Y ⟶ Z) [IsImmersion f] [QuasiCompact f]
    (U V : X.Opens) (hUV : U ≤ V) (hfU : Set.range (f ≫ p) ⊆ U)
    (hclosed : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ I₁ I₂ : X.IdealSheafData,
      let B := blowupDatum (I₁ ⊔ I₂)
      let W := boundaryComplement B.map U V
      let f' := pullback.snd f (pullback.fst p B.map)
      IsProper B.map ∧ IsIso (B.map ∣_ V) ∧
        (B.map ⁻¹ᵁ U ≤ W) ∧ (W ⊓ B.map ⁻¹ᵁ V = B.map ⁻¹ᵁ U) ∧
        ∃ g : f'.image ⟶ W.toScheme, g ≫ W.ι = f'.imageι ≫ pullback.snd p B.map := by
  obtain ⟨I₁, I₂, _, _, _, _, hproper, hiso, hsep⟩ :=
    exists_canonical_boundary_separation p f U V hUV hfU hclosed
  refine ⟨I₁, I₂, hproper, hiso, preimage_le_boundaryComplement _ U V,
    boundaryComplement_inf_preimage _ U V hUV, ?_⟩
  exact ⟨imageToBoundaryComplement _ _ _ U V hsep,
    imageToBoundaryComplement_ι _ _ _ U V hsep⟩

/-- A centre on the complementary open, trivial over the lifted `U`, extends
by its actual schematic-image ideal to a centre trivial over the whole lifted
`V`. The restriction is the original ideal, not merely the same support.
The corresponding cartesian blowup restriction is `extendedCentre_isPullback`. -/
theorem boundaryComplement_extendCentre {X B : Scheme.{u}} [IsLocallyNoetherian B]
    (q : B ⟶ X) (U V : X.Opens) (hUV : U ≤ V)
    [QuasiCompact (boundaryComplement q U V).ι]
    (J : (boundaryComplement q U V).toScheme.IdealSheafData)
    (hJ : J.comap ((boundaryComplement q U V).ι ⁻¹ᵁ (q ⁻¹ᵁ U)).ι = ⊤) :
    let I := J.map (boundaryComplement q U V).ι
    I.comap (boundaryComplement q U V).ι = J ∧ I.comap (q ⁻¹ᵁ V).ι = ⊤ ∧
      IsProper (blowupDatum I).map ∧ IsIso ((blowupDatum I).map ∣_ (q ⁻¹ᵁ V)) := by
  have hJV : J.comap ((boundaryComplement q U V).ι ⁻¹ᵁ (q ⁻¹ᵁ V)).ι = ⊤ := by
    rw [boundaryComplement_preimage_protected q U V hUV]
    exact hJ
  refine ⟨J.comap_map_of_isOpenImmersion _,
    J.map_comap_eq_top_of_comap_eq_top _ _ hJV,
    (blowupDatum _).isProper_of_isLocallyNoetherian,
    extendedCentre_restrict_isIso _ _ J hJV⟩

end AlgebraicGeometry.Scheme.Blowup
