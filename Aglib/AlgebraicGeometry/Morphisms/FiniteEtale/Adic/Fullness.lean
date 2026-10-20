/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.Affine
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Fullness of finite-etale closed-quotient pullback over a complete base
-/

@[expose] public section


noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange mk)
universe u
variable (R : Type u) [CommRing R]

instance cover_affine (Y : Scheme.FiniteEtale (Spec (.of R))) : IsAffine Y.obj.left :=
  isAffine_of_isAffineHom Y.obj.hom

/-- The global-section ring of a finite étale scheme over `Spec R`. -/
abbrev sections (Y : Scheme.FiniteEtale (Spec (.of R))) : CommRingCat := Γ(Y.obj.left, ⊤)

/-- The actual structural morphism gives the coordinate algebra over the base. -/
@[instance_reducible] def sectionsAlgebra (Y : Scheme.FiniteEtale (Spec (.of R))) :
    Algebra R (sections R Y) :=
  (Spec.preimage (Y.obj.left.isoSpec.inv ≫ Y.obj.hom)).hom.toAlgebra

/-- The base `R`-algebra structure on the section ring induced by the finite étale structure
morphism. -/
local instance (Y : Scheme.FiniteEtale (Spec (.of R))) : Algebra R (sections R Y)
  := sectionsAlgebra R Y

theorem sections_over (Y : Scheme.FiniteEtale (Spec (.of R))) :
    Y.obj.left.isoSpec.inv ≫ Y.obj.hom = Spec.algebraMap R (sections R Y) := by
  symm
  change Spec.map (Spec.preimage (Y.obj.left.isoSpec.inv ≫ Y.obj.hom)) = _
  exact Spec.map_preimage _

instance sections_spec_finite (Y : Scheme.FiniteEtale (Spec (.of R))) :
    IsFinite (Spec.algebraMap R (sections R Y)) := by
  rw [← sections_over R Y]
  infer_instance

instance sections_spec_etale (Y : Scheme.FiniteEtale (Spec (.of R))) :
    Etale (Spec.algebraMap R (sections R Y)) := by
  rw [← sections_over R Y]
  infer_instance

instance sections_finite (Y : Scheme.FiniteEtale (Spec (.of R))) : Module.Finite R (sections R Y) :=
  RingHom.finite_algebraMap.mp
    ((AlgebraicGeometry.IsFinite.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R (sections R Y)))).mp inferInstance)

instance sections_etale (Y : Scheme.FiniteEtale (Spec (.of R))) : Algebra.Etale R (sections R Y) :=
  RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp (sections_spec_etale R Y))

/-- The finite etale affine coordinate model of the actual cover. -/
def specCover (Y : Scheme.FiniteEtale (Spec (.of R))) : Scheme.FiniteEtale (Spec (.of R)) :=
  mk (Spec.algebraMap R (sections R Y))

/-- The actual cover is isomorphic over the base to its coordinate model. -/
def specCoverIso (Y : Scheme.FiniteEtale (Spec (.of R))) : specCover R Y ≅ Y :=
  ObjectProperty.isoMk _ (Over.isoMk Y.obj.left.isoSpec.symm (sections_over R Y))


/-- Closed-fibre base change on the actual finite-etale scheme category is full
for a Noetherian adically complete base. No cohomological injectivity is assumed. -/
instance quotient_baseChange_full [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] :
    (baseChange (Spec.algebraMap R (R ⧸ I))).Full where
  map_surjective {Y Z} φ := by
    let F := baseChange (Spec.algebraMap R (R ⧸ I))
    let eY := specCoverIso R Y
    let eZ := specCoverIso R Z
    let φ' : F.obj (specCover R Y) ⟶ F.obj (specCover R Z) :=
      F.map eY.hom ≫ φ ≫ F.map eZ.inv
    have : Module.Finite R (sections R Y) := sections_finite R Y
    have : Algebra.Etale R (sections R Z) := sections_etale R Z
    obtain ⟨g, hg⟩ := affine_fibre_hom_lift (R := R) (A := sections R Z) (B := sections R Y)
      I φ'.hom.left (Over.w φ'.hom)
    let gC : specCover R Y ⟶ specCover R Z :=
      ⟨Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (Spec.map_algHom_algebraMap g)⟩
    have hgc : F.map gC = φ' := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change fibreMap (T := R ⧸ I) g = φ'.hom.left
      exact hg
    refine ⟨eY.inv ≫ gC ≫ eZ.hom, ?_⟩
    change F.map (eY.inv ≫ gC ≫ eZ.hom) = φ
    rw [Functor.map_comp, Functor.map_comp, hgc]
    calc
      _ = φ ≫ 𝟙 (F.obj Z) := by
        simp only [φ', Category.assoc, Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id]
      _ = φ := Category.comp_id φ

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/Adic/Fullness.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 e10dbe06b1047bffc0b52da23e8a23d692bf8347708968e8bc5fd7a96e52c233.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
