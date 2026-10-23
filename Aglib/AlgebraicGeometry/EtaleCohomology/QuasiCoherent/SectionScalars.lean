/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections

/-!
# Semilinearity of the original quasi-coherent section restrictions

The scalar map is the original map on scheme global sections. This does not
choose or replace a ring-valued coefficient on the étale site.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The original geometric unit is semilinear for the original map of section rings. -/
theorem pullbackUnitSections_smul {U V : Scheme.{u}} (f : U ⟶ V) (M : V.Modules)
    (r : Γ(V, ⊤)) (s : Γ(M, ⊤)) :
    (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) (r • s) =
      SMul.smul (M := Γ(U, ⊤)) (α := Γ((pullback f).obj M, ⊤))
        (f.appTop.hom r) ((((pullbackPushforwardAdjunction f).unit.app M).app ⊤) s) :=
  Scheme.Modules.Hom.app_smul ((pullbackPushforwardAdjunction f).unit.app M) r s

/-- The unit-Hom description of pullback has the same genuine semilinearity. -/
theorem nativeSectionPullback_smul {U V : Scheme.{u}} (f : U ⟶ V) (M : V.Modules)
    (r : Γ(V, ⊤)) (s : Γ(M, ⊤)) :
    nativeSectionPullback f M (r • s) = f.appTop.hom r • nativeSectionPullback f M s := by
  rw [nativeSectionPullback_eq_unit, nativeSectionPullback_eq_unit]
  exact pullbackUnitSections_smul f M r s

/-- Native coefficient morphisms commute with the actual section pullback. -/
theorem nativeSectionPullback_naturality {U V : Scheme.{u}} (f : U ⟶ V)
    {M N : V.Modules} (g : M ⟶ N) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((pullback f).map g) ⊤ (nativeSectionPullback f M s) =
      nativeSectionPullback f N (Scheme.Modules.Hom.app g ⊤ s) := by
  rw [nativeSectionPullback_eq_unit, nativeSectionPullback_eq_unit]
  exact (congrArg (fun q => Scheme.Modules.Hom.app q ⊤ s)
    ((pullbackPushforwardAdjunction f).unit.naturality g)).symm

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]

/-- The actual over-site restriction is semilinear for the original scheme-section map. -/
theorem sectionsPresheaf_map_smul {T U : Over X} (f : U ⟶ T)
    (r : Γ(T.left, ⊤)) (s : Γ((pullback T.hom).obj F, ⊤)) :
    (sectionsPresheaf X F).map f.op (r • s) =
      SMul.smul (M := Γ(U.left, ⊤)) (α := Γ((pullback U.hom).obj F, ⊤))
        (f.left.appTop.hom r) ((sectionsPresheaf X F).map f.op s) := by
  rw [sectionsPresheaf_map_eq, sectionsPresheaf_map_eq, pullbackUnitSections_smul]
  exact Scheme.Modules.Hom.app_smul _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
