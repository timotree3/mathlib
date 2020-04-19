/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.natural_isomorphism

-- run_cmd (do tactic.unsafe_run_io (tcache.rm_cache_dir >> tcache.mk_cache_dir))
cache_file?
-- cache_clear

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section
variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
          {E : Type u₃} [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

@[simps] def whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) : (F ⋙ G) ⟶ (F ⋙ H) :=
{ app := λ c, α.app (F.obj c),
  naturality' := λ X Y f, by rw [functor.comp_map, functor.comp_map, α.naturality] }

@[simps] def whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : (G ⋙ F) ⟶ (H ⋙ F) :=
{ app := λ c, F.map (α.app c),
  naturality' := λ X Y f, by rw [functor.comp_map, functor.comp_map, ←F.map_comp, ←F.map_comp, α.naturality] }

variables (C D E)

@[simps] def whiskering_left : (C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E)) :=
{ obj := λ F,
  { obj := λ G, F ⋙ G,
    map := λ G H α, whisker_left F α },
  map := λ F G τ,
  { app := λ H,
    { app := λ c, H.map (τ.app c),
      naturality' := λ X Y f, begin dsimp, rw [←H.map_comp, ←H.map_comp, ←τ.naturality] end },
    naturality' := λ X Y f, begin ext, dsimp, rw [f.naturality] end } }

@[simps] def whiskering_right : (D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E)) :=
{ obj := λ H,
  { obj := λ F, F ⋙ H,
    map := λ _ _ α, whisker_right α H },
  map := λ G H τ,
  { app := λ F,
    { app := λ c, τ.app (F.obj c),
      naturality' := λ X Y f, begin dsimp, rw [τ.naturality] end },
    naturality' := λ X Y f, begin ext, dsimp, rw [←nat_trans.naturality] end } }

variables {C} {D} {E}

@[simp] lemma whisker_left_id (F : C ⥤ D) {G : D ⥤ E} :
  whisker_left F (nat_trans.id G) = nat_trans.id (F.comp G) :=
rfl
@[simp] lemma whisker_left_id' (F : C ⥤ D) {G : D ⥤ E} :
  whisker_left F (𝟙 G) = 𝟙 (F.comp G) :=
rfl

@[simp] lemma whisker_right_id {G : C ⥤ D} (F : D ⥤ E) :
  whisker_right (nat_trans.id G) F = nat_trans.id (G.comp F) :=
((whiskering_right C D E).obj F).map_id _
@[simp] lemma whisker_right_id' {G : C ⥤ D} (F : D ⥤ E) :
  whisker_right (𝟙 G) F = 𝟙 (G.comp F) :=
((whiskering_right C D E).obj F).map_id _

@[simp] lemma whisker_left_comp (F : C ⥤ D) {G H K : D ⥤ E} (α : G ⟶ H) (β : H ⟶ K) :
  whisker_left F (α ≫ β) = (whisker_left F α) ≫ (whisker_left F β) :=
rfl

@[simp] lemma whisker_right_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E)  :
  whisker_right (α ≫ β) F = (whisker_right α F) ≫ (whisker_right β F) :=
((whiskering_right C D E).obj F).map_comp α β

def iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : (F ⋙ G) ≅ (F ⋙ H) :=
((whiskering_left C D E).obj F).map_iso α
@[simp] lemma iso_whisker_left_hom (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).hom = whisker_left F α.hom :=
rfl
@[simp] lemma iso_whisker_left_inv (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) :
  (iso_whisker_left F α).inv = whisker_left F α.inv :=
rfl

def iso_whisker_right {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : (G ⋙ F) ≅ (H ⋙ F) :=
((whiskering_right C D E).obj F).map_iso α
@[simp] lemma iso_whisker_right_hom {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).hom = whisker_right α.hom F :=
rfl
@[simp] lemma iso_whisker_right_inv {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
  (iso_whisker_right α F).inv = whisker_right α.inv F :=
rfl

instance is_iso_whisker_left (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [is_iso α] : is_iso (whisker_left F α) :=
{ .. iso_whisker_left F (as_iso α) }
instance is_iso_whisker_right {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [is_iso α] : is_iso (whisker_right α F) :=
{ .. iso_whisker_right (as_iso α) F }

variables {B : Type u₄} [ℬ : category.{v₄} B]
include ℬ

local attribute [elab_simple] whisker_left whisker_right

@[simp] lemma whisker_left_twice (F : B ⥤ C) (G : C ⥤ D) {H K : D ⥤ E} (α : H ⟶ K) :
  whisker_left F (whisker_left G α) = whisker_left (F ⋙ G) α :=
rfl

@[simp] lemma whisker_right_twice {H K : B ⥤ C} (F : C ⥤ D) (G : D ⥤ E) (α : H ⟶ K) :
  whisker_right (whisker_right α F) G = whisker_right α (F ⋙ G) :=
rfl

lemma whisker_right_left (F : B ⥤ C) {G H : C ⥤ D} (α : G ⟶ H) (K : D ⥤ E) :
  whisker_right (whisker_left F α) K = whisker_left F (whisker_right α K) :=
rfl
end

namespace functor

universes u₅ v₅

variables {A : Type u₁} [𝒜 : category.{v₁} A]
variables {B : Type u₂} [ℬ : category.{v₂} B]
include 𝒜 ℬ

@[simps] def left_unitor (F : A ⥤ B) : ((𝟭 _) ⋙ F) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

@[simps] def right_unitor (F : A ⥤ B) : (F ⋙ (𝟭 _)) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

variables {C : Type u₃} [𝒞 : category.{v₃} C]
variables {D : Type u₄} [𝒟 : category.{v₄} D]
include 𝒞 𝒟

@[simps] def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) : ((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H)) :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

omit 𝒟

lemma triangle (F : A ⥤ B) (G : B ⥤ C) :
  (associator F (𝟭 B) G).hom ≫ (whisker_left F (left_unitor G).hom) =
    (whisker_right (right_unitor F).hom G) :=
by { ext, dsimp, simp }

variables {E : Type u₅} [ℰ : category.{v₅} E]
include 𝒟 ℰ

variables (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

lemma pentagon :
  (whisker_right (associator F G H).hom K) ≫ (associator F (G ⋙ H) K).hom ≫ (whisker_left F (associator G H K).hom) =
    ((associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom) :=
by { ext, dsimp, simp }

end functor

end category_theory
