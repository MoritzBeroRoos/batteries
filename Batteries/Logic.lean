/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn, Mario Carneiro
-/
import Batteries.Tactic.Alias

instance {f : α → β} [DecidablePred p] : DecidablePred (p ∘ f) :=
  inferInstanceAs <| DecidablePred fun x => p (f x)

/-! ## id -/

theorem Function.id_def : @id α = fun x => x := rfl

/-! ## decidable -/

protected alias ⟨Decidable.exists_not_of_not_forall, _⟩ := Decidable.not_forall

/-! ## classical logic -/

namespace Classical

alias ⟨exists_not_of_not_forall, _⟩ := not_forall

end Classical

/-! ## equality -/

theorem heq_iff_eq {a b : α} : a ≍ b ↔ a = b := ⟨eq_of_heq, heq_of_eq⟩

@[simp] theorem eq_rec_constant {α : Sort _} {a a' : α} {β : Sort _} (y : β) (h : a = a') :
    (@Eq.rec α a (fun _ _ => β) y a' h) = y := by cases h; rfl

theorem congrArg₂ (f : α → β → γ) {x x' : α} {y y' : β}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by subst hx hy; rfl

theorem congrFun₂ {β : α → Sort _} {γ : ∀ a, β a → Sort _}
    {f g : ∀ a b, γ a b} (h : f = g) (a : α) (b : β a) :
    f a b = g a b :=
  congrFun (congrFun h _) _

theorem congrFun₃ {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}
      {f g : ∀ a b c, δ a b c} (h : f = g) (a : α) (b : β a) (c : γ a b) :
    f a b c = g a b c :=
  congrFun₂ (congrFun h _) _ _

theorem funext₂ {β : α → Sort _} {γ : ∀ a, β a → Sort _}
    {f g : ∀ a b, γ a b} (h : ∀ a b, f a b = g a b) : f = g :=
  funext fun _ => funext <| h _

theorem funext₃ {β : α → Sort _} {γ : ∀ a, β a → Sort _} {δ : ∀ a b, γ a b → Sort _}
    {f g : ∀ a b c, δ a b c} (h : ∀ a b c, f a b c = g a b c) : f = g :=
  funext fun _ => funext₂ <| h _

protected theorem Eq.congr (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁; subst h₂; rfl

theorem Eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]

theorem Eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

alias congr_arg := congrArg
alias congr_arg₂ := congrArg₂
alias congr_fun := congrFun
alias congr_fun₂ := congrFun₂
alias congr_fun₃ := congrFun₃

theorem heq_of_cast_eq : ∀ (e : α = β) (_ : cast e a = a'), a ≍ a'
  | rfl, rfl => .rfl

theorem cast_eq_iff_heq : cast e a = a' ↔ a ≍ a' :=
  ⟨heq_of_cast_eq _, fun h => by cases h; rfl⟩

theorem eqRec_eq_cast {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a rfl) {a' : α} (e : a = a') :
    @Eq.rec α a motive x a' e = cast (e ▸ rfl) x := by
  subst e; rfl

--Porting note: new theorem. More general version of `eqRec_heq`
theorem eqRec_heq_self {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    (x : motive a rfl) {a' : α} (e : a = a') : @Eq.rec α a motive x a' e ≍ x := by
  subst e; rfl

@[simp]
theorem eqRec_heq_iff_heq {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    {x : motive a rfl} {a' : α} {e : a = a'} {β : Sort _} {y : β} :
    @Eq.rec α a motive x a' e ≍ y ↔ x ≍ y := by
  subst e; rfl

@[simp]
theorem heq_eqRec_iff_heq {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}
    {x : motive a rfl} {a' : α} {e : a = a'} {β : Sort _} {y : β} :
    y ≍ @Eq.rec α a motive x a' e ↔ y ≍ x := by
  subst e; rfl

/-! ## miscellaneous -/

@[simp] theorem not_nonempty_empty  : ¬Nonempty Empty := fun ⟨h⟩ => h.elim
@[simp] theorem not_nonempty_pempty : ¬Nonempty PEmpty := fun ⟨h⟩ => h.elim

-- TODO(Mario): profile first, this is a dangerous instance
-- instance (priority := 10) {α} [Subsingleton α] : DecidableEq α
--   | a, b => isTrue (Subsingleton.elim a b)

-- TODO(Mario): profile adding `@[simp]` to `eq_iff_true_of_subsingleton`

/-- If all points are equal to a given point `x`, then `α` is a subsingleton. -/
theorem subsingleton_of_forall_eq (x : α) (h : ∀ y, y = x) : Subsingleton α :=
  ⟨fun a b => h a ▸ h b ▸ rfl⟩

theorem subsingleton_iff_forall_eq (x : α) : Subsingleton α ↔ ∀ y, y = x :=
  ⟨fun _ y => Subsingleton.elim y x, subsingleton_of_forall_eq x⟩

theorem congr_eqRec {β : α → Sort _} (f : (x : α) → β x → γ) (h : x = x') (y : β x) :
  f x' (Eq.rec y h) = f x y := by cases h; rfl
