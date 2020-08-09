import tactic
import data.setoid.basic
import data.real.basic
import data.set
import topology.metric_space.basic

namespace apartness

@[class]
structure setoid_ppapart (α : Type) extends setoid α :=
(ar : α → α → Prop)
(ar_not_r : ∀ x y, ar x y → ¬ setoid.r x y)
(ar_symm : ∀ x y, ar x y → ar y x)

variables (α : Type) [setoid_ppapart α] (S : set α)

def logical_complement : set α :=
{x | ∀ y ∈ S, ¬ setoid.r x y}

def complement : set α :=
{x | ∀ y ∈ S, setoid_ppapart.ar x y}

end apartness

namespace point_set_apartness

@[class]
structure point_set_apartness_space (α : Type) extends apartness.setoid_ppapart α :=
(apart : α → set α → Prop)
(ar_to_apart : ∀ x y, apartness.setoid_ppapart.ar x y → apart x {y})
(apart_to_nin : ∀ x A, apart x A → x ∉ A)
(apart_union_iff_apart_and_apart : ∀ x A B, apart x (A ∪ B) ↔ apart x A ∧ apart x B)
(apart_conj_to_apart : ∀ x A B, apart x A ∧ {x' | apart x' A} ⊆ apartness.complement α B → apart x B)
(apart_to_or_apart : ∀ x A, apart x A → ∀ y, apartness.setoid_ppapart.ar x y ∨ apart y A)

def real_ar : ℝ → ℝ → Prop :=
λ x y, x ≠ y

@[instance]
lemma real_ppapart : point_set_apartness_space ℝ := { r := λ x y, x = y,
  iseqv := eq_equivalence,
  ar := λ x y, x ≠ y,
  ar_not_r := λ _ _ _, by finish,
  ar_symm := λ _ _ _, by finish,
  apart := λ x A, x ∉ A,
  ar_to_apart := λ _ _ _ _, by finish,
  apart_to_nin := λ _ _ p, p,
  apart_union_iff_apart_and_apart := by finish,
  apart_conj_to_apart := λ x A B l l', l.1 (false.rec (x ∈ A) ((l.2 l.1 x l') rfl)),
  apart_to_or_apart := by finish, }

@[simp]
lemma ne_cotransitive (X : Type) : ∀ x z : X, x ≠ z → (∀ y : X, x ≠ y ∨ y ≠ z) :=
by finish

def apart (X : Type) (w : point_set_apartness_space X) :=
w.apart

def set_diff (X : Type) (w : point_set_apartness_space X) : set X → set X → set X :=
λ A S, A ∩ {x | (apart X w x S)}

def near (X : Type) (w : point_set_apartness_space X) :=
λ x A, ∀ S, (apart X w x S → ∃ y, y ∈ set_diff X w A S)

end point_set_apartness