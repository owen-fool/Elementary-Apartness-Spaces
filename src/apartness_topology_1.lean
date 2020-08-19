import tactic
import topology.basic
import apartness_spaces

variables (X : Type) (τ : topological_space X)

namespace top_apart

def apart (x : X) (A : set X) : Prop :=
∃ U : set X, (τ.is_open U) ∧ (x ∈ U ∧ U ⊆ {z | ∀ y, y ∈ A → z ≠ y})

def apartness_complement (S : set X) : set X :=
{x | apart X τ x S}

def apartness_difference (A : set X) (S : set X) : set X :=
A ∩ (apartness_complement X τ S)

def near (x : X) (A : set X) : Prop :=
∀ S : set X, x ∈ (apartness_complement X τ S) → ∃ y : X, y ∈ (apartness_difference X τ A S)

variable (A5 : ∀ (x : X) (A : set X), apart X τ x A → (∀ y : X, x ≠ y ∨ apart X τ y A))

open point_set_apartness

@[instance]
lemma topological_apartness_structure 
(TTA₁ : ∀ (x y : X), x ≠ y → ∃ (U V : set X), 
                                     (τ.is_open U ∧ τ.is_open V)
                                   ∧ (x ∈ U ∧ y ∉ U)
                                   ∧ (x ∉ V ∧ y ∈ V))
: point_set_apartness_space X :=
{ r := λ x y, x = y,
  iseqv := eq_equivalence,
  ar := λ x y, x ≠ y,
  ar_not_r := λ _ _ p, p,
  ar_symm := λ _ _ p, by finish,
  apart := apart X τ,
  ar_to_apart := begin
    intros x y p,
    unfold apart,
    have h := TTA₁ x y p,
    cases h with U h,
    cases h with V h,
    cases h with h0 h1,
    cases h0 with oU oV,
    cases h1 with h0 h1,
    use U,
    split,
    exact oU,
    split,
    exact h0.1,
    intros hh hhi y' hy' hhhy',
    apply h0.2,
    cases hy',
    rw ← hhhy',
    exact hhi
  end,
  apart_to_nin := begin
    intros x A axA,
    cases axA with U hUA,
    cases hUA with oU huA,
    cases huA with hUx hUA,
    intro hxA,
    specialize hUA hUx x hxA,
    apply hUA,
    refl,
  end,
  apart_union_iff_apart_and_apart := begin
    intros x A B,
    split,
    intro axAB,
    cases axAB with U axAB,
    cases axAB with oU axAB,
    cases axAB with hxU axAB,
    split,
    use U,
    split,
    exact oU,
    split,
    exact hxU,
    intros x' hx',
    specialize axAB hx',
    intros y' hy',
    specialize axAB y',
    apply axAB,
    exact set.mem_union_left B hy',
    use U,
    split,
    exact oU,
    split,
    exact hxU,
    intros x' hx',
    specialize axAB hx',
    intros y' hy',
    specialize axAB y',
    apply axAB,
    exact set.mem_union_right A hy',
    intro h,
    cases h with h1 h2,
    cases h1 with U h1,
    cases h2 with U' h2,
    cases h1 with oU h1,
    cases h2 with oU' h2,
    cases h1 with hxU h1,
    cases h2 with hxU' h2,
    use U ∩ U',
    split,
    exact topological_space.is_open_inter τ U U' oU oU',
    split,
    split,
    exact hxU,
    exact hxU',
    intros x'' hx'',
    cases hx'' with hx''1 hx''2,
    intros y hy,
    specialize h1 hx''1,
    specialize h2 hx''2,
    cases hy,
    exact h1 y hy,
    exact h2 y hy,
  end,
  apart_conj_to_apart := begin
    intros x A B h,
    cases h with h1 h2,
    dsimp at *,
    unfold apartness.complement at h2,
    unfold apart,
    cases h1 with U h1,
    cases h1 with hU h1,
    cases h1 with korn h1,
    use U,
    split,
    exact hU,
    split,
    exact korn,
    intros x' hx' y hy,
    apply h2,
    use U,
    split,
    exact hU,
    split,
    exact hx',
    exact h1,
    exact hy,
  end,
  apart_to_or_apart := A5 }
-- possibly need to refactor so that these definitions can be accessed



end top_apart