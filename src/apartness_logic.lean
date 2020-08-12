import tactic
import apartness_spaces

open point_set_apartness

open apartness

lemma napart_of_near (X : Type) (w : point_set_apartness_space X) (A : set X) :
∀ x, near X x A → ¬ apart X x A := 
begin
intros x h h',
specialize h A h',
cases h with y h,
cases h with yh Ah,
dsimp at *,
apply apart_to_nin X y A Ah yh,
end

lemma set_prop_in_iff_prop (X : Type) (p : Prop) (x : X) : x ∈ {i : X | p} ↔ p :=
begin
simp,
end

lemma set_prop_nin_iff_not (X : Type) (p : Prop) (x : X) : x ∉ {i : X | p} ↔ ¬ p :=
begin
split,
{
    intros h ph,
    apply h,
    exact ph,
},
{
    intros ph h,
    apply ph,
    exact h,
}
end

lemma doub_neg_of_napart_near_equiv :
(∀ A x, real_near x A ↔ ¬ real_apart x A) → (∀ p : Prop, ¬ ¬ p → p) :=
begin
intros h p,
specialize h {x | p},
intro ph,
have hapart : ∀ x : ℝ, ¬ real_apart x {x : ℝ | p},
{
    intros x hx,
    apply ph,
    rw ← set_prop_nin_iff_not ℝ p x,
    exact hx, 
},
have hnear : ∀ x : ℝ, real_near x {i : ℝ | p},
{
    intro x,
    exact (h x).2 (hapart x),
},
specialize hnear 0 {1} (by finish),
cases hnear with y hy,
cases hy with hy1 hy2,
exact (set_prop_in_iff_prop ℝ p y).1 hy1,
end