import YesMetaZFC.Model.SmallGraph.Closure

namespace Zf_research

/-- 两点图仅在 p 成立时含一条边；其构造和良基性均无需判定 p。 -/
def Fr_edge (p : Prop) (a b : Bool) : Prop := a = false ∧ b = true ∧ p

def fr_bound (b : Bool) : Nat := if b then 1 else 0

theorem fr_decreases (p : Prop) {a b : Bool} (h : Fr_edge p a b) :
    fr_bound a < fr_bound b := by
  rcases h with ⟨rfl, rfl, _⟩
  exact Nat.zero_lt_one

theorem fr_wf (p : Prop) : WellFounded (Fr_edge p) :=
  Subrelation.wf (fun h => fr_decreases p h) (InvImage.wf fr_bound Nat.lt_wfRel.wf)

theorem fr_tc (p : Prop) (a b : Bool) :
    Relation.TransGen (Fr_edge p) a b ↔ Fr_edge p a b := by
  constructor
  · intro h
    induction h with
    | single h => exact h
    | tail _ h ih =>
      rcases ih with ⟨_, e, _⟩
      rcases h with ⟨f, _, _⟩
      cases e.symm.trans f
  · exact Relation.TransGen.single

/-- Swan 秩压缩所用的精确秩像恒等式，在这张图上退化为此性质。 -/
def Fr_exact (p : Prop) (r : Bool → Nat) : Prop :=
  ∀ b k, k < r b ↔ ∃ a, Relation.TransGen (Fr_edge p) a b ∧ r a = k

/-- 若能给这张两点图一个精确自然数秩，则 p 已可判定。 -/
def fr_decidable (p : Prop) (r : Bool → Nat) (h : Fr_exact p r) : Decidable p :=
  if e : r true = 0 then
    isFalse (fun hp => by
      have hlt := (h true (r false)).mpr
        ⟨false, Relation.TransGen.single ⟨rfl, rfl, hp⟩, rfl⟩
      exact Nat.not_lt_zero _ (e ▸ hlt))
  else
    isTrue (by
      have hpos : 0 < r true := Nat.pos_of_ne_zero e
      rcases (h true 0).mp hpos with ⟨a, ha, _⟩
      exact ((fr_tc p a true).mp ha).2.2)

/-- 不是所有良基秩都受阻：严格上界 fr_bound 总存在，受阻的是精确秩像。 -/
theorem fr_exact_iff (p : Prop) : (∃ r, Fr_exact p r) ↔ p ∨ ¬ p := by
  constructor
  · rintro ⟨r, h⟩
    exact @Decidable.em p (fr_decidable p r h)
  · rintro (hp | hp)
    · refine ⟨fr_bound, fun b k => ?_⟩
      cases b
      · constructor
        · exact fun h => (Nat.not_lt_zero _ h).elim
        · rintro ⟨a, ha, _⟩
          cases ((fr_tc p a false).mp ha).2.1
      · constructor
        · intro hk
          have e : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
          exact ⟨false, Relation.TransGen.single ⟨rfl, rfl, hp⟩, e.symm⟩
        · rintro ⟨a, ha, hr⟩
          rcases (fr_tc p a true).mp ha with ⟨rfl, _, _⟩
          exact hr ▸ Nat.zero_lt_one
    · refine ⟨fun _ => 0, fun b k => ?_⟩
      exact ⟨fun h => (Nat.not_lt_zero _ h).elim,
        fun ⟨a, ha, _⟩ => (hp ((fr_tc p a b).mp ha).2.2).elim⟩

#print axioms fr_wf
#print axioms fr_exact_iff
#print axioms fr_decidable

open YesMetaZFC.Model.SmallGraph

/-- 精确的集合值秩本身并不受阻：根秩可以保留条件集合 {∅ | p}，而不判定其是否为空。 -/
theorem fr_set_rank (p : Prop) : ∃ r : Bool → SG_set.{u},
    ∀ b z, z ∈ r b ↔ ∃ a, Relation.TransGen (Fr_edge p) a b ∧ r a = z := by
  rcases SG_set.pair SG_set.empty SG_set.empty with ⟨s, hs⟩
  rcases SG_set.separation s (fun _ => p) with ⟨t, ht⟩
  refine ⟨fun b => if b then t else SG_set.empty, fun b z => ?_⟩
  cases b
  · constructor
    · exact fun hz => (SG_set.not_mem_empty z hz).elim
    · rintro ⟨a, ha, _⟩
      cases ((fr_tc p a false).mp ha).2.1
  · constructor
    · intro hz
      rcases (ht z).mp hz with ⟨hz, hp⟩
      rcases (hs z).mp hz with e | e <;>
        exact ⟨false, Relation.TransGen.single ⟨rfl, rfl, hp⟩, e.symm⟩
    · rintro ⟨a, ha, hr⟩
      rcases (fr_tc p a true).mp ha with ⟨rfl, _, hp⟩
      exact (ht z).mpr ⟨(hs z).mpr (Or.inl hr.symm), hp⟩

#print axioms fr_set_rank

/-- 实际的稳定真值载体；其等号稳定不需要排中律。 -/
def Fr_sp := {p : Prop // ¬¬p → p}

theorem fr_sp_eq_stable (p q : Fr_sp) (h : ¬¬(p = q)) : p = q := by
  apply Subtype.ext
  apply propext
  exact ⟨fun hp => q.2 (fun hn => h (fun e => hn (e ▸ hp))),
    fun hq => p.2 (fun hn => h (fun e => hn (e.symm ▸ hq)))⟩

section StableEmbedding
variable {X : Type v} (f : SG_set.{u} → X)
  (hf : ∀ {x y}, f x = f y → x = y)
  (hs : ∀ x y, ¬¬(f x = f y) → f x = f y)
include f hf hs

/-- 这是嵌入的障碍定理，不假设或宣称已经构造此嵌入。只需像中等号稳定。 -/
theorem fr_dne_of_stable_embed (p : Prop) (hn : ¬¬p) : p := by
  rcases SG_set.pair SG_set.empty SG_set.empty with ⟨s, h⟩
  rcases SG_set.separation s (fun _ => p) with ⟨a, ha⟩
  have he : a = s ↔ p := by
    constructor
    · intro e
      exact ((ha SG_set.empty).mp (e.symm ▸ (h _).mpr (Or.inl rfl))).2
    · intro hp
      exact SG_set.ext (fun z => (ha z).trans ⟨And.left, fun hz => ⟨hz, hp⟩⟩)
  apply he.mp
  apply hf
  exact hs a s (fun hne => hn (fun hp => hne (congrArg f (he.mpr hp))))

theorem fr_em_of_stable_embed (p : Prop) : p ∨ ¬p :=
  fr_dne_of_stable_embed f hf hs (p ∨ ¬p)
    (fun h => h (Or.inr (fun hp => h (Or.inl hp))))
end StableEmbedding

#print axioms fr_sp_eq_stable
#print axioms fr_dne_of_stable_embed
#print axioms fr_em_of_stable_embed

end Zf_research
