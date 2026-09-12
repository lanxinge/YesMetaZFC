import YesMetaZFC.Model.Boolean.Algebra

namespace ZFResearch
open YesMetaZFC.Model.Boolean

def SP := {p : Prop // (¬¬p) → p}

def sp_alg : CB_alg SP where
  le p q := p.1 → q.1
  bot := ⟨False, fun h => h id⟩
  le_refl _ := id
  le_trans h k := k ∘ h
  le_antisymm h k := Subtype.ext (propext ⟨h, k⟩)
  bot_le _ := False.elim
  meet p q := ⟨p.1 ∧ q.1, fun h =>
    ⟨p.2 (fun hn => h (fun hpq => hn hpq.1)),
     q.2 (fun hn => h (fun hpq => hn hpq.2))⟩⟩
  imp p q := ⟨p.1 → q.1, fun h hp => q.2 (fun hn => h (fun f => hn (f hp)))⟩
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩,
    fun ⟨h, k⟩ hp => ⟨h hp, k hp⟩⟩
  le_imp_iff _ _ _ := ⟨fun h ⟨hp, hq⟩ => h hp hq, fun h hp hq => h ⟨hp, hq⟩⟩
  double_neg p := Subtype.ext (propext ⟨p.2, fun h hn => hn h⟩)
  sup p := ⟨¬¬∃ q, p q ∧ q.1, fun h hn => h (fun hp => hp hn)⟩
  sup_le_iff _ a := ⟨fun h q hq hq' => h (fun hn => hn ⟨q, hq, hq'⟩),
    fun h hp => a.2 (fun hn => hp (fun ⟨q, hq, hq'⟩ => hn (h q hq hq')))⟩

theorem sp_nontrivial : ¬ sp_alg.le sp_alg.top sp_alg.bot := fun h => h id

/-- 两个稳定真值覆盖顶元，却不提供元层的二选一见证。 -/
def sp_split (p : Prop) : Bool → SP
  | false => ⟨¬p, fun h hp => h (fun hn => hn hp)⟩
  | true => ⟨¬¬p, fun h hn => h (fun hnn => hnn hn)⟩

theorem sp_split_sup (p : Prop) : sp_alg.le sp_alg.top (sp_alg.iSup (sp_split p)) := by
  intro _ hn
  apply hn
  refine ⟨sp_split p true, ⟨true, rfl⟩, ?_⟩
  intro hp
  apply hn
  exact ⟨sp_split p false, ⟨false, rfl⟩, hp⟩

theorem sp_split_witness (p : Prop) :
    (∃ b, sp_alg.le sp_alg.top (sp_split p b)) ↔ ¬p ∨ ¬¬p := by
  constructor
  · intro ⟨b, h⟩
    cases b with
    | false => exact Or.inl (h id)
    | true => exact Or.inr (h id)
  · intro h
    cases h with
    | inl h => exact ⟨false, fun _ => h⟩
    | inr h => exact ⟨true, fun _ => h⟩

#print axioms sp_alg
#print axioms sp_nontrivial
#print axioms sp_split_sup
#print axioms sp_split_witness
end ZFResearch
