import YesMetaZFC.Model.Forcing.Applications.Cohen.Presentation

/-! # 指定坐标集上的 Cohen 位翻转

S 中的坐标交换 o、l，S 外的坐标保持原值。S 是任意内部集合，不要求它在外部
有限；有限性只施加于条件本身。逐条目翻转及整个条件的像均给出实际原公式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Cflip_val_d (S o l a b c : M.Domain) : Prop :=
  (M.mem a S ∧ ((b = o ∧ c = l) ∨ (b = l ∧ c = o))) ∨ (¬ M.mem a S ∧ c = b)

def cflip_val_m {n} (S o l a b c : Term n) : Formula 1 n :=
  .disj (.conj (.mem a S) (.disj
    (.conj (Formula.extensionalEq b o) (Formula.extensionalEq c l))
    (.conj (Formula.extensionalEq b l) (Formula.extensionalEq c o))))
    (.conj (.neg (.mem a S)) (Formula.extensionalEq c b))
derive_free_closed cflip_val_m

def Cflip_pair_d (S o l v w : M.Domain) : Prop := ∃ a b c,
  KPair_d M v a b ∧ KPair_d M w a c ∧ Cflip_val_d S o l a b c

def cflip_pair_m {n} (S o l v w : Term n) : Formula 1 n :=
  .existsE <| .existsE <| .existsE <|
    .conj (kpair_m v.weaken.weaken.weaken (.bound 2) (.bound 1)) <|
    .conj (kpair_m w.weaken.weaken.weaken (.bound 2) .newest)
      (cflip_val_m S.weaken.weaken.weaken o.weaken.weaken.weaken l.weaken.weaken.weaken
        (.bound 2) (.bound 1) .newest)
derive_free_closed cflip_pair_m

def Cflip_d (S o l p q : M.Domain) : Prop :=
  (∀ v, M.mem v q → ∃ a b, KPair_d M v a b) ∧
  ∀ v, M.mem v q ↔ ∃ w, M.mem w p ∧ Cflip_pair_d S o l w v

def cflip_m {n} (S o l p q : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l q)
    (.forallE (.iff (.mem .newest q.weaken) (.existsE
      (.conj (.mem .newest p.weaken.weaken)
        (cflip_pair_m S.weaken.weaken o.weaken.weaken l.weaken.weaken .newest (.bound 1))))))
derive_free_closed cflip_m

theorem cflip_val_sat_l (hE : Extensional M) {n} (ρ : Env M n) (S o l a b c : Term n) :
    Formula.satisfies ρ (cflip_val_m S o l a b c) ↔
      Cflip_val_d (S.eval ρ) (o.eval ρ) (l.eval ρ) (a.eval ρ) (b.eval ρ) (c.eval ρ) := by
  simp only [cflip_val_m, Cflip_val_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE]

theorem cflip_pair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (S o l v w : Term n) :
    Formula.satisfies ρ (cflip_pair_m S o l v w) ↔
      Cflip_pair_d (S.eval ρ) (o.eval ρ) (l.eval ρ) (v.eval ρ) (w.eval ρ) := by
  simp only [cflip_pair_m, Cflip_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, cflip_val_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem cflip_sat_l (hE : Extensional M) {n} (ρ : Env M n) (S o l p q : Term n) :
    Formula.satisfies ρ (cflip_m S o l p q) ↔
      Cflip_d (S.eval ρ) (o.eval ρ) (l.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [cflip_m, Cflip_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, cflip_pair_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

variable {S o l a b c d v w t p q : M.Domain}

theorem cflip_val_symm_l (h : Cflip_val_d S o l a b c) : Cflip_val_d S o l a c b := by
  rcases h with ⟨ha, ⟨hb, hc⟩ | ⟨hb, hc⟩⟩ | ⟨ha, hc⟩
  · exact Or.inl ⟨ha, Or.inr ⟨hc, hb⟩⟩
  · exact Or.inl ⟨ha, Or.inl ⟨hc, hb⟩⟩
  · exact Or.inr ⟨ha, hc.symm⟩

theorem cflip_val_unique_l (h : Cflip_val_d S o l a b c) (k : Cflip_val_d S o l a b d) : c = d := by
  rcases h with ⟨ha, ⟨hb, hc⟩ | ⟨hb, hc⟩⟩ | ⟨ha, hc⟩ <;>
    rcases k with ⟨ka, ⟨kb, kd⟩ | ⟨kb, kd⟩⟩ | ⟨ka, kd⟩
  · exact hc.trans kd.symm
  · exact hc.trans (kb.symm.trans (hb.trans kd.symm))
  · exact False.elim (ka ha)
  · exact hc.trans (kb.symm.trans (hb.trans kd.symm))
  · exact hc.trans kd.symm
  · exact False.elim (ka ha)
  · exact False.elim (ha ka)
  · exact False.elim (ha ka)
  · exact hc.trans kd.symm

theorem cflip_val_total_l {Y} (hY : Pair_d M Y o l) (hb : M.mem b Y) (S a : M.Domain) :
    ∃ c, M.mem c Y ∧ Cflip_val_d S o l a b c := by
  classical
  by_cases ha : M.mem a S
  · rcases (hY b).mp hb with rfl | rfl
    · exact ⟨l, (hY l).mpr (Or.inr rfl), Or.inl ⟨ha, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨o, (hY o).mpr (Or.inl rfl), Or.inl ⟨ha, Or.inr ⟨rfl, rfl⟩⟩⟩
  · exact ⟨b, hb, Or.inr ⟨ha, rfl⟩⟩

theorem cflip_val_target_l {Y} (hY : Pair_d M Y o l) (hb : M.mem b Y)
    (h : Cflip_val_d S o l a b c) : M.mem c Y := by
  rcases h with ⟨_, ⟨_, hc⟩ | ⟨_, hc⟩⟩ | ⟨_, hc⟩
  · exact (hY c).mpr (Or.inr hc)
  · exact (hY c).mpr (Or.inl hc)
  · exact hc.symm ▸ hb

theorem cflip_pair_symm_l (h : Cflip_pair_d S o l v w) : Cflip_pair_d S o l w v :=
  h.elim fun a ⟨b, c, hv, hw, h⟩ => ⟨a, c, b, hw, hv, cflip_val_symm_l h⟩

theorem cflip_pair_unique_l (hE : Extensional M)
    (h : Cflip_pair_d S o l v w) (k : Cflip_pair_d S o l v t) : w = t := by
  obtain ⟨a, b, c, hv, hw, h⟩ := h
  obtain ⟨a', b', d, hv', ht, k⟩ := k
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
  exact kpair_unique_l M hE ((cflip_val_unique_l h k) ▸ hw) ht

theorem cflip_unique_l (hE : Extensional M) {r} (h : Cflip_d S o l p q) (k : Cflip_d S o l p r) : q = r :=
  hE.eq_of_same_members q r (fun v => (h.2 v).trans (k.2 v).symm)

/-- 逐条目刻画把集合像转换为有限部分函数可直接消费的值关系。 -/
theorem cflip_entry_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (h : Cflip_d S o l p q) (a c) :
    Entry_d M a c q ↔ ∃ b, Entry_d M a b p ∧ Cflip_val_d S o l a b c := by
  constructor
  · rintro ⟨v, hv, hvq⟩
    obtain ⟨w, hwp, a', b, c', hw, hv', hh⟩ := (h.2 v).mp hvq
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    exact ⟨b, ⟨w, hw, hwp⟩, hh⟩
  · rintro ⟨b, ⟨w, hw, hwp⟩, hh⟩
    obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total a c
    exact ⟨v, hv, (h.2 v).mpr ⟨w, hwp, a, b, c, hw, hv, hh⟩⟩

end YesMetaZFC.Model.Forcing.Internal
