import YesMetaZFC.Model.Forcing.Internal.Forcing.Truth

/-! # 不依赖泛型的规范名称配对

每个子名称都配上全部条件作为权重，因而同一个名称在所有泛型下解释为配对。
原模型内的配对名称本身唯一，供两步名称的递归转换使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Npair_d (B a b t : M.Domain) : Prop :=
  ∀ v, M.mem v t ↔ ∃ p, M.mem p B ∧ (KPair_d M v a p ∨ KPair_d M v b p)

def npair_m {n} (B a b t : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest t.weaken) (.existsE (.conj (.mem .newest B.weaken.weaken)
    (.disj (kpair_m (.bound 1) a.weaken.weaken .newest) (kpair_m (.bound 1) b.weaken.weaken .newest)))))
derive_free_closed npair_m

def Nkpair_d (B a b t : M.Domain) : Prop :=
  ∃ s v, Npair_d M B a a s ∧ Npair_d M B a b v ∧ Npair_d M B s v t

def nkpair_m {n} (B a b t : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (npair_m B.weaken.weaken a.weaken.weaken a.weaken.weaken (.bound 1))
    (.conj (npair_m B.weaken.weaken a.weaken.weaken b.weaken.weaken .newest)
      (npair_m B.weaken.weaken (.bound 1) .newest t.weaken.weaken))))
derive_free_closed nkpair_m

theorem npair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B a b t : Term n) :
    Formula.satisfies ρ (npair_m B a b t) ↔ Npair_d M (B.eval ρ) (a.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [npair_m, Npair_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem nkpair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B a b t : Term n) :
    Formula.satisfies ρ (nkpair_m B a b t) ↔ Nkpair_d M (B.eval ρ) (a.eval ρ) (b.eval ρ) (t.eval ρ) := by
  simp only [nkpair_m, Nkpair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    npair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem npair_l (hZF : M.Models ZF) (B a b : M.Domain) : ∃ t, Npair_d M B a b t := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨D, hD⟩ := KP.exists_pair (ZF.modelsKP hZF) a b
  obtain ⟨t, ht⟩ := ZF.exists_cartesianProduct hZF I D B
  refine ⟨t, fun v => (ht v).trans ?_⟩
  constructor
  · rintro ⟨s, hs, p, hp, hv⟩
    exact ⟨p, hp, ((hD s).mp hs).elim (fun he => Or.inl (he ▸ hv)) (fun he => Or.inr (he ▸ hv))⟩
  · rintro ⟨p, hp, hv | hv⟩
    · exact ⟨a, (hD a).mpr (Or.inl rfl), p, hp, hv⟩
    · exact ⟨b, (hD b).mpr (Or.inr rfl), p, hp, hv⟩

theorem npair_unique_l (hE : Extensional M) {B a b s t} (hs : Npair_d M B a b s)
    (ht : Npair_d M B a b t) : s = t := hE.eq_of_same_members s t (fun v => (hs v).trans (ht v).symm)

theorem nkpair_l (hZF : M.Models ZF) (B a b : M.Domain) : ∃ t, Nkpair_d M B a b t := by
  obtain ⟨s, hs⟩ := npair_l M hZF B a a
  obtain ⟨v, hv⟩ := npair_l M hZF B a b
  obtain ⟨t, ht⟩ := npair_l M hZF B s v
  exact ⟨t, s, v, hs, hv, ht⟩

theorem nkpair_unique_l (hE : Extensional M) {B a b s t} (hs : Nkpair_d M B a b s)
    (ht : Nkpair_d M B a b t) : s = t := by
  obtain ⟨c, d, hc, hd, hs⟩ := hs
  obtain ⟨e, f, he, hf, ht⟩ := ht
  have heq := npair_unique_l M hE hc he
  have hfq := npair_unique_l M hE hd hf
  subst e; subst f
  exact npair_unique_l M hE hs ht

theorem npair_name_l (hZF : M.Models ZF) {B a b t} (ha : Name_d M B a) (hb : Name_d M B b)
    (ht : Npair_d M B a b t) : Name_d M B t := by
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  let hU := KP.exists_union (ZF.modelsKP hZF)
  obtain ⟨W, haW, hbW, hW⟩ := name_support_l M hP hU ha hb
  apply name_adjoin_l M hP hU hW
  intro v hv
  obtain ⟨p, hp, hv | hv⟩ := (ht v).mp hv
  · exact ⟨a, p, hv, haW, hp⟩
  · exact ⟨b, p, hv, hbW, hp⟩

theorem nkpair_name_l (hZF : M.Models ZF) {B a b t} (ha : Name_d M B a) (hb : Name_d M B b)
    (ht : Nkpair_d M B a b t) : Name_d M B t := by
  obtain ⟨s, v, hs, hv, ht⟩ := ht
  exact npair_name_l M hZF (npair_name_l M hZF ha ha hs) (npair_name_l M hZF ha hb hv) ht

theorem npair_entry_l (hE : Extensional M) (hP : ∀ a b, ∃ t, Pair_d M t a b) {B a b t}
    (ht : Npair_d M B a b t) (s p) : Entry_d M s p t ↔ M.mem p B ∧ (s = a ∨ s = b) := by
  constructor
  · rintro ⟨v, hv, hvt⟩
    obtain ⟨q, hq, h | h⟩ := (ht v).mp hvt
    · have he := kpair_injective_l M hv h
      exact ⟨he.2.symm ▸ hq, Or.inl he.1⟩
    · have he := kpair_injective_l M hv h
      exact ⟨he.2.symm ▸ hq, Or.inr he.1⟩
  · rintro ⟨hp, hs⟩
    obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total s p
    exact ⟨v, hv, (ht v).mpr ⟨p, hp, hs.elim (fun h => Or.inl (h ▸ hv)) (fun h => Or.inr (h ▸ hv))⟩⟩

/-- 非空条件集上，配对名称的两个分量都是名称。 -/
theorem npair_components_l (hE : Extensional M) (hP : ∀ a b, ∃ t, Pair_d M t a b)
    {B a b t p} (hp : M.mem p B) (ht : Name_d M B t) (h : Npair_d M B a b t) :
    Name_d M B a ∧ Name_d M B b := by
  exact ⟨(name_entry_l M ht ((npair_entry_l M hE hP h a p).mpr ⟨hp, Or.inl rfl⟩)).1,
    (name_entry_l M ht ((npair_entry_l M hE hP h b p).mpr ⟨hp, Or.inr rfl⟩)).1⟩

theorem nkpair_components_l (hE : Extensional M) (hP : ∀ a b, ∃ t, Pair_d M t a b)
    {B a b t p} (hp : M.mem p B) (ht : Name_d M B t) (h : Nkpair_d M B a b t) :
    Name_d M B a ∧ Name_d M B b := by
  obtain ⟨s, v, _, hv, h⟩ := h
  exact npair_components_l M hE hP hp (npair_components_l M hE hP hp ht h).2 hv

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem npair_val_l {a b t} {x y v : (E).Domain} (ht : Npair_d M B a b t)
    (ha : Qval_d M B R z U a x) (hb : Qval_d M B R z U b y) (hv : Qval_d M B R z U t v) :
    Pair_d E v x y := by
  intro c
  constructor
  · intro hc
    obtain ⟨s, p, hsp, _, hsc⟩ := (qval_mem_l O hZF hU hv).mp hc
    obtain ⟨_, he⟩ := (npair_entry_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ht s p).mp hsp
    exact he.elim (fun e => Or.inl (qval_unique_l (e ▸ hsc) ha)) (fun e => Or.inr (qval_unique_l (e ▸ hsc) hb))
  · rintro (rfl | rfl) <;> obtain ⟨p, hp⟩ := hU.inhabited
    · exact (qval_mem_l O hZF hU hv).mpr ⟨a, p,
        (npair_entry_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ht a p).mpr ⟨(hU.proper p hp).1, Or.inl rfl⟩, hp, ha⟩
    · exact (qval_mem_l O hZF hU hv).mpr ⟨b, p,
        (npair_entry_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ht b p).mpr ⟨(hU.proper p hp).1, Or.inr rfl⟩, hp, hb⟩

theorem nkpair_val_l {a b t} {x y v : (E).Domain} (ht : Nkpair_d M B a b t)
    (ha : Qval_d M B R z U a x) (hb : Qval_d M B R z U b y) (hv : Qval_d M B R z U t v) :
    KPair_d E v x y := by
  obtain ⟨s, u, hs, hu, ht⟩ := ht
  obtain ⟨c, hc⟩ := name_value_l (R := R) (z := z) (U := U) (npair_name_l M hZF (qval_name_l ha) (qval_name_l ha) hs)
  obtain ⟨d, hd⟩ := name_value_l (R := R) (z := z) (U := U) (npair_name_l M hZF (qval_name_l ha) (qval_name_l hb) hu)
  have hc' := npair_val_l O hZF hU hs ha ha hc
  exact ⟨c, d, fun z => (hc' z).trans ⟨fun h => h.elim id id, Or.inl⟩, npair_val_l O hZF hU hu ha hb hd,
    npair_val_l O hZF hU ht hc hd hv⟩

end YesMetaZFC.Model.Forcing.Internal
