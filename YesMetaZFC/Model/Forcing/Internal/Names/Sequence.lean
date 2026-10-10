import YesMetaZFC.Model.Forcing.Proper.Generic.Evaluation

/-! # 内部函数图的逐坐标名称装配

把地函数图中的 (i,s) 变为名称对 (check(i),s)，再赋予全部条件。
构造是原模型内唯一确定的集合运算，不枚举外部长度，也不选择泛型商类代表。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Nseq_pair_d (B b f i q : M.Domain) : Prop :=
  ∃ s c, Entry_d M i s f ∧ Check_d M b i c ∧ Nkpair_d M B c s q

def nseq_pair_m {n} (B b f i q : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (entry_m i.weaken.weaken (.bound 1) f.weaken.weaken)
    (.conj (check_m b.weaken.weaken i.weaken.weaken .newest)
      (nkpair_m B.weaken.weaken .newest (.bound 1) q.weaken.weaken))))
derive_free_closed nseq_pair_m

theorem nseq_pair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b f i q : Term n) :
    Formula.satisfies ρ (nseq_pair_m B b f i q) ↔
      Nseq_pair_d M (B.eval ρ) (b.eval ρ) (f.eval ρ) (i.eval ρ) (q.eval ρ) := by
  simp only [nseq_pair_m, Nseq_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, check_sat_l M hE, nkpair_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Nseq_d (B b f t : M.Domain) : Prop := Name_d M B t ∧
  ∀ q p, Entry_d M q p t ↔ M.mem p B ∧ ∃ i, Nseq_pair_d M B b f i q

def nseq_m {n} (B b f t : Term n) : Formula 1 n :=
  .conj (name_m B t) (.forallE (.forallE (.iff (entry_m (.bound 1) .newest t.weaken.weaken)
    (.conj (.mem .newest B.weaken.weaken) (.existsE
      (nseq_pair_m B.weaken.weaken.weaken b.weaken.weaken.weaken f.weaken.weaken.weaken .newest (.bound 2)))))))
derive_free_closed nseq_m

theorem nseq_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b f t : Term n) :
    Formula.satisfies ρ (nseq_m B b f t) ↔
      Nseq_d M (B.eval ρ) (b.eval ρ) (f.eval ρ) (t.eval ρ) := by
  simp only [nseq_m, Nseq_d, Formula.satisfies_conj_iff, name_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, nseq_pair_sat_l M hE,
    Definitional.Term.eval_weaken]
  rfl

/-- 任意实际函数图的名称值可逐项装配；不要求其定义域在外部有限。 -/
theorem nseq_exists_l (hZF : M.Models ZF) {B b f n X} (hb : M.mem b B)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f n X)
    (hs : ∀ i s, Entry_d M i s f → Name_d M B s) : ∃ t, Nseq_d M B b f t := by
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push b).push f
  let φ : BinarySchema 3 := { body := nseq_pair_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ i q : φ.denote ρ i q ↔ Nseq_pair_d M B b f i q := nseq_pair_sat_l M hZF.1 _ _ _ _ _ _
  obtain ⟨T, hT⟩ := ZF.exists_functionalImage hZF φ ρ n (by
    intro i hi
    obtain ⟨s, _, his⟩ := hf.2.2 i hi
    obtain ⟨c, hc, _, _⟩ := zf_check_l M hZF hb i
    obtain ⟨q, hq⟩ := nkpair_l M hZF B c s
    exact ⟨q, (hφ i q).mpr ⟨s, c, his, hc, hq⟩⟩) (by
    intro i q r hq hr
    obtain ⟨s, c, his, hc, hq⟩ := (hφ i q).mp hq
    obtain ⟨v, d, hiv, hd, hr⟩ := (hφ i r).mp hr
    have hvs := hf.1.2 i s v his hiv
    have hcd := check_unique_l M hZF.1 (check_ind_l M hZF) b i c d hc hd
    subst v d
    exact nkpair_unique_l M hZF.1 hq hr)
  have ht q : M.mem q T ↔ ∃ i, Nseq_pair_d M B b f i q := by
    rw [hT q]
    constructor
    · exact fun ⟨i, _, hi⟩ => ⟨i, (hφ i q).mp hi⟩
    · rintro ⟨i, hi⟩
      obtain ⟨s, c, his, hc, hq⟩ := hi
      exact ⟨i, hf.input_mem_of_pairMember his, (hφ i q).mpr ⟨s, c, his, hc, hq⟩⟩
  have hn q (hq : M.mem q T) : Name_d M B q := by
    obtain ⟨i, s, c, his, hc, hq⟩ := (ht q).mp hq
    exact nkpair_name_l M hZF (check_name_l M (check_range_l M hZF) hb hc) (hs i s his) hq
  obtain ⟨t, htn⟩ := ng_name_exists_l M hZF B T
  refine ⟨t, htn.1, fun q p => (htn.2 q p).trans ?_⟩
  exact ⟨fun h => ⟨h.2.2, (ht q).mp h.1⟩, fun h => ⟨(ht q).mpr h.2, hn q ((ht q).mpr h.2), h.1⟩⟩

theorem nseq_unique_l (hE : Extensional M) {B b f s t}
    (hs : Nseq_d M B b f s) (ht : Nseq_d M B b f t) : s = t := by
  have rel {t} (ht : Name_d M B t) : ∀ p, M.mem p t → ∃ a b, KPair_d M p a b := by
    obtain ⟨S, ht, hS⟩ := ht
    exact fun p hp => (hS t ht p hp).elim fun a h => h.elim fun b h => ⟨a, b, h.1⟩
  exact entry_ext_l M hE (rel hs.1) (rel ht.1) (fun q p => (hs.2 q p).trans (ht.2 q p).symm)

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

/-- 装配名称的泛型值恰为逐坐标求值后的函数图。 -/
theorem nseq_value_l {b f t} {v : (E).Domain} (hb : M.mem b B) (ht : Nseq_d M B b f t)
    (hv : Qval_d M B R z U t v) (e : M.Domain → (E).Domain)
    (he : ∀ i c, Check_d M b i c → Qval_d M B R z U c (e i)) :
    (∀ p, p ∈ v → ∃ x y, KPair_d E p x y) ∧ ∀ x y, Entry_d E x y v ↔
      ∃ i s, Entry_d M i s f ∧ e i = x ∧ Qval_d M B R z U s y := by
  have members p : p ∈ v ↔ ∃ i s y, Entry_d M i s f ∧ Qval_d M B R z U s y ∧ KPair_d E p (e i) y := by
    rw [qval_mem_l O hZF hU hv]
    constructor
    · rintro ⟨q, r, hqr, _, hqp⟩
      obtain ⟨_, i, s, c, his, hc, hq⟩ := (ht.2 q r).mp hqr
      obtain ⟨ys, hy⟩ := name_value_l (R := R) (z := z) (U := U)
        (nkpair_components_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hb (name_entry_l M ht.1 hqr).1 hq).2
      exact ⟨i, s, ys, his, hy, nkpair_val_l O hZF hU hq (he i c hc) hy hqp⟩
    · rintro ⟨i, s, y, his, hy, hp⟩
      obtain ⟨r, hr⟩ := hU.inhabited
      obtain ⟨c, hc, _, _⟩ := zf_check_l M hZF hb i
      obtain ⟨q, hq⟩ := nkpair_l M hZF B c s
      have hqr := (ht.2 q r).mpr ⟨(hU.proper r hr).1, i, s, c, his, hc, hq⟩
      obtain ⟨p', hp'⟩ := name_value_l (R := R) (z := z) (U := U) (name_entry_l M ht.1 hqr).1
      have hEq := kpair_unique_l E (extension_ext_l O hZF hU) (nkpair_val_l O hZF hU hq (he i c hc) hy hp') hp
      exact ⟨q, r, hqr, hr, hEq ▸ hp'⟩
  refine ⟨fun p hp => (members p).mp hp |>.elim fun i h => h.elim fun _ h => h.elim fun y h => ⟨e i, y, h.2.2⟩, fun x y => ?_⟩
  constructor
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨i, s, y', his, hy, hp'⟩ := (members p).mp hpv
    obtain ⟨hx, heq⟩ := kpair_injective_l E hp' hp
    exact ⟨i, s, his, hx, heq ▸ hy⟩
  · rintro ⟨i, s, his, rfl, hy⟩
    obtain ⟨p, hp⟩ := (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)).total (e i) y
    exact ⟨p, hp, (members p).mpr ⟨i, s, y, his, hy, hp⟩⟩

end YesMetaZFC.Model.Forcing.Internal
