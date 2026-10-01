import YesMetaZFC.Model.Forcing.Proper.Generic.Hull
import YesMetaZFC.Model.Forcing.Internal.Names.PairConstruction
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 名称集合上的实际泛型求值函数图

每个地名称 s 对应名称对 (check(s),s)。收集这些名称对，再取泛型值，得到
扩张内从地名称集合到 N[G] 的实际满射；不把外部求值关系直接假定为集合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Ng_pair_d (B b s q : M.Domain) : Prop := ∃ t, Check_d M b s t ∧ Nkpair_d M B t s q

def ng_pair_m {n} (B b s q : Term n) : Formula 1 n :=
  .existsE (.conj (check_m b.weaken s.weaken .newest) (nkpair_m B.weaken .newest s.weaken q.weaken))
derive_free_closed ng_pair_m

theorem ng_pair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B b s q : Term n) :
    Formula.satisfies ρ (ng_pair_m B b s q) ↔ Ng_pair_d M (B.eval ρ) (b.eval ρ) (s.eval ρ) (q.eval ρ) := by
  simp only [ng_pair_m, Ng_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_sat_l M hE, nkpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem ng_pair_family_l (hZF : M.Models ZF) {B b S} (hb : M.mem b B)
    (hS : ∀ s, M.mem s S → Name_d M B s) : ∃ T,
    (∀ q, M.mem q T ↔ ∃ s, M.mem s S ∧ Ng_pair_d M B b s q) ∧ ∀ q, M.mem q T → Name_d M B q := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push b
  let φ : BinarySchema 2 := { body := ng_pair_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ s q : φ.denote ρ s q ↔ Ng_pair_d M B b s q := ng_pair_sat_l M hZF.1 _ _ _ _ _
  obtain ⟨T, hT⟩ := ZF.exists_functionalImage hZF φ ρ S (by
    intro s _
    obtain ⟨t, ht, _, _⟩ := zf_check_l M hZF hb s
    obtain ⟨q, hq⟩ := nkpair_l M hZF B t s
    exact ⟨q, (hφ s q).mpr ⟨t, ht, hq⟩⟩) (by
    intro s q r hq hr
    obtain ⟨t, ht, hq⟩ := (hφ s q).mp hq
    obtain ⟨v, hv, hr⟩ := (hφ s r).mp hr
    have he := check_unique_l M hZF.1 (check_ind_l M hZF) b s t v ht hv
    subst v
    exact nkpair_unique_l M hZF.1 hq hr)
  have he q : M.mem q T ↔ ∃ s, M.mem s S ∧ Ng_pair_d M B b s q :=
    (hT q).trans (exists_congr fun s => and_congr_right fun _ => hφ s q)
  refine ⟨T, he, fun q hq => ?_⟩
  obtain ⟨s, hs, t, ht, hq⟩ := (he q).mp hq
  exact nkpair_name_l M hZF (check_name_l M (check_range_l M hZF) hb ht) (hS s hs) hq

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

/-- 实际求值关系的精确图方程；输入是规范嵌入的地名称，输出是其泛型商类。 -/
theorem ng_graph_l {b S} (hb : M.mem b B) (hS : ∀ s, M.mem s S → Name_d M B s)
    (e : M.Domain → (E).Domain) (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a)) :
    ∃ F : (E).Domain, (∀ p, p ∈ F → ∃ x y, KPair_d E p x y) ∧ ∀ x y, Entry_d E x y F ↔
      ∃ s, M.mem s S ∧ e s = x ∧ Qval_d M B R z U s y := by
  obtain ⟨T, hT, hTN⟩ := ng_pair_family_l M hZF hb hS
  obtain ⟨t, ht⟩ := ng_name_exists_l M hZF B T
  obtain ⟨F, hF⟩ := name_value_l (R := R) (z := z) (U := U) ht.1
  have members p : p ∈ F ↔ ∃ s, M.mem s S ∧ ∃ y, Qval_d M B R z U s y ∧ KPair_d E p (e s) y := by
    rw [ng_value_l O hZF hU ht hF]
    constructor
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨s, hs, v, hv', hpair⟩ := (hT q).mp hq
      obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) (hS s hs)
      exact ⟨s, hs, y, hy, nkpair_val_l O hZF hU hpair (hv s v hv') hy hqp⟩
    · rintro ⟨s, hs, y, hy, hp⟩
      obtain ⟨v, hv', _, _⟩ := zf_check_l M hZF hb s
      obtain ⟨q, hpair⟩ := nkpair_l M hZF B v s
      have hq := (hT q).mpr ⟨s, hs, v, hv', hpair⟩
      obtain ⟨w, hw⟩ := name_value_l (R := R) (z := z) (U := U) (hTN q hq)
      have he := kpair_unique_l E (extension_ext_l O hZF hU) (nkpair_val_l O hZF hU hpair (hv s v hv') hy hw) hp
      exact ⟨q, hq, he ▸ hw⟩
  have rel p (hp : p ∈ F) : ∃ x y, KPair_d E p x y := by
    obtain ⟨s, _, y, _, hpair⟩ := (members p).mp hp
    exact ⟨e s, y, hpair⟩
  refine ⟨F, rel, fun x y => ?_⟩
  constructor
  · rintro ⟨p, hp, hpF⟩
    obtain ⟨s, hs, v, hv, hp'⟩ := (members p).mp hpF
    obtain ⟨hx, hy⟩ := kpair_injective_l E hp' hp
    exact ⟨s, hs, hx, hy ▸ hv⟩
  · rintro ⟨s, hs, rfl, hy⟩
    obtain ⟨p, hp⟩ := (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)).total (e s) y
    exact ⟨p, hp, (members p).mpr ⟨s, hs, y, hy, hp⟩⟩

/-- 名称集合的规范像到 N[G] 的满射存在于泛型扩张内部。 -/
theorem ng_surjection_l {b N S} {Y : (E).Domain} (hb : M.mem b B) (hS : Ng_source_d M B N S)
    (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M B R z U t (e a)) :
    ∃ F : (E).Domain, (E).IsSetFunctionFromTo (kpair_interpretation_l E
      (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) F (e S) Y ∧
      (E).IsSetSurjectiveOnto (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) F (e S) Y := by
  obtain ⟨F, hF, hf⟩ := ng_graph_l O hZF hU hb (fun s hs => ((hS s).mp hs).2) e hv
  have total x (hx : x ∈ e S) : ∃ y, y ∈ Y ∧ Entry_d E x y F := by
    obtain ⟨s, hs, rfl⟩ := (he S x).mp hx
    obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) ((hS s).mp hs).2
    exact ⟨y, (hY y).mpr ⟨s, ((hS s).mp hs).1, hy⟩, (hf (e s) y).mpr ⟨s, hs, rfl, hy⟩⟩
  refine ⟨F, ⟨⟨hF, ?_⟩, fun x => ⟨fun hx => (total x hx).elim fun y hy => ⟨y, hy.2⟩, ?_⟩, total⟩, ?_⟩
  · intro x y w hy hw
    obtain ⟨s, _, hs, hy⟩ := (hf x y).mp hy
    obtain ⟨t, _, ht, hw⟩ := (hf x w).mp hw
    have he := hi (hs.trans ht.symm)
    subst t
    exact qval_unique_l hy hw
  · rintro ⟨y, hy⟩
    obtain ⟨s, hs, hx, _⟩ := (hf x y).mp hy
    exact (he S x).mpr ⟨s, hs, hx⟩
  · intro y hy
    obtain ⟨s, hs, hv⟩ := (hY y).mp hy
    have hsS := (hS s).mpr ⟨hs, qval_name_l hv⟩
    exact ⟨e s, (he S (e s)).mpr ⟨s, hsS, rfl⟩, (hf (e s) y).mpr ⟨s, hsS, rfl, hv⟩⟩

end YesMetaZFC.Model.Forcing.Internal
