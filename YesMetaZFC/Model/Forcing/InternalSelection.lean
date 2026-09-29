import YesMetaZFC.Model.Forcing.InternalNameConstruction
import YesMetaZFC.SetTheory.Choice

/-! # 按内部序数枚举选择名称

在每个条件以下，取仍可能属于目标集合的最小枚举指标，再加强条件实现该隶属。
较早指标已不可能出现，因此泛型滤子得到的选择与目标名称的不同呈现无关。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Poss_mem_d (B R z F p i t : M.Domain) : Prop :=
  ∃ s, Entry_d M i s F ∧ ∃ q, Below_d M B R z q p ∧ Mem_force_d M B R z q s t

def Min_mem_d (B R z F κ p s t : M.Domain) : Prop :=
  ∃ i, M.mem i κ ∧ Entry_d M i s F ∧ Mem_force_d M B R z p s t ∧
    ∀ j, M.mem j i → ¬ Poss_mem_d M B R z F p j t

def poss_mem_m {n} (B R z F p i t : Term n) : Formula 1 n :=
  .existsE (.conj (entry_m i.weaken .newest F.weaken)
    (.existsE (.conj (below_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest p.weaken.weaken)
      (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken .newest (.bound 1) t.weaken.weaken))))
derive_free_closed poss_mem_m

def min_mem_m {n} (B R z F κ p s t : Term n) : Formula 1 n :=
  .existsE (.conj (.mem .newest κ.weaken) (.conj (entry_m .newest s.weaken F.weaken)
    (.conj (mem_force_m B.weaken R.weaken z.weaken p.weaken s.weaken t.weaken)
      (.forallE (.imp (.mem .newest (.bound 1)) (.neg
        (poss_mem_m B.weaken.weaken R.weaken.weaken z.weaken.weaken F.weaken.weaken
          p.weaken.weaken .newest t.weaken.weaken)))))))
derive_free_closed min_mem_m

theorem poss_mem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F p i t : Term n) :
    Formula.satisfies ρ (poss_mem_m B R z F p i t) ↔
      Poss_mem_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (p.eval ρ) (i.eval ρ) (t.eval ρ) := by
  simp only [poss_mem_m, Poss_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, below_sat_l M hE, mem_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem min_mem_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F κ p s t : Term n) :
    Formula.satisfies ρ (min_mem_m B R z F κ p s t) ↔
      Min_mem_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (κ.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [min_mem_m, Min_mem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, entry_sat_l M hE, mem_force_sat_l M hE, poss_mem_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_one_push,
    Term.eval_bound_zero_push]

theorem min_mem_defined_l (hE : Extensional M) (B R z F κ t : M.Domain) :
    Defined_d M (fun p => ∃ s, Min_mem_d M B R z F κ p s t) := by
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push t
  let φ : UnarySchema 6 := {
    body := .existsE (min_mem_m (.bound 7) (.bound 6) (.bound 5) (.bound 4)
      (.bound 3) (.bound 1) .newest (.bound 2)) }
  refine ⟨6, φ, ρ, fun p => ?_⟩
  simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, min_mem_sat_l M hE]
  rfl

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z)
include O

theorem poss_mem_extend_l {F p q i t} (hp : M.mem p B) (hq : Below_d M B R z q p)
    (h : Poss_mem_d M B R z F q i t) : Poss_mem_d M B R z F p i t := by
  obtain ⟨s, hs, r, hr, hm⟩ := h
  exact ⟨s, hs, r, below_trans_l O hp hr hq, hm⟩

theorem min_mem_lower_l (F κ s t : M.Domain) : Lower_d M B R z (fun p => Min_mem_d M B R z F κ p s t) := by
  rintro p q hp hq ⟨i, hi, hs, hm, hn⟩
  exact ⟨i, hi, hs, (regular_mem_l O s t).1 p q hp hq hm,
    fun j hj h => hn j hj (poss_mem_extend_l O hp hq h)⟩

/-- 候选指标组成模型内集合，其内部最小元给出稠密的最早隶属条件。 -/
theorem min_mem_dense_l (hZF : M.Models ZF) {F κ p i s t}
    (hκ : M.IsOrdinal κ) (hi : M.mem i κ) (his : Entry_d M i s F)
    (hm : Mem_force_d M B R z p s t) :
    Dense_d M B R z (fun q => ∃ a, Min_mem_d M B R z F κ q a t) p := by
  intro q hq
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push q).push t
  let φ : UnarySchema 6 := {
    body := poss_mem_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1) }
  obtain ⟨J, hJ⟩ := ZF.separation_exists_d hZF φ ρ κ
  have hj j : M.mem j J ↔ M.mem j κ ∧ Poss_mem_d M B R z F q j t := by
    rw [hJ j]
    simp only [φ, poss_mem_sat_l M hZF.1]
    rfl
  have hiJ := (hj i).mpr ⟨hi, s, his, q, below_refl_l O hq.1 hq.2.1,
    (regular_mem_l O s t).1 p q hm.1 hq hm⟩
  obtain ⟨k, hkJ, hk⟩ := hκ.wellOrder.least J (fun j hjJ => ((hj j).mp hjJ).1) ⟨i, hiJ⟩
  obtain ⟨hkκ, a, hka, r, hr, ham⟩ := (hj k).mp hkJ
  refine ⟨r, hr, a, k, hkκ, hka, ham, fun j hjk hposs => ?_⟩
  have hjκ := hκ.transitive k hkκ j hjk
  have hjJ := (hj j).mpr ⟨hjκ, poss_mem_extend_l O hq.1 hr hposs⟩
  rcases hk j hjJ with he | hkj
  · have he := hZF.1.eq_of_same_members k j he
    exact hκ.wellOrder.linear.irrefl j hjκ (he ▸ hjk)
  · exact hκ.wellOrder.linear.irrefl j hjκ
      (hκ.wellOrder.linear.trans j hjκ k hkκ j hjκ hjk hkj)

/-- 相同解释的两个目标名称给出同一个被选元素，即使枚举或名称有重复呈现。 -/
theorem min_mem_unique_l (hZF : M.Models ZF) {U : M.Domain → Prop}
    (hU : Generic_d M B R z U) {F κ S p q s t a b} {x y w : Name_quot_l M B R z U}
    (hκ : M.IsOrdinal κ)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F κ S)
    (hp : U p) (hq : U q) (hs : Qval_d M B R z U s x) (ha : Qval_d M B R z U a y)
    (ht : Qval_d M B R z U t w) (hb : Qval_d M B R z U b w)
    (hm : Min_mem_d M B R z F κ p s t) (hn : Min_mem_d M B R z F κ q a b) : x = y := by
  obtain ⟨i, hi, his, hmt, hmi⟩ := hm
  obtain ⟨j, hj, hja, hnb, hnj⟩ := hn
  have hm := (qval_mem_forcing_l O hZF hU hs ht).mp ⟨p, hp, hmt⟩
  have hn := (qval_mem_forcing_l O hZF hU ha hb).mp ⟨q, hq, hnb⟩
  have impossible {i j s t p} {x : Name_quot_l M B R z U}
      (hi : Entry_d M i s F) (hij : M.mem i j) (hp : U p)
      (hs : Qval_d M B R z U s x) (ht : Qval_d M B R z U t w) (hx : x ∈ w)
      (hn : ∀ k, M.mem k j → ¬ Poss_mem_d M B R z F p k t) : False := by
    obtain ⟨q, hq, hm⟩ := (qval_mem_forcing_l O hZF hU hs ht).mpr hx
    obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
    have hr' := hU.proper r hr
    exact hn i hij ⟨s, hi, r, ⟨hr'.1, hr'.2, hrp⟩,
      (regular_mem_l O s t).1 q r hm.1 ⟨hr'.1, hr'.2, hrq⟩ hm⟩
  rcases hκ.wellOrder.linear.compare i hi j hj with he | hij | hji
  · have he := hZF.1.eq_of_same_members i j he
    subst j
    have he := hf.1.2 i s a his hja
    subst a
    exact qval_unique_l hs ha
  · exact False.elim (impossible his hij hq hs hb hm hnj)
  · exact False.elim (impossible hja hji hp ha ht hn hmi)

end YesMetaZFC.Model.Forcing.Internal
