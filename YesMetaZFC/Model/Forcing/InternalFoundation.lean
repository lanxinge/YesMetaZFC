import YesMetaZFC.Model.Forcing.InternalQuotient
import YesMetaZFC.SetTheory.MembershipInduction

/-! # 泛型商中的基础公理

把实际归纳公式加强到两层成员，便可沿 Kuratowski 名称条目的三条成员边归纳。
这给出模型内名称集合的条目极小元；在可定义的可能成员集合中选取该极小元，
再由泛型性取得扩张中的基础公理见证。模型内部的基础公理不被提升为外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

private def member_schema_m {n} (φ : UnarySchema n) : UnarySchema n where
  body := Formula.forallMem .newest (pred_m φ (fun i => .bound ⟨i.val + 2, by omega⟩) .newest)

private theorem member_schema_l {n} (φ : UnarySchema n) (ρ : Env M n) (x : M.Domain) :
    (member_schema_m φ).denote ρ x ↔ ∀ y, M.mem y x → φ.denote ρ y := by
  simp only [UnarySchema.denote, member_schema_m, Formula.satisfies_forallMem_iff,
    pred_sat_l M]
  rfl

/-- 将 P 加强为 P∧∀a∈x,P(a)∧∀a∈x,∀b∈a,P(b)，再消费原成员归纳模式。 -/
theorem entry_ind_l (hI : Mem_ind_d M) {n} (φ : UnarySchema n) (ρ : Env M n)
    (h : ∀ t, (∀ s b, Entry_d M s b t → φ.denote ρ s) → φ.denote ρ t) : ∀ t, φ.denote ρ t := by
  let ψ : UnarySchema n := {
    body := .conj φ.body (.conj (member_schema_m φ).body (member_schema_m (member_schema_m φ)).body) }
  have he t : ψ.denote ρ t ↔ φ.denote ρ t ∧
      (∀ a, M.mem a t → φ.denote ρ a) ∧ ∀ a, M.mem a t → ∀ b, M.mem b a → φ.denote ρ b := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_conj_iff]
    change (φ.denote ρ t ∧ (member_schema_m φ).denote ρ t ∧
      (member_schema_m (member_schema_m φ)).denote ρ t) ↔ _
    simp only [member_schema_l]
    rfl
  have hall := hI ψ ρ (fun t ih => (he t).mpr (by
    refine ⟨h t (fun s b ⟨p, hp, hpt⟩ => ?_), ?_, ?_⟩
    · obtain ⟨a, hap, hsa⟩ := (kpair_union_l M hp s).mpr (Or.inl rfl)
      exact ((he p).mp (ih p hpt)).2.2 a hap s hsa
    · exact fun a ha => ((he a).mp (ih a ha)).1
    · exact fun a ha b hb => ((he a).mp (ih a ha)).2.1 b hb))
  exact fun t => ((he t).mp (hall t)).1

/-- 模型内非空集合对条目关系有极小元，无须该关系在宿主中良基。 -/
theorem entry_min_l (hZF : M.Models ZF) {D : M.Domain} (hn : ∃ t, M.mem t D) :
    ∃ t, M.mem t D ∧ ∀ s b, Entry_d M s b t → ¬ M.mem s D := by
  classical
  apply Classical.byContradiction
  intro h
  let φ : UnarySchema 1 := { body := .neg (.mem .newest (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => D, fun _ => D⟩
  have he t : φ.denote ρ t ↔ ¬ M.mem t D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
    rfl
  have hall := entry_ind_l (ZF.mem_ind_l M hZF
    (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))) φ ρ
    (fun t ih => (he t).mpr (fun ht => h ⟨t, ht, fun s b hs => (he s).mp (ih s b hs)⟩))
  obtain ⟨t, ht⟩ := hn
  exact (he t).mp (hall t) ht

def Min_name_d (M : SetTheory.Structure.{u}) (B R z p a t : M.Domain) : Prop :=
  Name_d M B a ∧ Mem_force_d M B R z p a t ∧
    ∀ s b, Entry_d M s b a → Neg_d M B R z (fun q => Mem_force_d M B R z q s t) p

def min_name_m {n} (B R z p a t : Term n) : Formula 1 n :=
  .conj (name_m B a) (.conj (mem_force_m B R z p a t)
    (.forallE (.forallE (.imp (entry_m (.bound 1) .newest a.weaken.weaken)
      (.forallE (.imp (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken
        .newest p.weaken.weaken.weaken) (.neg (mem_force_m B.weaken.weaken.weaken
          R.weaken.weaken.weaken z.weaken.weaken.weaken .newest (.bound 2) t.weaken.weaken.weaken))))))))
derive_free_closed min_name_m

theorem min_name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z p a t : Term n) :
    Formula.satisfies ρ (min_name_m B R z p a t) ↔
      Min_name_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (a.eval ρ) (t.eval ρ) := by
  simp only [min_name_m, Min_name_d, Neg_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff,
    name_sat_l M hE, mem_force_sat_l M hE, entry_sat_l M hE, below_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

variable {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
include O hZF hU

/-- 极小可能成员的可定义稠密集给出商模型的基础公理。 -/
theorem internal_foundation_l (X : (extension_l M hZF B R z U).Domain)
    (hn : ∃ x, (extension_l M hZF B R z U).mem x X) :
    ∃ x, (extension_l M hZF B R z U).mem x X ∧
      ∀ y, (extension_l M hZF B R z U).mem y X → ¬ (extension_l M hZF B R z U).mem y x := by
  obtain ⟨t, ⟨S, htS, hS⟩, ht⟩ := value_name_l X
  obtain ⟨x, hx⟩ := hn
  obtain ⟨s, b, hs, hb, _⟩ := (qval_mem_l O hZF hU ht).mp hx
  let δ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push t
  let φ : UnarySchema 4 := {
    body := .existsE (min_name_m (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest (.bound 2)) }
  have hd : Defined_d M (fun p => ∃ a, Min_name_d M B R z p a t) := by
    refine ⟨4, φ, δ, fun p => ?_⟩
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, min_name_sat_l hZF.1]
    rfl
  obtain ⟨p, hp, a, ha, ham, hmin⟩ := generic_pick_l hZF hU hd hb (by
    intro q hq
    let ρ := δ.push q
    let ψ : UnarySchema 5 := {
      body := .existsE (.conj (below_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 2))
        (mem_force_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1) (.bound 3))) }
    obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF ψ ρ S
    have hd a : M.mem a D ↔ M.mem a S ∧ ∃ r, Below_d M B R z r q ∧ Mem_force_d M B R z r a t := by
      rw [hD a]
      simp only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        below_sat_l M hZF.1, mem_force_sat_l M hZF.1]
      rfl
    obtain ⟨a, ha, hmin⟩ := entry_min_l hZF ⟨s, (hd s).mpr
      ⟨(supp_entry_l M hS htS hs).1, q, below_refl_l O hq.1 hq.2.1,
        mem_force_entry_l O hZF hq.1 ⟨S, (supp_entry_l M hS htS hs).1, hS⟩
          (hU.proper b hb).1 hs hq.2.2⟩⟩
    obtain ⟨haS, r, hr, ham⟩ := (hd a).mp ha
    refine ⟨r, hr, a, ⟨S, haS, hS⟩, ham, fun c d hcd v hv hm => ?_⟩
    exact hmin c d hcd ((hd c).mpr ⟨(supp_entry_l M hS haS hcd).1,
      v, below_trans_l O hq.1 hv hr, hm⟩))
  obtain ⟨A, hA⟩ := name_value_l (R := R) (z := z) (U := U) ha
  refine ⟨A, (qval_mem_forcing_l O hZF hU hA ht).mp ⟨p, hp, ham⟩, fun y hy hya => ?_⟩
  obtain ⟨c, d, hcd, _, hcy⟩ := (qval_mem_l O hZF hU hA).mp hya
  obtain ⟨q, hq, hqt⟩ := (qval_mem_forcing_l O hZF hU hcy ht).mpr hy
  obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
  have hr' := hU.proper r hr
  exact hmin c d hcd r ⟨hr'.1, hr'.2, hrp⟩ ⟨hr'.1,
    fun v hv => hqt.2 v (below_trans_l O hqt.1 hv ⟨hr'.1, hr'.2, hrq⟩)⟩

end YesMetaZFC.Model.Forcing.Internal
