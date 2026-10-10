import YesMetaZFC.Model.Forcing.Internal.Forcing.Rules

/-! # 条件域上的序关系决定全部名称力迫

域外条目不参与闭名称的带条件双模拟。先在共同闭支撑上搬运实际双模拟集合，
再由原公式归纳传递全部连接词和名称量词；不要求域外关系满足序律。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R S z : M.Domain}
variable (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
include hR

theorem below_order_l {p q} (hp : M.mem p B) :
    Below_d M B R z q p ↔ Below_d M B S z q p :=
  and_congr_right fun hq => and_congr_right fun _ => hR q p hq hp

/-- 泛型性只依赖条件域内的关系边，两个方向均无需集合论公理。 -/
theorem generic_order_l (U : M.Domain → Prop) : Generic_d M B R z U ↔ Generic_d M B S z U := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (hU : Generic_d M B R z U) : Generic_d M B S z U := by
    refine ⟨hU.proper, hU.inhabited, ?_, ?_, ?_⟩
    · intro p q hp hq hpq
      exact hU.upward p q hp hq ((hR p q (hU.proper p hp).1 hq).mpr hpq)
    · intro p q hp hq
      obtain ⟨r, hr, hrp, hrq⟩ := hU.directed p q hp hq
      exact ⟨r, hr, (hR r p (hU.proper r hr).1 (hU.proper p hp).1).mp hrp,
        (hR r q (hU.proper r hr).1 (hU.proper q hq).1).mp hrq⟩
    · intro p hp D hd
      apply hU.meets p hp D
      intro q hq
      obtain ⟨r, hr, hrD⟩ := hd q ((below_order_l hR (hU.proper p hp).1).mp hq)
      exact ⟨r, (below_order_l hR hq.1).mpr hr, hrD⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

variable (hZF : M.Models ZF)
include hZF

/-- 闭支撑上的最大双模拟可沿逐边对应直接搬运，无须外部良基归纳。 -/
theorem eq_force_order_l {s t p} (hs : Name_d M B s) (ht : Name_d M B t) :
    Eq_force_d M B R z p s t ↔ Eq_force_d M B S z p s t := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (he : Eq_force_d M B R z p s t) : Eq_force_d M B S z p s t := by
    obtain ⟨W, hsW, htW, hW⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
      (KP.exists_union (ZF.modelsKP hZF)) hs ht
    obtain ⟨X, hX⟩ := triple_carrier_l M hZF B W
    obtain ⟨F, hF⟩ := bisim_max_l M hZF B R z X
    have hf := (eq_force_local_l M hZF hW hX hF he.1 hsW htW).mp he
    refine ⟨he.1, F, ?_, hf⟩
    intro v a b hab
    obtain ⟨w, hw, hwF⟩ := hab
    obtain ⟨v', a', b', hv, ha, hb, hw'⟩ := (hX w).mp (hF.subset w hwF)
    obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hw hw'
    have hm (k : Bool) {a b} (ha : M.mem a W) (hb : M.mem b W)
        (hm : Match_d M k B R z F v a b) : Match_d M k B S z F v a b := by
      intro c d hcd q hq hqd
      have hd := (supp_entry_l M hW ha hcd).2
      obtain ⟨r, e, f, hr, hef, hrf, hre⟩ := hm c d hcd q
        ((below_order_l hR hv).mpr hq) ((hR q d hq.1 hd).mpr hqd)
      exact ⟨r, e, f, (below_order_l hR hq.1).mp hr, hef,
        (hR r f hr.1 (supp_entry_l M hW hb hef).2).mp hrf, hre⟩
    have hh := hF.bisim v a b ⟨w, hw, hwF⟩
    exact ⟨hm false ha hb hh.1, hm true hb ha hh.2⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

theorem mem_force_order_l {s t p} (hs : Name_d M B s) (ht : Name_d M B t) :
    Mem_force_d M B R z p s t ↔ Mem_force_d M B S z p s t := by
  have tr {R S} (hR : ∀ p q, M.mem p B → M.mem q B → (Entry_d M p q R ↔ Entry_d M p q S))
      (he : Mem_force_d M B R z p s t) : Mem_force_d M B S z p s t := by
    refine ⟨he.1, fun q hq => ?_⟩
    obtain ⟨r, a, b, hr, hab, hrb, hea⟩ := he.2 q ((below_order_l hR he.1).mpr hq)
    have hn := name_entry_l M ht hab
    exact ⟨r, a, b, (below_order_l hR hq.1).mp hr, hab, (hR r b hr.1 hn.2).mp hrb,
      (eq_force_order_l hR hZF hs hn.1).mp hea⟩
  exact ⟨tr hR, tr (fun p q hp hq => (hR p q hp hq).symm)⟩

omit hZF in
private theorem neg_order_l {P Q : M.Domain → Prop}
    (h : ∀ p, M.mem p B → (P p ↔ Q p)) {p} (hp : M.mem p B) :
    Neg_d M B R z P p ↔ Neg_d M B S z Q p :=
  ⟨fun hn q hq hQ => hn q ((below_order_l hR hp).mpr hq) ((h q hq.1).mpr hQ),
    fun hn q hq hP => hn q ((below_order_l hR hp).mp hq) ((h q hq.1).mp hP)⟩

/-- 任意原公式的名称力迫在删除、加入或改写域外关系条目后保持不变。 -/
theorem forces_order_l {a n} (φ : Formula a n) (ρ : Env M n)
    (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) :
    ∀ p, M.mem p B → (Forces_d M B R z φ ρ p ↔ Forces_d M B S z φ ρ p) := by
  have hn := @neg_order_l M B R S z hR
  have hc {P Q V W : M.Domain → Prop}
      (h : ∀ p, M.mem p B → (P p ↔ Q p)) (k : ∀ p, M.mem p B → (V p ↔ W p)) :=
    fun p hp => and_congr (h p hp) (k p hp)
  have push {n} {ρ : Env M n} (hρ : ∀ t : Term n, Name_d M B (t.eval ρ)) {s} (hs : Name_d M B s) :
      ∀ t : Term (n+1), Name_d M B (t.eval (ρ.push s)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hs (fun i => hρ (.bound i)) i
  induction φ with
  | falsum => intro p _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_falsum_iff]
  | truth => intro p _; simp only [Forces_d, force_code_m, Code_d, Formula.satisfies_truth_iff]
  | mem s t =>
    intro p _
    rw [forces_mem_l hZF.1, forces_mem_l hZF.1]
    exact mem_force_order_l hR hZF (hρ s) (hρ t)
  | atom r _ ts =>
    cases r
    · intro p _
      simp only [Forces_d, force_code_m, code_eq_l M hZF.1]
      exact eq_force_order_l hR hZF (hρ (ts 0)) (hρ (ts 1))
    · intro p hp
      simp only [Forces_d, force_code_m, code_all_l M hZF.1, imp_code_m, code_neg_l M hZF.1,
        Neg_d, code_conj_l, code_mem_l M hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
      refine forall_congr' fun s => imp_congr_right fun hs => ?_
      have hm (t : Term _) (q : M.Domain) (_ : M.mem q B) := mem_force_order_l (z := z) hR hZF (p := q) hs (hρ t)
      simpa only [Neg_d] using hn (hc (hm (ts 0)) (fun q hq => hn (hm (ts 1)) hq)) hp
  | neg φ ih =>
    intro p hp
    simpa only [forces_neg_l hZF.1] using hn (ih ρ hρ) hp
  | conj φ ψ ih jh =>
    simpa only [forces_conj_l] using hc (ih ρ hρ) (jh ρ hρ)
  | disj φ ψ ih jh =>
    intro p hp
    simpa only [forces_disj_l, forces_neg_l hZF.1, forces_conj_l, Neg_d] using
      hn (hc (fun q hq => hn (ih ρ hρ) hq) (fun q hq => hn (jh ρ hρ) hq)) hp
  | imp φ ψ ih jh =>
    intro p hp
    simpa only [forces_imp_l hZF.1, Neg_d] using hn (hc (ih ρ hρ) (fun q hq => hn (jh ρ hρ) hq)) hp
  | iff φ ψ ih jh =>
    intro p hp
    simpa only [forces_iff_l, forces_conj_l, forces_imp_l hZF.1, Neg_d] using
      and_congr (hn (hc (ih ρ hρ) (fun q hq => hn (jh ρ hρ) hq)) hp)
        (hn (hc (jh ρ hρ) (fun q hq => hn (ih ρ hρ) hq)) hp)
  | forallE φ ih =>
    intro p hp
    rw [forces_all_l hZF.1, forces_all_l hZF.1]
    exact forall_congr' fun s => imp_congr_right fun hs => ih (ρ.push s) (push hρ hs) p hp
  | existsE φ ih =>
    have hall p (hp : M.mem p B) :
        (∀ s, Name_d M B s → Neg_d M B R z (Forces_d M B R z φ (ρ.push s)) p) ↔
        ∀ s, Name_d M B s → Neg_d M B S z (Forces_d M B S z φ (ρ.push s)) p :=
      forall_congr' fun s => imp_congr_right fun hs => hn (ih (ρ.push s) (push hρ hs)) hp
    intro p hp
    simpa only [forces_exists_l, forces_neg_l hZF.1, forces_all_l hZF.1, Neg_d] using hn hall hp

end YesMetaZFC.Model.Forcing.Internal
