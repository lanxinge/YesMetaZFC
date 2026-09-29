import YesMetaZFC.Model.Forcing.InternalAtomicClosure

/-! # 内部原子力迫的递归方程

最大双模拟在任意闭支撑上计算同一个等号谓词。将局部关系换回这个谓词，
得到通常的稠密匹配递归；隶属力迫则是带权等号匹配的稠密闭包。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Eq_match_d (k : Bool) (B R z p s t : M.Domain) : Prop :=
  ∀ a b, Entry_d M a b s → ∀ q, Below_d M B R z q p → Entry_d M q b R →
    ∃ r d c, Below_d M B R z r q ∧ Entry_d M d c t ∧ Entry_d M r c R ∧
      (if k then Eq_force_d M B R z r d a else Eq_force_d M B R z r a d)

def Mem_force_d (B R z p s t : M.Domain) : Prop := M.mem p B ∧
  ∀ q, Below_d M B R z q p → ∃ r a b,
    Below_d M B R z r q ∧ Entry_d M a b t ∧ Entry_d M r b R ∧ Eq_force_d M B R z r s a

def mem_force_m {n} (B R z p s t : Term n) : Formula 1 n :=
  .conj (.mem p B) (.forallE (.imp (below_m B.weaken R.weaken z.weaken .newest p.weaken)
    (.existsE (.existsE (.existsE (.conj
      (below_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
        z.weaken.weaken.weaken.weaken (.bound 2) (.bound 3))
      (.conj (entry_m (.bound 1) .newest t.weaken.weaken.weaken.weaken)
        (.conj (entry_m (.bound 2) .newest R.weaken.weaken.weaken.weaken)
          (eq_force_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            z.weaken.weaken.weaken.weaken (.bound 2) s.weaken.weaken.weaken.weaken (.bound 1))))))))))
derive_free_closed mem_force_m

theorem mem_force_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z p s t : Term n) :
    Formula.satisfies ρ (mem_force_m B R z p s t) ↔
      Mem_force_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [mem_force_m, Mem_force_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    below_sat_l M hE, entry_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push,
    Term.eval_bound_three_push]

private theorem match_local_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    (k : Bool) {p s t} (hs : M.mem s S) (ht : M.mem t S) :
    Match_d M k B R z F p s t ↔ Eq_match_d M k B R z p s t := by
  have he {r a d} (hr : M.mem r B) (ha : M.mem a S) (hd : M.mem d S) :
      (if k then Rel_d M F r d a else Rel_d M F r a d) ↔
      (if k then Eq_force_d M B R z r d a else Eq_force_d M B R z r a d) := by
    cases k
    · exact (eq_force_local_l M hZF hS hX hF hr ha hd).symm
    · exact (eq_force_local_l M hZF hS hX hF hr hd ha).symm
  constructor
  · intro h a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, hF⟩ := h a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he hr.1 (supp_entry_l M hS hs hab).1
      (supp_entry_l M hS ht hd).1).mp hF⟩
  · intro h a b hab q hq hqb
    obtain ⟨r, d, c, hr, hd, hrc, hE⟩ := h a b hab q hq hqb
    exact ⟨r, d, c, hr, hd, hrc, (he hr.1 (supp_entry_l M hS hs hab).1
      (supp_entry_l M hS ht hd).1).mpr hE⟩

/-- 等号的双向递归方程由实际最大双模拟证明，不把该方程作为输入假设。 -/
theorem eq_force_unfold_l (hZF : M.Models ZF) {B R z p s t}
    (hs : Name_d M B s) (ht : Name_d M B t) : Eq_force_d M B R z p s t ↔
      M.mem p B ∧ Eq_match_d M false B R z p s t ∧ Eq_match_d M true B R z p t s := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht
  obtain ⟨X, hX⟩ := triple_carrier_l M hZF B S
  obtain ⟨F, hF⟩ := bisim_max_l M hZF B R z X
  have he hp : Eq_force_d M B R z p s t ↔
      Eq_match_d M false B R z p s t ∧ Eq_match_d M true B R z p t s :=
    (eq_force_local_l M hZF hS hX hF hp hsS htS).trans
      ((bisim_unfold_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
        (KP.exists_union (ZF.modelsKP hZF)) hX hF hp hsS htS).trans
          (and_congr (match_local_l M hZF hS hX hF false hsS htS)
            (match_local_l M hZF hS hX hF true htS hsS)))
  exact ⟨fun h => ⟨h.1, (he h.1).mp h⟩, fun h => (he h.1).mpr h.2⟩

/-- 原子真值是条件集内的实际可定义子集。 -/
theorem eq_force_set_l (hZF : M.Models ZF) (B R z s t : M.Domain) :
    ∃ E, ∀ p, M.mem p E ↔ Eq_force_d M B R z p s t := by
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push s).push t
  let φ : UnarySchema 5 :=
    { body := eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 0) (.bound 2) (.bound 1) }
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF φ ρ B
  refine ⟨E, fun p => (hE p).trans ?_⟩
  have h := eq_force_sat_l M hZF.1 (ρ.push p) (.bound 5) (.bound 4) (.bound 3)
    (.bound 0) (.bound 2) (.bound 1)
  exact (and_congr_right fun _ => h).trans ⟨And.right, fun h => ⟨h.1, h⟩⟩

end YesMetaZFC.Model.Forcing.Internal
