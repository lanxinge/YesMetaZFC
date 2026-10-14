import YesMetaZFC.SetTheory.Descriptive.TreeBounded

/-! # 有限前缀树上的秩沿任意真延长下降

对较长节点的内部长度归纳，把任意延长分解为一个末项和较短前缀。
中间前缀由实际树的向下封闭性给出，所有秩值来自同一函数。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tb_rank_prefix_l {ω X F R α H : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (tree : Tree_d F R) (ordinal : M.IsOrdinal α)
    (rank : Fn0_d R α H)
    (decrease : ∀ s t a b, Rd_entry_d s a H → Rd_entry_d t b H → Tb_step_d ω X s t → M.mem b a) :
    ∀ s t a b, Rd_entry_d s a H → Rd_entry_d t b H → M.MemberSubset s t → s ≠ t → M.mem b a := by
  let η : Env M 2 := ⟨Fin.cases X (fun _ => H), fun _ => X⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪∀ t b,
    ⌜fn0_m⌝ₚ(⌜(Term.bound 0 : Term 3)⌝ₛ, ⌜(Term.bound 1 : Term 3)⌝ₛ, t) →
    ⌜rd_entry0_m⌝ₚ(t, b, ⌜(Term.bound 2 : Term 3)⌝ₛ) → ∀ s a,
    ⌜rd_entry0_m⌝ₚ(s, a, ⌜(Term.bound 2 : Term 3)⌝ₛ) → s ⊆ t → s = t ∨ b ∈ a⟫ }
  have sat n : φ.denote η n ↔ ∀ t b, Fn0_d n X t → Rd_entry_d t b H →
      ∀ s a, Rd_entry_d s a H → M.MemberSubset s t → s = t ∨ M.mem b a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_mem_iff,
      Definitional.Term.eval_weaken]; rfl
  have all := hw.induction (fun n => ∀ t b, Fn0_d n X t → Rd_entry_d t b H →
      ∀ s a, Rd_entry_d s a H → M.MemberSubset s t → s = t ∨ M.mem b a) (by
    obtain ⟨D, ds⟩ := ZF.separation_exists_d hZF φ η ω
    exact ⟨D, fun n => (ds n).trans (and_congr_right fun _ => sat n)⟩) (by
    intro e he t b ft _ s a _ sub
    have ft := fn0_function_l (ZF.modelsKP hZF) ft
    have empty p (hp : M.mem p t) : False := by
      obtain ⟨i, x, pair⟩ := ft.1.1 p hp
      exact he i (ft.input_mem_of_pairMember ⟨p, pair, hp⟩)
    exact Or.inl (hZF.1.eq_of_same_members s t (fun p => iff_of_false (fun hp => empty p (sub p hp)) (empty p)))) (by
    intro n hn ih m succ t b ft ht s a hs sub
    classical
    by_cases eq : s = t
    · exact Or.inl eq
    have htR := (rank.bound_l ht).1
    have hsR := (rank.bound_l hs).1
    obtain ⟨k, hk, fs⟩ := (space s).mp (tree.1 s hsR)
    have ft' := fn0_function_l (ZF.modelsKP hZF) ft
    obtain ⟨m', sm', hm'⟩ := hw.1.2 n hn
    have hm : M.mem m ω := sm'.eq hZF.1 succ ▸ hm'
    have km : M.MemberSubset k m := fun i hi => by
      obtain ⟨x, _, p, pair, hp⟩ := fs.2.2 i hi
      exact ft'.input_mem_of_pairMember ⟨p, pair, sub p hp⟩
    have km' : M.mem k m := by
      rcases (hw.isOrdinal hZF).wellOrder.linear.compare k hk m hm with e | lt | gt
      · have e := hZF.1.eq_of_same_members k m e
        have res := (ds_restrict_iff_l I fs ft'.1).mpr sub
        have own := (ds_restrict_iff_l I ft' ft'.1).mpr (fun _ h => h)
        exact (eq ((e ▸ res).eq hZF.1 own)).elim
      · exact lt
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (km m gt)).elim
    have kn : M.MemberSubset k n := ((succ k).mp km').elim
      (fun h => (hw.members_areOrdinals hZF n hn).transitive k h)
      (fun e => (hZF.1.eq_of_same_members k n e).symm ▸ (fun _ h => h))
    obtain ⟨p, res⟩ := ZF.exists_restriction hZF I t n
    have fp := res.isSetFunctionFromTo ft' (fun i hi => (succ i).mpr (Or.inl hi))
    have pt := (ds_restrict_iff_l I fp ft'.1).mp res
    have hpR := tree.2 t htR p ((space p).mpr ⟨n, hn, fp⟩) pt
    obtain ⟨r, _, hr⟩ := rank.2.1 p hpR
    have sp := ds_prefix_mono_l I fs fp.1 ((ds_restrict_iff_l I fs ft'.1).mpr sub) res kn
    have br := decrease p t r b hr ht ⟨n, hn, m, hm, fn0_of_function_l (ZF.modelsKP hZF) fp, ft, succ, pt⟩
    exact Or.inr ((ih p r (fn0_of_function_l (ZF.modelsKP hZF) fp) hr s a hs sp).elim
      (fun e => ((fn0_function_l (ZF.modelsKP hZF) rank).1.2 s r a (e.symm ▸ hr) hs) ▸ br)
      (fun ra => (ordinal.mem (rank.bound_l hs).2).transitive r ra b br)))
  intro s t a b hs ht sub ne
  obtain ⟨n, hn, ft⟩ := (space t).mp (tree.1 t (rank.bound_l ht).1)
  exact (all n hn t b (fn0_of_function_l (ZF.modelsKP hZF) ft) ht s a hs sub).elim (fun eq => (ne eq).elim) id

end YesMetaZFC.SetTheory.Descriptive
