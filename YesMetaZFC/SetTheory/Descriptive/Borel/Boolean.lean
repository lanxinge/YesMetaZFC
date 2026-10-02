import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 内部良基布尔递归

节点的值由叶值、补和并三条规则确定。先证明前驱封闭的部分解相容，再把所有
部分解的域和值分别用原公式分离收集；内部关系归纳证明合并后的域覆盖全部节点。
此处只使用模型内部良基性，不要求外部可达性，也不选择节点的值。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Br_step_d (T R L N U V a : M.Domain) : Prop := M.mem a L ∨
  (M.mem a N ∧ ∀ b, M.mem b T → Rd_entry_d b a R → ¬ M.mem b V) ∨
  (M.mem a U ∧ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V)
def br_step_m {d} (T R L N U V a : Term d) : Formula 1 d := .disj (.mem a L) (.disj
  (.conj (.mem a N) (Formula.forallMem T (.imp (rd_entry_m .newest a.weaken R.weaken)
    (.neg (.mem .newest V.weaken)))))
  (.conj (.mem a U) (Formula.existsMem T (.conj (rd_entry_m .newest a.weaken R.weaken)
    (.mem .newest V.weaken)))))
derive_free_closed br_step_m
theorem br_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R L N U V a : Term d) :
    Formula.satisfies ρ (br_step_m T R L N U V a) ↔
      Br_step_d (T.eval ρ) (R.eval ρ) (L.eval ρ) (N.eval ρ) (U.eval ρ) (V.eval ρ) (a.eval ρ) := by
  simp only [br_step_m, Br_step_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Br_part_d (T R L N U A V : M.Domain) : Prop := M.MemberSubset A T ∧ M.MemberSubset V A ∧
  (∀ a, M.mem a A → ∀ b, M.mem b T → Rd_entry_d b a R → M.mem b A) ∧
  ∀ a, M.mem a A → (M.mem a V ↔ Br_step_d T R L N U V a)
def br_part_m {d} (T R L N U A V : Term d) : Formula 1 d := .conj (Formula.subset A T)
  (.conj (Formula.subset V A) (.conj
    (Formula.forallMem A (Formula.forallMem T.weaken (.imp (rd_entry_m .newest (.bound 1) R.weaken.weaken)
      (.mem .newest A.weaken.weaken))))
    (Formula.forallMem A (.iff (.mem .newest V.weaken)
      (br_step_m T.weaken R.weaken L.weaken N.weaken U.weaken V.weaken .newest)))))
derive_free_closed br_part_m
theorem br_part_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R L N U A V : Term d) :
    Formula.satisfies ρ (br_part_m T R L N U A V) ↔
      Br_part_d (T.eval ρ) (R.eval ρ) (L.eval ρ) (N.eval ρ) (U.eval ρ) (A.eval ρ) (V.eval ρ) := by
  simp only [br_part_m, Br_part_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry_sat_l hE,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, br_step_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Br_eval_d (T R L N U V : M.Domain) : Prop := M.MemberSubset V T ∧
  ∀ a, M.mem a T → (M.mem a V ↔ Br_step_d T R L N U V a)
def br_eval_m {d} (T R L N U V : Term d) : Formula 1 d := .conj (Formula.subset V T)
  (Formula.forallMem T (.iff (.mem .newest V.weaken)
    (br_step_m T.weaken R.weaken L.weaken N.weaken U.weaken V.weaken .newest)))
derive_free_closed br_eval_m
theorem br_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R L N U V : Term d) :
    Formula.satisfies ρ (br_eval_m T R L N U V) ↔
      Br_eval_d (T.eval ρ) (R.eval ρ) (L.eval ρ) (N.eval ρ) (U.eval ρ) (V.eval ρ) := by
  simp only [br_eval_m, Br_eval_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    br_step_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem br_step_congr_l {T R L N U V W a : M.Domain}
    (h : ∀ b, M.mem b T → Rd_entry_d b a R → (M.mem b V ↔ M.mem b W)) :
    Br_step_d T R L N U V a ↔ Br_step_d T R L N U W a := by
  apply or_congr Iff.rfl
  apply or_congr
  · exact and_congr_right fun _ => ⟨fun hv b hb hr hw => hv b hb hr ((h b hb hr).mpr hw),
      fun hw b hb hr hv => hw b hb hr ((h b hb hr).mp hv)⟩
  · exact and_congr_right fun _ => exists_congr fun b => and_congr_right fun hb =>
      and_congr_right fun hr => h b hb hr

/-- 任意两个部分求值在共同定义域上一致。 -/
theorem br_agree_l (hZF : M.Models ZF) {T R L N U A V C W} (hw : Wf_rel_d T R)
    (h : Br_part_d T R L N U A V) (k : Br_part_d T R L N U C W) :
    ∀ a, M.mem a A → M.mem a C → (M.mem a V ↔ M.mem a W) := by
  let ρ : Env M 4 := (((⟨fun _ => A, fun _ => A⟩ : Env M 1).push C).push V).push W
  let φ : UnarySchema 4 := {
    body := .imp (.mem .newest (.bound 4))
      (.imp (.mem .newest (.bound 3)) (.iff (.mem .newest (.bound 2)) (.mem .newest (.bound 1)))) }
  have hp a : φ.denote ρ a ↔ M.mem a A → M.mem a C → (M.mem a V ↔ M.mem a W) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_iff_iff]; rfl
  have hall := wf_rel_ind_l hZF hw φ ρ (fun a _ ih => (hp a).mpr (fun ha hc =>
    (h.2.2.2 a ha).trans ((br_step_congr_l (fun b hb hr =>
      (hp b).mp (ih b hb hr) (h.2.2.1 a ha b hb hr) (k.2.2.1 a hc b hb hr))).trans (k.2.2.2 a hc).symm)))
  exact fun a ha hc => (hp a).mp (hall a (h.1 a ha)) ha hc

/-- 当前节点的前驱已有值时，实际添加这一节点及其布尔值。 -/
theorem br_extend_l (hZF : M.Models ZF) {T R L N U A V a}
    (h : Br_part_d T R L N U A V) (ha : M.mem a T) (hna : ¬ M.mem a A)
    (hp : ∀ b, M.mem b T → Rd_entry_d b a R → M.mem b A) :
    ∃ C W, Br_part_d T R L N U C W ∧ M.mem a C := by
  obtain ⟨C, hC⟩ := KP.exists_insert (ZF.modelsKP hZF) A a
  let ρ : Env M 7 := ((((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push R).push L).push N).push U).push V).push a
  let φ : UnarySchema 7 := {
    body := .disj (.mem .newest (.bound 2)) (.conj (Formula.extensionalEq .newest (.bound 1))
      (br_step_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1))) }
  have hφ b : φ.denote ρ b ↔ M.mem b V ∨ (b = a ∧ Br_step_d T R L N U V a) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, br_step_sat_l hZF.1]; rfl
  obtain ⟨W, hW'⟩ := ZF.separation_exists_d hZF φ ρ C
  have hW b : M.mem b W ↔ M.mem b V ∨ (b = a ∧ Br_step_d T R L N U V a) :=
    ((hW' b).trans (and_congr_right fun _ => hφ b)).trans
      ⟨And.right, fun h' => ⟨(hC b).mpr (h'.elim (fun hb => Or.inl (h.2.1 b hb)) (fun hb => Or.inr hb.1)), h'⟩⟩
  have old b (hb : M.mem b A) : M.mem b W ↔ M.mem b V := (hW b).trans
    ⟨fun h' => h'.elim id (fun e => (hna (e.1 ▸ hb)).elim), Or.inl⟩
  refine ⟨C, W, ⟨fun b hb => ((hC b).mp hb).elim (h.1 b) (fun e => e.symm ▸ ha),
    fun b hb => ((hW' b).mp hb).1, ?_, ?_⟩, (hC a).mpr (Or.inr rfl)⟩
  · intro b hb c hc hr
    exact (hC c).mpr (Or.inl (((hC b).mp hb).elim
      (fun hb => h.2.2.1 b hb c hc hr) (fun e => hp c hc (e ▸ hr))))
  · intro b hb
    rcases (hC b).mp hb with hb | e
    · exact (old b hb).trans ((h.2.2.2 b hb).trans (br_step_congr_l
        (fun c hc hr => (old c (h.2.2.1 b hb c hc hr)).symm)))
    · subst b
      have here : M.mem a W ↔ Br_step_d T R L N U V a := (hW a).trans
        ⟨fun h' => h'.elim (fun haV => (hna (h.2.1 a haV)).elim) And.right, fun h' => Or.inr ⟨rfl, h'⟩⟩
      exact here.trans (br_step_congr_l (fun b hb hr => (old b (hp b hb hr)).symm))

/-- 每个内部良基布尔树有唯一的模型内总求值集。 -/
theorem br_eval_exists_unique_l (hZF : M.Models ZF) {T R : M.Domain} (hw : Wf_rel_d T R)
    (L N U : M.Domain) : ∃ V, Br_eval_d T R L N U V ∧ ∀ W, Br_eval_d T R L N U W → W = V := by
  let ρ : Env M 5 := ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push R).push L).push N).push U
  let φ (v : Bool) : UnarySchema 5 := {
    body := .existsE (.existsE (.conj
      (br_part_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (.mem (.bound 2) (if v then .newest else .bound 1))))
    freeClosed := by cases v <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have hp v a : (φ v).denote ρ a ↔ ∃ C W, Br_part_d T R L N U C W ∧ M.mem a (if v then W else C) := by
    cases v <;> simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      br_part_sat_l hZF.1, Formula.satisfies_mem_iff, Bool.false_eq_true, ↓reduceIte] <;> rfl
  obtain ⟨A, hA'⟩ := ZF.separation_exists_d hZF (φ false) ρ T
  obtain ⟨V, hV'⟩ := ZF.separation_exists_d hZF (φ true) ρ T
  have hA a : M.mem a A ↔ ∃ C W, Br_part_d T R L N U C W ∧ M.mem a C :=
    ((hA' a).trans (and_congr_right fun _ => hp false a)).trans
      ⟨And.right, fun h => ⟨h.elim fun C h => h.elim fun W h => h.1.1 a h.2, h⟩⟩
  have hV a : M.mem a V ↔ ∃ C W, Br_part_d T R L N U C W ∧ M.mem a W :=
    ((hV' a).trans (and_congr_right fun _ => hp true a)).trans
      ⟨And.right, fun h => ⟨h.elim fun C h => h.elim fun W h => h.1.1 a (h.1.2.1 a h.2), h⟩⟩
  have agree {C W a} (h : Br_part_d T R L N U C W) (ha : M.mem a C) : M.mem a V ↔ M.mem a W := by
    refine ⟨fun hv => ?_, fun hv => (hV a).mpr ⟨C, W, h, hv⟩⟩
    obtain ⟨E, Z, hz, haz⟩ := (hV a).mp hv
    exact (br_agree_l hZF hw hz h a (hz.2.1 a haz) ha).mp haz
  have part : Br_part_d T R L N U A V := by
    refine ⟨fun a ha => ((hA' a).mp ha).1, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨C, W, h, ha⟩ := (hV a).mp ha
      exact (hA a).mpr ⟨C, W, h, h.2.1 a ha⟩
    · intro a ha b hb hr
      obtain ⟨C, W, h, ha⟩ := (hA a).mp ha
      exact (hA b).mpr ⟨C, W, h, h.2.2.1 a ha b hb hr⟩
    · intro a ha
      obtain ⟨C, W, h, ha⟩ := (hA a).mp ha
      exact (agree h ha).trans ((h.2.2.2 a ha).trans
        (br_step_congr_l (fun b hb hr => (agree h (h.2.2.1 a ha b hb hr)).symm)))
  have full : M.MemberSubset T A := by
    let ψ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
    let η : Env M 1 := ⟨fun _ => A, fun _ => A⟩
    have hψ a : ψ.denote η a ↔ M.mem a A := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_mem_iff]; rfl
    have all := wf_rel_ind_l hZF hw ψ η (fun a ha ih => (hψ a).mpr (by
      classical
      by_cases h : M.mem a A
      · exact h
      · obtain ⟨C, W, hw, hac⟩ := br_extend_l hZF part ha h (fun b hb hr => (hψ b).mp (ih b hb hr))
        exact (hA a).mpr ⟨C, W, hw, hac⟩))
    exact fun a ha => (hψ a).mp (all a ha)
  have ev : Br_eval_d T R L N U V := ⟨fun a ha => part.1 a (part.2.1 a ha),
    fun a ha => part.2.2.2 a (full a ha)⟩
  refine ⟨V, ev, fun W hW => ?_⟩
  have pv : Br_part_d T R L N U T V := ⟨fun _ h => h, ev.1, fun _ _ _ hb _ => hb, ev.2⟩
  have pw : Br_part_d T R L N U T W := ⟨fun _ h => h, hW.1, fun _ _ _ hb _ => hb, hW.2⟩
  have eqv := br_agree_l hZF hw pw pv
  exact hZF.1.eq_of_same_members W V (fun a =>
    ⟨fun ha => (eqv a (hW.1 a ha) (hW.1 a ha)).mp ha,
      fun ha => (eqv a (ev.1 a ha) (ev.1 a ha)).mpr ha⟩)

end YesMetaZFC.SetTheory.Descriptive
