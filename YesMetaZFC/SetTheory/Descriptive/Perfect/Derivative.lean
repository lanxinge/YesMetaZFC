import YesMetaZFC.SetTheory.Descriptive.Analytic.Separation
import YesMetaZFC.SetTheory.Card.Aleph.Hartogs

/-! # 解析树的分裂导集与内部超限迭代

保留有两个自由坐标不相容的延伸的节点；在每个阶段同时施行全部先前阶段的
导集条件。Hartogs 定理保证在模型内部某一序数处稳定，不预设 ω₁ 正则。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Inc_d (s t : M.Domain) : Prop := ∃ i a b,
  M.PairMember I i a s ∧ M.PairMember I i b t ∧ a ≠ b
def inc_m {d} (s t : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) s.weaken.weaken.weaken) (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) .newest t.weaken.weaken.weaken)
  (.neg (Formula.extensionalEq (.bound 1) .newest))))))
derive_free_closed inc_m
theorem inc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (s t : Term d) :
    Formula.satisfies ρ (inc_m (𝒞 := 𝒞) s t) ↔ Inc_d I (s.eval ρ) (t.eval ρ) := by
  simp only [inc_m, Inc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]; rfl

def Pin_d (ω J a b : M.Domain) : Prop := ∃ s t u v,
  Fp_d I ω J a s t ∧ Fp_d I ω J b u v ∧ Inc_d I s u
def pin_m {d} (ω J a b : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken a.weaken.weaken.weaken.weaken (.bound 3) (.bound 2)) (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken (.bound 1) .newest)
  (inc_m (𝒞 := 𝒞) (.bound 3) (.bound 1)))))))
derive_free_closed pin_m
theorem pin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J a b : Term d) :
    Formula.satisfies ρ (pin_m (𝒞 := 𝒞) ω J a b) ↔ Pin_d I (ω.eval ρ) (J.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [pin_m, Pin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fp_sat_l I hE, inc_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Sp_d (ω J U a : M.Domain) : Prop := M.mem a U ∧ ∃ b c,
  M.mem b U ∧ M.mem c U ∧ M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c
def sp_m {d} (ω J U a : Term d) : Formula 1 d := .conj (.mem a U) (.existsE (.existsE (.conj
  (.mem (.bound 1) U.weaken.weaken) (.conj (.mem .newest U.weaken.weaken) (.conj
  (Formula.subset a.weaken.weaken (.bound 1)) (.conj (Formula.subset a.weaken.weaken .newest)
  (pin_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed sp_m
theorem sp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U a : Term d) :
    Formula.satisfies ρ (sp_m (𝒞 := 𝒞) ω J U a) ↔ Sp_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (a.eval ρ) := by
  simp only [sp_m, Sp_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_subset_iff, pin_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem sp_mono_l {ω J U V a} (h : M.MemberSubset U V) (hs : Sp_d I ω J U a) : Sp_d I ω J V a := by
  obtain ⟨ha, b, c, hb, hc, hab, hac, hp⟩ := hs
  exact ⟨h a ha, b, c, h b hb, h c hc, hab, hac, hp⟩

def Sd_step_d (ω J T F U : M.Domain) : Prop := ∀ a, M.mem a U ↔ M.mem a T ∧
  ∀ β V, M.PairMember I β V F → Sp_d I ω J V a
def sd_step_m {d} (ω J T F U : Term d) : Formula 1 d := .forallE (.iff (.mem .newest U.weaken)
  (.conj (.mem .newest T.weaken) (.forallE (.forallE (.imp
  (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken.weaken)
  (sp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken J.weaken.weaken.weaken .newest (.bound 2)))))))
derive_free_closed sd_step_m
theorem sd_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T F U : Term d) :
    Formula.satisfies ρ (sd_step_m (𝒞 := 𝒞) ω J T F U) ↔
      Sd_step_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (F.eval ρ) (U.eval ρ) := by
  simp only [sd_step_m, Sd_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, sp_sat_l I hE, Definitional.Term.eval_weaken]; rfl
def sd_op_s : BinarySchema 3 := { body := sd_step_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
def sd_env_l (ω J T : M.Domain) : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T
theorem sd_op_l (hE : Extensional M) (ρ : Env M 3) :
    (sd_op_s (𝒞 := 𝒞)).denote ρ = Sd_step_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext F U
  exact propext (sd_step_sat_l I hE ((ρ.push F).push U) _ _ _ _ _)

def Sd_d (ω J T α U : M.Domain) : Prop := M.IsRecursionValue I (Sd_step_d I ω J T) α U
def sd_m {d} (ω J T α U : Term d) : Formula 1 d := Formula.isRecursionValue 𝒞 (sd_op_s (𝒞 := 𝒞))
  (Definitional.TermVector.ofFn (Fin.cases T (Fin.cases J (fun _ => ω)))) α U
@[simp] theorem sd_closed_l {d} (ω J T α U : Term d) (hω : ω.freeSupport = []) (hJ : J.freeSupport = [])
    (hT : T.freeSupport = []) (hα : α.freeSupport = []) (hU : U.freeSupport = []) : (sd_m (𝒞 := 𝒞) ω J T α U).FreeClosed := by
  have he : (Definitional.TermVector.ofFn (Fin.cases T (Fin.cases J (fun _ : Fin 1 => ω)))).FreeClosed := by
    intro i
    cases i using Fin.cases with
    | zero => exact hT
    | succ i => cases i using Fin.cases with
      | zero => exact hJ
      | succ i => simpa only [Definitional.TermVector.get_ofFn, Fin.cases_succ] using hω
  exact Formula.isRecursionValue_freeClosed _ _ _ _ _ he hα hU
theorem sd_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T α U : Term d) :
    Formula.satisfies ρ (sd_m (𝒞 := 𝒞) ω J T α U) ↔
      Sd_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (α.eval ρ) (U.eval ρ) := by
  rw [sd_m, Formula.satisfies_isRecursionValue_iff I hE, sd_op_l I hE]; rfl

theorem sd_class_l (hZF : M.Models ZF) (ω J T : M.Domain) : M.IsClassFunctionOnTransfiniteSequences I (Sd_step_d I ω J T) := by
  intro F _
  let ρ := (sd_env_l ω J T).push F
  let φ : UnarySchema 4 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 3))
    (sp_m (𝒞 := 𝒞) (.bound 6) (.bound 5) .newest (.bound 2)))) }
  obtain ⟨U, hu⟩ := ZF.separation_exists_d hZF φ ρ T
  have step : Sd_step_d I ω J T F U := by
    intro a
    simpa only [φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, sp_sat_l I hZF.1] using! hu a
  exact ⟨U, step, fun V hv => hZF.1.eq_of_same_members V U (fun a => (hv a).trans (step a).symm)⟩
theorem sd_exists_l (hZF : M.Models ZF) {ω J T α} (hα : M.IsOrdinal α) : ∃ U, Sd_d I ω J T α U := by
  have hc := sd_class_l I hZF ω J T
  have op : (sd_op_s (𝒞 := 𝒞)).denote (sd_env_l ω J T) = Sd_step_d I ω J T := sd_op_l I hZF.1 _
  rw [← op] at hc
  obtain ⟨U, hu⟩ := ZF.recursionValue_exists hZF I (sd_env_l ω J T) sd_op_s hc hα
  exact ⟨U, by simpa only [Sd_d, op] using hu⟩
theorem sd_unique_l (hZF : M.Models ZF) {ω J T α U V} (h : Sd_d I ω J T α U) (k : Sd_d I ω J T α V) : U = V := by
  have hc := sd_class_l I hZF ω J T
  have op : (sd_op_s (𝒞 := 𝒞)).denote (sd_env_l ω J T) = Sd_step_d I ω J T := sd_op_l I hZF.1 _
  rw [← op] at hc
  exact ZF.recursionValue_unique hZF I (sd_env_l ω J T) sd_op_s hc
    (by simpa only [Sd_d, op] using h) (by simpa only [Sd_d, op] using k)

theorem sd_unfold_l (hZF : M.Models ZF) {ω J T α U} (h : Sd_d I ω J T α U) (a : M.Domain) :
    M.mem a U ↔ M.mem a T ∧ ∀ β V, M.mem β α → Sd_d I ω J T β V → Sp_d I ω J V a := by
  obtain ⟨F, hf, hu⟩ := h
  refine (hu a).trans (and_congr_right fun _ => ⟨?_, ?_⟩)
  · intro hs β V hb hv
    obtain ⟨W, hw⟩ := (hf.1.2.2 β).mp hb
    exact sd_unique_l I hZF (hf.recursionValue_of_pairMember hb hw) hv ▸ hs β W hw
  · intro hs β V hb
    have hβ := (hf.1.2.2 β).mpr ⟨V, hb⟩
    exact hs β V hβ (hf.recursionValue_of_pairMember hβ hb)
theorem sd_sub_l {ω J T α U} (h : Sd_d I ω J T α U) : M.MemberSubset U T :=
  h.elim fun _ h => fun a ha => ((h.2 a).mp ha).1
theorem sd_antitone_l (hZF : M.Models ZF) {ω J T α β U V}
    (hu : Sd_d I ω J T α U) (hv : Sd_d I ω J T β V) (hαβ : M.mem α β) : M.MemberSubset V U :=
  fun a ha => (((sd_unfold_l I hZF hv a).mp ha).2 α U hαβ hu).1

theorem sd_stable_l (hZF : M.Models ZF) (ω J T : M.Domain) :
    ∃ α U, M.IsOrdinal α ∧ Sd_d I ω J T α U ∧ ∀ a, M.mem a U ↔ Sp_d I ω J U a := by
  classical
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF T
  obtain ⟨κ, hk⟩ := ZF.exists_hartogsNumber hZF I P
  have hc := sd_class_l I hZF ω J T
  have op : (sd_op_s (𝒞 := 𝒞)).denote (sd_env_l ω J T) = Sd_step_d I ω J T := sd_op_l I hZF.1 _
  rw [← op] at hc
  obtain ⟨F, hf'⟩ := ZF.recursiveSequence_exists hZF I (sd_env_l ω J T) sd_op_s hc hk.1
  have hf : M.IsRecursiveSequence I (Sd_step_d I ω J T) F κ := by simpa only [op] using hf'
  have val {α U} (h : M.PairMember I α U F) : Sd_d I ω J T α U :=
    hf.recursionValue_of_pairMember ((hf.1.2.2 α).mpr ⟨U, h⟩) h
  apply Classical.byContradiction
  intro no
  -- 若没有稳定阶段，任意两层相等都会迫使较早层已稳定，故各层两两不同。
  have inj : M.IsSetInjectionFromTo I F κ P := by
    refine ⟨⟨hf.1.2.1, hf.1.2.2, fun α ha => ((hf.1.2.2 α).mp ha).imp fun U hu => ⟨(hp U).mpr (sd_sub_l I (val hu)), hu⟩⟩, ?_⟩
    intro α β U ha hb
    have same {α β U} (ha : M.PairMember I α U F) (hb : M.PairMember I β U F) (hαβ : M.mem α β) : False := by
      exact no ⟨α, U, hk.1.mem ((hf.1.2.2 α).mpr ⟨U, ha⟩), val ha,
        fun a => ⟨fun h => ((sd_unfold_l I hZF (val hb) a).mp h).2 α U hαβ (val ha), And.left⟩⟩
    rcases hk.1.wellOrder.linear.compare α ((hf.1.2.2 α).mpr ⟨U, ha⟩) β ((hf.1.2.2 β).mpr ⟨U, hb⟩) with e | e | e
    · exact hZF.1.eq_of_same_members α β e
    · exact (same ha hb e).elim
    · exact (same hb ha e).elim
  exact KP.mem_irrefl_d (ZF.modelsKP hZF) κ ((hk.2 κ hk.1).mpr ⟨F, inj⟩)

end YesMetaZFC.SetTheory.Descriptive
