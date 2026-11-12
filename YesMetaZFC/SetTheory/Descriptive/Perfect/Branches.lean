import YesMetaZFC.SetTheory.Descriptive.Analytic.Suslin
import YesMetaZFC.SetTheory.Card.Aleph.Hartogs
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.SetTheory.Descriptive.Demand.MapIteration

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

/-! ## 导集消失时的可数性

每个投影实数都有一个首次丧失分裂能力的前缀。同一前缀的消失阶段唯一，
且此阶段至多容纳一个投影实数，故这些前缀给出实际可数编号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sp_of_two_l (hZF : M.Models ZF) {ω A B J U q x v} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hq : M.mem q A)
    (hx : M.mem x B) (hv : M.mem v B) (ax : As_d I A B J U q x) (av : As_d I A B J U q v) (ne : x ≠ v) : Sp_d I ω J U q := by
  obtain ⟨y, p, hy, hp, pr, path, hqp⟩ := ax
  obtain ⟨w, r, hw, hr, rr, rpath, hqr⟩ := av
  have xf := (hB.2 x).mp hx
  have vf := (hB.2 v).mp hv
  have pf := (hB.2 p).mp hp
  have rf := (hB.2 r).mp hr
  obtain ⟨i, a, b, hi, hia, hib, hab⟩ := ds_differ_l I hZF.1 xf vf ne
  obtain ⟨c, hc, hic⟩ := ((hB.2 y).mp hy).2.2 i hi
  obtain ⟨d, hd, hid⟩ := ((hB.2 w).mp hw).2.2 i hi
  obtain ⟨j, _, hj⟩ := np_total_l I hJ (xf.output_mem_of_pairMember hia) hc
  obtain ⟨k, _, hk⟩ := np_total_l I hJ (vf.output_mem_of_pairMember hib) hd
  have pairs := no_and_l I hZF hB.1 pf rf
    (no_pair_l I hZF hB.1 pf rf false ((pr.2 i j).mpr ⟨a, c, hia, hic, hj⟩))
    (no_pair_l I hZF hB.1 pf rf true ((rr.2 i k).mpr ⟨b, d, hib, hid, hk⟩))
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := no_sub_l I hZF hB.1 hA rf pf hq hqr
  have back : No_d I ω p r (fun _ t => M.MemberSubset q t) := ⟨n, t, s, hn, ht, hs, fun _ _ h h' => obs _ _ h' h⟩
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := no_and_l I hZF hB.1 pf rf pairs
    (no_and_l I hZF hB.1 pf rf (no_sub_l I hZF hB.1 hA pf rf hq hqp) back)
  have sf := hs.isSetFunctionFromTo pf (hB.1.transitive (ZF.modelsKP hZF) n hn)
  have tf := ht.isSetFunctionFromTo rf (hB.1.transitive (ZF.modelsKP hZF) n hn)
  have ob := obs s t (fun _ => id) (fun _ => id)
  obtain ⟨s₀, s₁, hs₀, hs₁, ps⟩ := rp_decode_l I hZF hJ sf
  obtain ⟨t₀, t₁, ht₀, ht₁, pt⟩ := rp_decode_l I hZF hJ tf
  obtain ⟨a', c', ha', _, hc'⟩ := (ps.2 i j).mp ob.1.1
  obtain ⟨b', d', hb', _, hd'⟩ := (pt.2 i k).mp ob.1.2
  have ea := (np_injective_l I hJ hc' hj).1
  have eb := (np_injective_l I hJ hd' hk).1
  exact ⟨path q hq hqp, s, t,
    path s ((hA s).mpr ⟨n, hn, sf⟩) ((ds_restrict_iff_l I sf pf.1).mp hs),
    rpath t ((hA t).mpr ⟨n, hn, tf⟩) ((ds_restrict_iff_l I tf rf.1).mp ht), ob.2.1, ob.2.2,
    s₀, s₁, t₀, t₁, ⟨n, hn, hs₀, hs₁, ps⟩, ⟨n, hn, ht₀, ht₁, pt⟩,
    i, a', b', ha', hb', fun e => hab (ea.symm.trans (e.trans eb))⟩

def Thin_d (ω A B J T s x : M.Domain) : Prop := ∃ α U,
  Sd_d I ω J T α U ∧ M.mem s U ∧ ¬ Sp_d I ω J U s ∧ M.mem x B ∧ As_d I A B J U s x
def thin_m {d} (ω A B J T s x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (sd_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken T.weaken.weaken (.bound 1) .newest) (.conj
  (.mem s.weaken.weaken .newest) (.conj (.neg (sp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest s.weaken.weaken)) (.conj
  (.mem x.weaken.weaken B.weaken.weaken) (as_m (𝒞 := 𝒞) A.weaken.weaken B.weaken.weaken J.weaken.weaken .newest s.weaken.weaken x.weaken.weaken))))))
derive_free_closed thin_m
theorem thin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J T s x : Term d) :
    Formula.satisfies ρ (thin_m (𝒞 := 𝒞) ω A B J T s x) ↔
      Thin_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (T.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [thin_m, Thin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sd_sat_l I hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, sp_sat_l I hE,
    as_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem thin_unique_l (hZF : M.Models ZF) {ω A B J T s x y} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : M.mem s A)
    (hx : Thin_d I ω A B J T s x) (hy : Thin_d I ω A B J T s y) : x = y := by
  obtain ⟨α, U, hu, hsU, nu, hx, ax⟩ := hx
  obtain ⟨β, V, hv, hsV, nv, hy, ay⟩ := hy
  have ho {α U} (h : Sd_d I ω J T α U) : M.IsOrdinal α := h.elim fun _ h => h.1.1.1
  have e : α = β := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 (ho hu) (ho hv) (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α β) with e | e | e
    · exact hZF.1.eq_of_same_members α β e
    · exact (nu (((sd_unfold_l I hZF hv s).mp hsV).2 α U e hu)).elim
    · exact (nv (((sd_unfold_l I hZF hu s).mp hsU).2 β V e hv)).elim
  subst β
  have e := sd_unique_l I hZF hv hu
  subst V
  exact Classical.byContradiction (fun ne => nu (sp_of_two_l I hZF hB hA hJ hs hx hy ax ay ne))

theorem thin_exists_l (hZF : M.Models ZF) {ω A B J T K α U x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hT : Atree_d I A B J T K) (hu : Sd_d I ω J T α U)
    (he : ∀ s, ¬ M.mem s U) (hx : M.mem x K) : ∃ s, M.mem s A ∧ Thin_d I ω A B J T s x := by
  classical
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨hxB, y, p, hy, hp, pair, path, _⟩ := (as_root_l I hT hz x).mp hx
  have ha : M.IsOrdinal α := hu.elim fun _ h => h.1.1.1
  obtain ⟨δ, hd⟩ := KP.exists_successor (ZF.modelsKP hZF) α
  have ho := KP.successor_isOrdinal (ZF.modelsKP hZF) ha hd
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push A).push p
  let φ : UnarySchema 5 := { body := .existsE (.conj
    (sd_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)
    (.neg (branch_m (.bound 3) .newest (.bound 2)))) }
  have hv β : φ.denote ρ β ↔ ∃ V, Sd_d I ω J T β V ∧ ¬ Branch_d A V p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      sd_sat_l I hZF.1, Formula.satisfies_neg_iff, branch_sat_l]; rfl
  obtain ⟨D, hd'⟩ := ZF.separation_exists_d hZF φ ρ δ
  have hD β := (hd' β).trans (and_congr_right fun _ => hv β)
  have bad : ¬ Branch_d A U p := fun h => he z (h z ((hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩) (fun a h => (hz a h).elim))
  obtain ⟨β, hb, least⟩ := ho.wellOrder.least D (fun β hb => ((hD β).mp hb).1) ⟨α, (hD α).mpr ⟨hd.predecessor_mem, U, hu, bad⟩⟩
  obtain ⟨hbδ, V, hv, bad⟩ := (hD β).mp hb
  obtain ⟨s, hs, hsp, hn⟩ : ∃ s, M.mem s A ∧ M.MemberSubset s p ∧ ¬ M.mem s V := by
    exact Classical.byContradiction (fun h => bad (fun s hs sub => Classical.byContradiction (fun hn => h ⟨s, hs, sub, hn⟩)))
  obtain ⟨γ, W, hγβ, hw, ns⟩ : ∃ γ W, M.mem γ β ∧ Sd_d I ω J T γ W ∧ ¬ Sp_d I ω J W s := by
    exact Classical.byContradiction (fun h => hn ((sd_unfold_l I hZF hv s).mpr ⟨path s hs hsp,
      fun γ W hγ hw => Classical.byContradiction (fun ns => h ⟨γ, W, hγ, hw, ns⟩)⟩))
  have good : Branch_d A W p := by
    apply Classical.byContradiction
    intro no
    rcases least γ ((hD γ).mpr ⟨ho.transitive β hbδ γ hγβ, W, hw, no⟩) with e | e
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) γ (hZF.1.eq_of_same_members β γ e ▸ hγβ)
    · exact KP.mem_irrefl_d (ZF.modelsKP hZF) β ((ho.mem hbδ).transitive γ hγβ β e)
  exact ⟨s, hs, γ, W, hw, good s hs hsp, ns, hxB, y, p, hy, hp, pair, good, hsp⟩

theorem sd_empty_countable_l (hZF : M.Models ZF) {ω A B J T K α U} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hc : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hu : Sd_d I ω J T α U) (he : ∀ s, ¬ M.mem s U) :
    M.CardinalLessOrEqual I K ω := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push T).push K
  let φ : BinarySchema 6 := {
    body := .conj (.mem .newest (.bound 2))
      (thin_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have hp s x : φ.denote ρ s x ↔ M.mem x K ∧ Thin_d I ω A B J T s x := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, thin_sat_l I hZF.1]; rfl
  let ψ : UnarySchema 6 := { body := .existsE φ.body }
  obtain ⟨D, hd'⟩ := ZF.separation_exists_d hZF ψ ρ A
  have hd s : M.mem s D ↔ M.mem s A ∧ ∃ x, φ.denote ρ s x := by
    simpa only [ψ, Formula.satisfies_exists_iff, BinarySchema.denote] using hd' s
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := K)
    (fun s hs => ((hd s).mp hs).2)
    (fun s hs x y hx hy => thin_unique_l I hZF hB hA hJ ((hd s).mp hs).1 ((hp s x).mp hx).2 ((hp s y).mp hy).2)
    (fun s x _ hx => ((hp s x).mp hx).1)
  obtain ⟨E, hE⟩ := hc
  obtain ⟨G, hg⟩ := ZF.exists_inclusionInjection hZF I (fun s hs => ((hd s).mp hs).1)
  apply ZF.ordinal_image_bound_l I hZF (hB.1.isOrdinal (ZF.modelsKP hZF)) (ZF.exists_compositionInjection hZF I hg hE) hf
  intro x hx
  obtain ⟨s, hs, ht⟩ := thin_exists_l I hZF hB hA hT hu he hx
  have hsD := (hd s).mpr ⟨hs, x, (hp s x).mpr ⟨hx, ht⟩⟩
  exact ⟨s, hsD, (ef s x).mpr ⟨hsD, (hp s x).mpr ⟨hx, ht⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 稳定核上的规范二分函数

在候选子节点对的内部自然数编号中取最小者，形成两个实际函数图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pin_not_sub_l {ω J a b} (hJ : Npair_d I ω J) (h : Pin_d I ω J a b) :
    ¬ M.MemberSubset a b ∧ ¬ M.MemberSubset b a := by
  obtain ⟨s, t, u, v, pa, pb, i, x, y, hx, hy, ne⟩ := h
  have inc {f g} (h : M.MemberSubset f g) {x} (hx : M.PairMember I i x f) : M.PairMember I i x g :=
    hx.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
  refine ⟨fun sub => ?_, fun sub => ?_⟩
  · have hu : M.IsSetFunction I u := pb.elim fun _ h => h.2.1.1
    exact ne (hu.2 i x y (inc ((fp_sub_l I hJ pa pb).mp sub).1 hx) hy)
  · have hs : M.IsSetFunction I s := pa.elim fun _ h => h.2.1.1
    exact ne (hs.2 i x y hx (inc ((fp_sub_l I hJ pb pa).mp sub).1 hy))

def Split_d (ω A J U L R : M.Domain) : Prop := M.MemberSubset U A ∧
  M.IsSetFunctionFromTo I L U U ∧ M.IsSetFunctionFromTo I R U U ∧
  ∀ a b c, M.PairMember I a b L → M.PairMember I a c R →
    M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c

theorem splitting_l (hZF : M.Models ZF) {ω A J U} (hω : M.IsOmega ω)
    (hc : M.CardinalLessOrEqual I A ω) (sub : M.MemberSubset U A)
    (split : ∀ a, M.mem a U → Sp_d I ω J U a) : ∃ L R, Split_d I ω A J U L R := by
  obtain ⟨P, hp⟩ := ZF.exists_cartesianProduct hZF I U U
  obtain ⟨A', hA'⟩ := ZF.exists_cartesianProduct hZF I A A
  obtain ⟨E', he'⟩ := ZF.countable_product_l I hZF hω hc hc hA'
  have psub : M.MemberSubset P A' := fun p h => ((hp p).mp h).elim fun b h => h.2.elim fun c h' =>
    (hA' p).mpr ⟨b, sub b h.1, c, sub c h'.1, h'.2⟩
  obtain ⟨E, he⟩ := ZF.exists_restriction hZF I E' P
  have hei : M.IsSetInjectionFromTo I E P ω := ⟨he.isSetFunctionFromTo he'.1 psub,
    fun a b i ha hb => he'.2 a b i ((he.2 a i).mp ha).2 ((he.2 b i).mp hb).2⟩
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) P U
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.conj (𝒞.code (.bound 3) (.bound 1) .newest) (.conj
    (.mem (.bound 1) (.bound 4)) (.conj (.mem .newest (.bound 4)) (.conj
    (Formula.subset (.bound 2) (.bound 1)) (.conj (Formula.subset (.bound 2) .newest)
    (pin_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 1) .newest))))))) }
  have hφ p a : φ.denote ρ p a ↔ ∃ b c, I.Codes p b c ∧ M.mem b U ∧ M.mem c U ∧
      M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      I.satisfies_code_iff, Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, pin_sat_l I hZF.1]; rfl
  obtain ⟨Q, _, eqn⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ W
  let η : Env M 3 := ((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push E).push P
  let ψ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
    (nj_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))) }
  have hs a p : ψ.denote η a p ↔ M.mem p P ∧ ∃ i, M.PairMember I p i E ∧ Nj_d I Q E P a i := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, nj_sat_l I hZF.1]; rfl
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η (source := U) (target := P) (by
    intro a ha
    obtain ⟨_, b, c, hb, hc, hab, hac, pin⟩ := split a ha
    obtain ⟨p, pair⟩ := I.total b c
    have hpP := (hp p).mpr ⟨b, hb, c, hc, pair⟩
    obtain ⟨i, hi⟩ := nj_exists_l I hZF hei.1 ⟨p, hpP,
      (eqn p a).mpr ⟨(hw p).mpr (Or.inl hpP), (hw a).mpr (Or.inr ha), (hφ p a).mpr ⟨b, c, pair, hb, hc, hab, hac, pin⟩⟩, hpP⟩
    obtain ⟨q, hq, _, hqi⟩ := hi.1
    exact ⟨q, (hs a q).mpr ⟨hq, i, hqi, hi⟩⟩) (by
      intro a _ p q ha hb
      obtain ⟨_, i, hpi, hi⟩ := (hs a p).mp ha
      obtain ⟨_, j, hqj, hj⟩ := (hs a q).mp hb
      exact hei.2 p q i hpi (nj_unique_l I hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) hei.1 hj hi ▸ hqj))
    (fun a p _ h => ((hs a p).mp h).1)
  have selected {a p} (h : M.PairMember I a p F) : ∃ b c, I.Codes p b c ∧ M.mem b U ∧ M.mem c U ∧
      M.MemberSubset a b ∧ M.MemberSubset a c ∧ Pin_d I ω J b c := by
    obtain ⟨_, i, hpi, hi⟩ := (hs a p).mp ((ef a p).mp h).2
    obtain ⟨q, _, hqa, hqi⟩ := hi.1
    have e := hei.2 q p i hqi hpi
    exact (hφ p a).mp ((eqn p a).mp (e ▸ hqa)).2.2
  let δ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let χ (b : Bool) : BinarySchema 1 := {
    body := .existsE (.existsE (.conj
      (Formula.orderedPairMem 𝒞 (.bound 3) (.bound 1) (.bound 4))
      (𝒞.code (.bound 1) (if b then .newest else .bound 2) (if b then .bound 2 else .newest))))
    freeClosed := by cases b <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have hχ b a x : (χ b).denote δ a x ↔ ∃ p y, M.PairMember I a p F ∧ I.Codes p (if b then y else x) (if b then x else y) := by
    cases b <;> simp only [χ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff] <;> rfl
  have build (b : Bool) : ∃ L, M.IsSetFunctionFromTo I L U U ∧ ∀ a x,
      M.PairMember I a x L ↔ M.mem a U ∧ ∃ p y, M.PairMember I a p F ∧ I.Codes p (if b then y else x) (if b then x else y) := by
    obtain ⟨L, hl, el⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I (χ b) δ (source := U) (target := U) (by
      intro a ha
      obtain ⟨p, hpP, hap⟩ := hf.2.2 a ha
      obtain ⟨x, hx, y, hy, pair⟩ := (hp p).mp hpP
      cases b
      · exact ⟨x, (hχ false a x).mpr ⟨p, y, hap, pair⟩⟩
      · exact ⟨y, (hχ true a y).mpr ⟨p, x, hap, pair⟩⟩) (by
      intro a _ x y hx hy
      obtain ⟨p, u, hap, px⟩ := (hχ b a x).mp hx
      obtain ⟨q, v, haq, py⟩ := (hχ b a y).mp hy
      have e := I.injective px (hf.1.2 a q p haq hap ▸ py)
      cases b
      · exact e.1
      · exact e.2) (by
      intro a x _ hx
      obtain ⟨p, y, hap, pair⟩ := (hχ b a x).mp hx
      obtain ⟨u, hu, v, hv, pair'⟩ := (hp p).mp (hf.output_mem_of_pairMember hap)
      have e := I.injective pair pair'
      cases b
      · have ex : x = u := by simpa only [Bool.false_eq_true, ↓reduceIte] using e.1
        exact ex.symm ▸ hu
      · have ex : x = v := by simpa only [↓reduceIte] using e.2
        exact ex.symm ▸ hv)
    exact ⟨L, hl, fun a x => (el a x).trans (and_congr_right fun _ => hχ b a x)⟩
  obtain ⟨L, hl, el⟩ := build false
  obtain ⟨R, hr, er⟩ := build true
  refine ⟨L, R, sub, hl, hr, fun a b c hab hac => ?_⟩
  obtain ⟨_, p, v, hap, pair⟩ := (el a b).mp hab
  obtain ⟨_, q, u, haq, pair'⟩ := (er a c).mp hac
  obtain ⟨eu, ev⟩ := I.injective pair (hf.1.2 a q p haq hap ▸ pair')
  simp only [Bool.false_eq_true, ↓reduceIte] at eu ev
  subst u v
  obtain ⟨x, y, pxy, _, _, incb, incc, pin⟩ := selected hap
  obtain ⟨rfl, rfl⟩ := I.injective pxy pair
  exact ⟨incb, incc, pin⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 分裂节点的长度增长与自由坐标柱集 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem split_extend_l {ω A J U L R a b} (hs : Split_d I ω A J U L R)
    (h : M.PairMember I a b L ∨ M.PairMember I a b R) : M.MemberSubset a b := by
  rcases h with h | h
  · obtain ⟨c, _, hc⟩ := hs.2.2.1.2.2 a (hs.2.1.input_mem_of_pairMember h)
    exact (hs.2.2.2 a b c h hc).1
  · obtain ⟨c, _, hc⟩ := hs.2.1.2.2 a (hs.2.2.1.input_mem_of_pairMember h)
    exact (hs.2.2.2 a c b hc h).2.1

theorem split_grow_l (hZF : M.Models ZF) {ω A J U L R a b n m} (hω : M.IsOmega ω)
    (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (hn : M.mem n ω) (hm : M.mem m ω)
    (ha : M.IsSetFunctionFromTo I a n ω) (hb : M.IsSetFunctionFromTo I b m ω)
    (h : M.PairMember I a b L ∨ M.PairMember I a b R) : M.mem n m := by
  have sub := split_extend_l I hs h
  have ne : a ≠ b := by
    intro e
    subst b
    rcases h with h | h
    · obtain ⟨c, _, hc⟩ := hs.2.2.1.2.2 a (hs.2.1.input_mem_of_pairMember h)
      have s := hs.2.2.2 a a c h hc
      exact (pin_not_sub_l I hJ s.2.2).1 s.2.1
    · obtain ⟨c, _, hc⟩ := hs.2.1.2.2 a (hs.2.2.1.input_mem_of_pairMember h)
      have s := hs.2.2.2 a c a hc h
      exact (pin_not_sub_l I hJ s.2.2).2 s.1
  have nm : M.MemberSubset n m := fun i hi => (ha.2.2 i hi).elim fun x hx =>
    hb.input_mem_of_pairMember (hx.2.elim fun p hp => ⟨p, hp.1, sub p hp.2⟩)
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with e | e | e
  · have e := hZF.1.eq_of_same_members n m e
    subst m
    exact (ne (((ds_restrict_iff_l I ha hb.1).mpr sub).eq hZF.1 ((ds_restrict_iff_l I hb hb.1).mpr (fun _ => id)))).elim
  · exact e
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) m (nm m e)).elim

def Pre_d (ω J a x : M.Domain) : Prop := ∃ s t, Fp_d I ω J a s t ∧ M.MemberSubset s x
def pre_m {d} (ω J a x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken a.weaken.weaken (.bound 1) .newest)
  (Formula.subset (.bound 1) x.weaken.weaken)))
derive_free_closed pre_m
theorem pre_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J a x : Term d) :
    Formula.satisfies ρ (pre_m (𝒞 := 𝒞) ω J a x) ↔ Pre_d I (ω.eval ρ) (J.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [pre_m, Pre_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fp_sat_l I hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl
theorem pre_iff_l (hE : Extensional M) {ω J a s t x} (hJ : Npair_d I ω J) (h : Fp_d I ω J a s t) :
    Pre_d I ω J a x ↔ M.MemberSubset s x :=
  ⟨fun ⟨_, _, hp, sub⟩ => (fp_unique_l I hE hJ hp h).1 ▸ sub, fun sub => ⟨s, t, h, sub⟩⟩
theorem pre_mono_l (hZF : M.Models ZF) {ω A J a b x} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (ha : M.mem a A) (hab : M.MemberSubset a b) (h : Pre_d I ω J b x) : Pre_d I ω J a x := by
  obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ ha
  obtain ⟨u, v, hq, sub⟩ := h
  exact ⟨s, t, hp, fun p h => sub p (((fp_sub_l I hJ hp hq).mp hab).1 p h)⟩
theorem pre_disjoint_l (hE : Extensional M) {ω J a b x} (hJ : Npair_d I ω J)
    (h : Pin_d I ω J a b) (hx : M.IsSetFunction I x) (ha : Pre_d I ω J a x) (hb : Pre_d I ω J b x) : False := by
  obtain ⟨s, t, u, v, pa, pb, i, c, d, hc, hd, ne⟩ := h
  have hs := (pre_iff_l I hE hJ pa).mp ha
  have ht := (pre_iff_l I hE hJ pb).mp hb
  exact ne (hx.2 i c d (hc.elim fun p hp => ⟨p, hp.1, hs p hp.2⟩) (hd.elim fun p hp => ⟨p, hp.1, ht p hp.2⟩))

def Lc_d (A B x : M.Domain) (P : M.Domain → Prop) : Prop :=
  ∃ s, M.mem s A ∧ M.MemberSubset s x ∧ ∀ y, M.mem y B → M.MemberSubset s y → P y
theorem lc_and_l (hZF : M.Models ZF) {ω A B x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hx : M.mem x B) {P Q : M.Domain → Prop}
    (h : Lc_d A B x P) (k : Lc_d A B x Q) : Lc_d A B x (fun y => P y ∧ Q y) := by
  obtain ⟨s, hs, hsx, h⟩ := h
  obtain ⟨t, ht, htx, k⟩ := k
  obtain ⟨n, hn, hsf⟩ := (hA s).mp hs
  obtain ⟨m, hm, htf⟩ := (hA t).mp ht
  rcases ds_prefix_compare_l I hZF.1 (hB.1.isOrdinal (ZF.modelsKP hZF)) hn hm hsf htf ((hB.2 x).mp hx).1 hsx htx with inc | inc
  · exact ⟨t, ht, htx, fun y hy sub => ⟨h y hy (fun p hp => sub p (inc p hp)), k y hy sub⟩⟩
  · exact ⟨s, hs, hsx, fun y hy sub => ⟨h y hy sub, k y hy (fun p hp => sub p (inc p hp))⟩⟩

theorem pre_local_l (hZF : M.Models ZF) {ω A B J a x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (ha : M.mem a A) (hx : M.mem x B) :
    Lc_d A B x (fun y => Pre_d I ω J a y ↔ Pre_d I ω J a x) := by
  classical
  obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ ha
  have hs := (fp_type_l I hZF hA hJ hp).2.1
  have ep y := pre_iff_l I hZF.1 hJ (x := y) hp
  by_cases sub : M.MemberSubset s x
  · exact ⟨s, hs, sub, fun y _ hy => (ep y).trans (iff_of_true hy sub) |>.trans (ep x).symm⟩
  · obtain ⟨n, hn, hf⟩ := (hA s).mp hs
    obtain ⟨C, hc⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
    obtain ⟨u, V, hu, hv, hxV, disj⟩ := cyl_outside_l I hZF hB.1 hB.2 hA hn hf hc hx (fun h => sub ((hc x).mp h).2)
    exact ⟨u, hu, ((hv x).mp hxV).2, fun y hy huy => (ep y).trans
      ((iff_of_false (fun h => disj y ⟨(hc y).mpr ⟨hy, h⟩, (hv y).mpr ⟨hy, huy⟩⟩) sub).trans (ep x).symm)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 由自由实数决定的规范分裂路径

若左子柱集包含该实数就走左边，否则走右边。每个输入都有实际后继函数和
沿内部 ω 的轨道，后续闭性由有限段轨道的局部稳定性给出。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Hit_d (ω J L a x : M.Domain) : Prop := ∃ b, M.PairMember I a b L ∧ Pre_d I ω J b x
def hit_m {d} (ω J L a x : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 a.weaken .newest L.weaken) (pre_m (𝒞 := 𝒞) ω.weaken J.weaken .newest x.weaken))
derive_free_closed hit_m
theorem hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J L a x : Term d) :
    Formula.satisfies ρ (hit_m (𝒞 := 𝒞) ω J L a x) ↔ Hit_d I (ω.eval ρ) (J.eval ρ) (L.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [hit_m, Hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, pre_sat_l I hE, Definitional.Term.eval_weaken]; rfl
def Ws_d (ω J L R a b x : M.Domain) : Prop :=
  (Hit_d I ω J L a x ∧ M.PairMember I a b L) ∨ (¬ Hit_d I ω J L a x ∧ M.PairMember I a b R)
def ws_m {d} (ω J L R a b x : Term d) : Formula 1 d := .disj
  (.conj (hit_m (𝒞 := 𝒞) ω J L a x) (Formula.orderedPairMem 𝒞 a b L))
  (.conj (.neg (hit_m (𝒞 := 𝒞) ω J L a x)) (Formula.orderedPairMem 𝒞 a b R))
derive_free_closed ws_m
theorem ws_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J L R a b x : Term d) :
    Formula.satisfies ρ (ws_m (𝒞 := 𝒞) ω J L R a b x) ↔
      Ws_d I (ω.eval ρ) (J.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (b.eval ρ) (x.eval ρ) := by
  simp only [ws_m, Ws_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    hit_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff]
def Sel_d (ω J U L R x F : M.Domain) : Prop := M.IsSetFunctionFromTo I F U U ∧
  ∀ a b, M.PairMember I a b F ↔ M.mem a U ∧ Ws_d I ω J L R a b x
def sel_m {d} (ω J U L R x F : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 F U U)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
  (.conj (.mem (.bound 1) U.weaken.weaken)
    (ws_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken L.weaken.weaken R.weaken.weaken (.bound 1) .newest x.weaken.weaken)))))
derive_free_closed sel_m
theorem sel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R x F : Term d) :
    Formula.satisfies ρ (sel_m (𝒞 := 𝒞) ω J U L R x F) ↔
      Sel_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (x.eval ρ) (F.eval ρ) := by
  simp only [sel_m, Sel_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, ws_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem sel_exists_l (hZF : M.Models ZF) {ω A J U L R} (hs : Split_d I ω A J U L R) (x : M.Domain) :
    ∃ F, Sel_d I ω J U L R x F := by
  classical
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push L).push R).push x
  let φ : BinarySchema 5 := { body := ws_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest (.bound 2) }
  have hp a b : φ.denote ρ a b ↔ Ws_d I ω J L R a b x := ws_sat_l I hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨F, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := U) (target := U) (by
    intro a ha
    by_cases h : Hit_d I ω J L a x
    · obtain ⟨b, _, hb⟩ := hs.2.1.2.2 a ha
      exact ⟨b, (hp a b).mpr (Or.inl ⟨h, hb⟩)⟩
    · obtain ⟨b, _, hb⟩ := hs.2.2.1.2.2 a ha
      exact ⟨b, (hp a b).mpr (Or.inr ⟨h, hb⟩)⟩) (by
    intro a _ b c hb hc
    rcases (hp a b).mp hb with ⟨h, hb⟩ | ⟨h, hb⟩ <;> rcases (hp a c).mp hc with ⟨k, hc⟩ | ⟨k, hc⟩
    · exact hs.2.1.1.2 a b c hb hc
    · exact (k h).elim
    · exact (h k).elim
    · exact hs.2.2.1.1.2 a b c hb hc) (fun a b _ h => ((hp a b).mp h).elim
      (fun h => hs.2.1.output_mem_of_pairMember h.2) (fun h => hs.2.2.1.output_mem_of_pairMember h.2))
  exact ⟨F, hf, fun a b => (ef a b).trans (and_congr_right fun _ => hp a b)⟩
theorem sel_unique_l (hE : Extensional M) {ω J U L R x F G}
    (h : Sel_d I ω J U L R x F) (k : Sel_d I ω J U L R x G) : F = G :=
  h.1.1.1.eq_of_pairMember_iff hE k.1.1.1 (fun a b => (h.2 a b).trans (k.2 a b).symm)

def Walk_d (ω J U L R a n b x : M.Domain) : Prop := ∃ F, Sel_d I ω J U L R x F ∧ Iv_d I ω U F a n b
def walk_m {d} (ω J U L R a n b x : Term d) : Formula 1 d := .existsE (.conj
  (sel_m (𝒞 := 𝒞) ω.weaken J.weaken U.weaken L.weaken R.weaken x.weaken .newest)
  (iv_m (𝒞 := 𝒞) ω.weaken U.weaken .newest a.weaken n.weaken b.weaken))
derive_free_closed walk_m
theorem walk_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R a n b x : Term d) :
    Formula.satisfies ρ (walk_m (𝒞 := 𝒞) ω J U L R a n b x) ↔
      Walk_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (n.eval ρ) (b.eval ρ) (x.eval ρ) := by
  simp only [walk_m, Walk_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sel_sat_l I hE, iv_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem walk_bound_l {ω J U L R a n b x} (h : Walk_d I ω J U L R a n b x) : M.mem b U :=
  h.elim fun _ h => iv_bound_l I h.2
theorem walk_fixed_l (hE : Extensional M) {ω J U L R a n b x F} (hf : Sel_d I ω J U L R x F) :
    Walk_d I ω J U L R a n b x ↔ Iv_d I ω U F a n b := by
  exact ⟨fun ⟨G, hg, h⟩ => sel_unique_l I hE hg hf ▸ h, fun h => ⟨F, hf, h⟩⟩
theorem walk_exists_l (hZF : M.Models ZF) {ω A J U L R a n} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (hn : M.mem n ω) (x : M.Domain) : ∃ b, Walk_d I ω J U L R a n b x := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  exact (iv_exists_l I hZF hω hf.1 ha hn).imp fun b h => ⟨F, hf, h⟩
theorem walk_zero_l (hZF : M.Models ZF) {ω A J U L R a z b x} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (hz : ∀ p, ¬ M.mem p z) :
    Walk_d I ω J U L R a z b x ↔ b = a := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  exact (walk_fixed_l I hZF.1 hf).trans (iv_zero_l I hZF hω hf.1 ha hz)
theorem walk_succ_l (hZF : M.Models ZF) {ω J U L R a n m b x} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) : Walk_d I ω J U L R a m b x ↔
      ∃ c, Walk_d I ω J U L R a n c x ∧ Ws_d I ω J L R c b x := by
  constructor
  · rintro ⟨F, hf, h⟩
    obtain ⟨c, hc, hb⟩ := (iv_succ_l I hZF hω hf.1.1 hn hm).mp h
    exact ⟨c, ⟨F, hf, hc⟩, ((hf.2 c b).mp hb).2⟩
  · rintro ⟨c, ⟨F, hf, hc⟩, hb⟩
    exact ⟨F, hf, (iv_succ_l I hZF hω hf.1.1 hn hm).mpr ⟨c, hc, (hf.2 c b).mpr ⟨iv_bound_l I hc, hb⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 规范路径的局部稳定性与闭集解释 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ws_local_l (hZF : M.Models ZF) {ω A B J U L R a b x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (ha : M.mem a U) (hx : M.mem x B) (h : Ws_d I ω J L R a b x) : Lc_d A B x (fun y => Ws_d I ω J L R a b y) := by
  obtain ⟨c, hc, hac⟩ := hs.2.1.2.2 a ha
  have hit y : Hit_d I ω J L a y ↔ Pre_d I ω J c y :=
    ⟨fun ⟨d, hd, hy⟩ => hs.2.1.1.2 a d c hd hac ▸ hy, fun hy => ⟨c, hac, hy⟩⟩
  obtain ⟨s, hsa, sub, obs⟩ := pre_local_l I hZF hB hA hJ (hs.1 c hc) hx
  refine ⟨s, hsa, sub, fun y hy hyS => ?_⟩
  have eqn := (hit y).trans ((obs y hy hyS).trans (hit x).symm)
  exact h.elim (fun h => Or.inl ⟨eqn.mpr h.1, h.2⟩) (fun h => Or.inr ⟨fun hh => h.1 (eqn.mp hh), h.2⟩)

def wloc_m {d} (ω A B J U L R a n b x : Term d) : Formula 1 d := Formula.existsMem A (.conj
  (Formula.subset .newest x.weaken) (Formula.forallMem B.weaken (.imp (Formula.subset (.bound 1) .newest)
  (walk_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken U.weaken.weaken L.weaken.weaken R.weaken.weaken
    a.weaken.weaken n.weaken.weaken b.weaken.weaken .newest))))
derive_free_closed wloc_m
theorem wloc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J U L R a n b x : Term d) :
    Formula.satisfies ρ (wloc_m (𝒞 := 𝒞) ω A B J U L R a n b x) ↔ Lc_d (A.eval ρ) (B.eval ρ) (x.eval ρ)
      (fun y => Walk_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (n.eval ρ) (b.eval ρ) y) := by
  simp only [wloc_m, Lc_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    walk_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem walk_local_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∀ n, M.mem n ω → ∀ b x, M.mem x B → Walk_d I ω J U L R a n b x → Lc_d A B x (fun y => Walk_d I ω J U L R a n b y) := by
  let ρ : Env M 8 := (((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push U).push L).push R).push a
  let φ : UnarySchema 8 := { body := .forallE (.forallE (.imp (.mem .newest (.bound 8)) (.imp
    (walk_m (𝒞 := 𝒞) (.bound 10) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (wloc_m (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ b x, M.mem x B → Walk_d I ω J U L R a n b x → Lc_d A B x (fun y => Walk_d I ω J U L R a n b y) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, walk_sat_l I hZF.1, wloc_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz b x _ hb
    have e := (walk_zero_l I hZF hB.1 hs ha hz).mp hb
    obtain ⟨o, ho, hoω⟩ := hB.1.1.1
    exact ⟨o, (hA o).mpr ⟨o, hoω, ds_empty_fun_l I ho⟩, fun p hp => (ho p hp).elim,
      fun y _ _ => (walk_zero_l I hZF hB.1 hs ha hz).mpr e⟩
  · intro n hn ih m hm b x hx hb
    obtain ⟨c, hc, step⟩ := (walk_succ_l I hZF hB.1 hn hm).mp hb
    obtain ⟨s, hsA, sub, obs⟩ := lc_and_l I hZF hB hA hx (ih c x hx hc)
      (ws_local_l I hZF hB hA hJ hs (walk_bound_l I hc) hx step)
    exact ⟨s, hsA, sub, fun y hy hsy => (walk_succ_l I hZF hB.1 hn hm).mpr ⟨c, (obs y hy hsy).1, (obs y hy hsy).2⟩⟩

def Pw_d (ω J U L R a x : M.Domain) : Prop := ∀ n b, M.mem n ω → Walk_d I ω J U L R a n b x → Pre_d I ω J b x
def pw_m {d} (ω J U L R a x : Term d) : Formula 1 d := Formula.forallMem ω (.forallE (.imp
  (walk_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken U.weaken.weaken L.weaken.weaken R.weaken.weaken a.weaken.weaken (.bound 1) .newest x.weaken.weaken)
  (pre_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken .newest x.weaken.weaken)))
derive_free_closed pw_m
theorem pw_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J U L R a x : Term d) :
    Formula.satisfies ρ (pw_m (𝒞 := 𝒞) ω J U L R a x) ↔
      Pw_d I (ω.eval ρ) (J.eval ρ) (U.eval ρ) (L.eval ρ) (R.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [pw_m, Pw_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, walk_sat_l I hE, pre_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h n b hn => h n hn b, fun h n hn b => h n b hn⟩

theorem pw_closed_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∃ P, Cl_d A B P ∧ ∀ x, M.mem x P ↔ M.mem x B ∧ Pw_d I ω J U L R a x := by
  classical
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push U).push L).push R).push a
  let φ : UnarySchema 6 := { body := pw_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, hp'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hp x : M.mem x P ↔ M.mem x B ∧ Pw_d I ω J U L R a x :=
    (hp' x).trans (and_congr_right fun _ => pw_sat_l I hZF.1 _ _ _ _ _ _ _ _)
  obtain ⟨V, hv⟩ := cm_exists_l (ZF.modelsKP hZF) B P
  refine ⟨P, ⟨fun x hx => ((hp x).mp hx).1, V, hv, ⟨fun x hx => ((hv x).mp hx).1, fun x hx => ?_⟩⟩, hp⟩
  obtain ⟨hxB, hxP⟩ := (hv x).mp hx
  obtain ⟨n, b, hn, hb, bad⟩ : ∃ n b, M.mem n ω ∧ Walk_d I ω J U L R a n b x ∧ ¬ Pre_d I ω J b x := by
    exact Classical.byContradiction (fun h => hxP ((hp x).mpr ⟨hxB, fun n b hn hb =>
      Classical.byContradiction (fun bad => h ⟨n, b, hn, hb, bad⟩)⟩))
  obtain ⟨s, hsA, sub, obs⟩ := lc_and_l I hZF hB hA hxB (walk_local_l I hZF hB hA hJ hs ha n hn b x hxB hb)
    (pre_local_l I hZF hB hA hJ (hs.1 b (walk_bound_l I hb)) hxB)
  exact ⟨s, hsA, sub, fun y hy hsy => (hv y).mpr ⟨hy, fun hyP =>
    bad ((obs y hy hsy).2.mp (((hp y).mp hyP).2 n b hn (obs y hy hsy).1))⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 严格增长的内部前缀链之并

每一步至少增长一个内部坐标，因而第 n 个节点已经覆盖 n。
这同时给出无限函数图及任意有限前缀的阶段界。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem split_iter_length_l (hZF : M.Models ZF) {ω A J U L R F a H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hH : It_d I ω U F a H) (step : ∀ b c, M.PairMember I b c F → M.PairMember I b c L ∨ M.PairMember I b c R) :
    ∀ n, M.mem n ω → ∀ b m, M.PairMember I n b H → M.IsSetFunctionFromTo I b m ω → M.MemberSubset n m := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H
  let φ : UnarySchema 2 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 3)) (.imp
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest (.bound 4)) (Formula.subset (.bound 2) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ b m, M.PairMember I n b H → M.IsSetFunctionFromTo I b m ω → M.MemberSubset n m := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionFromTo_iff I hZF.1, Formula.satisfies_subset_iff]; rfl
  apply hω.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · exact fun z hz _ _ _ _ i hi => (hz i hi).elim
  · intro n hn ih j hj b m hb hbf
    obtain ⟨c, hc, hnc⟩ := hH.1.2.2 n hn
    obtain ⟨k, hk, hcf⟩ := (hA c).mp (hs.1 c hc)
    obtain ⟨m', hm', hbf'⟩ := (hA b).mp (hs.1 b (hH.1.output_mem_of_pairMember hb))
    have e := hbf'.2.1.eq hZF.1 hbf.2.1
    subst m'
    have hkm := split_grow_l I hZF hω hJ hs hk hm' hcf hbf (step c b (hH.2.2 n j c b hj hnc hb))
    have hnk := ih c k hnc hcf
    have hnm : M.mem n m := by
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn k hk with e | e | e
      · exact (hZF.1.eq_of_same_members n k e).symm ▸ hkm
      · exact ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm').transitive k hkm n e
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (hnk k e)).elim
    exact fun i hi => ((hj i).mp hi).elim
      (fun hi => ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm').transitive k hkm i (hnk i hi))
      (fun e => (hZF.1.eq_of_same_members i n e).symm ▸ hnm)

theorem split_fusion_l (hZF : M.Models ZF) {ω A J U L R F a H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hH : It_d I ω U F a H) (step : ∀ b c, M.PairMember I b c F → M.PairMember I b c L ∨ M.PairMember I b c R) :
    ∃ f, M.IsSetFunctionFromTo I f ω ω ∧ Cc_union_d I H f ∧
      ∀ s, M.mem s A → M.MemberSubset s f → ∃ n b, M.PairMember I n b H ∧ M.MemberSubset s b := by
  have len := split_iter_length_l I hZF hω hA hJ hs hH step
  have inc := ZF.cc_increasing_of_successor_l I hZF hω hH.1 (fun i j b c hij hb hc =>
    split_extend_l I hs (step b c (hH.2.2 i j b c hij hb hc)))
  obtain ⟨V, hv⟩ := ZF.exists_range_of_setFunction hZF I hH.1.1 hH.1.2.1
  obtain ⟨f, hf⟩ := KP.exists_union (ZF.modelsKP hZF) V
  have union : Cc_union_d I H f := fun p => (hf p).trans ⟨fun ⟨b, hb, hp⟩ =>
    ((hv b).mp hb).elim fun n hn => ⟨n, b, hn, hp⟩, fun ⟨n, b, hb, hp⟩ => ⟨b, (hv b).mpr ⟨n, hb⟩, hp⟩⟩
  have sub {n b} (hb : M.PairMember I n b H) : M.MemberSubset b f := fun p hp => (union p).mpr ⟨n, b, hb, hp⟩
  have nodes {n b} (hb : M.PairMember I n b H) := (hA b).mp (hs.1 b (hH.1.output_mem_of_pairMember hb))
  have pair i v : M.PairMember I i v f ↔ ∃ n b, M.PairMember I n b H ∧ M.PairMember I i v b := by
    exact ⟨fun ⟨p, hp, hpf⟩ => ((union p).mp hpf).elim fun n h => h.elim fun b h => ⟨n, b, h.1, p, hp, h.2⟩,
      fun ⟨n, b, hb, p, hp, hpb⟩ => ⟨p, hp, sub hb p hpb⟩⟩
  have total i (hi : M.mem i ω) : ∃ v, M.mem v ω ∧ M.PairMember I i v f := by
    obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    obtain ⟨b, _, hb⟩ := hH.1.2.2 n hnω
    obtain ⟨m, _, hbf⟩ := nodes hb
    obtain ⟨v, hv, hiv⟩ := hbf.2.2 i (len n hnω b m hb hbf i hn.predecessor_mem)
    exact ⟨v, hv, (pair i v).mpr ⟨n, b, hb, hiv⟩⟩
  have ff : M.IsSetFunctionFromTo I f ω ω := by
    refine ⟨⟨fun p hp => ((union p).mp hp).elim fun n h => h.elim fun b h =>
      (nodes h.1).elim fun m h' => h'.2.1.1 p h.2, ?_⟩, fun i => ⟨fun hi => (total i hi).imp fun _ h => h.2, ?_⟩, total⟩
    · intro i v w hv hw
      obtain ⟨n, b, hb, hv⟩ := (pair i v).mp hv
      obtain ⟨m, c, hc, hw⟩ := (pair i w).mp hw
      obtain ⟨_, _, hbf⟩ := nodes hb
      obtain ⟨_, _, hcf⟩ := nodes hc
      have lift {b c} (h : M.MemberSubset b c) {v} (hv : M.PairMember I i v b) : M.PairMember I i v c :=
        hv.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n (hH.1.input_mem_of_pairMember hb) m (hH.1.input_mem_of_pairMember hc) with e | e | e
      · have eqn := hH.1.1.2 m b c (hZF.1.eq_of_same_members n m e ▸ hb) hc
        exact hcf.1.2 i v w (eqn ▸ hv) hw
      · exact hcf.1.2 i v w (lift (inc n m b c e hb hc) hv) hw
      · exact hbf.1.2 i v w hv (lift (inc m n c b e hc hb) hw)
    · rintro ⟨v, hv⟩
      obtain ⟨n, b, hb, hv⟩ := (pair i v).mp hv
      obtain ⟨m, hm, hbf⟩ := nodes hb
      exact hω.transitive (ZF.modelsKP hZF) m hm i (hbf.input_mem_of_pairMember hv)
  refine ⟨f, ff, union, fun s hs hsf => ?_⟩
  obtain ⟨n, hn, hsn⟩ := (hA s).mp hs
  obtain ⟨b, _, hb⟩ := hH.1.2.2 n hn
  obtain ⟨m, _, hbm⟩ := nodes hb
  exact ⟨n, b, hb, ds_prefix_mono_l I hsn hbm.1 ((ds_restrict_iff_l I hsn ff.1).mpr hsf)
    ((ds_restrict_iff_l I hbm ff.1).mpr (sub hb)) (len n hn b m hb hbm)⟩

theorem fusion_projection_l (hZF : M.Models ZF) {ω A J U H f x y p} (hA : Fseq_space_d I ω ω A)
    (hJ : Npair_d I ω J) (hU : M.MemberSubset U A) (hH : M.IsSetFunctionFromTo I H ω U)
    (hf : Cc_union_d I H f) (hx : M.IsSetFunctionFromTo I x ω ω) (hy : M.IsSetFunctionFromTo I y ω ω)
    (hp : M.IsSetFunctionFromTo I p ω ω) (pair : Rp_d I J p y f)
    (pre : ∀ n b, M.PairMember I n b H → Pre_d I ω J b x) : p = x := by
  have sub : M.MemberSubset p x := by
    intro q hq
    obtain ⟨i, a, hqa⟩ := hp.1.1 q hq
    have hi := hp.input_mem_of_pairMember ⟨q, hqa, hq⟩
    obtain ⟨b, hb, hib⟩ := hy.2.2 i hi
    obtain ⟨v, _, hv⟩ := np_total_l I hJ (hp.output_mem_of_pairMember ⟨q, hqa, hq⟩) hb
    obtain ⟨r, hr, hrf⟩ := (pair.2 i v).mpr ⟨a, b, ⟨q, hqa, hq⟩, hib, hv⟩
    obtain ⟨n, s, hs, hrs⟩ := (hf r).mp hrf
    obtain ⟨t, u, ps⟩ := fp_decode_l I hZF hA hJ (hU s (hH.output_mem_of_pairMember hs))
    have ps' : Rp_d I J t u s := ps.elim fun _ h => h.2.2.2
    obtain ⟨c, d, hic, _, hcd⟩ := (ps'.2 i v).mp ⟨r, hr, hrs⟩
    have ep := (np_injective_l I hJ hcd hv).1
    have sub := (pre_iff_l I hZF.1 hJ ps).mp (pre n s hs)
    obtain ⟨q', hq', hq'x⟩ := hic
    exact (I.unique hqa (ep ▸ hq')).symm ▸ sub q' hq'x
  exact ((ds_restrict_iff_l I hp hx.1).mpr sub).eq hZF.1 ((ds_restrict_iff_l I hx hx.1).mpr (fun _ => id))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 分裂路径的实现及有限初段拼接 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem pw_pre_l (hZF : M.Models ZF) {ω A J U L R a x} (hω : M.IsOmega ω)
    (hs : Split_d I ω A J U L R) (ha : M.mem a U) (h : Pw_d I ω J U L R a x) : Pre_d I ω J a x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  exact h z a hzω ((walk_zero_l I hZF hω hs ha hz).mpr rfl)

theorem ws_of_pre_l (hE : Extensional M) {ω A J U L R a b x} (hJ : Npair_d I ω J)
    (hs : Split_d I ω A J U L R) (hx : M.IsSetFunction I x)
    (hc : M.PairMember I a b L ∨ M.PairMember I a b R) (hb : Pre_d I ω J b x) : Ws_d I ω J L R a b x := by
  rcases hc with hc | hc
  · exact Or.inl ⟨⟨b, hc, hb⟩, hc⟩
  · exact Or.inr ⟨fun ⟨c, hL, hp⟩ => pre_disjoint_l I hE hJ (hs.2.2.2 a c b hL hc).2.2 hx hp hb, hc⟩

theorem pw_prepend_l (hZF : M.Models ZF) {ω A B J U L R a b x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R)
    (hx : M.mem x B) (child : M.PairMember I a b L ∨ M.PairMember I a b R)
    (h : Pw_d I ω J U L R b x) : Pw_d I ω J U L R a x := by
  classical
  have ha := child.elim hs.2.1.input_mem_of_pairMember hs.2.2.1.input_mem_of_pairMember
  have hb := child.elim hs.2.1.output_mem_of_pairMember hs.2.2.1.output_mem_of_pairMember
  have pb := pw_pre_l I hZF hB.1 hs hb h
  have pa := pre_mono_l I hZF hA hJ (hs.1 a ha) (split_extend_l I hs child) pb
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  have first := (hf.2 a b).mpr ⟨ha, ws_of_pre_l I hZF.1 hJ hs ((hB.2 x).mp hx).1 child pb⟩
  intro n c hn hc
  have val := (walk_fixed_l I hZF.1 hf).mp hc
  by_cases he : ∀ i, ¬ M.mem i n
  · exact (iv_zero_l I hZF hB.1 hf.1 ha he).mp val |>.symm ▸ pa
  · have ne : ∃ i, M.mem i n := Classical.byContradiction (fun h => he (fun i hi => h ⟨i, hi⟩))
    obtain ⟨k, hk, hnk⟩ := hB.1.exists_predecessor_of_mem_of_nonempty hZF hn ne
    exact h k c hk ((walk_fixed_l I hZF.1 hf).mpr ((iv_shift_l I hZF hB.1 hf.1 hk hnk first).mp val))

theorem pw_ancestor_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∀ n, M.mem n ω → ∀ b x y, M.mem y B → Walk_d I ω J U L R a n b x →
      Pw_d I ω J U L R b y → Pw_d I ω J U L R a y := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push J).push U).push L).push R).push a
  let φ : UnarySchema 7 := { body := .forallE (.forallE (.forallE (.imp (.mem .newest (.bound 9)) (.imp
    (walk_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1)) (.imp
    (pw_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) .newest)
    (pw_m (𝒞 := 𝒞) (.bound 10) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest)))))) }
  have hp n : φ.denote ρ n ↔ ∀ b x y, M.mem y B → Walk_d I ω J U L R a n b x →
      Pw_d I ω J U L R b y → Pw_d I ω J U L R a y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, walk_sat_l I hZF.1, pw_sat_l I hZF.1]; rfl
  apply hB.1.induction
  · obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨D, fun n => (hd n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz b x y _ hb h
    exact (walk_zero_l I hZF hB.1 hs ha hz).mp hb ▸ h
  · intro n hn ih m hm b x y hy hb h
    obtain ⟨c, hc, step⟩ := (walk_succ_l I hZF hB.1 hn hm).mp hb
    exact ih c x y hy hc (pw_prepend_l I hZF hB hA hJ hs hy (step.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)) h)

theorem pw_nonempty_l (hZF : M.Models ZF) {ω A B J U L R a} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U) :
    ∃ x, M.mem x B ∧ Pw_d I ω J U L R a x := by
  obtain ⟨H, hh, hz, next⟩ := ZFC.iterate_l I hZF hB.1 hs.2.1 ha
  have it : It_d I ω U L a H := ⟨hh, hz, next⟩
  obtain ⟨f, ff, union, _⟩ := split_fusion_l I hZF hB.1 hA hJ hs it (fun _ _ h => Or.inl h)
  obtain ⟨x, y, hx, hy, pair⟩ := rp_decode_l I hZF hJ ff
  have pre n b (hb : M.PairMember I n b H) : Pre_d I ω J b x := by
    obtain ⟨s, t, hp⟩ := fp_decode_l I hZF hA hJ (hs.1 b (hh.output_mem_of_pairMember hb))
    obtain ⟨m, hm, sf, tf, hp'⟩ := hp
    exact ⟨s, t, ⟨m, hm, sf, tf, hp'⟩, ((rp_subset_l I hJ sf tf hp' pair).mp (fun p hp => (union p).mpr ⟨n, b, hb, hp⟩)).1⟩
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  have walk : It_d I ω U F a H := ⟨hh, hz, fun n m b c hm hb hc =>
    (hf.2 b c).mpr ⟨hh.output_mem_of_pairMember hb, Or.inl ⟨⟨c, next n m b c hm hb hc, pre m c hc⟩, next n m b c hm hb hc⟩⟩⟩
  refine ⟨x, (hB.2 x).mpr hx, fun n b hn hb => ?_⟩
  obtain ⟨c, _, hc⟩ := hh.2.2 n hn
  have e := iv_unique_l I hZF hB.1 hf.1.1 ((walk_fixed_l I hZF.1 hf).mp hb) ⟨H, walk, hc⟩
  exact e.symm ▸ pre n c hc

theorem pw_realize_l (hZF : M.Models ZF) {ω A B J U L R T a x} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hs : Split_d I ω A J U L R) (ha : M.mem a U)
    (hT : Tree_d A T) (sub : M.MemberSubset U T) (hx : M.mem x B) (h : Pw_d I ω J U L R a x) :
    ∃ y p, M.mem y B ∧ M.mem p B ∧ Rp_d I J x y p ∧ Branch_d A T p := by
  obtain ⟨F, hf⟩ := sel_exists_l I hZF hs x
  obtain ⟨H, hh, hz, next⟩ := ZFC.iterate_l I hZF hB.1 hf.1 ha
  have it : It_d I ω U F a H := ⟨hh, hz, next⟩
  have step b c (hb : M.PairMember I b c F) := ((hf.2 b c).mp hb).2.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨p, pf, union, cover⟩ := split_fusion_l I hZF hB.1 hA hJ hs it step
  obtain ⟨v, y, vf, yf, pair⟩ := rp_decode_l I hZF hJ pf
  have e := fusion_projection_l I hZF hA hJ hs.1 hh union ((hB.2 x).mp hx) yf vf pair
    (fun n b hb => h n b (hh.input_mem_of_pairMember hb) ⟨F, hf, H, it, hb⟩)
  subst v
  refine ⟨y, p, (hB.2 y).mpr yf, (hB.2 p).mpr pf, pair, fun s hsA hsp => ?_⟩
  obtain ⟨n, b, hb, hsb⟩ := cover s hsA hsp
  exact hT.2 b (sub b (hh.output_mem_of_pairMember hb)) s hsA hsb

end YesMetaZFC.SetTheory.Descriptive
