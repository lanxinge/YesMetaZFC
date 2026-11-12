import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Ord.NaturalPrime
import YesMetaZFC.SetTheory.Descriptive.Coding.SequenceCons

/-! # 自然数博弈、策略与获胜

双方交替落子，先手占偶数坐标。策略是全部内部有限局面上的 ω 值函数；
另一方回合的值不参与服从条件。局面、策略及对局都是对象模型中的集合图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Gm_even_d (ω n : M.Domain) : Prop := ∃ k, M.mem k ω ∧ M.IsOrdinalAddition I n k k

def gm_even_m {d} (ω n : Term d) : Formula 1 d :=
  Formula.existsMem ω (Formula.isOrdinalAddition 𝒞 n.weaken .newest .newest)
derive_free_closed gm_even_m

theorem gm_even_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n : Term d) :
    Formula.satisfies ρ (gm_even_m (𝒞 := 𝒞) ω n) ↔ Gm_even_d I (ω.eval ρ) (n.eval ρ) := by
  simp only [gm_even_m, Gm_even_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_isOrdinalAddition_iff I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Gm_turn_d (p : Bool) (ω n : M.Domain) : Prop :=
  if p then Gm_even_d I ω n else ¬ Gm_even_d I ω n

def gm_turn_m (p : Bool) {d} (ω n : Term d) : Formula 1 d :=
  if p then gm_even_m (𝒞 := 𝒞) ω n else .neg (gm_even_m (𝒞 := 𝒞) ω n)

@[simp] theorem gm_turn_closed_l (p : Bool) {d} (ω n : Term d)
    (hω : ω.freeSupport = []) (hn : n.freeSupport = []) : (gm_turn_m (𝒞 := 𝒞) p ω n).FreeClosed := by
  cases p <;> simp [gm_turn_m, Definitional.Formula.FreeClosed, gm_even_m_freeClosed ω n hω hn]

theorem gm_turn_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω n : Term d) :
    Formula.satisfies ρ (gm_turn_m (𝒞 := 𝒞) p ω n) ↔ Gm_turn_d I p (ω.eval ρ) (n.eval ρ) := by
  cases p <;> simp only [gm_turn_m, Gm_turn_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_neg_iff, gm_even_sat_l I hE]

def Gm_follows_d (p : Bool) (ω σ x : M.Domain) : Prop :=
  ∀ n, M.mem n ω → Gm_turn_d I p ω n → ∀ s, M.IsRestrictionOf I s x n →
    ∀ a, M.PairMember I n a x → M.PairMember I s a σ

def gm_follows_m (p : Bool) {d} (ω σ x : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (gm_turn_m (𝒞 := 𝒞) p ω.weaken .newest)
    (.forallE (.imp (Formula.isRestriction 𝒞 .newest x.weaken.weaken (.bound 1))
      (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 2) .newest x.weaken.weaken.weaken)
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest σ.weaken.weaken.weaken))))))
derive_free_closed gm_follows_m

theorem gm_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω σ x : Term d) :
    Formula.satisfies ρ (gm_follows_m (𝒞 := 𝒞) p ω σ x) ↔
      Gm_follows_d I p (ω.eval ρ) (σ.eval ρ) (x.eval ρ) := by
  simp only [gm_follows_m, Gm_follows_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    gm_turn_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Gm_win_d (p : Bool) (ω B T A σ : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I σ T ω ∧ ∀ x, M.mem x B → Gm_follows_d I p ω σ x →
    if p then M.mem x A else ¬ M.mem x A

def gm_win_m (p : Bool) {d} (ω B T A σ : Term d) : Formula 1 d :=
  .conj (Formula.isFunctionFromTo 𝒞 σ T ω) (Formula.forallMem B
    (.imp (gm_follows_m (𝒞 := 𝒞) p ω.weaken σ.weaken .newest)
      (if p then .mem .newest A.weaken else .neg (.mem .newest A.weaken))))

@[simp] theorem gm_win_closed_l (p : Bool) {d} (ω B T A σ : Term d)
    (hω : ω.freeSupport = []) (hB : B.freeSupport = []) (hT : T.freeSupport = [])
    (hA : A.freeSupport = []) (hσ : σ.freeSupport = []) : (gm_win_m (𝒞 := 𝒞) p ω B T A σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [gm_win_m, Definitional.Formula.FreeClosed,
    Formula.isFunctionFromTo, hω, hB, hT, hA, hσ]

theorem gm_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω B T A σ : Term d) :
    Formula.satisfies ρ (gm_win_m (𝒞 := 𝒞) p ω B T A σ) ↔
      Gm_win_d I p (ω.eval ρ) (B.eval ρ) (T.eval ρ) (A.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [gm_win_m, Gm_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, gm_follows_sat_l I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]

def Det_d (ω B T A : M.Domain) : Prop :=
  (∃ σ, Gm_win_d I true ω B T A σ) ∨ ∃ σ, Gm_win_d I false ω B T A σ

def det_m {d} (ω B T A : Term d) : Formula 1 d :=
  .disj (.existsE (gm_win_m (𝒞 := 𝒞) true ω.weaken B.weaken T.weaken A.weaken .newest))
    (.existsE (gm_win_m (𝒞 := 𝒞) false ω.weaken B.weaken T.weaken A.weaken .newest))
derive_free_closed det_m

theorem det_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω B T A : Term d) :
    Formula.satisfies ρ (det_m (𝒞 := 𝒞) ω B T A) ↔ Det_d I (ω.eval ρ) (B.eval ρ) (T.eval ρ) (A.eval ρ) := by
  simp only [det_m, Det_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    gm_win_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 两个常值收益集合具有实际内部获胜策略；策略空间并非额外存在性前提。 -/
theorem gm_trivial_l (hZF : M.Models ZF) {ω B T e} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) :
    (∃ σ, Gm_win_d I true ω B T B σ) ∧ ∃ τ, Gm_win_d I false ω B T e τ := by
  obtain ⟨z, _, hz⟩ := hω.1.1
  obtain ⟨σ, hσ, _⟩ := ZF.exists_constantFunction hZF I (source := T) hz
  exact ⟨⟨σ, hσ, fun _ hx _ => hx⟩, ⟨σ, hσ, fun x _ _ => he x⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## AD 的原一阶句子

收益集合遍历内部 Baire 空间的全部内部子集；策略和对局也由同一模型量化。
存在量化的 ω、Baire 空间和有限局面空间在 ZF 中自动构造且唯一。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def AD_d : Prop := ∃ ω B T, Baire_d I ω B ∧ Fseq_space_d I ω ω T ∧
  ∀ A, M.MemberSubset A B → Det_d I ω B T A

def ad_m (𝒞 : OrderedPairConvention) : Formula 1 0 :=
  .existsE (.existsE (.existsE (.conj (baire_m (𝒞 := 𝒞) (.bound 2) (.bound 1))
    (.conj (fseq_space_m (𝒞 := 𝒞) (.bound 2) (.bound 2) .newest)
      (.forallE (.imp (Formula.subset .newest (.bound 2))
        (det_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest)))))))

theorem ad_closed_l : (ad_m 𝒞).FreeClosed := by
  simp -implicitDefEqProofs [ad_m, Definitional.Formula.FreeClosed]

theorem ad_sat_l (hE : Extensional M) (ρ : Env M 0) :
    Formula.satisfies ρ (ad_m 𝒞) ↔ AD_d I := by
  simp only [ad_m, AD_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    baire_sat_l I hE, fseq_space_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, det_sat_l I hE]
  rfl

/-- 固定任何实际空间后，AD 恰好断言每个收益集合有一方的内部获胜策略。 -/
theorem ad_iff_l (hE : Extensional M) {ω B T} (hB : Baire_d I ω B) (hT : Fseq_space_d I ω ω T) :
    AD_d I ↔ ∀ A, M.MemberSubset A B → Det_d I ω B T A := by
  refine ⟨?_, fun h => ⟨ω, B, T, hB, hT, h⟩⟩
  rintro ⟨v, C, U, hC, hU, h⟩
  have ev : v = ω := hE.eq_of_same_members v ω (fun n =>
    ⟨hC.1.2 ω hB.1.1 n, hB.1.2 v hC.1.1 n⟩)
  subst v
  have eC := baire_unique_l I hE hC hB
  subst C
  have eU : U = T := hE.eq_of_same_members U T (fun s => (hU s).trans (hT s).symm)
  exact eU ▸ h

end YesMetaZFC.SetTheory.Descriptive

namespace YesMetaZFC.SetTheory
open Definitional.Project

def Axioms.ad_axiom : Sentence := Sentence.ofFormula
  (Descriptive.ad_m kpair_convention_l) Descriptive.ad_closed_l

namespace ZFAD
inductive Axiom : Theory where
  | zf {s : Sentence} : ZF s → Axiom s
  | ad : Axiom Axioms.ad_axiom
end ZFAD

abbrev ZFAD : Theory := ZFAD.Axiom

theorem ad_axiom_sat_l {M : Structure.{u}} (hKP : M.Models KP) :
    M.SatisfiesSentence Axioms.ad_axiom ↔ Descriptive.AD_d (InnerModel.kp_pair_l hKP) := by
  rw [Structure.satisfiesSentence_iff]
  constructor
  · intro h
    obtain ⟨x⟩ := M.nonempty
    exact (Descriptive.ad_sat_l (InnerModel.kp_pair_l hKP) hKP.1 ⟨Fin.elim0, fun _ => x⟩).mp (h (fun _ => x))
  · intro h f
    exact (Descriptive.ad_sat_l (InnerModel.kp_pair_l hKP) hKP.1 ⟨Fin.elim0, f⟩).mpr h

end YesMetaZFC.SetTheory

/-! ## 内部回合在后继处换手

用模型自己的除二商余分解证明奇偶翻转，不对外部自然数作归纳。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem gm_even_zero_l {ω z : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) : Gm_even_d I ω z := by
  obtain ⟨e, he, heω⟩ := hw.1.1
  have eq := hZF.1.eq_of_same_members e z fun x => iff_of_false (he x) (hz x)
  exact ⟨z, eq ▸ heω, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩

theorem gm_even_successor_l {ω n m : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (sm : M.SuccessorOf m n) : Gm_even_d I ω m ↔ ¬ Gm_even_d I ω n := by
  obtain ⟨z, hz, hzω⟩ := hw.1.1
  obtain ⟨o, so, ho⟩ := hw.1.2 z hzω
  obtain ⟨t, st, ht⟩ := hw.1.2 o ho
  obtain ⟨m', sm', hm'⟩ := hw.1.2 n hn
  have hm := sm'.eq hZF.1 sm ▸ hm'
  have ot := hw.members_areOrdinals (ZF.modelsKP hZF) t ht
  have oo := hw.members_areOrdinals (ZF.modelsKP hZF) o ho
  have oz : o ≠ z := fun eq => hz z (eq ▸ so.predecessor_mem)
  have zt : M.mem z t := (st z).mpr (Or.inl so.predecessor_mem)
  -- 自然数乘法交换律把除二的乘积与博弈所用的 k+k 对齐。
  have twice {k v} (hk : M.mem k ω) : M.IsOrdinalMultiplication I v t k ↔ M.IsOrdinalAddition I v k k := by
    have read {v} (mul : M.IsOrdinalMultiplication I v t k) : M.IsOrdinalAddition I v k k := by
      obtain ⟨r, kr, _⟩ := ZF.ordinalMultiplication_existsUnique hZF I k ot
      have eq := Structure.natural_mul_comm hZF I hw ht hk mul kr; subst r
      obtain ⟨p, kp, add⟩ := (ZF.ordinalMultiplication_successor_iff hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) k hk) oo st).mp kr
      exact ZF.ordinalMultiplication_one_right hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) k hk) ⟨z, hz, so⟩ kp ▸ add
    refine ⟨read, fun add => ?_⟩
    obtain ⟨p, mul, _⟩ := ZF.ordinalMultiplication_existsUnique hZF I t (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
    obtain ⟨_, _, unique⟩ := ZF.ordinalAddition_existsUnique hZF I k (hw.members_areOrdinals (ZF.modelsKP hZF) k hk)
    exact (unique p (read mul)).trans (unique v add).symm ▸ mul
  -- 商余唯一性给出“偶数当且仅当余数为零”；后继只交换两个余数。
  have rem {i q r} (hi : M.mem i ω) (div : M.IsOrdinalDivision I i t q r) : Gm_even_d I ω i ↔ r = z := by
    constructor
    · rintro ⟨k, hk, add⟩
      have dz : M.IsOrdinalDivision I i t k z := ⟨hw.members_areOrdinals (ZF.modelsKP hZF) k hk, zt, i,
        (twice hk).mpr add, (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩
      obtain ⟨_, _, _, unique⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) i hi) ot ⟨o, st.predecessor_mem⟩
      exact (unique q r div).2.trans (unique k z dz).2.symm
    · intro eq; subst r
      have hq := Structure.nat_div_quotient_mem_omega hZF I hw hi ht ⟨o, st.predecessor_mem⟩ div
      obtain ⟨_, _, p, mul, add⟩ := div
      exact ⟨q, hq, (ZF.ordinalAddition_zero_iff hZF I hz).mp add |>.symm ▸ (twice hq).mp mul⟩
  obtain ⟨q, r, div, _⟩ := ZF.ordinalDivision_existsUnique_pair hZF I (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) ot ⟨o, st.predecessor_mem⟩
  have cases : r = z ∨ r = o := ((st r).mp div.2.1).elim
    (fun h => ((so r).mp h).elim (fun h => (hz r h).elim) (fun h => Or.inl (hZF.1.eq_of_same_members r z h)))
    (fun h => Or.inr (hZF.1.eq_of_same_members r o h))
  rcases cases with rfl | rfl
  · have d := div
    obtain ⟨oq, _, p, mul, add⟩ := d
    have next : M.IsOrdinalDivision I m t q o := ⟨oq, st.predecessor_mem, p, mul,
      (ZF.ordinalAddition_successor_iff hZF I (Structure.IsOrdinal.of_no_members hz) so).mpr ⟨n, add, sm⟩⟩
    exact ⟨fun even => (oz ((rem hm next).mp even)).elim, fun no => (no ((rem hn div).mpr rfl)).elim⟩
  · have hq := Structure.nat_div_quotient_mem_omega hZF I hw hn ht ⟨_, st.predecessor_mem⟩ div
    obtain ⟨q', sq, hq'⟩ := hw.1.2 q hq
    have d := div
    obtain ⟨oq, _, p, mul, add⟩ := d
    have next : M.IsOrdinalDivision I m t q' z := ⟨hw.members_areOrdinals (ZF.modelsKP hZF) q' hq', zt, m,
      (ZF.ordinalMultiplication_successor_iff hZF I ot oq sq).mpr ⟨p, mul,
        (ZF.ordinalAddition_successor_iff hZF I oo st).mpr ⟨n, add, sm⟩⟩,
      (ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl⟩
    exact ⟨fun _ even => oz ((rem hn div).mp even), fun _ => (rem hm next).mpr rfl⟩

theorem gm_turn_successor_l (b : Bool) {ω n m : M.Domain} (hw : M.IsOmega ω) (hn : M.mem n ω)
    (sm : M.SuccessorOf m n) : Gm_turn_d I b ω m ↔ Gm_turn_d I (!b) ω n := by
  cases b
  · change (¬ Gm_even_d I ω m) ↔ Gm_even_d I ω n
    exact ⟨fun no => Classical.byContradiction (fun odd => no ((gm_even_successor_l I hZF hw hn sm).mpr odd)),
      fun even next => ((gm_even_successor_l I hZF hw hn sm).mp next) even⟩
  · exact gm_even_successor_l I hZF hw hn sm

end YesMetaZFC.SetTheory.Descriptive

/-! ## 插入一手后换手的实际策略

新策略在局面 s 查询旧策略于 a⌢s 的值。首手属于旧 I 时必须取旧策略自身的输出；
此后所有回合由内部后继奇偶律对应，有限前缀保证策略调用具有因果性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem gm_shift_l {ω A F z a σ : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (strategy : M.IsSetFunctionFromTo I σ F A) :
    ∃ τ, M.IsSetFunctionFromTo I τ F A ∧ ∀ s v, M.PairMember I s v τ ↔
      M.mem s F ∧ ∃ t, Cons_d I z a s t ∧ M.PairMember I t v σ := by
  let ρ : Env M 2 := ⟨fun i => [z, a].get i, fun _ => z⟩
  let φ : BinarySchema 2 := { body := cons_m (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat s t : φ.denote ρ s t ↔ Cons_d I z a s t := cons_sat_l I hZF.1 ..
  obtain ⟨C, fc, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := F) (by
    intro s hs
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨_, t, _, _, _, ct⟩ := cons_exists_l I hZF hw hz ha hn fs
    exact ⟨t, (sat s t).mpr ct⟩)
    (fun _ _ _ _ ht hu => cons_unique_l I hZF.1 ((sat ..).mp ht) ((sat ..).mp hu)) (by
      intro s t hs ht
      obtain ⟨n, hn, fs⟩ := (space s).mp hs
      obtain ⟨k, hk, _, ft⟩ := cons_type_l I hZF hw hz ha hn fs ((sat s t).mp ht)
      exact (space t).mpr ⟨k, hk, ft⟩)
  obtain ⟨τ, fτ, values⟩ := ZF.exists_compositionFunction hZF I fc strategy
  refine ⟨τ, fτ, fun s v => (values s v).trans (and_congr_right fun hs => ?_)⟩
  exact exists_congr fun t => and_congr_left fun _ => ((graph s t).trans
    ((and_congr_right fun _ => sat s t).trans ⟨And.right, fun h => ⟨hs, h⟩⟩))

theorem gm_shift_follows_l {b : Bool} {ω A F z a σ τ f g : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (values : ∀ s v, M.PairMember I s v τ ↔ M.mem s F ∧ ∃ t, Cons_d I z a s t ∧ M.PairMember I t v σ)
    (first : b = true → M.PairMember I z a σ) (ff : M.IsSetFunctionFromTo I f ω A)
    (fg : M.IsSetFunctionFromTo I g ω A) (cons : Cons_d I z a f g)
    (follow : Gm_follows_d I (!b) ω τ f) : Gm_follows_d I b ω σ g := by
  intro j hj turn s cut v jv
  rcases omega_zero_or_succ_l hZF hw hz hj with eq | ⟨i, hi, sj⟩
  · subst j
    have eq : s = z := hZF.1.eq_of_same_members s z fun q => iff_of_false (fun hq => by
      obtain ⟨i, x, c⟩ := cut.1 q hq
      exact hz i ((cut.2 i x).mp ⟨q, c, hq⟩).1) (hz q)
    subst s
    have ev : v = a := ((cons.2 z v).mp jv).elim And.right (fun ⟨i, _, sz⟩ => (hz i sz.predecessor_mem).elim)
    subst v
    cases b
    · exact (turn (gm_even_zero_l I hZF hw hz)).elim
    · exact first rfl
  · obtain ⟨r, fr, rf, _⟩ := ds_prefix_l I hZF hw ff hi
    obtain ⟨k, t, _, sk, ft, ct⟩ := cons_exists_l I hZF hw hz ha hi fr
    have eq := sk.eq hZF.1 sj; subst k
    have tg := (cons_subset_l I hZF hw hz hi fr ct cons).mpr ⟨rfl, (ds_restrict_iff_l I fr ff.1).mp rf⟩
    have eq := ((ds_restrict_iff_l I ft fg.1).mpr tg).eq hZF.1 cut; subst s
    have rv := follow i hi ((gm_turn_successor_l I hZF b hw hi sj).mp turn) r rf v
      ((cons.successor_l I hZF hw hz hi sj).mp jv)
    obtain ⟨_, u, cu, uv⟩ := (values r v).mp rv
    exact cons_unique_l I hZF.1 cu ct ▸ uv

end YesMetaZFC.SetTheory.Descriptive
