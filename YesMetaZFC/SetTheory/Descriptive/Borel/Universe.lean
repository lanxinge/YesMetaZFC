import YesMetaZFC.SetTheory.Descriptive.Borel.Relabel
import YesMetaZFC.SetTheory.Collapse.RelationEvaluationExistence

/-! # 基本柱集的规范单节点码

直接用单元素集合打包，码构造只需 KP；唯一性只需外延性。
先固定规范码再按内部指标收集，避免为每个基本开集任选一个码。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bbasic_d (s c : M.Domain) : Prop := ∃ z T p F,
  (∀ x, ¬ M.mem x z) ∧ M.IsSingletonOf T z ∧ I.Codes p z s ∧ M.IsSingletonOf F p ∧ Bpack_d I c T z z F
def bbasic_m {d} (s c : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (Formula.isEmpty (.bound 3)) (.conj (Formula.isSingleton (.bound 2) (.bound 3))
    (.conj (𝒞.code (.bound 1) (.bound 3) s.weaken.weaken.weaken.weaken)
      (.conj (Formula.isSingleton .newest (.bound 1))
        (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 2) (.bound 3) (.bound 3) .newest))))))))
derive_free_closed bbasic_m

theorem bbasic_sat_l (hE : Extensional M) {d} (ρ : Env M d) (s c : Term d) :
    Formula.satisfies ρ (bbasic_m (𝒞 := 𝒞) s c) ↔ Bbasic_d I (s.eval ρ) (c.eval ρ) := by
  simp only [bbasic_m, Bbasic_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSingleton_iff hE, I.satisfies_code_iff,
    bpack_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem bbasic_exists_l (hKP : M.Models KP) (s : M.Domain) : ∃ c, Bbasic_d I s c := by
  obtain ⟨z, hz⟩ := KP.exists_empty hKP
  obtain ⟨T, hT⟩ := KP.exists_singleton hKP z
  obtain ⟨p, hp⟩ := I.total z s
  obtain ⟨F, hF⟩ := KP.exists_singleton hKP p
  obtain ⟨c, hc⟩ := bpack_exists_l I T z z F
  exact ⟨c, z, T, p, F, hz, hT, hp, hF, hc⟩

theorem bbasic_unique_l (hE : Extensional M) {s c d} (h : Bbasic_d I s c) (k : Bbasic_d I s d) : c = d := by
  obtain ⟨z, T, p, F, hz, hT, hp, hF, hc⟩ := h
  obtain ⟨z', T', p', F', hz', hT', hp', hF', hd⟩ := k
  have e := hE.eq_of_same_members z z' (fun x => iff_of_false (hz x) (hz' x))
  subst z'
  have e := hT.eq hE hT'
  subst T'
  have e := I.unique hp hp'
  subst p'
  have e := hF.eq hE hF'
  subst F'
  exact bpack_ext_l I hc hd

theorem bbasic_correct_l (hZF : M.Models ZF) {ω A S s c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.mem s S) (h : Bbasic_d I s c) :
    Bcode_d I ω A S c ∧ ∀ x, Bsat_d I ω A S c x ↔ M.MemberSubset s x := by
  obtain ⟨z, T, p, F, hz, hT, hp, hF, hc⟩ := h
  obtain ⟨e, he, heω⟩ := hω.1.1
  have e := hZF.1.eq_of_same_members e z (fun x => iff_of_false (he x) (hz x))
  have hzA := (hA z).mpr ⟨z, e ▸ heω, ds_empty_fun_l I hz⟩
  have noedge a b : ¬ Rd_entry_d a b z := fun ⟨q, _, hq⟩ => hz q hq
  have edge : Edge_d I ω T z := by
    refine ⟨fun q hq => (hz q hq).elim, fun a b => iff_of_false (noedge b a) ?_⟩
    exact fun ⟨_, hb, h⟩ => tree_step_not_empty_l I hz ((hT b).mp hb ▸ h)
  have label a b : M.PairMember I a b F ↔ a = z ∧ b = s := by
    constructor
    · rintro ⟨q, hq, hqF⟩
      exact I.injective ((hF q).mp hqF ▸ hq) hp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, hp, (hF p).mpr rfl⟩
  have funF : M.IsSetFunction I F := ⟨fun q hq => ⟨z, s, ((hF q).mp hq).symm ▸ hp⟩,
    fun a b d hb hd => ((label a b).mp hb).2.trans ((label a d).mp hd).2.symm⟩
  have hw : Wf_rel_d T z := fun Y _ ⟨a, ha⟩ => ⟨a, ha, fun b _ => noedge b a⟩
  have ht : Btree_d I ω A S T z z F := by
    refine ⟨⟨fun a ha => (hT a).mp ha ▸ hzA, fun a ha t _ hta => ?_⟩,
      edge, hw, ⟨z, hz, (hT z).mpr rfl⟩, fun a ha => (hz a ha).elim, funF, ?_, fun a ha => (hz a ha).elim⟩
    · apply (hT t).mpr
      exact hZF.1.eq_of_same_members t z (fun q => iff_of_false (fun hq => hz q ((hT a).mp ha ▸ hta q hq)) (hz q))
    · intro a b hab
      obtain ⟨ea, eb⟩ := (label a b).mp hab
      subst a b
      exact ⟨(hT z).mpr rfl, hs, hz z, fun b _ => noedge b z⟩
  refine ⟨⟨T, z, z, F, hc, ht⟩, fun x => ?_⟩
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hw z F x
  exact (bsat_root_l I hZF hc ht hv hz).trans
    (bsem_leaf_l I hv funF ((hT z).mpr rfl) (hz z) ((label z s).mpr ⟨rfl, rfl⟩))

theorem bcode_basic_l (hZF : M.Models ZF) {ω A S s} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.mem s S) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x, Bsat_d I ω A S c x ↔ M.MemberSubset s x := by
  obtain ⟨c, hc⟩ := bbasic_exists_l I (ZF.modelsKP hZF) s
  exact ⟨c, bbasic_correct_l I hZF hω hA hs hc⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数并交的规范码算子

规范性是语法码的唯一性，因而递归中逐行构造码族不需要选择公理。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bsup_d (ω H c : M.Domain) : Prop := ∃ z, (∀ x, ¬ M.mem x z) ∧ Bjoin_d I ω z H z c
def bsup_m {d} (ω H c : Term d) : Formula 1 d := .existsE (.conj (Formula.isEmpty .newest)
  (bjoin_m (𝒞 := 𝒞) ω.weaken .newest H.weaken .newest c.weaken))
derive_free_closed bsup_m
theorem bsup_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H c : Term d) :
    Formula.satisfies ρ (bsup_m (𝒞 := 𝒞) ω H c) ↔ Bsup_d I (ω.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [bsup_m, Bsup_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, bjoin_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem bsup_unique_l (hE : Extensional M) {ω H c d} (h : Bsup_d I ω H c) (k : Bsup_d I ω H d) : c = d := by
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨w, hw, k⟩ := k
  have e := hE.eq_of_same_members w z (fun x => iff_of_false (hw x) (hz x))
  subst w
  exact bjoin_unique_l I hE h k
theorem bsup_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bsup_d I ω H c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨c, hc, ht, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH (E := z) (fun h => (hz z h).elim)
  exact ⟨c, ⟨z, hz, hc⟩, ht, fun x => by
    simpa only [hz z, false_and, not_false_eq_true, true_and, false_or] using hv x⟩

def Bdual_d (ω H G : M.Domain) : Prop := M.IsSetRelation I G ∧ ∀ i d,
  M.PairMember I i d G ↔ ∃ c, M.PairMember I i c H ∧ Bneg_d I ω c d
def bdual_m {d} (ω H G : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 G)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest G.weaken.weaken)
    (.existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest H.weaken.weaken.weaken)
      (bneg_m (𝒞 := 𝒞) ω.weaken.weaken.weaken .newest (.bound 1)))))))
derive_free_closed bdual_m
theorem bdual_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H G : Term d) :
    Formula.satisfies ρ (bdual_m (𝒞 := 𝒞) ω H G) ↔ Bdual_d I (ω.eval ρ) (H.eval ρ) (G.eval ρ) := by
  simp only [bdual_m, Bdual_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_orderedPairMem_iff I, bneg_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem bdual_unique_l (hE : Extensional M) {ω H G F} (h : Bdual_d I ω H G) (k : Bdual_d I ω H F) : G = F :=
  h.1.eq_of_pairMember_iff hE k.1 (fun i d => (h.2 i d).trans (k.2 i d).symm)

theorem bdual_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ G, Bdual_d I ω H G ∧ Bfam_d I ω A S G ∧ ∀ x,
      (∃ i d, M.PairMember I i d G ∧ Bsat_d I ω A S d x) ↔
        ¬ ∀ i c, M.PairMember I i c H → Bsat_d I ω A S c x := by
  classical
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3))
    (bneg_m (𝒞 := 𝒞) (.bound 4) .newest (.bound 1))) }
  have hp i d : φ.denote ρ i d ↔ ∃ c, M.PairMember I i c H ∧ Bneg_d I ω c d := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bneg_sat_l I hZF.1]; rfl
  obtain ⟨D, _, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
  have total i (hi : M.mem i D) : ∃ d, φ.denote ρ i d :=
    ((hD i).mp hi).elim fun c hc => (bneg_exists_l I hZF hω hA (hH.2 i c hc).2).imp
      fun d hd => (hp i d).mpr ⟨c, hc, hd.1⟩
  have unique i (_ : M.mem i D) c d (hc : φ.denote ρ i c) (hd : φ.denote ρ i d) : c = d := by
    obtain ⟨a, ha, hc⟩ := (hp i c).mp hc
    obtain ⟨b, hb, hd⟩ := (hp i d).mp hd
    exact bneg_unique_l I hZF.1 hc (hH.1.2 i b a hb ha ▸ hd)
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ ρ D total unique
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := C)
    total unique (fun i d hi hd => (hC d).mpr ⟨i, hi, hd⟩)
  have dual : Bdual_d I ω H G := ⟨hg.1.1, fun i d => ((eg i d).trans
    (and_congr_right fun _ => hp i d)).trans ⟨And.right, fun h => ⟨(hD i).mpr (h.imp fun _ h => h.1), h⟩⟩⟩
  have value i d (hd : M.PairMember I i d G) : ∃ c, M.PairMember I i c H ∧ Bcode_d I ω A S d ∧
      ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
    obtain ⟨c, hc, hn⟩ := (dual.2 i d).mp hd
    obtain ⟨e, he, he', hev⟩ := bneg_exists_l I hZF hω hA (hH.2 i c hc).2
    exact ⟨c, hc, bneg_unique_l I hZF.1 he hn ▸ he', bneg_unique_l I hZF.1 he hn ▸ hev⟩
  refine ⟨G, dual, ⟨hg.1, fun i d hd => (value i d hd).elim fun c hc => ⟨(hH.2 i c hc.1).1, hc.2.1⟩⟩, fun x => ?_⟩
  constructor
  · rintro ⟨i, d, hd, hx⟩ hall
    obtain ⟨c, hc, _, hv⟩ := value i d hd
    exact (hv x).mp hx (hall i c hc)
  · intro hn
    obtain ⟨i, c, hc, hx⟩ : ∃ i c, M.PairMember I i c H ∧ ¬ Bsat_d I ω A S c x := by
      exact Classical.byContradiction (fun h => hn (fun i c hc =>
        Classical.byContradiction (fun hx => h ⟨i, c, hc, hx⟩)))
    obtain ⟨d, hd, _, hv⟩ := bneg_exists_l I hZF hω hA (hH.2 i c hc).2
    exact ⟨i, d, (dual.2 i d).mpr ⟨c, hc, hd⟩, (hv x).mpr hx⟩

def Binf_d (ω H c : M.Domain) : Prop := ∃ G u, Bdual_d I ω H G ∧ Bsup_d I ω G u ∧ Bneg_d I ω u c
def binf_m {d} (ω H c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bdual_m (𝒞 := 𝒞) ω.weaken.weaken H.weaken.weaken (.bound 1)) (.conj
  (bsup_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) .newest) (bneg_m (𝒞 := 𝒞) ω.weaken.weaken .newest c.weaken.weaken))))
derive_free_closed binf_m
theorem binf_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H c : Term d) :
    Formula.satisfies ρ (binf_m (𝒞 := 𝒞) ω H c) ↔ Binf_d I (ω.eval ρ) (H.eval ρ) (c.eval ρ) := by
  simp only [binf_m, Binf_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bdual_sat_l I hE, bsup_sat_l I hE, bneg_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem binf_unique_l (hE : Extensional M) {ω H c d} (h : Binf_d I ω H c) (k : Binf_d I ω H d) : c = d := by
  obtain ⟨G, u, hg, hu, hc⟩ := h
  obtain ⟨F, v, hf, hv, hd⟩ := k
  have e := bdual_unique_l I hE hf hg
  subst F
  exact bneg_unique_l I hE hc (bsup_unique_l I hE hv hu ▸ hd)
theorem binf_exists_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Binf_d I ω H c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∀ i d, M.PairMember I i d H → Bsat_d I ω A S d x := by
  obtain ⟨G, hg, hf, hv⟩ := bdual_exists_l I hZF hω hA hH
  obtain ⟨u, hu, hf, uv⟩ := bsup_exists_l I hZF hω hA hf
  obtain ⟨c, hc, hf, cv⟩ := bneg_exists_l I hZF hω hA hf
  exact ⟨c, ⟨G, u, hg, hu, hc⟩, hf, fun x => (cv x).trans
    ((not_congr ((uv x).trans (hv x))).trans Classical.not_not)⟩

/-- 可数交的解释直接由规范交码给出。 -/
theorem bcode_countable_inter_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x, Bsat_d I ω A S c x ↔
      ∀ i d, M.PairMember I i d H → Bsat_d I ω A S d x := by
  obtain ⟨c, _, hc, hv⟩ := binf_exists_l I hZF hω hA hH
  exact ⟨c, hc, hv⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 开集与闭树体的 Borel 码

固定一个已有的内部前缀编号，把柱集包含于开集的前缀送到其唯一规范基本码，
形成实际部分可数码族，再调用可数并。整个过程在 ZF 内完成，不需要可数选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bcover_d (B U s : M.Domain) : Prop := ∀ x, M.mem x B → M.MemberSubset s x → M.mem x U
def bcover_m {d} (B U s : Term d) : Formula 1 d := Formula.forallMem B
  (.imp (Formula.subset s.weaken .newest) (.mem .newest U.weaken))
derive_free_closed bcover_m
theorem bcover_sat_l {d} (ρ : Env M d) (B U s : Term d) :
    Formula.satisfies ρ (bcover_m B U s) ↔ Bcover_d (M := M) (B.eval ρ) (U.eval ρ) (s.eval ρ) := by
  simp only [bcover_m, Bcover_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

/-- 有内部可数基的前缀空间，其每个内部开集都有 Borel 码。 -/
theorem bcode_open_l (hZF : M.Models ZF) {ω A S B U} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.CardinalLessOrEqual I S ω) (ho : Open_d S B U) :
    ∃ c, Bcode_d I ω A S c ∧ Bden_d I ω A S B c U := by
  obtain ⟨J, hJ⟩ := hs
  let η : Env M 0 := ⟨Fin.elim0, fun _ => S⟩
  let φ : BinarySchema 0 := { body := bbasic_m (𝒞 := 𝒞) (.bound 1) .newest }
  have hp s c : φ.denote η s c ↔ Bbasic_d I s c := bbasic_sat_l I hZF.1 _ _ _
  obtain ⟨C, hC⟩ := ZF.exists_functionalImageOn hZF φ η S
    (fun s _ => (bbasic_exists_l I (ZF.modelsKP hZF) s).imp fun c h => (hp s c).mpr h)
    (fun s _ c d hc hd => bbasic_unique_l I hZF.1 ((hp s c).mp hc) ((hp s d).mp hd))
  let ρ : Env M 4 := (((⟨fun _ => S, fun _ => S⟩ : Env M 1).push J).push B).push U
  let ψ : BinarySchema 4 := {
    body := Formula.existsMem (.bound 5) (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 5))
      (.conj (bcover_m (.bound 4) (.bound 3) .newest) (bbasic_m (𝒞 := 𝒞) .newest (.bound 1)))) }
  have hψ i c : ψ.denote ρ i c ↔ ∃ s, M.mem s S ∧ M.PairMember I s i J ∧ Bcover_d B U s ∧ Bbasic_d I s c := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bcover_sat_l, bbasic_sat_l I hZF.1]; rfl
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω C
  obtain ⟨H, hH, he⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ W
  have pair i c : M.PairMember I i c H ↔ ∃ s, M.mem s S ∧ M.PairMember I s i J ∧ Bcover_d B U s ∧ Bbasic_d I s c := by
    refine ((he i c).trans (and_congr_right fun _ => and_congr_right fun _ => hψ i c)).trans
      ⟨fun h => h.2.2, fun h => ?_⟩
    obtain ⟨s, hs, hi, hu, hc⟩ := h
    exact ⟨(hW i).mpr (Or.inl (hJ.1.output_mem_of_pairMember hi)),
      (hW c).mpr (Or.inr ((hC c).mpr ⟨s, hs, (hp s c).mpr hc⟩)), s, hs, hi, hu, hc⟩
  have family : Bfam_d I ω A S H := by
    refine ⟨⟨hH.1, ?_⟩, ?_⟩
    · intro i c d hc hd
      obtain ⟨s, _, hi, _, hc⟩ := (pair i c).mp hc
      obtain ⟨t, _, hj, _, hd⟩ := (pair i d).mp hd
      have e := hJ.2 s t i hi hj
      exact bbasic_unique_l I hZF.1 hc (e.symm ▸ hd)
    · intro i c hc
      obtain ⟨s, hs, hi, _, hc⟩ := (pair i c).mp hc
      exact ⟨hJ.1.output_mem_of_pairMember hi, (bbasic_correct_l I hZF hω hA hs hc).1⟩
  obtain ⟨c, hc, hv⟩ := bcode_union_l I hZF hω hA family
  refine ⟨c, hc, fun x => ⟨fun hx => ⟨ho.1 x hx, ?_⟩, ?_⟩⟩
  · obtain ⟨s, hs, hsx, hu⟩ := ho.2 x hx
    obtain ⟨d, hd⟩ := bbasic_exists_l I (ZF.modelsKP hZF) s
    obtain ⟨i, _, hi⟩ := hJ.1.2.2 s hs
    exact (hv x).mpr ⟨i, d, (pair i d).mpr ⟨s, hs, hi, hu, hd⟩,
      ((bbasic_correct_l I hZF hω hA hs hd).2 x).mpr hsx⟩
  · rintro ⟨hxB, hx⟩
    obtain ⟨i, d, hi, hx⟩ := (hv x).mp hx
    obtain ⟨s, hs, _, hu, hd⟩ := (pair i d).mp hi
    exact hu x hxB (((bbasic_correct_l I hZF hω hA hs hd).2 x).mp hx)

def Borel_d (ω A S B K : M.Domain) : Prop := ∃ c, Bcode_d I ω A S c ∧ Bden_d I ω A S B c K
def borel_m {d} (ω A S B K : Term d) : Formula 1 d := .existsE (.conj
  (bcode_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken .newest)
  (bden_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken B.weaken .newest K.weaken))
derive_free_closed borel_m

theorem borel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S B K : Term d) :
    Formula.satisfies ρ (borel_m (𝒞 := 𝒞) ω A S B K) ↔
      Borel_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (B.eval ρ) (K.eval ρ) := by
  simp only [borel_m, Borel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bcode_sat_l I hE, bden_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 取补直接作用于码，返回实际相对补集。 -/
theorem borel_compl_l (hZF : M.Models ZF) {ω A S B K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hK : Borel_d I ω A S B K) :
    ∃ L, (∀ x, M.mem x L ↔ M.mem x B ∧ ¬ M.mem x K) ∧ Borel_d I ω A S B L := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨d, hd, hv⟩ := bcode_compl_l I hZF hω hA hc
  obtain ⟨L, hL⟩ := KP.difference_exists_d (ZF.modelsKP hZF) K B
  refine ⟨L, hL, d, hd, fun x => (hL x).trans (and_congr_right fun hx => ?_)⟩
  exact (not_congr ((hK x).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).trans (hv x).symm

theorem tree_body_borel_l (hZF : M.Models ZF) {ω A S B T K} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hs : M.CardinalLessOrEqual I S ω) (hK : Body_d S B T K) :
    Borel_d I ω A S B K := by
  classical
  obtain ⟨U, hU, ho⟩ := tree_body_closed_l (M := M) (ZF.modelsKP hZF) hK
  obtain ⟨c, hc, hv⟩ := bcode_open_l I hZF hω hA hs ho
  obtain ⟨d, hd, he⟩ := bcode_compl_l I hZF hω hA hc
  refine ⟨d, hd, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    refine ⟨((hK x).mp hx).1, (he x).mpr (fun hn => ?_)⟩
    exact ((hU x).mp ((hv x).mpr ⟨((hK x).mp hx).1, hn⟩)).2 hx
  · rintro ⟨hxB, hx⟩
    apply Classical.byContradiction
    intro hn
    exact (he x).mp hx (((hv x).mp ((hU x).mpr ⟨hxB, hn⟩)).2)

end YesMetaZFC.SetTheory.Descriptive

/-! ## 内部 Borel 集及空间实例

合法码是内部良基的带标签前缀树，求值及码的补、内部可数并均已实际构造。
`Borel_d` 表示有内部码的集合；可数并接口的输入是内部码族，在 ZF 中不擅自
从逐项有码推断可以同时选择一族码。地址长度、良基性和求值全部留在原模型中。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 所有有码子集组成实际内部集合，不把 Borel 性只留作外部类谓词。 -/
theorem borel_collection_l (hZF : M.Models ZF) (ω A S B : M.Domain) :
    ∃ C, ∀ K, M.mem K C ↔ Borel_d I ω A S B K := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push B
  let φ : UnarySchema 4 := { body := borel_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨C, fun K => ((hC K).trans (and_congr_right fun _ => borel_sat_l I hZF.1 _ _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨c, _, hk⟩ := h
  exact (hP K).mpr (fun x hx => ((hk x).mp hx).1)

/-- 同一码限制到内部子空间，解释恰为原解释与子空间的交。 -/
theorem borel_restrict_l (hZF : M.Models ZF) {ω A S B D K} (hD : M.MemberSubset D B)
    (hK : Borel_d I ω A S B K) :
    ∃ L, Borel_d I ω A S D L ∧ ∀ x, M.mem x L ↔ M.mem x D ∧ M.mem x K := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨L, hL, _⟩ := bden_exists_unique_l I hZF ω A S D c
  exact ⟨L, ⟨c, hc, hL⟩, fun x => (hL x).trans (and_congr_right fun hx =>
    ((hK x).trans ⟨And.right, fun h => ⟨hD x hx, h⟩⟩).symm)⟩

/-- 一次给出 Baire、Cantor 的实际空间、前缀空间和开集／闭树体的有码性。 -/
theorem baire_cantor_borel_l (hZF : M.Models ZF) : ∃ ω D B C A S,
    Baire_d I ω B ∧ Cantor_d I ω C ∧ Fseq_space_d I ω ω A ∧ Fseq_space_d I ω D S ∧
    (∀ U, Open_d A B U → Borel_d I ω A A B U) ∧
    (∀ U, Open_d S C U → Borel_d I ω A S C U) ∧
    (∀ T, ∃ K, Body_d A B T K ∧ Borel_d I ω A A B K) ∧
    (∀ T, ∃ K, Body_d S C T K ∧ Borel_d I ω A S C K) := by
  obtain ⟨ω, D, B, C, A, S, hB, hD, hC, hA, ha, hS, hs⟩ := ds_spaces_l I hZF
  have body {P Y} (hp : M.CardinalLessOrEqual I P ω) (T : M.Domain) :
      ∃ K, Body_d P Y T K ∧ Borel_d I ω A P Y K := by
    obtain ⟨K, hK⟩ := tree_body_exists_l (ZF.modelsKP hZF) P Y T
    exact ⟨K, hK, tree_body_borel_l I hZF hB.1 hA hp hK⟩
  exact ⟨ω, D, B, C, A, S, hB, ⟨hB.1, D, hD, hC⟩, hA, hS,
    fun _ h => bcode_open_l I hZF hB.1 hA ha h, fun _ h => bcode_open_l I hZF hB.1 hA hs h,
    body ha, body hs⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 全部内部 Borel 码组成集合

地址、边、补标记、叶标记各有固定幂集界。这给代码上的良基递归提供实际值域。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_universe_l (hZF : M.Models ZF) (ω A S : M.Domain) :
    ∃ C, ∀ c, M.mem c C ↔ Bcode_d I ω A S c := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF (kp_pair_l (ZF.modelsKP hZF)) A A
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF D
  obtain ⟨V, hV⟩ := ZF.exists_cartesianProduct hZF I A S
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF V
  obtain ⟨U, hU⟩ := ZF.exists_cartesianProduct hZF I P W
  obtain ⟨L, hL⟩ := ZF.exists_cartesianProduct hZF I Q U
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I P L
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S
  let φ : UnarySchema 3 := { body := bcode_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ K
  refine ⟨C, fun c => ((hC c).trans (and_congr_right fun _ => bcode_sat_l I hZF.1 _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨T, R, N, F, ⟨p, q, hc, hp, hq⟩, ht⟩ := h
  have hR : M.mem R Q := (hQ R).mpr (fun r hr => by
    obtain ⟨b, a, hb⟩ := ht.edges.1 r hr
    have ha := (ht.edges.2 a b).mp ⟨r, hb, hr⟩
    exact (hD r).mpr ⟨b, ht.tree.1 b ha.2.1, a, ht.tree.1 a ha.1, hb⟩)
  have hN : M.mem N P := (hP N).mpr (fun a ha => ht.tree.1 a (ht.neg_sub a ha))
  have hF : M.mem F W := (hW F).mpr (fun r hr => by
    obtain ⟨a, s, ha⟩ := ht.leaf_fn.1 r hr
    have hh := ht.leaf a s ⟨r, ha, hr⟩
    exact (hV r).mpr ⟨a, ht.tree.1 a hh.1, s, hh.2.1, ha⟩)
  exact (hK c).mpr ⟨T, (hP T).mpr ht.tree.1, p,
    (hL p).mpr ⟨R, hR, q, (hU q).mpr ⟨N, hN, F, hF, hq⟩, hp⟩, hc⟩

/-- 原公式给出的单值部分码族自动集合化；允许空指标域。 -/
theorem bf_defined_l (hZF : M.Models ZF) {ω A S} {n} (φ : BinarySchema n) (ρ : Env M n)
    (unique : ∀ i c d, φ.denote ρ i c → φ.denote ρ i d → c = d)
    (bound : ∀ i c, φ.denote ρ i c → M.mem i ω ∧ Bcode_d I ω A S c) :
    ∃ H, Bfam_d I ω A S H ∧ ∀ i c, M.PairMember I i c H ↔ φ.denote ρ i c := by
  obtain ⟨C, hC⟩ := bcode_universe_l I hZF ω A S
  obtain ⟨V, hV⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω C
  obtain ⟨H, hh, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ V
  have pair i c : M.PairMember I i c H ↔ φ.denote ρ i c := (he i c).trans
    ⟨fun h => h.2.2, fun h => ⟨(hV i).mpr (Or.inl (bound i c h).1),
      (hV c).mpr (Or.inr ((hC c).mpr (bound i c h).2)), h⟩⟩
  exact ⟨H, ⟨⟨hh.1, fun i c d hc hd => unique i c d ((pair i c).mp hc) ((pair i d).mp hd)⟩,
    fun i c hc => bound i c ((pair i c).mp hc)⟩, pair⟩

end YesMetaZFC.SetTheory.Descriptive
