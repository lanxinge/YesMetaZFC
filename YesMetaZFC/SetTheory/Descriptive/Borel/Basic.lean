import YesMetaZFC.SetTheory.Descriptive.Borel.Rules

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
@[prove_auto_norm semantic]
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
