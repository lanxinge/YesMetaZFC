import YesMetaZFC.Model.Forcing.Applications.Collapse.FiniteSequence
import YesMetaZFC.Model.Forcing.Internal.Extension.DenseNames
import YesMetaZFC.Model.Forcing.Internal.Check.Order
import YesMetaZFC.SetTheory.Descriptive.Path

/-! # 小坍缩之上的大坍缩稠密集名称

从两个实际内部有限序列条件域出发，小坍缩的空条件自动给出规范名称基点。
大坍缩的条件域和序关系的规范名称满足预序力迫，故上层名称库覆盖小泛型
扩张中大坍缩的全部稠密集。构造只需 ZF，不另交名称覆盖或力迫正确性假设。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_dense_names_l {ω κ B R : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω κ B) (O : Cond_order_d M B R B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (δ : M.Domain) :
    ∃ F S b A T W D, Fseq_space_d I ω δ F ∧ Cond_order_d M F S F ∧
      (∀ p q, Entry_d M p q S ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p) ∧
      (∀ x, ¬ M.mem x b) ∧ M.mem b B ∧ Check_d M b F A ∧ Check_d M b S T ∧ Name_pool_d M B A A W ∧
      (∀ s, M.mem s D ↔ M.mem s W ∧ ∀ p, M.mem p B → p ≠ B →
        Forces_d M B R B dn_s.body ((ord_env_l M A T).push s) p) ∧
      ∀ U, Generic_d M B R B U → ∀ C V K : (extension_l M hZF B R B U).Domain,
        Qval_d M B R B U A C → Qval_d M B R B U T V →
        Dense_set_d (extension_l M hZF B R B U) C V C K →
        ∃ s, M.mem s D ∧ Qval_d M B R B U s K := by
  obtain ⟨F, S, fs, L, ord⟩ := fseq_collapse_order_l hZF hw δ
  obtain ⟨b, empty, hbω⟩ := hw.1.1
  have hb := (space b).mpr ⟨b, hbω, ds_empty_fun_l I empty⟩
  have top p (hp : M.mem p B) := (order p b).mpr ⟨hp, hb, fun a ha => (empty a ha).elim⟩
  obtain ⟨A, hA, hnA, _⟩ := zf_check_l M hZF hb F
  obtain ⟨T, hT, hnT, _⟩ := zf_check_l M hZF hb S
  obtain ⟨W, D, pool, spec, cover⟩ := dense_names_l O hZF hnA hnT (fun p hp hz =>
    check_preord_force_l O hZF hb hA hT ⟨L.refl, L.trans⟩ ⟨hp, hz, top p hp⟩)
  exact ⟨F, S, b, A, T, W, D, fs, L, ord, empty, hb, hA, hT, pool, spec, cover⟩

end YesMetaZFC.Model.Forcing.Internal
