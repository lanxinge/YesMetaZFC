import YesMetaZFC.SetTheory.LargeCardinal.TypeGameVacuous
import YesMetaZFC.SetTheory.Descriptive.HistoryTree

/-! # 二坐标树的历史筛选

实际第一坐标映射把截面树与策略反例树统一为原树和历史树逆像的交。
标签集任意，空标签集也使用同一构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tp_left_d (Y A d : M.Domain) : Prop := M.IsSetFunctionFromTo I d Y A ∧
  ∀ v a, M.PairMember I v a d ↔ M.mem v Y ∧ ∃ z, (I).Codes v a z

theorem tp_left_l (hZF : M.Models ZF) {Y A Γ : M.Domain}
    (pair : M.IsCartesianProduct I Y A Γ) : ∃ d, Tp_left_d I Y A d := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Y⟩
  let φ : BinarySchema 0 := { body := .existsE (kpair_convention_l.code (.bound 2) (.bound 1) .newest) }
  have sat v a : φ.denote ρ v a ↔ ∃ z, (I).Codes v a z := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, I.satisfies_code_iff]; rfl
  obtain ⟨d, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := A)
    (fun v hv => ((pair v).mp hv).elim fun a ha => ⟨a, (sat v a).mpr
      (ha.2.elim fun z hz => ⟨z, hz.2⟩)⟩)
    (fun _ _ _ _ h k => ((sat ..).mp h).elim fun z hz =>
      ((sat ..).mp k).elim fun w hw => (I.injective hz hw).1) (by
        intro v a hv h
        obtain ⟨z, code⟩ := (sat v a).mp h
        obtain ⟨b, hb, w, _, code'⟩ := (pair v).mp hv
        exact (I.injective code code').1.symm ▸ hb)
  exact ⟨d, fn, fun v a => (graph v a).trans (and_congr_right fun _ => sat v a)⟩

theorem Tp_left_d.projection_l (hZF : M.Models ZF) {Y A d n q x : M.Domain}
    (left : Tp_left_d I Y A d) (fq : M.IsSetFunctionFromTo I q n Y) :
    Fseq_recode_d I d q x ↔ M.IsLeftFunctionProjection I x q n A := by
  have graph i a : (∃ v, M.PairMember I i v q ∧ M.PairMember I v a d) ↔
      ∃ v z, M.PairMember I i v q ∧ (I).Codes v a z := by
    constructor
    · rintro ⟨v, iv, va⟩
      obtain ⟨_, z, code⟩ := (left.2 v a).mp va
      exact ⟨v, z, iv, code⟩
    · rintro ⟨v, z, iv, code⟩
      exact ⟨v, iv, (left.2 v a).mpr ⟨fq.output_mem_of_pairMember iv, z, code⟩⟩
  exact ⟨fun h => ⟨h.function_l I hZF left.1 fq, fun i a => (h.2 i a).trans (graph i a)⟩,
    fun h => ⟨h.1.1.1, fun i a => (h.2 i a).trans (graph i a).symm⟩⟩

def Tp_filter_d (d F T K C : M.Domain) : Prop :=
  ∃ S, Tr_pull_d I d F K S ∧ ∀ s, M.mem s C ↔ M.mem s T ∧ M.mem s S

theorem tp_filter_l (hZF : M.Models ZF) (d F T K : M.Domain) : ∃ C, Tp_filter_d I d F T K C := by
  obtain ⟨S, pull⟩ := tr_pull_exists_l I hZF d F K
  obtain ⟨C, inter⟩ := tree_inter_exists_l hZF T S
  exact ⟨C, S, pull, inter⟩

theorem Tp_filter_d.tree_l (hZF : M.Models ZF) {ω A Y d F H T K C : M.Domain}
    (left : Tp_left_d I Y A d) (space : Fseq_space_d I ω Y F) (hist : Fseq_space_d I ω A H)
    (tree : Tree_d F T) (control : Tree_d H K) (filter : Tp_filter_d I d F T K C) : Tree_d F C := by
  obtain ⟨S, pull, inter⟩ := filter
  exact tree_inter_l tree (pull.tree_l I hZF left.1 space hist control) inter

theorem Tp_filter_d.branch_l (hZF : M.Models ZF) {ω A Y d F H T K C q x : M.Domain}
    (hw : M.IsOmega ω) (left : Tp_left_d I Y A d) (space : Fseq_space_d I ω Y F)
    (hist : Fseq_space_d I ω A H) (filter : Tp_filter_d I d F T K C)
    (fq : M.IsSetFunctionFromTo I q ω Y) (proj : M.IsLeftFunctionProjection I x q ω A) :
    Branch_d F C q ↔ Branch_d F T q ∧ Branch_d H K x := by
  obtain ⟨S, pull, inter⟩ := filter
  exact (tree_inter_branch_l inter).trans (and_congr_right fun _ =>
    pull.branch_l I hZF hw left.1 space hist fq ((left.projection_l I hZF fq).mpr proj))

end YesMetaZFC.SetTheory.LargeCardinal
