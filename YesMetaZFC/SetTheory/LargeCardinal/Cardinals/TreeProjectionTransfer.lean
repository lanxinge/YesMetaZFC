import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree
import YesMetaZFC.SetTheory.Descriptive.Analytic.Suslin
import YesMetaZFC.Model.Forcing.Ground.TreeShift

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

/-! ## 解析正规形到类型投影的第一段重编码

`Tpath_d` 的逐坐标见证使用 `Npair_d` 中的自然数配对索引，而类型投影
的字母表需要直接的有序对编码。本模块先把前者规范重编码为后者，保留
实际函数图与目标笛卡尔积，供后续树回拉和左投影构造消费。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

theorem np_decode_function_l
    (hZF : M.Models ZF) {ω J P : M.Domain}
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω) :
    ∃ f, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω P ∧
      ∀ v p, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) v p f ↔
        M.mem v ω ∧ ∃ a b, M.mem a ω ∧ M.mem b ω ∧
          Np_d (kp_pair_l (ZF.modelsKP hZF)) J a b v ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes p a b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := ⟨fun i => [J, ω].get i, fun _ => J⟩
  let φ : BinarySchema 2 := {
    body := Definitional.Formula.existsE (Definitional.Formula.existsE
      (.conj (.mem (.bound 1) (.bound 5))
        (.conj (.mem .newest (.bound 5))
          (.conj (np_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 1) .newest (.bound 3))
            (kpair_convention_l.code (.bound 2) (.bound 1) .newest)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have sat v p : φ.denote ρ v p ↔
      ∃ a b, M.mem a ω ∧ M.mem b ω ∧ Np_d I J a b v ∧ I.Codes p a b := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, np_m, Np_d,
      Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    rfl
  obtain ⟨f, hf, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := ω) (target := P) (by
      intro v hv
      obtain ⟨a, b, ha, hb, hn⟩ := np_surj_l I hJ hv
      obtain ⟨p, hp⟩ := I.total a b
      exact ⟨p, (sat v p).mpr ⟨a, b, ha, hb, hn, hp⟩⟩)
    (by
      intro v hv p q hp hq
      obtain ⟨a, b, _, _, hn, hcp⟩ := (sat v p).mp hp
      obtain ⟨c, d, _, _, hn', hcq⟩ := (sat v q).mp hq
      obtain ⟨rfl, rfl⟩ := np_injective_l I hJ hn hn'
      exact I.unique hcp hcq)
    (by
      intro v p hv hp
      obtain ⟨a, b, ha, hb, _, hcp⟩ := (sat v p).mp hp
      exact (hP p).mpr ⟨a, ha, b, hb, hcp⟩)
  refine ⟨f, hf, ?_⟩
  intro v p
  exact (graph v p).trans (and_congr_right fun _ => sat v p)

theorem np_encode_function_l
    (hZF : M.Models ZF) {ω J P : M.Domain}
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω) :
    ∃ f, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) f P ω ∧
      ∀ p v, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) p v f ↔
        M.mem p P ∧ ∃ a b, M.mem a ω ∧ M.mem b ω ∧
          Np_d (kp_pair_l (ZF.modelsKP hZF)) J a b v ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes p a b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨g, hg, hgg⟩ := np_decode_function_l hZF hJ hP
  have injective : M.IsSetInjective I g := by
    intro v w p hp hq
    obtain ⟨_, a, b, _, _, hn, hcp⟩ := (hgg v p).mp hp
    obtain ⟨_, c, d, _, _, hn', hcp'⟩ := (hgg w p).mp hq
    have e := I.injective hcp hcp'
    obtain ⟨rfl, rfl⟩ := e
    exact np_unique_l I hJ hn hn'
  have surjective : M.IsSetSurjectiveOnto I g ω P := by
    intro p hp
    obtain ⟨a, ha, b, hb, hcode⟩ := (hP p).mp hp
    obtain ⟨v, hv, hn⟩ := np_total_l I hJ ha hb
    exact ⟨v, hv, (hgg v p).mpr ⟨hv, a, b, ha, hb, hn, hcode⟩⟩
  have bij : M.IsSetBijectionFromTo I g ω P := ⟨⟨hg, injective⟩, surjective⟩
  obtain ⟨f, hf, hfg⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  refine ⟨f, hf.1.1, ?_⟩
  intro p v
  rw [hfg p v]
  constructor
  · intro hp
    obtain ⟨hv, a, b, ha, hb, hn, hcode⟩ := (hgg v p).mp hp
    exact ⟨(hP p).mpr ⟨a, ha, b, hb, hcode⟩, a, b, ha, hb, hn, hcode⟩
  · rintro ⟨hp, a, b, ha, hb, hn, hcode⟩
    exact (hgg v p).mpr ⟨(np_type_l I hJ hn).2.2, a, b, ha, hb, hn, hcode⟩

theorem np_left_recode_l
    (hZF : M.Models ZF) {D P ω d x y q : M.Domain}
    (left : Tp_left_d (kp_pair_l (ZF.modelsKP hZF)) P ω d)
    (fq : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) q D P)
    (fx : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x D ω)
    (fy : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) y D ω)
    (graph : ∀ i p, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i p q ↔
      M.mem i D ∧ ∃ a b, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i a x ∧
        M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i b y ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes p a b) :
    Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) d q x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, y', iz⟩ := fx.1.1 z hz
    exact ⟨i, y', iz⟩
  · intro i a
    constructor
    · intro ia
      obtain ⟨b, hb, ib⟩ := fy.2.2 i (fx.input_mem_of_pairMember ia)
      obtain ⟨p, cp⟩ := I.total a b
      have ip := (graph i p).mpr ⟨fx.input_mem_of_pairMember ia, a, b, ia, ib, cp⟩
      exact ⟨p, ip, (left.2 p a).mpr ⟨fq.output_mem_of_pairMember ip, ⟨b, cp⟩⟩⟩
    · rintro ⟨p, ip, cp⟩
      obtain ⟨_, b, cp⟩ := (left.2 p a).mp cp
      obtain ⟨_, a', b', hax, hby, hab⟩ := (graph i p).mp ip
      have ea := I.injective cp hab
      exact ea.1.symm ▸ hax

/-! `Rp_d` 的一个分支先逐项改写为直接的有序对字母。
这一步只生产函数图和逐点规格，不涉及树回拉。 -/
theorem np_pair_recode_l
    (hZF : M.Models ZF) {D P ω J x y t : M.Domain}
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω)
    (fx : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x D ω)
    (fy : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) y D ω)
    (hr : Rp_d (kp_pair_l (ZF.modelsKP hZF)) J x y t) :
    ∃ q, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) q D P ∧
      ∀ i p, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i p q ↔
        M.mem i D ∧ ∃ a b,
          M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i a x ∧
          M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i b y ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes p a b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ft : M.IsSetFunctionFromTo I t D ω := rp_type_l I hZF hJ fx fy hr
  obtain ⟨g, hg, ggraph⟩ := np_decode_function_l hZF hJ hP
  obtain ⟨q, hq, hcomp⟩ := ZF.fseq_compose_l I hZF hg ft
  refine ⟨q, hq, ?_⟩
  intro i p
  rw [hcomp.2 i p]
  constructor
  · rintro ⟨v, iv, vp⟩
    obtain ⟨hv, a, b, _, _, np, code⟩ := (ggraph v p).mp vp
    obtain ⟨a', b', ia, ib, np'⟩ := (hr.2 i v).mp iv
    obtain ⟨rfl, rfl⟩ := np_injective_l I hJ np np'
    exact ⟨fx.input_mem_of_pairMember ia, a, b, ia, ib, code⟩
  · rintro ⟨hi, a, b, ia, ib, code⟩
    obtain ⟨v, hv, np⟩ := np_total_l I hJ (fx.output_mem_of_pairMember ia)
      (fy.output_mem_of_pairMember ib)
    exact ⟨v, (hr.2 i v).mpr ⟨a, b, ia, ib, np⟩,
      (ggraph v p).mpr ⟨hv, a, b, fx.output_mem_of_pairMember ia,
        fy.output_mem_of_pairMember ib, np, code⟩⟩

theorem np_inverse_recode_l
    (hZF : M.Models ZF) {ω J P D x y p q e : M.Domain}
    (encode_graph : ∀ r v, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) r v e ↔
      M.mem r P ∧ ∃ a b, M.mem a ω ∧ M.mem b ω ∧
        Np_d (kp_pair_l (ZF.modelsKP hZF)) J a b v ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes r a b)
    (fx : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x D ω)
    (fy : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) y D ω)
    (fp : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) p D ω)
    (fq : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) q D P)
    (hr : Rp_d (kp_pair_l (ZF.modelsKP hZF)) J x y p)
    (qgraph : ∀ i r, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i r q ↔
      M.mem i D ∧ ∃ a b, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i a x ∧
        M.PairMember (kp_pair_l (ZF.modelsKP hZF)) i b y ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes r a b) :
    Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) e q p := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, y', iz⟩ := fp.1.1 z hz
    exact ⟨i, y', iz⟩
  · intro i v
    constructor
    · intro iv
      obtain ⟨a, b, ia, ib, hn⟩ := (hr.2 i v).mp iv
      obtain ⟨r, hcode⟩ := I.total a b
      have iq := (qgraph i r).mpr ⟨fx.input_mem_of_pairMember ia, a, b, ia, ib, hcode⟩
      have er := (encode_graph r v).mpr ⟨fq.output_mem_of_pairMember iq,
        a, b, fx.output_mem_of_pairMember ia, fy.output_mem_of_pairMember ib, hn, hcode⟩
      exact ⟨r, iq, er⟩
    · rintro ⟨r, ir, rv⟩
      obtain ⟨_, a, b, ia, ib, hcode⟩ := (qgraph i r).mp ir
      obtain ⟨_, a', b', _, _, hn, hcode'⟩ := (encode_graph r v).mp rv
      have eab := I.injective hcode hcode'
      exact (hr.2 i v).mpr ⟨a, b, ia, ib, (eab.1 ▸ eab.2 ▸ hn)⟩

/-! 编码函数沿有限序列和树回拉运输。 -/
theorem np_tree_pullback_l
    (hZF : M.Models ZF) {ω J P A T : M.Domain}
    (hw : M.IsOmega ω)
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (tree : Tree_d A T) :
    ∃ d F S,
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) d P ω ∧
      (∀ p v, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) p v d ↔
        M.mem p P ∧ ∃ a b, M.mem a ω ∧ M.mem b ω ∧
          Np_d (kp_pair_l (ZF.modelsKP hZF)) J a b v ∧
            (kp_pair_l (ZF.modelsKP hZF)).Codes p a b) ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F ∧
      Tr_pull_d (kp_pair_l (ZF.modelsKP hZF)) d F T S ∧
      Tree_d F S ∧
      ∀ {q t},
        M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) q ω P →
        M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) t ω ω →
        Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) d q t →
        (Branch_d F S q ↔ Branch_d A T t) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨d, fd, dgraph⟩ := np_encode_function_l hZF hJ hP
  obtain ⟨F, fspace⟩ := ZF.fseq_space_exists_l I hZF hw P
  obtain ⟨S, pull⟩ := tr_pull_exists_l I hZF d F T
  have f_tree : Tree_d F S := pull.tree_l I hZF fd fspace space tree
  refine ⟨d, F, S, fd, dgraph, fspace, pull, f_tree, ?_⟩
  intro q t fq ft recode
  exact pull.branch_l I hZF hw fd fspace space fq recode

/-! 组合 pair-code 重编码、树回拉和左投影，直接把一条 `Rp_d` 分支
送成 `Tp_projection_d`。这正是 `Tpath_d` 接入 6.7 投影所需的桥。 -/
theorem rp_to_tp_projection_l
    (hZF : M.Models ZF) {ω J P A T x y p : M.Domain}
    (hw : M.IsOmega ω)
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (tree : Tree_d A T)
    (fx : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x ω ω)
    (fy : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) y ω ω)
    (fp : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) p ω ω)
    (hr : Rp_d (kp_pair_l (ZF.modelsKP hZF)) J x y p)
    (branch : Branch_d A T p) :
    ∃ F S, Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F ∧
      Tree_d F S ∧
        Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P F S x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨q, hq, qgraph⟩ := np_pair_recode_l hZF hJ hP fx fy hr
  obtain ⟨d, F, S, fd, dgraph, fspace, pull, f_tree, branchEq⟩ :=
    np_tree_pullback_l hZF hw hJ hP space tree
  have recode := np_inverse_recode_l hZF dgraph fx fy fp hq hr qgraph
  obtain ⟨dleft, left⟩ := tp_left_l I hZF hP
  have leftRecode := np_left_recode_l hZF left hq fx fy qgraph
  have qbranch := (branchEq hq fp recode).mpr branch
  have projection := (left.projection_l I hZF hq).mp leftRecode
  exact ⟨F, S, fspace, f_tree, ⟨q, hq, qbranch, projection⟩⟩

/-! 反向桥把任意回拉树上的 `Tp` 分支解码回原 `Rp_d` 分支。
它同时核验左右坐标、逆编码函数和原树分支，闭合前向桥遗漏的反向蕴含。 -/
theorem tp_to_rp_l
    (hZF : M.Models ZF) {ω J P A T F S d q x : M.Domain}
    (hw : M.IsOmega ω)
    (hP : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω)
    (spaceP : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F)
    (spaceω : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (fd : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) d P ω)
    (dgraph : ∀ p v, M.PairMember (kp_pair_l (ZF.modelsKP hZF)) p v d ↔
      M.mem p P ∧ ∃ a b, M.mem a ω ∧ M.mem b ω ∧
        Np_d (kp_pair_l (ZF.modelsKP hZF)) J a b v ∧
          (kp_pair_l (ZF.modelsKP hZF)).Codes p a b)
    (hq : M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) q ω P)
    (branch : Branch_d F S q)
    (pull : Tr_pull_d (kp_pair_l (ZF.modelsKP hZF)) d F T S)
    (left : M.IsLeftFunctionProjection (kp_pair_l (ZF.modelsKP hZF)) x q ω ω) :
    ∃ y t, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) y ω ω ∧
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) t ω ω ∧
      Fseq_recode_d (kp_pair_l (ZF.modelsKP hZF)) d q t ∧
      Rp_d (kp_pair_l (ZF.modelsKP hZF)) J x y t ∧
      Branch_d A T t := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨g, right⟩ := tp_right_l I hZF hP hq
  let y := g
  have hy : M.IsSetFunctionFromTo I y ω ω := right.1
  obtain ⟨t, ht, dt⟩ := ZF.fseq_compose_l I hZF fd hq
  have branchT := (pull.branch_l I hZF hw fd spaceP spaceω hq dt).mp branch
  refine ⟨y, t, hy, ht, dt, ?_, branchT⟩
  refine ⟨ht.1.1, ?_⟩
  intro i v
  constructor
  · intro iv
    obtain ⟨p, ip, pv⟩ := (dt.2 i v).mp iv
    obtain ⟨_, a, b, ha, hb, hn, hp⟩ := (dgraph p v).mp pv
    exact ⟨a, b, (left.2 i a).mpr ⟨p, b, ip, hp⟩,
      (right.2 i b).mpr ⟨p, a, ip, hp⟩, hn⟩
  · rintro ⟨a, b, ia, ib, hn⟩
    obtain ⟨p, hp⟩ := I.total a b
    obtain ⟨pL, r, ipL, hL⟩ := (left.2 i a).mp ia
    obtain ⟨pR, l, ipR, hR⟩ := (right.2 i b).mp ib
    have ep : pL = pR := hq.1.2 i pL pR ipL ipR
    have eab := I.injective hL (ep ▸ hR)
    have epab : p = pL := I.unique hp (eab.2 ▸ hL)
    have ip : M.PairMember I i p q := epab ▸ ipL
    have pv : M.PairMember I p v d := (dgraph p v).mpr
      ⟨(hP p).mpr ⟨a, left.1.output_mem_of_pairMember ia, b,
        right.1.output_mem_of_pairMember ib, hp⟩, a, b,
        left.1.output_mem_of_pairMember ia, right.1.output_mem_of_pairMember ib, hn, hp⟩
    exact (dt.2 i v).mpr ⟨p, ip, pv⟩

/-! `an_prefix_iff_l` 的树正规形现在与 `Tp_projection_d` 完全等价。
该桥固定同一 pair-code 字母表、有限列空间和回拉树，因此可直接交给
双树决定性，而不会在每个实数点重新选择树。 -/
theorem an_prefix_tp_l
    (hZF : M.Models ZF) {ω A B J K : M.Domain}
    (hw : M.IsOmega ω) (hB : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (hA : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (ha : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) A ω)
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hK : An_d (kp_pair_l (ZF.modelsKP hZF)) ω A B J K) :
    ∃ P F S, M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F ∧ Tree_d F S ∧
      ∀ x, M.mem x K ↔ M.mem x B ∧
        Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P F S x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨T, tree, path⟩ := (an_prefix_iff_l I hZF hB hA ha hJ).mp hK
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨d, F, S, fd, dgraph, fspace, pull, f_tree, branchEq⟩ :=
    np_tree_pullback_l hZF hw hJ hP hA tree
  obtain ⟨dleft, left⟩ := tp_left_l I hZF hP
  refine ⟨P, F, S, hP, fspace, f_tree, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxB, y, hyB, hxy⟩ := (path x).mp hx
    have fx : M.IsSetFunctionFromTo I x ω ω := (hB.2 x).mp hxB
    have fy : M.IsSetFunctionFromTo I y ω ω := (hB.2 y).mp hyB
    obtain ⟨p, fp, hr⟩ := rp_exists_l I hZF hJ fx fy
    have bp : Branch_d A T p :=
      (tpath_branch_l I hZF hw hA hJ fx fy hr).mpr hxy
    obtain ⟨q, hq, qgraph⟩ := np_pair_recode_l hZF hJ hP fx fy hr
    have recode := np_inverse_recode_l hZF dgraph fx fy fp hq hr qgraph
    have qbranch := (branchEq hq fp recode).mpr bp
    have leftRecode := np_left_recode_l hZF left hq fx fy qgraph
    exact ⟨hxB, ⟨q, hq, qbranch, (left.projection_l I hZF hq).mp leftRecode⟩⟩
  · rintro ⟨hxB, ⟨q, hq, qbranch, hleft⟩⟩
    have fx : M.IsSetFunctionFromTo I x ω ω := (hB.2 x).mp hxB
    obtain ⟨y, t, fy, ft, recode, hr, bp⟩ :=
      tp_to_rp_l hZF hw hP fspace hA fd dgraph hq qbranch pull hleft
    have hxy := (tpath_branch_l I hZF hw hA hJ fx fy hr).mp bp
    exact (path x).mpr ⟨hxB, y, (hB.2 y).mpr fy, hxy⟩


/-! Borel 码的补码与解析树正规形给出真实的 exhaustive 双树对。
该节点先闭合 Borel 特例，后续 Jensen 证书编译器只需生产 Borel 码。 -/
theorem borel_exhaustive_tp_pair_l
    (hZF : M.Models ZF)
    {ω B A J c : M.Domain}
    (hw : M.IsOmega ω) (hB : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (hA : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (ha : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) A ω)
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hc : Bcode_d (kp_pair_l (ZF.modelsKP hZF)) ω A A c) :
    ∃ P F S P' F' S',
      M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F ∧ Tree_d F S ∧
      M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P' ω ω ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P' F' ∧ Tree_d F' S' ∧
      ∀ x, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x ω ω →
        Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P F S x ∨
          Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P' F' S' x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK, _⟩ := bden_exists_unique_l I hZF ω A A B c
  obtain ⟨d, hd, complement⟩ := bcode_compl_l I hZF hw hA hc
  obtain ⟨L, hL, _⟩ := bden_exists_unique_l I hZF ω A A B d
  have anK : An_d I ω A B J K :=
    borel_an_l I hZF hB hA ha hJ ⟨c, hc, hK⟩
  have anL : An_d I ω A B J L :=
    borel_an_l I hZF hB hA ha hJ ⟨d, hd, hL⟩
  obtain ⟨P, F, S, pair, space, tree, eqK⟩ :=
    an_prefix_tp_l hZF hw hB hA ha hJ anK
  obtain ⟨P', F', S', pair', space', tree', eqL⟩ :=
    an_prefix_tp_l hZF hw hB hA ha hJ anL
  refine ⟨P, F, S, P', F', S', pair, space, tree, pair', space', tree', ?_⟩
  intro x fx
  have xb : M.mem x B := (hB.2 x).mpr fx
  by_cases hcx : Bsat_d I ω A A c x
  · left
    exact (eqK x).mp ((hK x).mpr ⟨xb, hcx⟩) |>.2
  · right
    exact (eqL x).mp ((hL x).mpr ⟨xb, (complement x).mpr hcx⟩) |>.2

/-! 内部可数 Borel 证书族直接生产 exhaustive 双树。
该接口把 Jensen 侧剩余义务精确化为一个 Bfam_d 证书族。 -/
theorem bfamily_exhaustive_tp_pair_l
    (hZF : M.Models ZF)
    {ω B A J H : M.Domain}
    (hw : M.IsOmega ω) (hB : Baire_d (kp_pair_l (ZF.modelsKP hZF)) ω B)
    (hA : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω ω A)
    (ha : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF)) A ω)
    (hJ : Npair_d (kp_pair_l (ZF.modelsKP hZF)) ω J)
    (hH : Bfam_d (kp_pair_l (ZF.modelsKP hZF)) ω A A H) :
    ∃ P F S P' F' S' c,
      Bcode_d (kp_pair_l (ZF.modelsKP hZF)) ω A A c ∧
      M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P ω ω ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P F ∧ Tree_d F S ∧
      M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) P' ω ω ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω P' F' ∧ Tree_d F' S' ∧
      ∀ x, M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) x ω ω →
        Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P F S x ∨
          Tp_projection_d (kp_pair_l (ZF.modelsKP hZF)) ω ω P' F' S' x := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, hc, _⟩ := bcode_union_l I hZF hw hA hH
  obtain ⟨P, F, S, P', F', S', pair, space, tree, pair', space', tree', cover⟩ :=
    borel_exhaustive_tp_pair_l hZF hw hB hA ha hJ hc
  exact ⟨P, F, S, P', F', S', c, hc, pair, space, tree, pair', space', tree', cover⟩
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 旧实数的投影成员关系回传

固定旧 x，实际构造 T 的 x 截面。若地面没有见证，该树有序数秩；
秩与截面构造都沿成员满嵌入保持，故外模型也不可能给同一个 x 添加见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
local notation "J" => kp_pair_l (ZF.modelsKP hN)
include hi he

theorem Tp_left_d.image_l {Y A d : M.Domain} (left : Tp_left_d I Y A d) :
    Tp_left_d J (e Y) (e A) (e d) := by
  refine ⟨image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he left.1,
    fun v a => ⟨?_, ?_⟩⟩
  · intro va
    obtain ⟨p, x, px, rfl, rfl⟩ := (image_entries_l e he left.1.1.1 v a).mp va
    obtain ⟨hp, z, code⟩ := (left.2 p x).mp px
    exact ⟨(image_member_l e hi he).mpr hp, e z, image_kpair_l e he code⟩
  · rintro ⟨hv, z, code⟩
    obtain ⟨p, hp, rfl⟩ := (he Y v).mp hv
    obtain ⟨x, _, px⟩ := left.1.2.2 p hp
    obtain ⟨_, w, code'⟩ := (left.2 p x).mp px
    have eq := ((J).injective (image_kpair_l e he code') code).1
    exact eq ▸ (image_entries_l e he left.1.1.1 (e p) (e x)).mpr ⟨p, x, px, rfl, rfl⟩

theorem Tp_filter_d.image_l {ω Y A d F T K C : M.Domain}
    (left : Tp_left_d I Y A d) (space : Fseq_space_d I ω Y F) (filter : Tp_filter_d I d F T K C) :
    Tp_filter_d J (e d) (e F) (e T) (e K) (e C) := by
  obtain ⟨S, pull, inter⟩ := filter
  refine ⟨e S, image_tree_pullback_l hM hN e hi he left.1 space pull, fun s => ⟨?_, ?_⟩⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := (he C s).mp hs
    exact ⟨(image_member_l e hi he).mpr ((inter t).mp ht).1,
      (image_member_l e hi he).mpr ((inter t).mp ht).2⟩
  · rintro ⟨ht, hs⟩
    obtain ⟨t, hg, rfl⟩ := (he T s).mp ht
    exact (image_member_l e hi he).mpr ((inter t).mpr ⟨hg, (image_member_l e hi he).mp hs⟩)

theorem tp_projection_reflect_l {ω A Γ Y F T x : M.Domain} (hw : M.IsOmega ω)
    (hwN : N.IsOmega (e ω)) (dc : Dc_d I ω) (pair : M.IsCartesianProduct I Y A Γ)
    (space : Fseq_space_d I ω Y F) (tree : Tree_d F T) (fx : M.IsSetFunctionFromTo I x ω A)
    (project : Tp_projection_d J (e ω) (e A) (e Y) (e F) (e T) (e x)) : Tp_projection_d I ω A Y F T x := by
  classical
  apply Classical.byContradiction
  intro no
  obtain ⟨H, hist⟩ := ZF.fseq_space_exists_l I hM hw A
  obtain ⟨d, left⟩ := tp_left_l I hM pair
  obtain ⟨K, cut⟩ := hg_section_exists_l hM H x
  obtain ⟨C, filter⟩ := tp_filter_l I hM d F T K
  have treeC := filter.tree_l I hM left space hist tree (hg_section_tree_l cut)
  obtain ⟨α, R, rank⟩ := tree_rank_l hM hw dc space treeC (by
    intro q fq branch
    obtain ⟨y, fy, qy⟩ := ZF.fseq_compose_l I hM left.1 fq
    have proj := (left.projection_l I hM fq).mp qy
    obtain ⟨bt, bk⟩ := (filter.branch_l I hM hw left space hist fq proj).mp branch
    have eq := (hg_section_branch_l hM hw hist cut fx fy).mp bk
    exact no ⟨q, fq, bt, eq ▸ proj⟩)
  have spaceN := image_fseq_l hM hN e hi he hw hwN space
  have histN := image_fseq_l hM hN e hi he hw hwN hist
  obtain ⟨q, fq, branch, proj⟩ := project
  have fxN := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fx
  have bk := (hg_section_branch_l hN hwN histN (image_hg_section_l e hi he cut) fxN fxN).mpr rfl
  have bc := ((filter.image_l hM hN e hi he left space).branch_l J hN hwN
    (left.image_l hM hN e hi he) spaceN histN fq proj).mpr ⟨branch, bk⟩
  exact (image_tree_rank_l hM hN e hi he rank).no_branch_l hN hwN spaceN
    (image_tree_l e hi he treeC) fq bc

end YesMetaZFC.SetTheory.LargeCardinal
