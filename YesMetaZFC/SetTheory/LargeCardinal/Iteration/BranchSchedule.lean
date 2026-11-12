import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalFunctionSection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableLimit

/-! # 内部共尾枝序列的 host 读取

允许经典选择后，从模型内部的 `Fn0_d ω B F` 读取每个标准自然数坐标的
实际枝节点。该层只保留原有的前驱证书，不把 host 序列误当成模型内部函数。 -/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

noncomputable def internal_num_l {hKP : M.Models KP} (k : Nat) : M.Domain :=
  Classical.choose (num_exists_l hKP k)

theorem internal_num_spec_l {hKP : M.Models KP} (k : Nat) :
    Num_d k (internal_num_l (M := M) (hKP := hKP) k) :=
  Classical.choose_spec (num_exists_l (M := M) hKP k)

/-! 在外部良基模型中，内部 ω 的任意成员都来自某个标准数码。 -/
theorem standard_num_eq_internal_l {hZF0 : M.Models ZF}
    {ω : M.Domain} (hω : M.IsOmega ω) (wf : _root_.WellFounded M.mem)
    (x : M.Domain) (hx : M.mem x ω) :
    ∃ k, internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k = x := by
  obtain ⟨k, hk⟩ := standard_num_l hZF0 hω wf x hx
  have heq : x = internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k :=
    num_unique_l hZF0.1 (k := k) (x := x)
      (y := internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k) hk
      (internal_num_spec_l (M := M) (hKP := ZF.modelsKP hZF0) k)
  exact ⟨k, heq.symm⟩

/-! 内部 ω 共尾列在外部良基模型中可读成真正的 `Nat` 共尾列。 -/
theorem host_cofinal_sequence_l {hZF0 : M.Models ZF}
    {ω α F : M.Domain}
    (hω : M.IsOmega ω)
    (cf : M.IsCofinalOrdinalSequence
      (kp_pair_l (ZF.modelsKP hZF0)) F ω α)
    (wf : _root_.WellFounded M.mem) :
    ∃ s : Nat → M.Domain,
      (∀ k, M.mem (s k) α) ∧
      ∀ i, M.mem i α → ∃ k, i = s k ∨ M.mem i (s k) := by
  let I := kp_pair_l (ZF.modelsKP hZF0)
  have seq := cf.isIncreasing.1.1
  have ff : M.IsSetFunctionFromTo I F ω α := ⟨seq.2.1, seq.2.2, fun n hn => by
    obtain ⟨k, hk⟩ := (seq.2.2 n).mp hn
    exact ⟨k, cf.value_mem hn hk, hk⟩⟩
  let s : Nat → M.Domain := fun k =>
    ext_eval_l ff (internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k)
      (num_mem_l hZF0.1 hω (internal_num_spec_l (M := M)
        (hKP := ZF.modelsKP hZF0) k))
  have smem : ∀ k, M.mem (s k) α := by
    intro k
    exact (ext_eval_spec_l ff _ _).1
  refine ⟨s, smem, ?_⟩
  intro i hi
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF0 I ff.1 ff.2.1
  obtain ⟨k, hk, hik⟩ := ((cf.range_isCofinalSubset hZF0.1 hD).2.2 i).mp hi
  obtain ⟨n, hnk⟩ := (hD k).mp hk
  have hnω := ff.input_mem_of_pairMember hnk
  obtain ⟨m, hmn⟩ := standard_num_eq_internal_l
    (hZF0 := hZF0) hω wf n hnω
  have hnumω := num_mem_l hZF0.1 hω (internal_num_spec_l
    (M := M) (hKP := ZF.modelsKP hZF0) m)
  have hsk : s m = k := by
    dsimp [s]
    apply ext_eval_unique_l ff hnumω
    exact hmn.symm ▸ hnk
  refine ⟨m, ?_⟩
  rw [hsk]
  exact Or.inr hik

/-! 外部良基的 `ω` 现在具有真正的外部 `Nat` 枚举。 -/
noncomputable def Bk_countable.omega_l {M : Structure} (hZF : M.Models ZF)
    {ω : M.Domain} (hω : M.IsOmega ω) (wf : _root_.WellFounded M.mem) :
    Bk_countable {n : M.Domain // M.mem n ω} where
  enum k := ⟨internal_num_l (M := M) (hKP := ZF.modelsKP hZF) k,
    num_mem_l hZF.1 hω (internal_num_spec_l (M := M)
      (hKP := ZF.modelsKP hZF) k)⟩
  pick n := Classical.choose (standard_num_l hZF hω wf n.1 n.2)
  pick_spec n := by
    apply Subtype.ext
    exact num_unique_l hZF.1
      (internal_num_spec_l (M := M) (hKP := ZF.modelsKP hZF)
        (Classical.choose (standard_num_l hZF hω wf n.1 n.2)))
      (Classical.choose_spec (standard_num_l hZF hω wf n.1 n.2))

theorem It_branch_d.host_successor_sequence_l
    (hZF : M.Models ZF) {ω T B z : M.Domain} (hw : M.IsOmega ω)
    (order : It_order_d ω T) (branch : It_branch_d ω T B) (hz : M.mem z B) :
    ∃ F, Fn0_d ω B F ∧ ∃ s : Nat → M.Domain,
      (∀ k, M.mem (s k) B ∧ ∃ n, Num_d k n ∧ Rd_entry_d n (s k) F) ∧
      (∀ i j x y, M.SuccessorOf j i → Rd_entry_d i x F → Rd_entry_d j y F →
        It_pred_d T x y) := by
  obtain ⟨F, hF, _, hpred, _⟩ := branch.successor_sequence_l hZF hw order hz
  let fn := fn0_function_l (ZF.modelsKP hZF) hF
  let s : Nat → M.Domain := fun k =>
    ext_eval_l fn (internal_num_l (M := M) (hKP := ZF.modelsKP hZF) k)
      (num_mem_l hZF.1 hw (internal_num_spec_l (M := M)
        (hKP := ZF.modelsKP hZF) k))
  refine ⟨F, hF, s, ?_, hpred⟩
  intro k
  have hn : Num_d k (internal_num_l (M := M) (hKP := ZF.modelsKP hZF) k) :=
    internal_num_spec_l (M := M) (hKP := ZF.modelsKP hZF) k
  have hnk := num_mem_l hZF.1 hw hn
  have hs := ext_eval_spec_l fn
    (internal_num_l (M := M) (hKP := ZF.modelsKP hZF) k) hnk
  exact ⟨hs.1, ⟨internal_num_l (M := M) (hKP := ZF.modelsKP hZF) k, hn, hs.2⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 内部 ω 的外部可数枚举

外部良基性先把内部 `ω` 标准化，再把内部的满射读成 host 满射。
这一步只负责把一个已有的内部可数证书接到 `Bk_countable`，不制造新的
可数模型或阶段覆盖假设。 -/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-! 外部可数地模型中的任意非空内部阶段域可直接取得 `Bk_countable`。 -/
noncomputable def Bk_countable.model_subtype_l {α : M.Domain}
    (count : Bk_countable M.Domain) (nonempty : ∃ i, M.mem i α) :
    Bk_countable {i : M.Domain // M.mem i α} :=
  count.subtype (fun i => M.mem i α) nonempty

noncomputable def Bk_countable.internal_omega_l
    (hZF0 : M.Models ZF) {ω : M.Domain} (hω : M.IsOmega ω)
    (_wf : _root_.WellFounded M.mem) :
    Bk_countable {x : M.Domain // M.mem x ω} where
  enum k := ⟨internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k,
    num_mem_l hZF0.1 hω (internal_num_spec_l (M := M)
      (hKP := ZF.modelsKP hZF0) k)⟩
  pick x := Classical.choose (standard_num_l hZF0 hω _wf x.1 x.2)
  pick_spec x := by
    apply Subtype.ext
    have hk := Classical.choose_spec (standard_num_l hZF0 hω _wf x.1 x.2)
    exact num_unique_l hZF0.1
      (internal_num_spec_l (M := M) (hKP := ZF.modelsKP hZF0)
        (Classical.choose (standard_num_l hZF0 hω _wf x.1 x.2))) hk

/-! 任意内部 `ω` 到 `α` 的满射都给出 α 的外部枚举。 -/
noncomputable def Bk_countable.of_internal_surjection_l
    (hZF0 : M.Models ZF) {ω α e : M.Domain} (hω : M.IsOmega ω)
    (wf : _root_.WellFounded M.mem)
    (fn : M.IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP hZF0)) e ω α)
    (onto : M.IsSetSurjectiveOnto
      (kp_pair_l (ZF.modelsKP hZF0)) e ω α) :
    Bk_countable {x : M.Domain // M.mem x α} where
  enum k :=
    let n := internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k
    let hn := num_mem_l hZF0.1 hω (internal_num_spec_l (M := M)
      (hKP := ZF.modelsKP hZF0) k)
    ⟨ext_eval_l fn n hn, (ext_eval_spec_l fn n hn).1⟩
  pick x :=
    let n := Classical.choose (onto x.1 x.2)
    let hn := (Classical.choose_spec (onto x.1 x.2)).1
    Classical.choose (standard_num_l hZF0 hω wf n hn)
  pick_spec x := by
    let n := Classical.choose (onto x.1 x.2)
    have hn : M.mem n ω := (Classical.choose_spec (onto x.1 x.2)).1
    have hnx : M.PairMember (kp_pair_l (ZF.modelsKP hZF0)) n x.1 e :=
      (Classical.choose_spec (onto x.1 x.2)).2
    let k := Classical.choose (standard_num_l hZF0 hω wf n hn)
    have hkn : Num_d k n := Classical.choose_spec (standard_num_l hZF0 hω wf n hn)
    have ek : internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k = n :=
      num_unique_l hZF0.1 (internal_num_spec_l (M := M)
        (hKP := ZF.modelsKP hZF0) k) hkn
    have hωk : M.mem (internal_num_l (M := M)
        (hKP := ZF.modelsKP hZF0) k) ω :=
      num_mem_l hZF0.1 hω (internal_num_spec_l (M := M)
        (hKP := ZF.modelsKP hZF0) k)
    have hgraph : M.PairMember (kp_pair_l (ZF.modelsKP hZF0))
        (internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k) x.1 e := by
      rw [ek]
      exact hnx
    have hval := ext_eval_unique_l fn hωk hgraph
    apply Subtype.ext
    dsimp
    exact hval

/-! 直接消费内部基数不超过 ω 的证书。 -/
noncomputable def Bk_countable.of_internal_countable_l
    (hZF0 : M.Models ZF) {ω α : M.Domain} (hω : M.IsOmega ω)
    (wf : _root_.WellFounded M.mem)
    (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF0)) α ω)
    (ha : ∃ x, M.mem x α) :
    Bk_countable {x : M.Domain // M.mem x α} := by
  let e := Classical.choose (countable_surjection_zf_l hZF0 count ha)
  have he := Classical.choose_spec (countable_surjection_zf_l hZF0 count ha)
  exact Bk_countable.of_internal_surjection_l hZF0 hω wf he.1 he.2

theorem Bk_countable.of_internal_surjection_spec_l
    (hZF0 : M.Models ZF) {ω α e : M.Domain} (hω : M.IsOmega ω)
    (wf : _root_.WellFounded M.mem)
    (fn : M.IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP hZF0)) e ω α)
    (onto : M.IsSetSurjectiveOnto
      (kp_pair_l (ZF.modelsKP hZF0)) e ω α) :
    Function.Surjective (Bk_countable.of_internal_surjection_l
      hZF0 hω wf fn onto).enum := by
  intro x
  exact ⟨(Bk_countable.of_internal_surjection_l
    hZF0 hω wf fn onto).pick x,
    (Bk_countable.of_internal_surjection_l
      hZF0 hω wf fn onto).pick_spec x⟩

/-! 共尾序列的每个阶段现在都有真正的外部 `Nat` 编号。 -/
theorem host_cofinal_stage_enum_l {M : Structure} {hZF0 : M.Models ZF}
    {ω α F : M.Domain} (hω : M.IsOmega ω)
    (cf : M.IsCofinalOrdinalSequence
      (kp_pair_l (ZF.modelsKP hZF0)) F ω α)
    (wf : _root_.WellFounded M.mem) :
    ∃ s : Nat → {i : M.Domain // M.mem i α},
      ∀ i : {i : M.Domain // M.mem i α}, ∃ k,
        i.1 = (s k).1 ∨ M.mem i.1 (s k).1 := by
  obtain ⟨s, hs, cofinal⟩ := @host_cofinal_sequence_l M hZF0 ω α F hω cf wf
  refine ⟨fun k => ⟨s k, hs k⟩, ?_⟩
  intro i
  exact cofinal i.1 i.2

/-! 内部可数阶段直接产生强 owner-front 结论。 -/
theorem It_cone_d.owner_code_front_of_internal_countable_l
    (hZF0 : M.Models ZF) {ω α T Q G B d N W P A Ec : M.Domain}
    (hω : M.IsOmega ω) (wf : _root_.WellFounded M.mem)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF0)) ω α T Q G)
    (inside : M.MemberSubset B α)
    (en : Ja_enum_d (kp_pair_l (ZF.modelsKP hZF0)) ω α Q Ec)
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (transitive : M.TransitiveSet N) (hA : M.mem A N)
    (branch : It_branch_d α T B)
    (count : M.CardinalLessOrEqual (kp_pair_l (ZF.modelsKP hZF0)) α ω)
    (nonempty : ∃ x, M.mem x α) :
    ∃ codeCount : Bk_countable {x : M.Domain // M.mem x α},
      ∀ y, M.mem y A → ∀ k, ∃ m i e n,
        k < m ∧ It_front_d α B i
          ((codeCount.enum
            (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) ∧
        M.mem i B ∧ M.mem n ω ∧
          It_owner_code_d P Ec Q y
            ((codeCount.enum
              (YesMetaZFC.Logic.Arithmetic.NatPairing.unpair_l m).1).1) e n := by
  let codeCount := Bk_countable.of_internal_countable_l
    hZF0 hω wf count nonempty
  refine ⟨codeCount, ?_⟩
  exact It_cone_d.owner_code_front_auto_l hZF0 diagram inside en cone
    transitive hA branch codeCount

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 外部单调共尾分支序列

有限定向前端律可以在外部 `Nat` 枚举上递归，得到真正单调的分支节点列。
它仍只负责树几何，不伪造阶段模型的早期代表或 transport/embed family。 -/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

noncomputable def It_branch_d.front_choose_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (i j : {x : M.Domain // M.mem x α}) :
    {x : M.Domain // M.mem x B} := by
  let h := branch.front_directed_l hZF0 order i.1 j.1 i.2 j.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1.2.1⟩

theorem It_branch_d.front_choose_spec_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (i j : {x : M.Domain // M.mem x α}) :
    It_front_d α B i.1 (It_branch_d.front_choose_l hZF0 order branch i j).1 ∧
      It_front_d α B j.1 (It_branch_d.front_choose_l hZF0 order branch i j).1 := by
  let h := branch.front_directed_l hZF0 order i.1 j.1 i.2 j.2
  simpa [It_branch_d.front_choose_l] using Classical.choose_spec h

noncomputable def It_branch_d.chain_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (count : Bk_countable {x : M.Domain // M.mem x α}) :
    Nat → {x : M.Domain // M.mem x B} :=
  Nat.rec
    (It_branch_d.front_choose_l hZF0 order branch (count.enum 0) (count.enum 0))
    (fun n prev => It_branch_d.front_choose_l hZF0 order branch
      (count.enum (n + 1)) ⟨prev.1, branch.subset prev.1 prev.2⟩)

theorem It_branch_d.chain_front_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (count : Bk_countable {x : M.Domain // M.mem x α}) (n : Nat) :
    It_front_d α B (count.enum n).1
      ((It_branch_d.chain_l hZF0 order branch count n).1) := by
  induction n with
  | zero =>
      exact (It_branch_d.front_choose_spec_l hZF0 order branch (count.enum 0) (count.enum 0)).1
  | succ n ih =>
      exact (It_branch_d.front_choose_spec_l hZF0 order branch (count.enum (n + 1))
        ⟨(It_branch_d.chain_l hZF0 order branch count n).1,
          branch.subset _ (It_branch_d.chain_l hZF0 order branch count n).2⟩).1

theorem It_branch_d.chain_mono_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (count : Bk_countable {x : M.Domain // M.mem x α}) (n : Nat) :
    (It_branch_d.chain_l hZF0 order branch count n).1 =
        (It_branch_d.chain_l hZF0 order branch count (n + 1)).1 ∨
      M.mem (It_branch_d.chain_l hZF0 order branch count n).1
        (It_branch_d.chain_l hZF0 order branch count (n + 1)).1 := by
  have h := It_branch_d.front_choose_spec_l hZF0 order branch (count.enum (n + 1))
    ⟨(It_branch_d.chain_l hZF0 order branch count n).1,
      branch.subset _ (It_branch_d.chain_l hZF0 order branch count n).2⟩
  simpa [It_branch_d.chain_l] using h.2.2.2

theorem It_branch_d.chain_le_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (count : Bk_countable {x : M.Domain // M.mem x α})
    {m n : Nat} (h : m ≤ n) :
    (It_branch_d.chain_l hZF0 order branch count m).1 =
        (It_branch_d.chain_l hZF0 order branch count n).1 ∨
      M.mem (It_branch_d.chain_l hZF0 order branch count m).1
        (It_branch_d.chain_l hZF0 order branch count n).1 := by
  induction h with
  | refl => exact Or.inl rfl
  | @step n h ih =>
      have hm := It_branch_d.chain_mono_l hZF0 order branch count n
      rcases ih with heq | hmem
      · rcases hm with hnext | hnext
        · exact Or.inl (heq.trans hnext)
        · exact Or.inr (heq ▸ hnext)
      · rcases hm with hnext | hnext
        · exact Or.inr (hnext ▸ hmem)
        · exact Or.inr ((order.ordinal.mem
            (branch.subset _ (It_branch_d.chain_l hZF0 order branch count (n + 1)).2)).transitive
              _ hnext _ hmem)

theorem It_branch_d.chain_cofinal_l
    {α T B : M.Domain} (hZF0 : M.Models ZF) (order : It_order_d α T)
    (branch : It_branch_d α T B)
    (count : Bk_countable {x : M.Domain // M.mem x α}) :
    ∀ i, M.mem i α → ∃ n,
      i = (It_branch_d.chain_l hZF0 order branch count n).1 ∨
        M.mem i (It_branch_d.chain_l hZF0 order branch count n).1 := by
  intro i hi
  let c : {x : M.Domain // M.mem x α} := ⟨i, hi⟩
  let n := count.pick c
  have hc : (count.enum n).1 = i := congrArg Subtype.val (count.pick_spec c)
  refine ⟨n, ?_⟩
  have hfront := It_branch_d.chain_front_l hZF0 order branch count n
  exact hc ▸ hfront.2.2

end YesMetaZFC.SetTheory.LargeCardinal
