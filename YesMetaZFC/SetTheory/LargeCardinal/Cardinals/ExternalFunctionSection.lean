import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalBookkeeping
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover
import YesMetaZFC.Model.SetTheory.CountableGround

/-! # 外部 host 函数的显式 section

在允许 ZFC 下的经典选择后，把模型内的函数图读取成 Lean 的 host 函数。
这层只消费已给出的集合函数证书，不把关系图误当成可计算函数。 -/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem countable_ground_bk_l :
    ∃ M : SetTheory.Structure.{1}, Nonempty (Bk_countable M.Domain) ∧
      M.Models ZFC ∧ _root_.WellFounded M.mem := by
  obtain ⟨M, hZFC, wf, e, he⟩ := SetTheory.countable_ground_l
  exact ⟨M, ⟨Bk_countable.of_surjective e he⟩, hZFC, wf⟩

/-! 外部良基性把模型内 `ω` 的每个成员标准化为有限数码。

这一点只使用 `ZF` 的“非空自然数有前驱”分类和外部 `mem` 良基性，
不把任意模型的内部 `ω` 误当作标准 ω。 -/
theorem standard_num_l {M : Structure} (hZF0 : M.Models ZF)
    {ω : M.Domain} (hω : M.IsOmega ω) (_wf : _root_.WellFounded M.mem) :
    ∀ x, M.mem x ω → ∃ k, Num_d k x := by
  intro x
  induction x using _wf.induction with
  | h x ih =>
      intro hxω
      by_cases hne : ∃ y, M.mem y x
      · obtain ⟨p, hpω, hsp⟩ :=
          Structure.IsOmega.exists_predecessor_of_mem_of_nonempty
            hZF0 hω hxω hne
        have hpmem : M.mem p x := hsp.predecessor_mem
        obtain ⟨k, hk⟩ := ih p hpmem hpω
        exact ⟨k + 1, p, hk, hsp⟩
      · exact ⟨0, fun y hy => hne ⟨y, hy⟩⟩

noncomputable def ext_eval_l {𝒞 : OrderedPairConvention} {I : 𝒞.Interpretation M}
    {F X Y : M.Domain} (function : M.IsSetFunctionFromTo I F X Y)
    (x : M.Domain) (hx : M.mem x X) : M.Domain :=
  Classical.choose (function.2.2 x hx)

theorem ext_eval_spec_l {𝒞 : OrderedPairConvention} {I : 𝒞.Interpretation M}
    {F X Y : M.Domain} (function : M.IsSetFunctionFromTo I F X Y)
    (x : M.Domain) (hx : M.mem x X) :
    M.mem (ext_eval_l function x hx) Y ∧
      M.PairMember I x (ext_eval_l function x hx) F :=
  Classical.choose_spec (function.2.2 x hx)

theorem ext_eval_unique_l {𝒞 : OrderedPairConvention} {I : 𝒞.Interpretation M}
    {F X Y : M.Domain} (function : M.IsSetFunctionFromTo I F X Y)
    {x y : M.Domain} (hx : M.mem x X)
    (hxy : M.PairMember I x y F) :
    ext_eval_l function x hx = y := by
  exact function.1.2 x _ _ (ext_eval_spec_l function x hx).2 hxy

noncomputable def ext_internal_num_l {hKP : M.Models KP} (k : Nat) : M.Domain :=
  Classical.choose (num_exists_l hKP k)

theorem ext_internal_num_spec_l {hKP : M.Models KP} (k : Nat) :
    Num_d k (ext_internal_num_l (M := M) (hKP := hKP) k) :=
  Classical.choose_spec (num_exists_l (M := M) hKP k)

/-! 外部读取内部 ω-共尾序列。`standard_num_l` 把内部索引归约到标准自然数，
再由函数图唯一性把对应值读成 host 序列。 -/
theorem cofinal_host_sequence_l {M : Structure} (hZF0 : M.Models ZF)
    {ω α F : M.Domain} (hω : M.IsOmega ω)
    (cf : M.IsCofinalOrdinalSequence
      (kp_pair_l (ZF.modelsKP hZF0)) F ω α)
    (wf : _root_.WellFounded M.mem) :
    ∃ s : Nat → M.Domain,
      (∀ k, M.mem (s k) α) ∧
      ∀ i, M.mem i α → ∃ k, i = s k ∨ M.mem i (s k) := by
  let I := kp_pair_l (ZF.modelsKP hZF0)
  let seq := cf.isIncreasing.1.1
  have ff : M.IsSetFunctionFromTo I F ω α := by
    refine ⟨seq.2.1, seq.2.2, ?_⟩
    intro n hn
    obtain ⟨k, hk⟩ := (seq.2.2 n).mp hn
    exact ⟨k, cf.value_mem hn hk, hk⟩
  let s : Nat → M.Domain := fun k =>
    ext_eval_l ff (ext_internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k)
      (num_mem_l hZF0.1 hω (ext_internal_num_spec_l (M := M)
        (hKP := ZF.modelsKP hZF0) k))
  refine ⟨s, ?_, ?_⟩
  · intro k
    exact (ext_eval_spec_l ff _ _).1
  · intro i hi
    rcases cf.isLimit.2.2 with ⟨range, hRange, hUnion⟩
    obtain ⟨value, hvalueRange, hivalue⟩ := (hUnion i).mp hi
    obtain ⟨index, hindex⟩ := (hRange value).mp hvalueRange
    have hindexω := ff.input_mem_of_pairMember hindex
    obtain ⟨k, hk⟩ := standard_num_l hZF0 hω wf index hindexω
    have hnum : Num_d k (ext_internal_num_l (M := M)
        (hKP := ZF.modelsKP hZF0) k) := ext_internal_num_spec_l (M := M)
      (hKP := ZF.modelsKP hZF0) k
    have hnumEq : ext_internal_num_l (M := M)
        (hKP := ZF.modelsKP hZF0) k = index :=
      num_unique_l hZF0.1 (k := k)
        (x := ext_internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k)
        (y := index) hnum hk
    have hnumω : M.mem (ext_internal_num_l (M := M)
        (hKP := ZF.modelsKP hZF0) k) ω :=
      num_mem_l hZF0.1 hω hnum
    have hgraph : M.PairMember (kp_pair_l (ZF.modelsKP hZF0))
        (ext_internal_num_l (M := M) (hKP := ZF.modelsKP hZF0) k)
        value F := by
      rw [hnumEq]
      exact hindex
    have hs : s k = value := by
      dsimp [s]
      exact ext_eval_unique_l ff hnumω hgraph
    exact ⟨k, Or.inr (hs ▸ hivalue)⟩

/-! `Smap_d` 的图证书可直接提升为两个传递载体之间的 host 函数。 -/
theorem Smap_d.output_mem_of_pairMember_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j x y : M.Domain} (h : Smap_d ι ω c d X Y j)
    (hxy : M.PairMember ι x y j) :
    M.mem y Y := by
  exact h.1.1.output_mem_of_pairMember hxy

theorem It_cone_d.image_member_l
    (hZF0 : M.Models ZF) {ω B Q G d N W P i f c X R : M.Domain}
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (hf : Rd_entry_d i f P) (hc : Rd_entry_d i c Q)
    (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) c X R)
    {x y : M.Domain}
    (hxy : M.PairMember (kp_pair_l (ZF.modelsKP hZF0)) x y f) :
    M.mem y N := by
  exact Smap_d.output_mem_of_pairMember_l
    (cone.elementary i f c X R hf hc mx) hxy

noncomputable def Smap_d.host_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j : M.Domain} (h : Smap_d ι ω c d X Y j) :
    {x : M.Domain // M.mem x X} → {y : M.Domain // M.mem y Y} :=
  fun x => ⟨Smap_d.value_l h x.property, Smap_d.value_mem_l h x.property⟩

theorem Smap_d.host_graph_l
    {M : Structure} {𝒞 : OrderedPairConvention} {ι : 𝒞.Interpretation M}
    {ω c d X Y j : M.Domain} (h : Smap_d ι ω c d X Y j)
    (x : {x : M.Domain // M.mem x X}) :
    M.PairMember ι x.1 (Smap_d.host_l h x).1 j :=
  Smap_d.value_graph_l h x.property

theorem Smap_d.host_comp_l
    {M : Structure} {ω c d e X Y Z j k l : M.Domain}
    (hKP : M.Models KP)
    (left : Smap_d (kp_pair_l hKP) ω c d X Y j)
    (middle : Smap_d (kp_pair_l hKP) ω d e Y Z k)
    (direct : Smap_d (kp_pair_l hKP) ω c e X Z l)
    (coherent : It_comp_d j k l)
    (x : {x : M.Domain // M.mem x X}) :
    Smap_d.host_l direct x = Smap_d.host_l middle (Smap_d.host_l left x) := by
  apply Subtype.ext
  have hleft := Smap_d.host_graph_l left x
  have hmiddle := Smap_d.host_graph_l middle (Smap_d.host_l left x)
  change Rd_entry_d x.1 (Smap_d.host_l left x).1 j at hleft
  change Rd_entry_d (Smap_d.host_l left x).1
    (Smap_d.host_l middle (Smap_d.host_l left x)).1 k at hmiddle
  have hcomp : M.PairMember (kp_pair_l hKP) x.1
      (Smap_d.host_l middle (Smap_d.host_l left x)).1 l := by
    change Rd_entry_d x.1 (Smap_d.host_l middle (Smap_d.host_l left x)).1 l
    exact coherent.2 x.1 (Smap_d.host_l middle (Smap_d.host_l left x)).1 |>.mpr
      ⟨(Smap_d.host_l left x).1, hleft, hmiddle⟩
  exact direct.1.1.1.2 x.1 _ _ (Smap_d.host_graph_l direct x) hcomp

/-! 锥的每个 owner embedding 现在可直接作为 host 函数 section 使用。 -/
noncomputable def It_cone_d.owner_host_l
    (hZF0 : M.Models ZF) {ω B Q G d N W P i f c X R : M.Domain}
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (hf : Rd_entry_d i f P) (hc : Rd_entry_d i c Q)
    (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) c X R) :
    {x : M.Domain // M.mem x X} → {y : M.Domain // M.mem y N} :=
  Smap_d.host_l (cone.elementary i f c X R hf hc mx)

theorem It_cone_d.owner_host_graph_l
    (hZF0 : M.Models ZF) {ω B Q G d N W P i f c X R : M.Domain}
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (hf : Rd_entry_d i f P) (hc : Rd_entry_d i c Q)
    (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) c X R)
    (x : {x : M.Domain // M.mem x X}) :
    M.PairMember (kp_pair_l (ZF.modelsKP hZF0)) x.1
      (It_cone_d.owner_host_l hZF0 cone hf hc mx x).1 f := by
  exact Smap_d.host_graph_l (cone.elementary i f c X R hf hc mx) x

/-! 沿原树边搬运 owner 时，锥的 `commute` 可直接提升为 host 值的相容性。
这里的 `stage` 是阶段模型之间的实际 `Smap_d` 图，故结论同时保留
阶段搬运和两端 owner 的完整函数值，不把关系图的单向包含误写成函数复合。 -/
theorem It_cone_d.owner_host_transport_l
    (hZF0 : M.Models ZF) {ω B Q G d N W P i j g u v c e X R Y S : M.Domain}
    (cone : It_cone_d (kp_pair_l (ZF.modelsKP hZF0)) ω B Q G d N W P)
    (hij : It_map_d G i j g)
    (hu : Rd_entry_d i u P) (hv : Rd_entry_d j v P)
    (hc : Rd_entry_d i c Q) (he : Rd_entry_d j e Q)
    (mx : Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) c X R)
    (my : Smdl_d (kp_pair_l (ZF.modelsKP hZF0)) e Y S)
    (stage : Smap_d (kp_pair_l (ZF.modelsKP hZF0)) ω c e X Y g)
    (x : {x : M.Domain // M.mem x X}) :
    Smap_d.host_l (cone.elementary i u c X R hu hc mx) x =
      Smap_d.host_l (cone.elementary j v e Y S hv he my)
        (Smap_d.host_l stage x) := by
  let left := cone.elementary i u c X R hu hc mx
  let right := cone.elementary j v e Y S hv he my
  have hxy := Smap_d.host_graph_l stage x
  have hyz := Smap_d.host_graph_l right (Smap_d.host_l stage x)
  change Rd_entry_d x.1 (Smap_d.host_l stage x).1 g at hxy
  change Rd_entry_d (Smap_d.host_l stage x).1
    (Smap_d.host_l right (Smap_d.host_l stage x)).1 v at hyz
  have hcomp : Rd_entry_d x.1
      (Smap_d.host_l right (Smap_d.host_l stage x)).1 u :=
    cone.commute i j g u v hij hu hv x.1 (Smap_d.host_l stage x).1
      (Smap_d.host_l right (Smap_d.host_l stage x)).1 hxy hyz
  have hleft := Smap_d.host_graph_l left x
  change Rd_entry_d x.1 (Smap_d.host_l left x).1 u at hleft
  apply Subtype.ext
  exact left.1.1.1.2 x.1 _ _ hleft hcomp

end YesMetaZFC.SetTheory.LargeCardinal
