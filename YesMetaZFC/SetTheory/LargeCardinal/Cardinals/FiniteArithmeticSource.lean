import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Internal.FiniteTailSource
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift

/-! # 有限读出层中原自然数加法与轮次奇偶的绝对性

加法历史只有内部有限长度。其限制及整张历史由已有有限函数闭性回收，
不要求工作层满足替换或 ZF；有限长度排除加法递归中的非零极限分支。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {ω C : M.Domain}
  (hw : M.IsOmega ω) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "N" => rt_model_l C nc
local notation "J" => rt_pair_l fs.transitive nc (And.left hZF) fs.pair
include hw

theorem fs_add_step_l (a f x n : (N).Domain) (hn : M.mem n.val ω) (seq : M.IsSequenceOfLength I f.val n.val) :
    (N).IsOrdinalAdditionStep J a f x ↔ M.IsOrdinalAdditionStep I a.val f.val x.val := by
  have sq := rt_sequence_l (ZF.modelsKP hZF) fs.transitive nc fs.pair
  have ent := rt_entry_l fs.transitive nc hZF.1
  have zero (z : (N).Domain) : (∀ b, ¬ (N).mem b z) ↔ ∀ b, ¬ M.mem b z.val :=
    ⟨fun h b hb => h ⟨b,fs.transitive _ z.property b hb⟩ hb,fun h b => h b.val⟩
  have first : (N).IsZeroLengthSequence J f ↔ M.IsZeroLengthSequence I f.val := by
    constructor
    · rintro ⟨z,hz,he⟩; exact ⟨z.val,(sq ..).mp hz,(zero z).mp he⟩
    · rintro ⟨z,hz,he⟩
      have eq := hz.2.2.eq hZF.1 seq.2.2
      let z' : (N).Domain := ⟨z,eq.symm ▸ n.property⟩
      exact ⟨z',(sq ..).mpr hz,(zero z').mpr he⟩
  have last (b : (N).Domain) : (N).IsSuccessorLengthSequenceWithLast J f b ↔ M.IsSuccessorLengthSequenceWithLast I f.val b.val := by
    constructor
    · rintro ⟨i,hi,k,hk,hf,hb⟩
      exact ⟨i.val,(rt_ordinal_iff_l fs.transitive nc (ZF.modelsKP hZF) i).mp hi,k.val,
        (rt_successor_l fs.transitive nc hZF.1 k i).mp hk,(sq ..).mp hf,(ent ..).mp hb⟩
    · rintro ⟨i,hi,k,hk,hf,hb⟩
      have eq := hf.2.2.eq hZF.1 seq.2.2
      let k' : (N).Domain := ⟨k,eq.symm ▸ n.property⟩
      let i' : (N).Domain := ⟨i,fs.transitive _ k'.property i hk.predecessor_mem⟩
      exact ⟨i',rt_ordinal_l fs.transitive nc i' hi,k',(rt_successor_l fs.transitive nc hZF.1 k' i').mpr hk,
        (sq ..).mpr hf,(ent ..).mpr hb⟩
  have no : ¬ M.IsLimitLengthSequenceWithUnion I f.val x.val := by
    rintro ⟨k,hk,hf,_⟩
    have eq := hf.2.2.eq hZF.1 seq.2.2
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) n.val (hw.subset_limitOrdinal (ZF.modelsKP hZF) (eq ▸ hk) n.val hn)
  have no' : ¬ (N).IsLimitLengthSequenceWithUnion J f x := by
    rintro ⟨k,hk,hf,_⟩
    have eq := ((sq ..).mp hf).2.2.eq hZF.1 seq.2.2
    have hk := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) k).mp hk
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) n.val (hw.subset_limitOrdinal (ZF.modelsKP hZF) (eq ▸ hk) n.val hn)
  refine or_congr (and_congr first ⟨congrArg Subtype.val,Subtype.ext⟩)
    (or_congr ?_ (iff_of_false no' no))
  constructor
  · rintro ⟨b,hb,hx⟩; exact ⟨b.val,(last b).mp hb,(rt_successor_l fs.transitive nc hZF.1 x b).mp hx⟩
  · rintro ⟨b,hb,hx⟩
    let b' : (N).Domain := ⟨b,fs.transitive _ x.property b hx.predecessor_mem⟩
    exact ⟨b',(last b').mpr hb,(rt_successor_l fs.transitive nc hZF.1 x b').mpr hx⟩

theorem fs_add_recursion_l (a f b : (N).Domain) (hb : M.mem b.val ω) :
    (N).IsRecursiveSequence J ((N).IsOrdinalAdditionStep J a) f b ↔
      M.IsRecursiveSequence I (M.IsOrdinalAdditionStep I a.val) f.val b.val := by
  have sq := rt_sequence_l (ZF.modelsKP hZF) fs.transitive nc fs.pair
  have ent := rt_entry_l fs.transitive nc hZF.1
  have cut := rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
  have bound (seq : M.IsSequenceOfLength I f.val b.val) : M.IsSetFunctionFromTo I f.val b.val C :=
    ⟨seq.2.1,seq.2.2,fun i hi => (seq.2.2 i).mp hi |>.imp fun y hy => ⟨(rd_entry_transitive_l fs.transitive f.property hy).2,hy⟩⟩
  constructor
  · rintro ⟨seq,step⟩
    have seq := (sq ..).mp seq
    refine ⟨seq,fun i hi x hx => ?_⟩
    have ix := rd_entry_transitive_l fs.transitive f.property hx
    obtain ⟨g,hg,hx⟩ := step ⟨i,ix.1⟩ hi ⟨x,ix.2⟩ ((ent ..).mpr hx)
    have hg := (cut ..).mp hg
    have gf := hg.isSetFunctionFromTo (bound seq) (seq.1.transitive i hi)
    exact ⟨g.val,hg,(fs_add_step_l hZF hw fs nc a g ⟨x,ix.2⟩ ⟨i,ix.1⟩ (hw.transitive (ZF.modelsKP hZF) _ hb i hi)
      ⟨seq.1.mem hi,gf.1,gf.2.1⟩).mp hx⟩
  · rintro ⟨seq,step⟩
    refine ⟨(sq ..).mpr seq,fun i hi x hx => ?_⟩
    obtain ⟨g,hg,hx⟩ := step i.val hi x.val ((ent ..).mp hx)
    have gf := hg.isSetFunctionFromTo (bound seq) (seq.1.transitive i.val hi)
    have hiω := hw.transitive (ZF.modelsKP hZF) _ hb i.val hi
    let g' : (N).Domain := ⟨g,fs.functions i.val C g hiω (fun _ h => h) (fn0_of_function_l (ZF.modelsKP hZF) gf)⟩
    exact ⟨g',(cut ..).mpr hg,(fs_add_step_l hZF hw fs nc a g' x i hiω ⟨seq.1.mem hi,gf.1,gf.2.1⟩).mpr hx⟩

theorem fs_add_l (a b x : (N).Domain) (ha : M.mem a.val ω) (hb : M.mem b.val ω) :
    (N).IsOrdinalAddition J x a b ↔ M.IsOrdinalAddition I x.val a.val b.val := by
  constructor
  · rintro ⟨f,hf,hx⟩
    have hf := (fs_add_recursion_l hZF hw fs nc a f b hb).mp hf
    exact ⟨f.val,hf,(fs_add_step_l hZF hw fs nc a f x b hb hf.1).mp hx⟩
  · rintro ⟨f,hf,hx⟩
    have range {i y} (iy : Rd_entry_d i y f) : M.mem y ω := by
      have hi := (hf.1.2.2 i).mpr ⟨y,iy⟩
      exact ZF.ordinalAddition_mem_omega hZF I hw ha (hw.transitive (ZF.modelsKP hZF) _ hb i hi) (hf.recursionValue_of_pairMember hi iy)
    have ff : M.IsSetFunctionFromTo I f b.val ω := ⟨hf.1.2.1,hf.1.2.2,
      fun i hi => (hf.1.2.2 i).mp hi |>.imp fun y hy => ⟨range hy,hy⟩⟩
    let f' : (N).Domain := ⟨f,fs.functions b.val ω f hb (fs.transitive ω fs.omega_mem) (fn0_of_function_l (ZF.modelsKP hZF) ff)⟩
    exact ⟨f',(fs_add_recursion_l hZF hw fs nc a f' b hb).mpr hf,(fs_add_step_l hZF hw fs nc a f' x b hb hf.1).mpr hx⟩

theorem fs_even_l (w n : (N).Domain) (hw' : w.val = ω) :
    Gm_even_d J w n ↔ Gm_even_d I ω n.val := by
  constructor
  · rintro ⟨k,hk,sum⟩
    exact ⟨k.val,hw' ▸ hk,(fs_add_l hZF hw fs nc k k n (hw' ▸ hk) (hw' ▸ hk)).mp sum⟩
  · rintro ⟨k,hk,sum⟩
    let k' : (N).Domain := ⟨k,fs.transitive ω fs.omega_mem k hk⟩
    exact ⟨k',(show M.mem k w.val from hw'.symm ▸ hk),(fs_add_l hZF hw fs nc k' k' n hk hk).mpr sum⟩

end YesMetaZFC.SetTheory.LargeCardinal
