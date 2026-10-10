import YesMetaZFC.Model.SetTheory.Internal.OrdinalFoldStepSource
import YesMetaZFC.SetTheory.Ord.Code.Sequence

/-! # 内部有限序列编码在极限秩层中的绝对性

递归历史的每个值都是较短前缀的实际编码。自然数前缀的整张历史因此是
ω 上的关系，而不是外部逐项选择出的列；非标准有限长度同样适用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {δ Z : M.Domain}
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z)
  (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => ZF.v_transitive_l I hZF hV
local notation "P" => sc_v_pair_l hZF hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

theorem rt_oc_recursion_l (F H n : (N).Domain) :
    (N).IsRecursiveSequence J (Oc_step_d J F) H n ↔
      M.IsRecursiveSequence I (Oc_step_d I F.val) H.val n.val := by
  have ent := rt_entry_l T nz hZF.1
  have cut := rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  refine and_congr (rt_sequence_l (ZF.modelsKP hZF) T nz P H n) ?_
  constructor
  · intro h i hi y hiy
    have iy := rd_entry_transitive_l T H.property hiy
    obtain ⟨K, hk, hs⟩ := h ⟨i, iy.1⟩ hi ⟨y, iy.2⟩ ((ent ..).mpr hiy)
    exact ⟨K.val, (cut ..).mp hk, (rt_oc_step_l hZF hδ hV nz ..).mp hs⟩
  · intro h i hi y hiy
    obtain ⟨K, hk, hs⟩ := h i.val hi y.val ((ent ..).mp hiy)
    let K' : (N).Domain := ⟨K, ZF.v_restriction_mem_l I hZF hV H.property hk⟩
    exact ⟨K', (cut ..).mpr hk, (rt_oc_step_l hZF hδ hV nz ..).mpr hs⟩

theorem rt_oc_fold_up_l (F n c : (N).Domain) (h : Oc_fold_d J F n c) :
    Oc_fold_d I F.val n.val c.val := by
  obtain ⟨H, hh, hc⟩ := h
  exact ⟨H.val, (rt_oc_recursion_l hZF hδ hV nz ..).mp hh,
    (rt_oc_step_l hZF hδ hV nz ..).mp hc⟩

theorem rt_oc_fold_down_l (ω F n c : (N).Domain) (hω : M.IsOmega ω.val)
    (hn : M.mem n.val ω.val) (hf : Oc_prefix_d I n.val F.val)
    (hv : ∀ i, M.mem i n.val → ∀ a, M.PairMember I i a F.val → M.mem a ω.val)
    (h : Oc_fold_d I F.val n.val c.val) : Oc_fold_d J F n c := by
  obtain ⟨H, hh, hc⟩ := h
  have hHZ := ZF.v_relation_mem_l I hZF hV hδ ω.property (fun p hp => by
    obtain ⟨i, a, code⟩ := hh.1.2.1.1 p hp
    have hia : M.PairMember I i a H := ⟨p, code, hp⟩
    have hi := (hh.1.2.2 i).mpr ⟨a, hia⟩
    have sub := hh.1.1.transitive i hi
    exact ⟨i, hω.transitive hZF n.val hn i hi, a,
      oc_fold_natural_l I hZF hω i (hω.transitive hZF n.val hn i hi) F.val a
        (hf.mono_l I sub) (fun j hj => hv j (sub j hj)) (hh.recursionValue_of_pairMember hi hia), code⟩)
  let H' : (N).Domain := ⟨H, hHZ⟩
  exact ⟨H', (rt_oc_recursion_l hZF hδ hV nz F H' n).mpr hh,
    (rt_oc_step_l hZF hδ hV nz F H' c).mpr hc⟩

/-- 自然数值图的规范序列码可以在源中原样解码。 -/
theorem rt_oc_seq_l (ω F c : (N).Domain) (hω : M.IsOmega ω.val)
    (hv : ∀ i a, M.PairMember I i a F.val → M.mem a ω.val) :
    Oc_seq_d J ω F c ↔ Oc_seq_d I ω.val F.val c.val := by
  constructor
  · rintro ⟨n, b, hn, hf, hb, hc⟩
    exact ⟨n.val, b.val, hn, (rt_ordinal_sequence_l (ZF.modelsKP hZF) T nz P ..).mp hf,
      rt_oc_fold_up_l hZF hδ hV nz F n b hb, (rt_oc_pair_l hZF hδ hV nz ..).mp hc⟩
  · rintro ⟨n, b, hn, hf, hb, hc⟩
    have pre := oc_seq_prefix_l I hf
    have nb := oc_fold_natural_l I hZF hω n hn F.val b pre (fun i _ => hv i) hb
    let n' : (N).Domain := ⟨n, T ω.val ω.property n hn⟩
    let b' : (N).Domain := ⟨b, T ω.val ω.property b nb⟩
    exact ⟨n', b', hn, (rt_ordinal_sequence_l (ZF.modelsKP hZF) T nz P F n').mpr hf,
      rt_oc_fold_down_l hZF hδ hV nz ω F n' b' hω hn pre (fun i _ => hv i) hb,
      (rt_oc_pair_l hZF hδ hV nz n' b' c).mpr hc⟩

end YesMetaZFC.SetTheory.Internal
