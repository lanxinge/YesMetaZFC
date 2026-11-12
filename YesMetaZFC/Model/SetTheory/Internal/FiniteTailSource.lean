import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.Ord.Arithmetic.Normal
import YesMetaZFC.SetTheory.Ord.FiniteTail

/-! # 极限秩层中原序数加法的绝对性

递归历史的坐标分别由右参数和加法值统一界定，因而整张历史仍在源内。
源只需是实际极限秩层；不要求它满足收集、替换或 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {η Y : M.Domain}
  (hη : M.IsLimitOrdinal η) (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y)
  (ny : Nonempty {x // M.mem x Y})
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => v_transitive_l Q hY
local notation "P" => sc_v_pair_l (ZF.modelsKP hZF) hη hY
local notation "N" => rt_model_l Y ny
local notation "J" => rt_pair_l T ny (And.left hZF) P

theorem rt_oa_step_l (a f x : (N).Domain) :
    (N).IsOrdinalAdditionStep J a f x ↔ M.IsOrdinalAdditionStep Q a.val f.val x.val := by
  have seq := rt_sequence_l (ZF.modelsKP hZF) T ny P
  have ent := rt_entry_l T ny hZF.1
  have zero (z : (N).Domain) : (∀ b, ¬ (N).mem b z) ↔ ∀ b, ¬ M.mem b z.val :=
    ⟨fun h b hb => h ⟨b, T z.val z.property b hb⟩ hb, fun h b => h b.val⟩
  have first : (N).IsZeroLengthSequence J f ↔ M.IsZeroLengthSequence Q f.val := by
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨z.val, (seq ..).mp hz, (zero z).mp he⟩
    · rintro ⟨z, hz, he⟩
      let z' : (N).Domain := ⟨z, ZF.v_domain_mem_l Q hZF hY f.property hz.2.2⟩
      exact ⟨z', (seq ..).mpr hz, (zero z').mpr he⟩
  have last (b : (N).Domain) : (N).IsSuccessorLengthSequenceWithLast J f b ↔
      M.IsSuccessorLengthSequenceWithLast Q f.val b.val := by
    constructor
    · rintro ⟨i, hi, k, hk, hf, hb⟩
      exact ⟨i.val, (rt_ordinal_iff_l T ny (ZF.modelsKP hZF) i).mp hi, k.val,
        (rt_successor_l T ny hZF.1 k i).mp hk, (seq ..).mp hf, (ent ..).mp hb⟩
    · rintro ⟨i, hi, k, hk, hf, hb⟩
      let k' : (N).Domain := ⟨k, ZF.v_domain_mem_l Q hZF hY f.property hf.2.2⟩
      let i' : (N).Domain := ⟨i, T k k'.property i hk.predecessor_mem⟩
      exact ⟨i', rt_ordinal_l T ny i' hi, k', (rt_successor_l T ny hZF.1 k' i').mpr hk,
        (seq ..).mpr hf, (ent ..).mpr hb⟩
  have limit : (N).IsLimitLengthSequenceWithUnion J f x ↔
      M.IsLimitLengthSequenceWithUnion Q f.val x.val := by
    constructor
    · rintro ⟨k, hk, hf, r, hr, hx⟩
      exact ⟨k.val, (rt_limit_l T ny (ZF.modelsKP hZF) k).mp hk, (seq ..).mp hf, r.val,
        (rt_range_l T ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) P r f).mp hr,
        (rt_union_l T ny x r).mp hx⟩
    · rintro ⟨k, hk, hf, r, hr, hx⟩
      let k' : (N).Domain := ⟨k, ZF.v_domain_mem_l Q hZF hY f.property hf.2.2⟩
      obtain ⟨β, B, hβ, hB, sub⟩ := (ZF.v_unfold_l Q hZF hY f.val).mp f.property
      have hrY : M.mem r Y := (ZF.v_unfold_l Q hZF hY r).mpr ⟨β, B, hβ, hB, fun b hb => by
        obtain ⟨i, p, code, hp⟩ := (hr b).mp hb
        exact (code.mem_l M (v_transitive_l Q hB) (sub p hp)).2⟩
      let r' : (N).Domain := ⟨r, hrY⟩
      exact ⟨k', (rt_limit_l T ny (ZF.modelsKP hZF) k').mpr hk, (seq ..).mpr hf, r',
        (rt_range_l T ny hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) P r' f).mpr hr,
        (rt_union_l T ny x r').mpr hx⟩
  refine or_congr (and_congr first ⟨congrArg Subtype.val, Subtype.ext⟩) (or_congr ?_ limit)
  constructor
  · rintro ⟨b, hb, hx⟩
    exact ⟨b.val, (last b).mp hb, (rt_successor_l T ny hZF.1 x b).mp hx⟩
  · rintro ⟨b, hb, hx⟩
    let b' : (N).Domain := ⟨b, T x.val x.property b hx.predecessor_mem⟩
    exact ⟨b', (last b').mpr hb, (rt_successor_l T ny hZF.1 x b').mpr hx⟩

theorem rt_oa_recursion_l (a f b : (N).Domain) :
    (N).IsRecursiveSequence J ((N).IsOrdinalAdditionStep J a) f b ↔
      M.IsRecursiveSequence Q (M.IsOrdinalAdditionStep Q a.val) f.val b.val := by
  have ent := rt_entry_l T ny hZF.1
  have cut := rt_restriction_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T ny P
  refine and_congr (rt_sequence_l (ZF.modelsKP hZF) T ny P f b) ?_
  constructor
  · intro h i hi x hix
    have ix := rd_entry_transitive_l T f.property hix
    obtain ⟨g, hg, hx⟩ := h ⟨i, ix.1⟩ hi ⟨x, ix.2⟩ ((ent ..).mpr hix)
    exact ⟨g.val, (cut ..).mp hg, (rt_oa_step_l hZF hη hY ny ..).mp hx⟩
  · intro h i hi x hix
    obtain ⟨g, hg, hx⟩ := h i.val hi x.val ((ent ..).mp hix)
    let g' : (N).Domain := ⟨g, ZF.v_restriction_mem_l Q hZF hY f.property hg⟩
    exact ⟨g', (cut ..).mpr hg, (rt_oa_step_l hZF hη hY ny ..).mpr hx⟩

/-- 右参数可为任意内部序数；有限后继层直接取 b∈ω。 -/
theorem rt_oa_l (a b x : (N).Domain) (ha : M.IsOrdinal a.val) :
    (N).IsOrdinalAddition J x a b ↔ M.IsOrdinalAddition Q x.val a.val b.val := by
  constructor
  · rintro ⟨f, hf, hx⟩
    exact ⟨f.val, (rt_oa_recursion_l hZF hη hY ny ..).mp hf, (rt_oa_step_l hZF hη hY ny ..).mp hx⟩
  · intro sum
    obtain ⟨f, hf, hx⟩ := sum
    obtain ⟨B, hB, hbB, hxB⟩ := v_joint_bound_l Q hY b.property x.property
    have hfY : M.mem f Y := v_relation_mem_l Q hY hη hB (fun p hp => by
      obtain ⟨i, v, code⟩ := hf.1.2.1.1 p hp
      have entry : M.PairMember Q i v f := ⟨p, code, hp⟩
      have hi := (hf.1.2.2 i).mpr ⟨v, entry⟩
      have add := hf.recursionValue_of_pairMember hi entry
      have hv := ZF.ordinalAddition_isIncreasingOnOrdinals hZF Q ha i b.val
        (hf.1.1.mem hi) hf.1.1 hi v x.val add ⟨f, hf, hx⟩
      exact ⟨i, hbB i hi, v, hxB v hv, code⟩)
    let f' : (N).Domain := ⟨f, hfY⟩
    exact ⟨f', (rt_oa_recursion_l hZF hη hY ny ..).mpr hf, (rt_oa_step_l hZF hη hY ny ..).mpr hx⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 极限秩层中的有限尾长绝对性

尾段基点不超过被分解的序数，因而属于同一传递秩层；
加法历史的存在性直接复用原序数加法的秩层绝对性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {η Y : M.Domain}
  (hη : M.IsLimitOrdinal η) (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y)
  (ny : Nonempty {x // M.mem x Y})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => v_transitive_l I hY
local notation "N" => rt_model_l Y ny
local notation "J" => rt_pair_l T ny (And.left hZF) (sc_v_pair_l (ZF.modelsKP hZF) hη hY)

theorem rt_ot_tail_l (ω n ν : (N).Domain) :
    Ot_tail_d J ω n ν ↔ Ot_tail_d I ω.val n.val ν.val := by
  have zero (a : (N).Domain) : (∀ x, ¬ (N).mem x a) ↔ ∀ x, ¬ M.mem x a.val :=
    ⟨fun h x hx => h ⟨x, T a.val a.property x hx⟩ hx, fun h x => h x.val⟩
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, ha, base, sum⟩
    have oa := (rt_ordinal_iff_l T ny (ZF.modelsKP hZF) a).mp ha
    exact ⟨a.val, oa, (or_congr (zero a) (rt_limit_l T ny (ZF.modelsKP hZF) a)).mp base,
      (rt_oa_l hZF hη hY ny a n ν oa).mp sum⟩
  · rintro ⟨a, ha, base, sum⟩
    have hAY : M.mem a Y := (ZF.ordinalAddition_left_eq_or_mem hZF I sum.right_isOrdinal sum).elim
      (fun eq => eq.symm ▸ ν.property) (T ν.val ν.property a)
    let a' : (N).Domain := ⟨a, hAY⟩
    exact ⟨a', (rt_ordinal_iff_l T ny (ZF.modelsKP hZF) a').mpr ha,
      (or_congr (zero a') (rt_limit_l T ny (ZF.modelsKP hZF) a')).mpr base,
      (rt_oa_l hZF hη hY ny a' n ν ha).mpr sum⟩

include hη hY in
theorem ot_tail_source_l {d} (ρ : Env (N) d) (ω n ν : Term d) :
    Formula.satisfies ρ (ot_tail_m (𝒞 := kpair_convention_l) ω n ν) ↔
      Ot_tail_d I (ω.eval ρ).val (n.eval ρ).val (ν.eval ρ).val :=
  (ot_tail_sat_l J (rt_model_ext_l hZF.1 T ny) ρ ω n ν).trans (rt_ot_tail_l hZF hη hY ny ..)

end YesMetaZFC.SetTheory.Internal
