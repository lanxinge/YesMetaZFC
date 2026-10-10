import YesMetaZFC.Model.SetTheory.Internal.OrdinalPairSource
import YesMetaZFC.Model.SetTheory.Internal.TransitiveSequence
import YesMetaZFC.SetTheory.Ord.Code.Prefix

/-! # 序数折叠的读取与递归步在极限秩层中绝对

读取见证的长度就是已有历史图的定义域，故可在同一秩层内恢复。
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

theorem rt_oc_read_l (F H b a : (N).Domain) :
    Oc_read_d J F H b a ↔ Oc_read_d I F.val H.val b.val a.val := by
  have ent := rt_entry_l T nz hZF.1
  have dom := rt_domain_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) T nz P
  have ord := rt_ordinal_iff_l T nz (ZF.modelsKP hZF)
  constructor
  · rintro ⟨n, i, hn, hs, hi, hb, ha, ob, oa⟩
    exact ⟨n.val, i.val, (dom ..).mp hn, (rt_successor_l T nz hZF.1 ..).mp hs,
      (ord ..).mp hi, (ent ..).mp hb, (ent ..).mp ha, (ord ..).mp ob, (ord ..).mp oa⟩
  · rintro ⟨n, i, hn, hs, hi, hb, ha, ob, oa⟩
    let n' : (N).Domain := ⟨n, ZF.v_domain_mem_l I hZF hV H.property hn⟩
    let i' : (N).Domain := ⟨i, T n n'.property i hs.predecessor_mem⟩
    exact ⟨n', i', (dom ..).mpr hn, (rt_successor_l T nz hZF.1 ..).mpr hs,
      (ord ..).mpr hi, (ent ..).mpr hb, (ent ..).mpr ha, (ord ..).mpr ob, (ord ..).mpr oa⟩

theorem rt_oc_step_l (F H c : (N).Domain) :
    Oc_step_d J F H c ↔ Oc_step_d I F.val H.val c.val := by
  have read := rt_oc_read_l hZF hδ hV nz
  have own {b a} (h : Oc_read_d I F.val H.val b a) : M.mem b Z ∧ M.mem a Z := by
    obtain ⟨n, i, _, _, _, hb, ha, _⟩ := h
    exact ⟨(rd_entry_transitive_l T H.property hb).2, (rd_entry_transitive_l T F.property ha).2⟩
  have ex : (∃ b a, Oc_read_d J F H b a) ↔ ∃ b a, Oc_read_d I F.val H.val b a := by
    constructor
    · rintro ⟨b, a, h⟩
      exact ⟨b.val, a.val, (read ..).mp h⟩
    · rintro ⟨b, a, h⟩
      exact ⟨⟨b, (own h).1⟩, ⟨a, (own h).2⟩, (read ..).mpr h⟩
  refine or_congr ?_ (and_congr (not_congr ex)
    ⟨fun h x hx => h ⟨x, T c.val c.property x hx⟩ hx, fun h x => h x.val⟩)
  constructor
  · rintro ⟨b, a, hr, hp⟩
    exact ⟨b.val, a.val, (read ..).mp hr, (rt_oc_pair_l hZF hδ hV nz ..).mp hp⟩
  · rintro ⟨b, a, hr, hp⟩
    exact ⟨⟨b, (own hr).1⟩, ⟨a, (own hr).2⟩,
      (read ..).mpr hr, (rt_oc_pair_l hZF hδ hV nz ..).mpr hp⟩

end YesMetaZFC.SetTheory.Internal
