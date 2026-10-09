import YesMetaZFC.SetTheory.FlatPairing.Functions
import YesMetaZFC.Model.SetTheory.Internal.Syntax

/-! # 平坦程序的秩界和指令绝对性

程序长度及所有编号仍来自内部 ω；只有四个固定构造符的标签使用外部有限归纳。
程序图是任意 Vν（ν≥ω）的子集，因此可在 V(ν+1) 中读取全部内部程序。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_node_naturals_l (hZF : M.Models ZF) {ω r c i j : M.Domain} {k : Nat}
    (hω : M.IsOmega ω) (hr : M.mem r ω) (h : Sfm_node_d I ω r c) (hs : Sop_d I k c i j) :
    M.mem i ω ∧ M.mem j ω := by
  rcases h with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
    obtain ⟨rfl, rfl, rfl⟩ := sop_injective_l I (ZF.modelsKP hZF) hs ht
  · exact ⟨ha, hb⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hω.transitive hZF r hr i ha, hω.transitive hZF r hr j hb⟩
  · exact ⟨ha, hω.transitive hZF r hr j hb⟩

variable (hZF : M.Models ZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem fp_program_rank_l {ω ν X n F : M.Domain} (hω : M.IsOmega ω)
    (hV : V_d I ν X) (hων : M.MemberSubset ω ν) (hF : Sfm_d K ω n F) : M.MemberSubset F X := by
  have natural x (hx : M.mem x ω) := ZF.v_ordinal_mem_l I hZF hV (hων x hx)
  have pair {p x y} (h : (K).Codes p x y) (hx : M.mem x X) (hy : M.mem y X) :=
    ((fp_fixed_l hZF.1 hω).mp h).rank_mem_l I hZF hω hV hων hx hy
  intro p hp
  obtain ⟨r, c, code⟩ := hF.2.1.2.1.1 p hp
  have hc : M.PairMember K r c F := ⟨p, code, hp⟩
  have hr := hω.transitive hZF n hF.1 r ((hF.2.1.2.2 r).mpr ⟨c, hc⟩)
  have op {k i j} (hs : Sop_d K k c i j) : M.mem c X := by
    have ij := sfm_node_naturals_l K hZF hω hr (hF.2.2 r c hc) hs
    obtain ⟨a, o, ho, ca, cc⟩ := hs
    exact pair cc (natural o (num_mem_l hZF.1 hω ho)) (pair ca (natural i ij.1) (natural j ij.2))
  apply pair code (natural r hr)
  rcases hF.2.2 r c hc with ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ | ⟨_, _, h, _, _⟩ <;> exact op h

theorem rt_num_l {Y : M.Domain} (hY : M.TransitiveSet Y) (ny : Nonempty {y // M.mem y Y})
    (hE : Extensional M) (k : Nat) (x : (rt_model_l Y ny).Domain) :
    Num_d (M := rt_model_l Y ny) k x ↔ Num_d k x.val := by
  induction k generalizing x with
  | zero => exact ⟨fun h y hy => h ⟨y, hY x.val x.property y hy⟩ hy, fun h y => h y.val⟩
  | succ k ih =>
    constructor
    · rintro ⟨y, hn, succ⟩
      exact ⟨y.val, (ih y).mp hn, (rt_successor_l hY ny hE x y).mp succ⟩
    · rintro ⟨y, hn, succ⟩
      let y' : (rt_model_l Y ny).Domain := ⟨y, hY x.val x.property y succ.predecessor_mem⟩
      exact ⟨y', (ih y').mpr hn, (rt_successor_l hY ny hE x y').mpr succ⟩

variable {ω μ Y : M.Domain} (hω : M.IsOmega ω) (hW : V_d I μ Y) (hωY : M.mem ω Y)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY
include hω hW

theorem fp_sop_coordinates_l {c i j : M.Domain} {k : Nat} (hc : M.mem c Y) (h : Sop_d K k c i j) :
    M.mem i Y ∧ M.mem j Y := by
  obtain ⟨a, o, _, ha, ht⟩ := h
  have oa := ((fp_fixed_l hZF.1 hω).mp ht).inverse_rank_l I hZF hω.1 hW hc
  exact ((fp_fixed_l hZF.1 hω).mp ha).inverse_rank_l I hZF hω.1 hW oa.2

theorem rt_fp_sop_l (k : Nat) (c i j : (N).Domain) :
    Sop_d J k c i j ↔ Sop_d K k c.val i.val j.val := by
  have num := rt_num_l (ZF.v_transitive_l I hZF hW) (Nonempty.intro (Subtype.mk ω hωY)) hZF.1 k
  constructor
  · rintro ⟨a, o, ho, ha, hc⟩
    exact ⟨a.val, o.val, (num o).mp ho, (fp_fixed_l hZF.1 hω).mpr ha, (fp_fixed_l hZF.1 hω).mpr hc⟩
  · rintro ⟨a, o, ho, ha, hc⟩
    have oa := ((fp_fixed_l hZF.1 hω).mp hc).inverse_rank_l I hZF hω.1 hW c.property
    let a' : (N).Domain := ⟨a, oa.2⟩
    let o' : (N).Domain := ⟨o, oa.1⟩
    exact ⟨a', o', (num o').mpr ho, (fp_fixed_l hZF.1 hω).mp ha, (fp_fixed_l hZF.1 hω).mp hc⟩

end YesMetaZFC.SetTheory.Internal
