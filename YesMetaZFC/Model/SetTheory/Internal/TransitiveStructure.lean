import YesMetaZFC.Model.SetTheory.Internal.TransitiveCardinal
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem

/-! # 传递子源中实际结构码的绝对性

只需配对闭包。图的坐标由传递性回收，既不假设子源满足 ZF，也不要求
子源包含所有背景子集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hKP hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_kpair_l (p a b : (N).Domain) : (J).Codes p a b ↔ (I).Codes p.val a.val b.val := by
  let ρ : Env N 3 := ⟨Fin.cases p (Fin.cases a (fun _ => b)), fun _ => p⟩
  exact (kpair0_sat_l (rt_model_ext_l hKP.1 hZ nz) ρ .newest (.bound 1) (.bound 2)).symm.trans
    ((rt_model_delta_l hZ nz (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hKP.1 ..))

theorem rt_relation_l (R : (N).Domain) : (N).IsSetRelation J R ↔ M.IsSetRelation I R.val := by
  constructor
  · intro h p hp
    obtain ⟨a, b, code⟩ := h ⟨p, hZ R.val R.property p hp⟩ hp
    exact ⟨a.val, b.val, (rt_kpair_l hKP hZ nz pair ..).mp code⟩
  · intro h p hp
    obtain ⟨a, b, code⟩ := h p.val hp
    have mem := code.mem_l M hZ p.property
    exact ⟨⟨a, mem.1⟩, ⟨b, mem.2⟩, (rt_kpair_l hKP hZ nz pair ..).mpr code⟩

theorem rt_smdl_l (c A R : (N).Domain) : Smdl_d J c A R ↔ Smdl_d I c.val A.val R.val := by
  refine and_congr (rt_kpair_l hKP hZ nz pair c A R) (and_congr ?_ ?_)
  · exact ⟨fun ⟨x, hx⟩ => ⟨x.val, hx⟩, fun ⟨x, hx⟩ => ⟨⟨x, hZ A.val A.property x hx⟩, hx⟩⟩
  · refine and_congr (rt_relation_l hKP hZ nz pair R) ?_
    constructor
    · intro h x y hxy
      have xy := rd_entry_transitive_l hZ R.property hxy
      exact h ⟨x, xy.1⟩ ⟨y, xy.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hxy)
    · intro h x y hxy
      exact h x.val y.val ((rt_entry_l hZ nz hKP.1 ..).mp hxy)

theorem rt_smem_l (c A R : (N).Domain) : Smem_d J c A R ↔ Smem_d I c.val A.val R.val := by
  refine and_congr (rt_smdl_l hKP hZ nz pair c A R) ?_
  constructor
  · intro h x y
    constructor
    · intro hxy
      have xy := rd_entry_transitive_l hZ R.property hxy
      exact (h ⟨x, xy.1⟩ ⟨y, xy.2⟩).mp ((rt_entry_l hZ nz hKP.1 ..).mpr hxy)
    · intro hxy
      exact (rt_entry_l hZ nz hKP.1 ..).mp ((h ⟨x, hZ A.val A.property x hxy.1⟩
        ⟨y, hZ A.val A.property y hxy.2.1⟩).mpr hxy)
  · intro h x y
    exact (rt_entry_l hZ nz hKP.1 ..).trans (h x.val y.val)

end YesMetaZFC.SetTheory.Internal
