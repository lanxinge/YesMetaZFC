import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetPull
import YesMetaZFC.SetTheory.LargeCardinal.IterationNice

/-! # 拥有的列图与操作三元组回拉

列的全定义域由原图反射；条目与操作码保留给定大图中的原值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem _root_.YesMetaZFC.SetTheory.Internal.Smap_d.column_l
    {ω B R b U S u π C V A A' f g : M.Domain} (hω : M.IsOmega ω)
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (vt : M.TransitiveSet V)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π) (hAA : Rd_entry_d A A' π) (hfg : Rd_entry_d f g π)
    (hf : M.mem f C) (gf : M.IsSetFunction I g) (gd : M.IsDomainOf I A' g) : Fn0_d A C f := by
  have hg := (hj.member_l I hZF hω mb mu hfg hCV).mp hf
  exact (hj.function_l hZF hω bt ut mb mu hAA hCV hfg).mpr
    (fn0_of_function_l (ZF.modelsKP hZF) ⟨gf, gd, fun i hi => by
      obtain ⟨x, hx⟩ := (gd i).mp hi
      exact ⟨x, (rd_entry_transitive_l vt hg hx).2, hx⟩⟩)

theorem _root_.YesMetaZFC.SetTheory.Internal.Smap_d.entry_preimage_l
    {ω B R b U S u π D C f g i i' y : M.Domain} (hω : M.IsOmega ω)
    (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (mb : Smem_d I b B R) (mu : Smem_d I u U S)
    (hj : Smap_d I ω b u B U π) (cb : M.MemberSubset C B) (ff : Fn0_d D C f)
    (gf : M.IsSetFunction I g) (hf : Rd_entry_d f g π) (hi : Rd_entry_d i i' π)
    (hiD : M.mem i D) (hy : Rd_entry_d i' y g) : ∃ x, M.mem x C ∧ Rd_entry_d i x f ∧ Rd_entry_d x y π := by
  obtain ⟨x, hx, hix⟩ := ff.2.1 i hiD
  obtain ⟨z, _, hxz⟩ := hj.1.1.2.2 x (cb x hx)
  have eq := gf.2 i' z y ((hj.entry_l hZF hω bt ut mb mu hi hxz hf).mp hix) hy
  exact ⟨x, hx, hix, eq ▸ hxz⟩

theorem it_payload_pull_l {ω B R b U S u π p p' κ' L' F' : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hpp : Rd_entry_d p p' π) (big : It_payload_d p' κ' L' F') :
    ∃ κ L F, It_payload_d p κ L F ∧ Rd_entry_d κ κ' π ∧ Rd_entry_d L L' π ∧ Rd_entry_d F F' π := by
  obtain ⟨r', hp, hr⟩ := big
  obtain ⟨κ, r, _, _, pair, hk, hrr⟩ := hj.kpair_preimage_l hZF hω bt ut mb mu hpp hp
  obtain ⟨L, F, _, _, pair', hl, hf⟩ := hj.kpair_preimage_l hZF hω bt ut mb mu hrr hr
  exact ⟨κ, L, F, ⟨r, pair, pair'⟩, hk, hl, hf⟩

end YesMetaZFC.SetTheory.LargeCardinal
