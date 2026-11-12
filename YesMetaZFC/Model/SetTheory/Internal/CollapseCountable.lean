import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed

/-! # 可数初等图的塌缩像保持原定义域

可数图的每个条目都在反塌缩像中，故每个定义域元素也在像中。
定义域的传递性使这些元素逐点固定；图的原像遂成为同域初等嵌入，
且其可数性见证实际属于新传递模型。种子中的传递部分保持不变。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.countable_factor_l {ω a c d D X R Y S j σ k ι T : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hD : M.TransitiveSet D) (hσ : Smap_d I ω a d D Y σ) (hk : Rd_entry_d k σ j)
    (hι : M.mem ι Y) (countable : M.IsSetInjectionFromTo I ι σ ω)
    (hT : M.TransitiveSet T) (hωT : M.mem ω T) (cover : ∀ x, M.mem x T → ∃ y, Rd_entry_d y x j) :
    M.mem k X ∧ M.MemberSubset D X ∧ M.MemberSubset T X ∧ Smap_d I ω a c D X k ∧
      (∃ η, M.mem η X ∧ M.IsSetInjectionFromTo I η k ω) ∧
      ∀ x y, Rd_entry_d x y σ → M.mem y T → Rd_entry_d x y k := by
  have rel x y u v (hx : Rd_entry_d x u j) (hy : Rd_entry_d y v j) : M.mem x y ↔ M.mem u v := by
    have tr := hj.relation_l I hZF hω hm.1 hn.1 hx hy
    exact ⟨fun h => ((hn.2 u v).mp (tr.mp ((hm.2 x y).mpr
      ⟨hj.1.1.input_mem_of_pairMember hx, hj.1.1.input_mem_of_pairMember hy, h⟩))).2.2,
      fun h => ((hm.2 x y).mp (tr.mpr ((hn.2 u v).mpr
        ⟨hj.1.1.output_mem_of_pairMember hx, hj.1.1.output_mem_of_pairMember hy, h⟩))).2.2⟩
  obtain ⟨hTX, fixed⟩ := mem_embedding_fixed_l hZF hX hj.1 rel hT cover
  obtain ⟨η, hη, bound, entries⟩ := hj.countable_preimage_l hZF hω hX hY hm hn (hTX ω hωT) hk hι countable
  -- 图的每个条目都有原像，故定义域全部落在像中；传递性将其逐点固定。
  have domain x (hx : M.mem x D) : ∃ y, Rd_entry_d y x j := by
    obtain ⟨y, _, p, code, hp⟩ := hσ.1.1.2.2 x hx
    obtain ⟨q, _, hqp⟩ := entries p hp
    obtain ⟨u, _, _, _, _, hu, _⟩ := hj.kpair_preimage_l hZF hω hX hY hm hn hqp code
    exact ⟨u, hu⟩
  obtain ⟨hDX, dx⟩ := mem_embedding_fixed_l hZF hX hj.1 rel hD domain
  have hkX := hj.1.1.input_mem_of_pairMember hk
  have pairs p (hp : M.mem p k) : ∃ x, M.mem x D ∧ ∃ y, M.mem y X ∧ KPair_d M p x y := by
    obtain ⟨q, _, hpq⟩ := hj.1.1.2.2 p (hX k hkX p hp)
    have hq := (rel p k q σ hpq hk).mp hp
    obtain ⟨x, y, code⟩ := hσ.1.1.1.1 q hq
    have hx := hσ.1.1.input_mem_of_pairMember ⟨q, code, hq⟩
    obtain ⟨u, v, _, hv, pair, hu, _⟩ := hj.kpair_preimage_l hZF hω hX hY hm hn hpq code
    have eq := hj.1.2 u x x hu (dx x hx)
    subst u
    exact ⟨x, hx, v, hv, pair⟩
  have fn : Fn0_d D X k := by
    refine ⟨pairs, fun x hx => ?_, fun x hx y hy z hz hxy hxz => ?_⟩
    · obtain ⟨y, _, p, code, hp⟩ := hσ.1.1.2.2 x hx
      obtain ⟨q, hq, hqp⟩ := entries p hp
      obtain ⟨u, v, _, hv, pair, hu, _⟩ := hj.kpair_preimage_l hZF hω hX hY hm hn hqp code
      have eq := hj.1.2 u x x hu (dx x hx)
      subst u
      exact ⟨v, hv, q, pair, hq⟩
    · obtain ⟨u, _, hyu⟩ := hj.1.1.2.2 y hy
      obtain ⟨v, _, hzv⟩ := hj.1.1.2.2 z hz
      have eq := hσ.1.1.1.2 x u v ((hj.entry_l hZF hω hX hY hm hn (dx x hx) hyu hk).mp hxy)
        ((hj.entry_l hZF hω hX hY hm hn (dx x hx) hzv hk).mp hxz)
      exact hj.1.2 y z v (eq ▸ hyu) hzv
  have comm x y z (hxy : Rd_entry_d x y k) (hyz : Rd_entry_d y z j) : Rd_entry_d x z σ :=
    (hj.entry_l hZF hω hX hY hm hn (dx x (fn.bound_l hxy).1) hyz hk).mp hxy
  -- 交换三角形恢复全部内部公式的初等性，传递种子给出指定值的一致性。
  refine ⟨hkX, hDX, hTX, smap_factor_l I hZF hσ hj (fn0_function_l (ZF.modelsKP hZF) fn) comm,
    ⟨η, hη, bound⟩, fun x y hxy hy => ?_⟩
  obtain ⟨z, hz, hxz⟩ := fn.2.1 x (hσ.1.1.input_mem_of_pairMember hxy)
  obtain ⟨v, _, hzv⟩ := hj.1.1.2.2 z hz
  have eq := hσ.1.1.1.2 x v y (comm x z v hxz hzv) hxy
  exact hj.1.2 z y y (eq ▸ hzv) (fixed y hy) ▸ hxz

end YesMetaZFC.SetTheory.Internal
