import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCollapse
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFactor

/-! # 坍塌后因子及原嵌入的交换三角

将极限因子与坍塌逆图复合；常值代表的源内证书使原 j 精确分解为 k ∘ j_E。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_comparison_d (hZF : M.Models ZF) (ω X R j Y q c C V : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ b d N W i k, Smem_d I b X R ∧ Smem_d I d N W ∧ M.TransitiveSet N ∧ Smap_d I ω b d X N i ∧
    M.IsSetInjectionFromTo I k N Y ∧
    (∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v)) ∧
    (∀ y, (∃ z, Rd_entry_d z y k) ↔ ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u y) ∧
    (∀ x y z, Rd_entry_d x y i → (Rd_entry_d y z k ↔ Rd_entry_d x z j)) ∧
    Ep_realizer_d hZF ω X q b c C V d N i

theorem ep_comparison_l (hZF : M.Models ZF) {ω X A Y B j R q c C V : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (collapse : Ep_collapse_d hZF ω X R q c C V) (factor : Ee_factor_d hZF j Y q C V) :
    Ep_comparison_d hZF ω X R j Y q c C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨_, b, t, N, e, inv, d, W, i, hm, ht, constants, hn, wc, bij, hd, he, bi, inverse, _, hi, is, _⟩ := collapse
  obtain ⟨g, hg, gs, rel, any⟩ := factor
  obtain ⟨k, hk, ks⟩ := ZF.exists_compositionFunction hZF I bi.1.1 hg.1
  have inj : M.IsSetInjectionFromTo I k N Y := ⟨hk, fun x y z hx hy => by
    obtain ⟨_, E, hxE, hEz⟩ := (ks x z).mp hx
    obtain ⟨_, H, hyH, hHz⟩ := (ks y z).mp hy
    exact bi.1.2 x y H (hg.2 E H z hEz hHz ▸ hxE) hyH⟩
  have constant x E y (hxE : Rd_entry_d x E t) : Rd_entry_d E y g ↔ Rd_entry_d x y j := by
    obtain ⟨u, a, D, f, Q, hQ, hf, hs, hfD, hu, huE⟩ := constants x E hxE
    constructor
    · intro hEy
      obtain ⟨z, _, hxz⟩ := hj.2.2 x (ht.1.1.input_mem_of_pairMember hxE)
      exact (ed_constant_value_l hZF hω h hX hY hQ hf hs hxz (any u a D f E y huE hu hfD hEy)).symm ▸ hxz
    · intro hxy
      obtain ⟨z, _, hEz⟩ := hg.1.2.2 E (ht.1.1.output_mem_of_pairMember hxE)
      exact ed_constant_value_l hZF hω h hX hY hQ hf hs hxy (any u a D f E z huE hu hfD hEz) ▸ hEz
  refine ⟨b, d, N, W, i, k, hm, hd, hn, hi, inj, ?_, ?_, ?_, t, e, ht, constants, wc, bij, he, is⟩
  · intro x y u v hx hy
    obtain ⟨_, E, hxE, hEu⟩ := (ks x u).mp hx
    obtain ⟨_, H, hyH, hHv⟩ := (ks y v).mp hy
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2
      ((inverse E x).mp hxE) ((inverse H y).mp hyH)).symm.trans (rel E H u v hEu hHv)
  · intro y
    constructor
    · rintro ⟨z, hzy⟩
      obtain ⟨_, E, _, hEy⟩ := (ks z y).mp hzy
      obtain ⟨hE, u, hu, value⟩ := (gs E y).mp hEy
      exact ⟨E, u, hE, hu, value⟩
    · rintro ⟨E, u, hE, hu, value⟩
      obtain ⟨z, hz, hEz⟩ := bij.1.1.2.2 E hE
      exact ⟨z, (ks z y).mpr ⟨hz, E, (inverse E z).mpr hEz, (gs E y).mpr ⟨hE, u, hu, value⟩⟩⟩
  · intro x y z hxy
    obtain ⟨_, E, hxE, hEy⟩ := (is x y).mp hxy
    constructor
    · intro hyz
      obtain ⟨_, H, hyH, hHz⟩ := (ks y z).mp hyz
      have eq := bij.1.2 H E y ((inverse H y).mp hyH) hEy
      exact (constant x E z hxE).mp (eq ▸ hHz)
    · intro hxz
      exact (ks y z).mpr ⟨hi.1.1.output_mem_of_pairMember hxy, E,
        (inverse E y).mpr hEy, (constant x E z hxE).mpr hxz⟩

end YesMetaZFC.SetTheory.LargeCardinal
