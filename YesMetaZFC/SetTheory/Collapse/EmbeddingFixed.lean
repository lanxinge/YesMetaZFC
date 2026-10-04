import YesMetaZFC.SetTheory.Collapse.Uniqueness
import YesMetaZFC.SetTheory.KP.Ordinal

/-! # 传递域的隶属嵌入固定其像中的传递集合

将嵌入倒转到实际像集合上，直接复用 Mostowski 规范性与传递参数固定定理。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem mem_embedding_ordinal_l (hKP : M.Models KP) {N Y k a α : M.Domain} (hN : M.TransitiveSet N)
    (hk : M.IsSetInjectionFromTo (kp_pair_l hKP) k N Y)
    (rel : ∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v))
    (ha : Rd_entry_d a α k) (hα : M.IsOrdinal α) : M.IsOrdinal a := by
  have trans b β (hb : Rd_entry_d b β k) (hβ : M.IsOrdinal β) : M.TransitiveSet b := by
    intro x hx y hy
    have hxN := hN b (hk.1.input_mem_of_pairMember hb) x hx
    obtain ⟨u, _, hxu⟩ := hk.1.2.2 x hxN
    obtain ⟨v, _, hyv⟩ := hk.1.2.2 y (hN x hxN y hy)
    exact (rel y b v β hyv hb).mpr (hβ.transitive u ((rel x b u β hxu hb).mp hx)
      v ((rel y x v u hyv hxu).mp hy))
  apply (KP.ord0_iff_l hKP).mp
  refine ⟨trans a α ha hα, ?_, ?_⟩
  · intro b hb
    obtain ⟨β, _, hbβ⟩ := hk.1.2.2 b (hN a (hk.1.input_mem_of_pairMember ha) b hb)
    exact trans b β hbβ (hα.mem ((rel b a β α hbβ ha).mp hb))
  · intro b hb c hc
    obtain ⟨β, _, hbβ⟩ := hk.1.2.2 b (hN a (hk.1.input_mem_of_pairMember ha) b hb)
    obtain ⟨γ, _, hcγ⟩ := hk.1.2.2 c (hN a (hk.1.input_mem_of_pairMember ha) c hc)
    rcases hα.wellOrder.linear.compare β ((rel b a β α hbβ ha).mp hb) γ ((rel c a γ α hcγ ha).mp hc) with he | he | he
    · exact Or.inl (hk.2 b c γ (hKP.1.eq_of_same_members β γ he ▸ hbβ) hcγ)
    · exact Or.inr (Or.inl ((rel b c β γ hbβ hcγ).mpr he))
    · exact Or.inr (Or.inr ((rel c b γ β hcγ hbβ).mpr he))

theorem mem_embedding_fixed_l (hZF : M.Models ZF) {N Y k T : M.Domain} (hN : M.TransitiveSet N)
    (hk : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) k N Y)
    (rel : ∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v))
    (hT : M.TransitiveSet T) (cover : ∀ x, M.mem x T → ∃ z, Rd_entry_d z x k) :
    M.MemberSubset T N ∧ ∀ x, M.mem x T → Rd_entry_d x x k := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨H, hs⟩ := ZF.exists_range_of_setFunction hZF I hk.1.1 hk.1.2.1
  have bij : M.IsSetBijectionFromTo I k N H := ⟨⟨⟨hk.1.1, hk.1.2.1, fun x hx =>
    (hk.1.2.2 x hx).imp fun y hy => ⟨(hs y).mpr ⟨x, hy.2⟩, hy.2⟩⟩, hk.2⟩,
      fun y hy => ((hs y).mp hy).imp fun x hx => ⟨hk.1.input_mem_of_pairMember hx, hx⟩⟩
  obtain ⟨F, hf, fs⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have iso : Mc_iso_d H N F := ⟨fn0_of_function_l (ZF.modelsKP hZF) hf.1.1, hf.1.2,
    fun y hy => (hf.2 y hy).imp fun _ h => h.2,
    fun a b x y ha hb => (rel x y a b ((fs a x).mp ha) ((fs b y).mp hb)).symm⟩
  have fixed x (hx : M.mem x T) : Rd_entry_d x x k := by
    obtain ⟨y, hy⟩ := cover x hx
    have eq := mc_fixed_transitive_l (ZF.models_kpi_l hZF) hT (fun z hz => (hs z).mpr (cover z hz)) hx
      (iso.canonical_l (ZF.models_kpi_l hZF) hN ((fs x y).mpr hy))
    exact eq.symm ▸ hy
  exact ⟨fun x hx => hk.1.input_mem_of_pairMember (fixed x hx), fixed⟩

end YesMetaZFC.SetTheory
