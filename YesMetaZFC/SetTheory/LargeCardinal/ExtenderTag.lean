import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystem
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Elementary
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingComposition

/-! # 分量类结构与带标签分量的实际同构

去掉支撑标签给出双射，逆图由集合逆关系构造。两个方向均保持全部内部码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_tag_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S a c C V d Y W : M.Domain}
    (hω : M.IsOmega ω) (h : Ep_graph_d hZF ω κ L X R F J O Z A p T S)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p S a d Y W)
    (hac : Rd_entry_d a c Z) (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V) :
    ∃ e u, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c Y C e ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d C Y u ∧
      (∀ x B, Rd_entry_d x B e ↔ M.mem x Y ∧ KPair_d M x a B) ∧
      ∀ B x, Rd_entry_d B x u ↔ M.mem x Y ∧ KPair_d M x a B := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz, _⟩ := h.models
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
  have sat x B : φ.denote ρ x B ↔ KPair_d M x a B := kpair_sat_l M hZF.1 _ _ _ _
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := C)
    (fun x hx => by
      obtain ⟨B, hp, _⟩ := h.label_l (((stage.2.1 x).mp hx).2)
      exact ⟨B, (sat x B).mpr hp⟩)
    (fun x _ B D hb hd => (kpair_injective_l M ((sat x B).mp hb) ((sat x D).mp hd)).2)
    (fun x B hx hb => (ep_at_read_l hz hac hm.1).mp (h.at_l (((stage.2.1 x).mp hx).1) ((sat x B).mp hb)))
  have spec x B : Rd_entry_d x B e ↔ M.mem x Y ∧ KPair_d M x a B :=
    (es x B).trans (and_congr_right fun _ => sat x B)
  have bij : M.IsSetBijectionFromTo I e Y C := by
    refine ⟨⟨he, fun x y B hx hy => I.unique (((spec x B).mp hx).2) (((spec y B).mp hy).2)⟩, fun B hb => ?_⟩
    obtain ⟨x, hp⟩ := I.total a B
    have hxA := (h.nodes x).mpr ⟨a, B, hp, c, C, V, hac, hm.1, hb⟩
    have hxY := (stage.2.1 x).mpr ⟨hxA, (h.index x a B hp).mpr hxA⟩
    exact ⟨x, hxY, (spec x B).mpr ⟨hxY, hp⟩⟩
  have rel x y B D (hx : Rd_entry_d x B e) (hy : Rd_entry_d y D e) : Rd_entry_d x y W ↔ Rd_entry_d B D V := by
    obtain ⟨hxY, hpx⟩ := (spec x B).mp hx
    obtain ⟨hyY, hpy⟩ := (spec y D).mp hy
    have hxA := ((stage.2.1 x).mp hxY).1
    have hyA := ((stage.2.1 y).mp hyY).1
    have localW : Rd_entry_d x y W ↔ Rd_entry_d x y S := (stage.2.2 x y).trans
      ⟨And.right ∘ And.right, fun hr => ⟨hxY, hyY, hr⟩⟩
    have localS : Rd_entry_d x y S ↔ Ep_rel_d Z a B D := (h.relation_l hpx hpy).trans
      ⟨And.right ∘ And.right, fun hr => ⟨hxA, hyA, hr⟩⟩
    exact localW.trans (localS.trans (ep_rel_read_l hz hac hm.1))
  obtain ⟨u, hu, us⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  exact ⟨e, u, smap_of_iso_l I hZF hω stage.1 hm bij rel,
    smap_of_iso_l I hZF hω hm stage.1 hu (fun B D x y hx hy =>
      (rel x y B D ((us B x).mp hx) ((us D y).mp hy)).symm), spec,
    fun B x => (us B x).trans (spec x B)⟩

end YesMetaZFC.SetTheory.LargeCardinal
