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

theorem ep_tag_l (hZF : M.Models ZF) {ω κ L X J O Z A p T S a c C V d Y W : M.Domain}
    (hω : M.IsOmega ω) (h : Eg_graph_d ω κ L X J O Z A p T S)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p S a d Y W)
    (hac : Rd_entry_d a c Z) (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V) :
    ∃ e u, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c Y C e ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d C Y u ∧
      (∀ x B, Rd_entry_d x B e ↔ M.mem x Y ∧ KPair_d M x a B) ∧
      ∀ B x, Rd_entry_d B x u ↔ M.mem x Y ∧ KPair_d M x a B := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz⟩ := h.codes
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

section RelationChange
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 更换关系后复用原标签双射，仅需 ZF。 -/
theorem ep_tag_change_l {ω κ L X R F J O Z D p T V V' q C W a b H U e U' d Q S v : M.Domain}
    (hω : M.IsOmega ω) (system : Ep_system_d I ω κ L X R F J O Z D p T V)
    (changed : Di_system_d J O D p T V') (limit : Di_limit_d D p T V' q C W)
    (stage : Di_stage_d I D p V' a d Q S) (hab : Rd_entry_d a b Z)
    (old : Smdl_d I b H U) (new : Smdl_d I e H U')
    (vr : ∀ E H x y, Rd_entry_d E x v → Rd_entry_d H y v → (Rd_entry_d E H U' ↔ Rd_entry_d x y W))
    (vs : ∀ E E', Rd_entry_d E E' v ↔ M.mem E H ∧ ∃ u, KPair_d M u a E ∧ Rd_entry_d u E' q) :
    ∃ t s, Smap_d I ω d e Q H t ∧ Smap_d I ω e d H Q s ∧
      (∀ x E, Rd_entry_d x E t ↔ M.mem x Q ∧ KPair_d M x a E) ∧
      ∀ E x, Rd_entry_d E x s ↔ M.mem x Q ∧ KPair_d M x a E := by
  obtain ⟨x, hx⟩ := stage.1.2.1
  obtain ⟨d₀, Q₀, S₀, st⟩ := di_stage_exists_l hZF system.diagram (((stage.2.1 x).mp hx).2)
  have eq := hZF.1.eq_of_same_members Q₀ Q (fun x => (st.2.1 x).trans (stage.2.1 x).symm)
  subst Q₀
  obtain ⟨t, s, ht, hs, ts, ss⟩ := ep_tag_l hZF hω system.toEg_graph_d st hab old
  have bt : M.IsSetBijectionFromTo I t Q H := ⟨ht.1, fun E hE => by
    obtain ⟨x, hx, hEx⟩ := hs.1.1.2.2 E hE
    exact ⟨x, hx, (ts x E).mpr ((ss E x).mp hEx)⟩⟩
  have bs : M.IsSetBijectionFromTo I s H Q := ⟨hs.1, fun x hx => by
    obtain ⟨E, hE, hxE⟩ := ht.1.1.2.2 x hx
    exact ⟨E, hE, (ss E x).mpr ((ts x E).mp hxE)⟩⟩
  obtain ⟨r, hr, rs, rr⟩ := di_projection_l hZF changed limit stage
  have rel x y E H (hxE : Rd_entry_d x E t) (hyH : Rd_entry_d y H t) : Rd_entry_d x y S ↔ Rd_entry_d E H U' := by
    obtain ⟨u, _, hxu⟩ := hr.1.2.2 x (ht.1.1.input_mem_of_pairMember hxE)
    obtain ⟨w, _, hyw⟩ := hr.1.2.2 y (ht.1.1.input_mem_of_pairMember hyH)
    exact (rr x y u w hxu hyw).trans (vr E H u w
      ((vs E u).mpr ⟨ht.1.1.output_mem_of_pairMember hxE, x, ((ts x E).mp hxE).2, ((rs x u).mp hxu).2⟩)
      ((vs H w).mpr ⟨ht.1.1.output_mem_of_pairMember hyH, y, ((ts y H).mp hyH).2, ((rs y w).mp hyw).2⟩)).symm
  exact ⟨t, s, smap_of_iso_l I hZF hω stage.1 new bt rel,
    smap_of_iso_l I hZF hω new stage.1 bs (fun E H x y hx hy =>
      (rel x y E H ((ts x E).mpr ((ss E x).mp hx)) ((ts y H).mpr ((ss H y).mp hy))).symm), ts, ss⟩

end RelationChange

end YesMetaZFC.SetTheory.LargeCardinal
