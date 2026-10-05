import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOrdinal
import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 相对秩层的实际初始实例与初等传输

层级存在性只从极限 Vδ 出发，不向一般 Hχ 源强加幂集封闭。
传输全称存在句子后，目标中的新序数也有唯一传递秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem vr_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) {n} (ρ : Env (rt_model_l X hn) n) (α V : Term n) :
    Formula.satisfies ρ (v_sigma_m α V) ↔ Vr_d X (α.eval ρ).val (V.eval ρ).val := by
  have matrix (η : Env (rt_model_l X hn) (n+3)) :
      Formula.satisfies η (vc_matrix_m α.weaken.weaken.weaken V.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) ↔
        Vc_d (α.weaken.weaken.weaken.eval η).val (V.weaken.weaken.weaken.eval η).val
          (η.bound 2).val (η.bound 1).val (η.bound 0).val := by
    have tr := (rt_model_delta_l hX hn (vc_matrix_delta_l α.weaken.weaken.weaken
      V.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) η).trans (vc_matrix_sat_l hKP ..)
    cases α <;> cases V <;> exact tr
  simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff, matrix,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨B, F, h⟩ => ⟨B.val, F.val, B.property, F.property, fun t ht => h ⟨t, ht⟩⟩,
    fun ⟨B, F, hB, hF, h⟩ => ⟨⟨B, hB⟩, ⟨F, hF⟩, fun t => h t.val t.property⟩⟩

def Sc_hierarchy_d (X : M.Domain) : Prop := ∀ α, M.mem α X → M.IsOrdinal α →
  ∃ V, M.mem V X ∧ Vr_d X α V

def sc_hierarchy_m : Formula 1 0 := .forallE (.imp (KP.ord0_m .newest)
  (.existsE (v_sigma_m (.bound 1) .newest)))

theorem sc_hierarchy_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_hierarchy_m ↔ Sc_hierarchy_d X := by
  have ord (η : Env (rt_model_l X hn) 1) : Formula.satisfies η (KP.ord0_m .newest) ↔ M.IsOrdinal (η.bound 0).val :=
    (rt_model_delta_l hX hn (KP.ord0_delta_l _) η).trans (KP.ord0_sat_l hKP ..)
  simp only [sc_hierarchy_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, ord, vr_sat_l hKP hX hn]
  exact ⟨fun h α hα ho => (h ⟨α, hα⟩ ho).elim fun V hV => ⟨V.val, V.property, hV⟩,
    fun h α ho => (h α.val α.property ho).elim fun V hV => ⟨⟨V, hV.1⟩, hV.2⟩⟩

theorem sc_v_hierarchy_l (hZF : M.Models ZF) {δ X : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) : Sc_hierarchy_d X := by
  intro α hα ho
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hαδ := ZF.v_ordinal_height_l hZF hX ho hα
  obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF ho
  obtain ⟨B, F, hB, hF, cert, _⟩ := vr_source_l hZF hX hδ hαδ hV
  exact ⟨V, ZF.v_mem_l I hZF hV hX hαδ, B, F, hB, hF, fun t _ => cert t⟩

theorem Sc_hierarchy_d.map_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (h : Sc_hierarchy_d X) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) : Sc_hierarchy_d Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny
    sc_hierarchy_m (by simp -implicitDefEqProofs [sc_hierarchy_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_hierarchy_sat_l (ZF.modelsKP hZF) hY ny η).mp
    (tr.mp ((sc_hierarchy_sat_l (ZF.modelsKP hZF) hX nx ρ).mpr h))

theorem Smap_d.hierarchy_l (hZF : M.Models ZF) {ω c d X R Y S j α β V W : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j)
    (ha : Rd_entry_d α β j) (hV : Rd_entry_d V W j) : Vr_d X α V ↔ Vr_d Y β W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hαX := hj.1.1.input_mem_of_pairMember ha
  have hβY := hj.1.1.output_mem_of_pairMember ha
  let nx : Nonempty {a // M.mem a X} := ⟨⟨α, hαX⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨β, hβY⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ nx ny
    (v_sigma_m (d := 2) (.bound 1) .newest) (by simp -implicitDefEqProofs)
    ⟨Fin.cases ⟨V, hj.1.1.input_mem_of_pairMember hV⟩ (fun _ => ⟨α, hαX⟩), fun _ => ⟨α, hαX⟩⟩
    ⟨Fin.cases ⟨W, hj.1.1.output_mem_of_pairMember hV⟩ (fun _ => ⟨β, hβY⟩), fun _ => ⟨β, hβY⟩⟩
    (Fin.cases hV (fun _ => ha))
  exact (vr_sat_l (ZF.modelsKP hZF) hX nx ..).symm.trans (tr.trans (vr_sat_l (ZF.modelsKP hZF) hY ny ..))

end YesMetaZFC.SetTheory.Internal
