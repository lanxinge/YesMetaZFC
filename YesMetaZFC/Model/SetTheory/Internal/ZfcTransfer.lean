import YesMetaZFC.Model.SetTheory.Internal.ZfcSource
import YesMetaZFC.Model.SetTheory.Internal.RelationCollectCode
import YesMetaZFC.Model.SetTheory.Internal.Extensionality

/-! # 完整内部 ZFC 在原关系后继中的保持

传输模式的内部全称闭包，而非只传输旧参数的实例。目标中的新参数与内部
非标准程序均被覆盖；源和目标都可以是尚未坍塌的关系模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Zc_model_d.map_l {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (h : Zc_model_d I ω c X R) (model : Smdl_d I d Y S) (map : Smap_d I ω c d X Y q) :
    Zc_model_d I ω d Y S := by
  refine ⟨model, map.extensional_l hZF hω h.model model h.ext, ?_, ?_, ?_⟩
  · intro η
    obtain ⟨x, hx⟩ := h.model.2.1
    let ρ : Env (smdl_structure_l I (R := R) h.model.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
    exact (smap_source_l I hZF hω h.model model map zc_base_m zc_base_closed_l ρ η
      (fun i => Fin.elim0 i)).mp (h.base ρ)
  · intro K F n r i g D hK hF hr hi hg hD
    obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, _, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hi
    obtain ⟨m, G, k, build, code⟩ := sfm_sep_raw_l I hZF hω hF hr hi hs ht hsi hti hst hb htb
    obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
    have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
      obtain ⟨A, hA, ha⟩ := ((hE f).mp hf).2.2 s hs
      exact (code X R E f A hE hf ha).mpr (h.schemas.separation E F n r i f A hE hF hr hi hf hA)
    obtain ⟨g', ug, fg⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
    obtain ⟨A, hA, sep⟩ := (code Y S K g' D hK ((hK g').mpr fg)
      ((ug.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
        ((map.valid_l I hZF hω h.model model build.program build.root hE hK).mp valid g' ((hK g').mpr fg))
    exact ⟨A, hA, (sr_sep_agree_l I hZF hF hb hr hi hK hg ((hK g').mpr fg) (ug.agree_l I hsb)).mpr sep⟩
  · intro K F n r i j g D hK hF hr hi hj hij hg hD total
    obtain ⟨b, s, t, hb, hs, ht, hsi, hti, _, htj, hst, hsb, htb⟩ := sbound_fresh_l I hZF hω hF hi hj
    obtain ⟨n₁, F₁, r₁, b₁, collect⟩ := sfm_collect_raw_l I hZF hω hF hr hi hj hs ht hsi hti htj hst hb htb
    obtain ⟨n₂, F₂, r₂, b₂, antecedent⟩ := sfm_total_raw_l I hZF hω b₁.program (b₁.span r hr) hi hj hs hsi
    obtain ⟨m, G, k, build, implication⟩ := sfm_imp_l I hZF hω b₂.program b₂.root (b₂.span r₁ b₁.root)
    have initial Z U E f x y : Sbin_d I Z U E F₁ n₁ r i j f x y ↔ Sbin_d I Z U E F n r i j f x y :=
      exists_congr fun v => exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
        (b₁.sat_l I hZF hF hr Z U E w).symm
    have read Z U E a f (md : Smdl_d I a Z U) (A : (smdl_structure_l I (R := U) md.2.1).Domain)
        (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E) (ha : M.PairMember I s A.val f) :
        Ssat_d I Z U E G m k f ↔
          ((∀ x : (smdl_structure_l I (R := U) md.2.1).Domain, M.PairMember I x.val A.val U →
            ∃ y : (smdl_structure_l I (R := U) md.2.1).Domain, Sbin_d I Z U E F n r i j f x.val y.val) →
          ∃ C : (smdl_structure_l I (R := U) md.2.1).Domain,
            ∀ x : (smdl_structure_l I (R := U) md.2.1).Domain, M.PairMember I x.val A.val U →
              ∃ y : (smdl_structure_l I (R := U) md.2.1).Domain,
                M.PairMember I y.val C.val U ∧ Sbin_d I Z U E F n r i j f x.val y.val) := by
      rw [implication Z U E f hf, antecedent Z U E a f md A hE hf ha,
        ← b₂.sat_l I hZF b₁.program b₁.root Z U E f, collect Z U E a f md A hE hf ha]
      exact imp_congr (forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => initial Z U E f x.val y.val) Iff.rfl
    obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
    have valid f (hf : M.mem f E) : Ssat_d I X R E G m k f := by
      obtain ⟨A, hA, ha⟩ := ((hE f).mp hf).2.2 s hs
      apply (read X R E c f h.model ⟨A, hA⟩ hE hf ha).mpr
      intro total
      obtain ⟨C, hC, bound⟩ := h.schemas.collection E F n r i j f A hE hF hr hi hj hij hf hA
        (fun x hx ha => (total ⟨x, hx⟩ ha).elim fun y hy => ⟨y.val, y.property, hy⟩)
      exact ⟨⟨C, hC⟩, fun x hx => (bound x.val x.property hx).elim fun y ⟨hy, hc, ht⟩ => ⟨⟨y, hy⟩, hc, ht⟩⟩
    obtain ⟨g', ug, fg⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hD
    have hg' := (hK g').mpr fg
    have agree x y (hx : M.mem x Y) (hy : M.mem y Y) :
        Sbin_d I Y S K F n r i j g x y ↔ Sbin_d I Y S K F n r i j g' x y :=
      sbin_agree_l I hZF hF hb hr hi hj hK hg hg' (ug.agree_l I hsb) hx hy
    obtain ⟨C, bound⟩ := (read Y S K d g' model ⟨D, hD⟩ hK hg'
      ((ug.2 s D).mpr (Or.inl ⟨rfl, rfl⟩))).mp
        ((map.valid_l I hZF hω h.model model build.program build.root hE hK).mp valid g' hg')
        (fun x hx => (total x.val x.property hx).elim fun y ⟨hy, ht⟩ =>
          ⟨⟨y, hy⟩, (agree x.val y x.property hy).mp ht⟩)
    exact ⟨C.val, C.property, fun x hx hd => (bound ⟨x, hx⟩ hd).elim fun y ⟨hc, ht⟩ =>
      ⟨y.val, y.property, hc, (agree x y.val hx y.property).mpr ht⟩⟩

end YesMetaZFC.SetTheory.Internal
