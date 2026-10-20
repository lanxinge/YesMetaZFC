import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawMeasure
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCommonImage
import YesMetaZFC.Model.SetTheory.Internal.RelationSmall
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationSuccessor

/-! # 真实测度下原关系源的下一分量与完整 Łoś

共同低秩段回收全部实际真值集，真实测度的限制遂满足相对超滤条件。
限制保持同一代表族、等价类和商关系；完整 Łoś 最终仍用原测度表述。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际共同秩段与下一张扩展器给出原关系后继；相对超滤由低层回收构造。 -/
theorem Eb_collapse_d.raw_reduced_l {ω κ K K₀ L X R N R₀ F J O Z A p T V q c C W
    D₀ a₀ f₀ H B E Q Γ e D U α β V₀ κ' L' F' a n : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (hV : M.mem V₀ X) (rank : Vr_d X α V₀) (hV' : M.mem V₀ N) (rank' : Vr_d N α V₀)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V₀) (hB : M.mem B V₀)
    (rankB : Vr_d X β B) (small : Sc_small_d X B)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (owned : Eb_collapse_d ω κ L K₀ N B F E Q Γ e) (hD : M.mem D Γ)
    (next : Em_source_d ω κ' L' N F') (support : Fn0_d n L' a) (space : Ep_space_d κ' n D)
    (hU : Rd_entry_d a U F') :
    ∃ k d t P U' G b r Y S, M.IsSetInjectionFromTo I k Γ C ∧ Rd_entry_d D d k ∧
      (∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y W ↔ ∃ s, M.mem s x ∧ Rd_entry_d s z k) ∧
      M.IsRestrictionOf I t k D ∧ Rt_source_d I C W D t P ∧ M.MemberSubset P N ∧
      Rel_ultra_d D P U' ∧ (∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) ∧
      Rp_model_d I D C U W b G r Y S ∧ Rp_model_d I D C U' W b G r Y S ∧
      (∃ j, Smap_d I ω c b C Y j ∧
        (∀ x B, Rd_entry_d x B j ↔ M.mem x C ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B r) ∧
        (∀ a A E, Rd_entry_d a A j → Rd_entry_d E A S →
          ∃ g, M.mem g G ∧ Rd_entry_d g E r ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a W) ∧
        ∃ c₀ i q', Smem_d I c₀ X R ∧ Smap_d I ω c₀ c X C i ∧ Smap_d I ω c₀ b X Y q' ∧
          ∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y i ∧ Rd_entry_d y z j) ∧
      ∃ hd : M.mem d C,
        (∀ g, M.mem g G ↔ Fn0_d D C g ∧ ∃ B f : (smdl_structure_l I (R := W) model.2.1).Domain,
          Fn0_d (⟨d, hd⟩ : (smdl_structure_l I (R := W) model.2.1).Domain) B f ∧
            ∀ s (x y : (smdl_structure_l I (R := W) model.2.1).Domain), Rd_entry_d s x.val t →
              (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ∧
        ∃ μ e : (smdl_structure_l I (R := W) model.2.1).Domain,
          Formula.satisfies (⟨Fin.cases μ (Fin.cases ⟨d, hd⟩ (fun _ => e)), fun _ => ⟨d, hd⟩⟩ :
            Env (smdl_structure_l I (R := W) model.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)) ∧
          ∀ E Z a v z, M.IsFunctionSpace I E ω C → Scode_d I ω Z →
            M.mem a E → M.IsSetFunctionFromTo I v ω Y → Rc_eval_d I ω d C W t r a v → M.mem z Z →
            (Satisfies_d I ω b z v ↔ ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
              ∃ f, M.mem f E ∧ Pe_assign_d I ω d C W a f x ∧ Satisfies_d I ω c z f) := by
  have common := source.common_functions_l hZF owner hV rank hV' rank' hα hκ hB
  have hBX := source.transitive V₀ hV B hB
  have trans := rankB.transitive_l hZF source.transitive hBX
  have closed a b (ha : M.mem a B) (hb : M.mem b X) (sub : M.MemberSubset b a) :=
    rankB.subset_mem_l source.transitive hBX ha hb sub
  have measure := next.at_l hZF.1 hU support space
  obtain ⟨c₀, i, k, mx, hi, hBH, fk, _, pred, _, _, _, components⟩ :=
    owned.raw_measure_l hZFC source owner common hBX trans closed family coherent system limit model ff constant fv
  obtain ⟨d, t, P, U', hDd, hdH, ht, ft, domain, hP, inside, ultra, restriction⟩ := components D U hD measure
  have hd := fk.1.output_mem_of_pairMember hDd
  have sizes := hi.small_raw_l hZF source.omega source.transitive mx model hBH trans small
  obtain ⟨μ, e, index⟩ := (sizes d hd hdH).index_l I model.2.1 ⟨d, hd⟩
  obtain ⟨G, b, r, Y, S, j, q', model₀, model₁, functions, embed, composite, square, constants, bounded, los⟩ :=
    rc_successor_l hZF source.omega source.transitive mx source.theory source.collection model hi
      ⟨d, hd⟩ μ e index ft domain hP inside measure ultra restriction
  exact ⟨k, d, t, P, U', G, b, r, Y, S, fk, hDd, pred, ht, hP, inside, ultra, restriction,
    model₀, model₁, ⟨j, embed, constants, bounded, c₀, i, q', mx, hi, composite, square⟩, hd, functions, μ, e, index, los⟩

end YesMetaZFC.SetTheory.LargeCardinal
