import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRealization
import YesMetaZFC.Model.SetTheory.Internal.RelationSubset
import YesMetaZFC.Model.SetTheory.Internal.RelationPower
import YesMetaZFC.Model.SetTheory.Internal.RelationHierarchy

/-! # 共同低层上的真实测度识别

任意原关系子集先截到定义域，再由所属模型的同一有界代表池回收。
原测度在精确坐标子集代数上的限制因而成为实际相对超滤。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_collapse_d.raw_measure_l {ω κ K K₀ L X R N R₀ F J O Z A p T V q c C W
    D₀ a₀ f₀ H B E Q Γ e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f N))
    (hB : M.mem B X) (trans : M.TransitiveSet B)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (owned : Eb_collapse_d ω κ L K₀ N B F E Q Γ e) :
    ∃ b i k, Smem_d I b X R ∧ Smap_d I ω b c X C i ∧ Rd_entry_d B H i ∧
      M.IsSetInjectionFromTo I k Γ C ∧
      (∀ a, Rd_entry_d a H W ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x a k) ∧
      (∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y W ↔ ∃ s, M.mem s x ∧ Rd_entry_d s z k) ∧
      M.MemberSubset Γ N ∧
      (∀ D P (d p : (smdl_structure_l I (R := W) model.2.1).Domain),
        Rd_entry_d D d.val k → Rd_entry_d P p.val k → Source_d N D P →
          (smdl_structure_l I (R := W) model.2.1).IsPowerSetOf p d) ∧
      (∀ α V (a v : (smdl_structure_l I (R := W) model.2.1).Domain),
        Rd_entry_d α a.val k → Rd_entry_d V v.val k → Vr_d Γ α V →
          Formula.satisfies (⟨Fin.cases v (fun _ => a), fun _ => a⟩ :
            Env (smdl_structure_l I (R := W) model.2.1) 2) (v_sigma_m (.bound 1) .newest)) ∧
      ∀ D U, M.mem D Γ → Sf_ultra_d N D U → ∃ d t P U',
        Rd_entry_d D d k ∧ Rd_entry_d d H W ∧ M.IsRestrictionOf I t k D ∧ Fn0_d D C t ∧
        (∀ s x, Rd_entry_d s x t → Rd_entry_d x d W) ∧
        Rt_source_d I C W D t P ∧ M.MemberSubset P N ∧ Rel_ultra_d D P U' ∧
        ∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U := by
  obtain ⟨b, i, mx, hi, hBH, k, fk, _, image, _, pred⟩ := owned.raw_l hZFC source owner common
    hB trans family coherent system limit model ff constant fv
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he, _, _, _, _, map, _⟩ := owned
  have inside x (hx : M.mem x Γ) : M.mem x N := by
    obtain ⟨u, _, hux⟩ := map.onto x hx
    exact (rd_entry_transitive_l owner.transitive he hux).2
  have closed' := hi.subsets_raw_l I hZF source.omega source.transitive mx model hBH closed
  refine ⟨b, i, k, mx, hi, hBH, fk, image, pred, inside, ?_, ?_, ?_⟩
  · exact fun D P d p hDd hPp power => rr_power_l I model.2.1 closed' map.transitive inside fk image pred d p hDd hPp power
  · have ext : Rf_ext_d I C W := hi.extensional_l hZF source.omega mx.1 model (rf_ext_mem_l I hZF.1 source.transitive mx)
    exact fun α V a v hα hV rank => rr_realize_rank_l hZF model ext map.transitive fk image pred
      closed' a v hα hV rank
  intro D U hD measure
  obtain ⟨d, t, P, U', hDd, hdH, ht, ft, domain, hP, contains, ultra, restriction⟩ :=
    hi.measure_raw_l I hZF source.omega source.transitive mx source.theory model
      closed' map.transitive inside fk image pred hD measure
  exact ⟨d, t, P, U', hDd, hdH, ht, fn0_of_function_l (ZF.modelsKP hZF) ft, domain, hP, contains, ultra, restriction⟩

end YesMetaZFC.SetTheory.LargeCardinal
