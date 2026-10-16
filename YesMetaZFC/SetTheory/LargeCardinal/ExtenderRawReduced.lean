import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRealization
import YesMetaZFC.Model.SetTheory.Internal.RelationFunctionFamily
import YesMetaZFC.Model.SetTheory.Internal.RelationCollection
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationLos

/-! # 以原始关系超幂为源的下一分量

先取原模型内部函数的全部实际坐标图，再按下一测度形成原约化幂。
共同有界部分给出定义域坐标；每个新代表保留原始商中的函数码，整个源不坍塌。
同一代表集合对全部内部二元程序的大集合见证封闭；见证与内部真值分离集
均从源理论及其原初等图取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_raw_reduced_l {ω κ K L X R F J O Z A p T V q c C W D t U : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (d : (smdl_structure_l I (R := W) model.2.1).Domain)
    (ft : Fn0_d D C t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val W)
    (measure : FilterZF.Base_d (ℳ := M) D U) :
    ∃ G b r H S, Rp_model_d I D C U W b G r H S ∧
      (∀ g, M.mem g G ↔ Fn0_d D C g ∧
        ∃ B f : (smdl_structure_l I (R := W) model.2.1).Domain, Fn0_d d B f ∧
          ∀ s (x y : (smdl_structure_l I (R := W) model.2.1).Domain), Rd_entry_d s x.val t →
            (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ∧
      (∀ B f : (smdl_structure_l I (R := W) model.2.1).Domain, Fn0_d d B f →
        ∃ g, M.mem g G ∧ ∀ s (x y : (smdl_structure_l I (R := W) model.2.1).Domain),
          Rd_entry_d s x.val t → (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ∧
      (∀ E P n r i j v (B μ e : (smdl_structure_l I (R := W) model.2.1).Domain),
        M.IsFunctionSpace I E ω C → Sfm_d I ω n P → M.mem r n → M.mem i ω → M.mem j ω → i ≠ j → M.mem v E →
        Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ : Env (smdl_structure_l I (R := W) model.2.1) 3)
          (sc_index_m .newest (.bound 1) (.bound 2)) →
        (∀ x : (smdl_structure_l I (R := W) model.2.1).Domain, Rd_entry_d x.val d.val W → Rd_entry_d x.val B.val W →
          ∃ y : (smdl_structure_l I (R := W) model.2.1).Domain, Sbin_d I C W E P n r i j v x.val y.val) →
        ∃ g, M.mem g G ∧ ∀ s (x y : (smdl_structure_l I (R := W) model.2.1).Domain),
          Rd_entry_d s x.val t → Rd_entry_d s y.val g → Rd_entry_d x.val B.val W →
            Sbin_d I C W E P n r i j v x.val y.val) ∧
      (∀ E P n r i v, M.IsFunctionSpace I E ω C → Sfm_d I ω n P → M.mem r n → M.mem i ω → M.mem v E →
        ∃ B, M.mem B C ∧ Sr_sep_d I C W E P n r i v d.val B) ∧
      ∃ P, Rt_source_d I C W D t P ∧
        (∀ E F n r b a, M.IsFunctionSpace I E ω C → Sfm_d I ω n F → M.mem r n →
          M.mem b ω → Sbound_d I F b → M.mem a E → Pe_repr_d I b d.val C W a →
          ∃ A, M.mem A P ∧ ∀ s x, Rd_entry_d s x t →
            (M.mem s A ↔ Pe_sat_d I b d.val C W E F n r a x)) ∧
        ∀ (μ e : (smdl_structure_l I (R := W) model.2.1).Domain),
          Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
            Env (smdl_structure_l I (R := W) model.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)) →
          FilterZF.Rel_ultra_d D P U → ∀ E Z a v z, M.IsFunctionSpace I E ω C → Scode_d I ω Z →
            M.mem a E → M.IsSetFunctionFromTo I v ω H → Rc_eval_d I ω d.val C W t r a v → M.mem z Z →
            (Satisfies_d I ω b z v ↔ ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
              ∃ f, M.mem f E ∧ Pe_assign_d I ω d.val C W a f x ∧ Satisfies_d I ω c z f) := by
  obtain ⟨b₀, i₀, mx, hi₀, _, ext⟩ := ep_constant_l hZF source family system limit model
    (system.toEp_graph_d.elementary_l hZFC source family coherent)
  obtain ⟨G, spec, all⟩ := smdl_function_family_l hZF model ext d ft domain
  obtain ⟨B, f, hf, _⟩ := ep_constant_function_raw_l hZFC source family coherent system limit model d d
  obtain ⟨g, hg, _⟩ := all B f hf
  obtain ⟨b, r, H, S, next⟩ := rp_model_exists_l I hZF measure (fun g hg => ((spec g).mp hg).1) ⟨g, hg⟩ W
  refine ⟨G, b, r, H, S, next, spec, all, ?_, ?_, ?_⟩
  · intro E P n r i j v B μ e hE hP hr hi hj hij hv small total
    obtain ⟨f, Q, fn, truth⟩ := sc_collection_on_raw_l I hZF source.omega source.transitive mx model
      (smdl_extensional_l hZF model ext) hi₀ source.collection hE hP hr hi hj hij hv d B μ e small total
    obtain ⟨g, hg, eval⟩ := all Q f fn
    exact ⟨g, hg, fun s x y hsx hsy => truth x y ((eval s x y hsx).mp hsy)⟩
  · intro E P n r i v hE hP hr hi hv
    exact sc_separation_raw_l I hZF source.omega source.transitive mx model hi₀ source.theory hE hP hr hi hv d.property
  · obtain ⟨P, hP⟩ := rt_source_exists_l I hZF C W D t
    refine ⟨P, hP, ?_, ?_⟩
    · intro E F n r b a hE hF hr hb bound ha repr
      obtain ⟨B, hBC, truth⟩ := hi₀.pe_trace_raw_l hZF source.omega source.transitive mx source.theory
        model d.property hE hF hr hb bound ha repr
      obtain ⟨A, trace⟩ := rt_trace_exists_l I hZF D t W B
      exact ⟨A, hP.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) ft) domain hBC trace truth⟩
    · intro μ e small ultra E Z a v z hE codes ha hv eval hz
      exact rc_satisfies_l hZF source.omega source.transitive mx source.theory source.collection model hi₀
        d μ e small ft domain hP ultra spec next hE codes ha hv eval hz

/-- 所属模型已有的有界坍塌实际给出坐标；其每个集合都可作为原始商下一分量的定义域。 -/
theorem Eb_collapse_d.raw_reduced_l {ω κ K K₀ L X R N R₀ F J O Z A p T V q c C W
    D₀ a₀ f₀ H B E Q Γ e D U : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f N))
    (hB : M.mem B X) (trans : M.TransitiveSet B) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (owned : Eb_collapse_d ω κ L K₀ N B F E Q Γ e) (hD : M.mem D Γ)
    (measure : FilterZF.Base_d (ℳ := M) D U) :
    ∃ k d, M.IsSetInjectionFromTo I k Γ C ∧ Rd_entry_d D d k ∧
      (∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y W ↔ ∃ s, M.mem s x ∧ Rd_entry_d s z k) ∧
      ∃ t G b r Y S, M.IsRestrictionOf I t k D ∧ Rp_model_d I D C U W b G r Y S ∧
        ∃ hd : M.mem d C, ∀ g, M.mem g G ↔ Fn0_d D C g ∧
          ∃ B f : (smdl_structure_l I (R := W) model.2.1).Domain,
            Fn0_d (⟨d, hd⟩ : (smdl_structure_l I (R := W) model.2.1).Domain) B f ∧
            ∀ s (x y : (smdl_structure_l I (R := W) model.2.1).Domain), Rd_entry_d s x.val t →
              (Rd_entry_d s y.val g ↔ Rd_entry_d x y f) := by
  obtain ⟨k, fk, _, _, _, predecessor⟩ := owned.raw_l hZFC source owner common hB trans family coherent
    system limit model ff constant fv
  obtain ⟨d, hd, hDd⟩ := fk.1.2.2 D hD
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, map, _⟩ := owned
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k D
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (map.transitive D hD))
  have domain s x (hsx : Rd_entry_d s x t) : Rd_entry_d x d W :=
    (predecessor D d hDd x).mpr ⟨s, (ht.2 s x).mp hsx |>.1, (ht.2 s x).mp hsx |>.2⟩
  obtain ⟨G, b, r, Y, S, next, spec, _⟩ := ep_raw_reduced_l hZFC source family coherent system limit model
    ⟨d, hd⟩ ft domain measure
  exact ⟨k, d, fk, hDd, predecessor, t, G, b, r, Y, S, ht, next, hd, spec⟩

end YesMetaZFC.SetTheory.LargeCardinal
