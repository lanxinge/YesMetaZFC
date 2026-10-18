import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationConstant
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationRestriction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationTrace
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationNormalize

/-! # 任意原关系源的后继与同一原始模型的复合初等图

每轮只使用到原始模型的完整初等图及已识别的真实测度。
新商直接返回同类初等图和源内函数代表，下一轮无需传递塌缩。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_successor_l {ω c X R c' Y S q D t N P U U' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d μ e : (smdl_structure_l I (R := S) source.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
      Env (smdl_structure_l I (R := S) source.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hP : Rt_source_d I Y S D t P) (inside : M.MemberSubset P N) (measure : Sf_ultra_d N D U)
    (ultra : Rel_ultra_d D P U') (restriction : ∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) :
    ∃ G b r C T j q', Rp_model_d I D Y U S b G r C T ∧ Rp_model_d I D Y U' S b G r C T ∧
      (∀ g, M.mem g G ↔ Fn0_d D Y g ∧
        ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
          ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
            (Rd_entry_d s y.val g ↔ Rd_entry_d x y f)) ∧
      Smap_d I ω c' b Y C j ∧ Smap_d I ω c b X C q' ∧
      (∀ x z, Rd_entry_d x z q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y z j) ∧
      (∀ x B, Rd_entry_d x B j ↔ M.mem x Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B r) ∧
      (∀ a A E, Rd_entry_d a A j → Rd_entry_d E A T →
        ∃ g, M.mem g G ∧ Rd_entry_d g E r ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a S) ∧
      ∀ E Z a v z, M.IsFunctionSpace I E ω Y → Scode_d I ω Z →
        M.mem a E → M.IsSetFunctionFromTo I v ω C → Rc_eval_d I ω d.val Y S t r a v → M.mem z Z →
        (Satisfies_d I ω b z v ↔ ∃ A, M.mem A U ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
          ∃ f, M.mem f E ∧ Pe_assign_d I ω d.val Y S a f x ∧ Satisfies_d I ω c' z f) := by
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm.1 source (rf_ext_mem_l I hZF.1 hX hm)
  obtain ⟨G, spec, all⟩ := smdl_function_family_l hZF source ext d ft domain
  obtain ⟨B, f, ff, _⟩ := sc_constant_raw_l hZF hω hX hm theory source hq (ext.native_l I source.2.1) d d
  obtain ⟨g, hg, _⟩ := all B f ff
  obtain ⟨b, r, C, T, next⟩ := rp_model_exists_l I hZF measure.base (fun g hg => ((spec g).mp hg).1) ⟨g, hg⟩ S
  have restricted := rc_restrict_model_l hZF hω hX hm theory source hq d ft domain hP inside measure restriction
    (fun g hg => by obtain ⟨_, _, f, _, decode⟩ := (spec g).mp hg; exact ⟨f, decode⟩) next
  obtain ⟨j, embed, constants⟩ := rc_constant_embedding_l hZF hω hX hm theory collection source hq
    d μ e small ft domain hP ultra spec restricted
  obtain ⟨q', composite, square⟩ := smap_comp_l I hZF hq embed
  refine ⟨G, b, r, C, T, j, q', next, restricted, spec, embed, composite, square, constants,
    fun a A E hA edge => rc_bounded_representative_l hZF hω hX hm theory source hq d ft domain
      measure.base measure.proper spec next ((constants a A).mp hA) edge,
    fun E Z a v z hE codes ha hv eval hz => ?_⟩
  have los := rc_satisfies_l hZF hω hX hm theory collection source hq d μ e small ft domain hP ultra
    spec restricted hE codes ha hv eval hz
  apply los.trans
  refine ⟨fun ⟨A, hA, truth⟩ => ⟨A, ((restriction A).mp hA).2, truth⟩, ?_⟩
  rintro ⟨A, hA, truth⟩
  obtain ⟨n, F, s, code⟩ := (codes z).mp hz
  obtain ⟨Q, hQ, read⟩ := rc_full_trace_l hZF hω hX hm theory source hq d.property ft domain hP hE code ha
    (eval.repr_l I ((hE a).mp ha).1)
  have large := measure.upward A Q hA (inside Q hQ) (ultra.field.bounds Q hQ) (fun s hs => by
    obtain ⟨x, _, hsx⟩ := ft.2.1 s (measure.base.bounds A hA s hs)
    exact (read s x hsx).mpr (truth s x hs hsx))
  exact ⟨Q, (restriction Q).mpr ⟨hQ, large⟩, fun s x hs hsx => (read s x hsx).mp hs⟩

end YesMetaZFC.SetTheory.Internal
