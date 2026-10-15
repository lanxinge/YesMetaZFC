import YesMetaZFC.Model.Forcing.Internal.Functions.Generic
import YesMetaZFC.Model.Forcing.Internal.Forcing.Definability
import YesMetaZFC.Model.Forcing.Internal.Extension.ZF
import YesMetaZFC.SetTheory.Descriptive.Prefix
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd

/-! # 有限初段条件的可数坍缩

条件为 X 值内部有限序列，顺序为反向包含。逐坐标与逐值稠密集实际给出
扩张内 ω 到旧 X 的满射，并保留每条泛型图边的原条件来源。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Descriptive
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_collapse_order_l {ω : M.Domain} (hw : M.IsOmega ω) (X : M.Domain) :
    ∃ F R, Fseq_space_d I ω X F ∧ Cond_order_d M F R F ∧
      (∀ p q, Entry_d M p q R ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p) := by
  obtain ⟨F, space⟩ := ZF.fseq_space_exists_l I hZF hw X
  obtain ⟨R, order, base, _⟩ := subset_order_l M hZF F
  exact ⟨F, R, space, base, order⟩

variable {ω X F R : M.Domain} {G : M.Domain → Prop}
  (hw : M.IsOmega ω)
  (space : Fseq_space_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X F)
  (order : ∀ p q, Entry_d M p q R ↔ M.mem p F ∧ M.mem q F ∧ M.MemberSubset q p)
  (generic : Generic_d M F R F G)
include hw space order generic

theorem fseq_generic_input_l (inh : ∃ x, M.mem x X) {i : M.Domain} (hi : M.mem i ω) :
    ∃ p, G p ∧ ∃ y, Entry_d M i y p := by
  classical
  obtain ⟨p, hp⟩ := generic.inhabited
  let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  have sat p : φ.denote ρ p ↔ ∃ y, Entry_d M i y p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]; rfl
  apply generic_pick_l hZF generic ⟨1, φ, ρ, sat⟩ hp
  intro p hp
  obtain ⟨n, hn, fn⟩ := (space p).mp hp.1
  by_cases hin : M.mem i n
  · exact ⟨p, subset_below_l hZF order hp.1 hp.1 (fun _ h => h),
      (fn.2.2 i hin).imp fun y hy => hy.2⟩
  · obtain ⟨x, hx⟩ := inh
    obtain ⟨f, ff, cut, _⟩ := ds_extend_l I hZF hw hn fn hx
    obtain ⟨j, succ, hj⟩ := hw.1.2 i hi
    obtain ⟨q, qr⟩ := ZF.exists_restriction hZF I f j
    have fq := qr.isSetFunctionFromTo ff (hw.transitive hZF j hj)
    have ni : M.MemberSubset n j := by
      rcases (hw.isOrdinal hZF).wellOrder.linear.compare n hn i hi with eq | lt | gt
      · exact fun a ha => (succ a).mpr (Or.inl ((eq a).mp ha))
      · exact fun a ha => (succ a).mpr (Or.inl ((hw.members_areOrdinals hZF i hi).transitive n lt a ha))
      · exact (hin gt).elim
    exact ⟨q, subset_below_l hZF order hp.1 ((space q).mpr ⟨j, hj, fq⟩)
      (ds_prefix_mono_l I fn fq.1 cut qr ni), (fq.2.2 i succ.predecessor_mem).imp fun y hy => hy.2⟩

theorem fseq_generic_output_l {x : M.Domain} (hx : M.mem x X) : ∃ p, G p ∧ ∃ i, Entry_d M i x p := by
  obtain ⟨p, hp⟩ := generic.inhabited
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 2) (.bound 1)) }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  have sat p : φ.denote ρ p ↔ ∃ i, Entry_d M i x p := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]; rfl
  apply generic_pick_l hZF generic ⟨1, φ, ρ, sat⟩ hp
  intro p hp
  obtain ⟨n, hn, fn⟩ := (space p).mp hp.1
  obtain ⟨m, q, hm, fq, endt⟩ := ZF.fseq_end_exists_l I hZF hw hn fn hx
  obtain ⟨m', n', decomp⟩ := endt
  have eq := decomp.prefix_sequence.2.2.2.eq hZF.1 fn.2.1
  subst n'
  exact ⟨q, subset_below_l hZF order hp.1 ((space q).mpr ⟨m, hm, fq⟩)
    (Fseq_end_d.subset_l I ⟨m', n, decomp⟩), n, decomp.last_value⟩

local notation "N" => extension_l M hZF F R F G

theorem fseq_generic_surjection_l (O : Cond_order_d M F R F) (inh : ∃ x, M.mem x X)
    {b : M.Domain} (hb : G b) (e : M.Domain → (N).Domain) (hi : Function.Injective e)
    (he : ∀ a y, (N).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M b a t → Qval_d M F R F G t (e a)) :
    let J := kpair_interpretation_l N (extension_ext_l O hZF generic) (internal_pair_l O hZF generic)
    ∃ g, (N).IsSetFunctionFromTo J g (e ω) (e X) ∧ (N).IsSetSurjectiveOnto J g (e ω) (e X) ∧
      ∀ x y, Entry_d N x y g ↔ ∃ p, G p ∧ ∃ a c, Entry_d M a c p ∧ e a = x ∧ e c = y := by
  have pf {p} (hp : G p) : Pfn_d I ω X p := by
    obtain ⟨n, hn, fn⟩ := (space p).mp (generic.proper p hp).1
    exact ⟨fn.1, fun i x ix => ⟨hw.transitive hZF n hn i (fn.input_mem_of_pairMember ix), fn.output_mem_of_pairMember ix⟩⟩
  obtain ⟨g, fn, graph⟩ := generic_function_l (hEN := extension_ext_l O hZF generic) (hPN := internal_pair_l O hZF generic)
    O hZF generic hb pf (fun p q h => ((order p q).mp h).2.2)
    (fun _ hi => fseq_generic_input_l hZF hw space order generic inh hi) e hi he hv
  refine ⟨g, fn, ?_, graph⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (he X x).mp hx
  obtain ⟨p, hp, i, ia⟩ := fseq_generic_output_l hZF hw space order generic ha
  exact ⟨e i, (image_member_l e hi he).mpr ((pf hp).2 i a ia).1,
    (graph (e i) (e a)).mpr ⟨p, hp, i, a, ia, rfl, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal
