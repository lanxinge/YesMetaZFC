import YesMetaZFC.Model.SetTheory.Internal.SourceFinite
import YesMetaZFC.Model.SetTheory.Internal.SourceSmall
import YesMetaZFC.SetTheory.HereditarySequences
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 有限序列空间在后继模型中的实际保持

先传输每个字母表的内部序列空间，再用源内有限函数闭性证明它已包含
全部背景内部有限图；新字母表不必来自旧嵌入的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Sc_sequences_d (I : kpair_convention_l.Interpretation M) (ω X : M.Domain) : Prop where
  space : ∀ A, M.mem A X → ∃ K, M.mem K X ∧ Fseq_space_d I ω A K
  index : ∀ A K μ e, M.mem A X → M.mem K X → M.mem μ X → M.mem e X →
    Fseq_space_d I ω A K → M.MemberSubset ω μ → Sc_index_d μ A e → ∃ f, M.mem f X ∧ Sc_index_d μ K f

def sc_seq_index_m {n} (ω A K : Term n) : Formula 1 n := .forallE (.forallE
  (.imp (Formula.subset ω.weaken.weaken (.bound 1))
    (.imp (sc_index_m (.bound 1) A.weaken.weaken .newest)
      (.existsE (sc_index_m (.bound 2) K.weaken.weaken.weaken .newest)))))
derive_free_closed sc_seq_index_m

theorem sc_seq_index_sat_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x // M.mem x Z}) {n} (ρ : Env (rt_model_l Z hz) n) (ω A K : Term n) :
    Formula.satisfies ρ (sc_seq_index_m ω A K) ↔ ∀ μ e, M.mem μ Z → M.mem e Z →
      M.MemberSubset (ω.eval ρ).val μ → Sc_index_d μ (A.eval ρ).val e → ∃ f, M.mem f Z ∧ Sc_index_d μ (K.eval ρ).val f := by
  have idx {d} (η : Env (rt_model_l Z hz) d) (a b c : Term d) : Formula.satisfies η (sc_index_m a b c) ↔
      Sc_index_d (a.eval η).val (b.eval η).val (c.eval η).val := by
    have tr := (rt_model_delta_l hZ hz (sc_index_delta_l a b c) η).trans (sc_index_sat_l hKP ..)
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using tr
  have sub {d} (η : Env (rt_model_l Z hz) d) (a b : Term d) : Formula.satisfies η (Formula.subset a b) ↔
      M.MemberSubset (a.eval η).val (b.eval η).val := by
    have tr := (rt_model_delta_l hZ hz (.atom _ _ _) η).trans (Formula.satisfies_subset_iff _ a b)
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using tr
  simp only [sc_seq_index_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, sub, idx, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h μ e hμ he hw hi => (h ⟨μ, hμ⟩ ⟨e, he⟩ hw hi).elim fun f hf => ⟨f.val, f.property, hf⟩,
    fun h μ e hw hi => (h μ.val e.val μ.property e.property hw hi).elim fun f hf => ⟨⟨f, hf.1⟩, hf.2⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_sequences_iff_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (tx : Sc_theory_d I ω X R) (ty : Sc_theory_d I ω Y S) :
    Sc_sequences_d I ω X ↔ Sc_sequences_d I ω Y := by
  have hωq := hq.omega_l I hZF hω hX hY hm hn hωX
  have hωY := hq.1.1.output_mem_of_pairMember hωq
  -- 固定句子 ∀A ∃K ∀f (f∈K ↔ ∃n∈ω，f:n→A) 覆盖目标中的全部字母表。
  let φ : Formula 1 1 := .forallE (.existsE (.conj (.forallE (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))))
      (sc_seq_index_m (.bound 2) (.bound 1) .newest)))
  have read Z (hZ : M.TransitiveSet Z) (hωZ : M.mem ω Z) (hz : Nonempty {x // M.mem x Z}) :
      Formula.satisfies (⟨fun _ => ⟨ω, hωZ⟩, fun _ => ⟨ω, hωZ⟩⟩ : Env (rt_model_l Z hz) 1) φ ↔
        ∀ A, M.mem A Z → ∃ K, M.mem K Z ∧ (∀ f, M.mem f Z →
          (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) ∧ (∀ μ e, M.mem μ Z → M.mem e Z → M.MemberSubset ω μ → Sc_index_d μ A e → ∃ f, M.mem f Z ∧ Sc_index_d μ K f) := by
    have fn (ρ : Env (rt_model_l Z hz) 5) : Formula.satisfies ρ (fn0_m .newest (.bound 3) (.bound 1)) ↔
        Fn0_d (ρ.bound 0).val (ρ.bound 3).val (ρ.bound 1).val :=
      (rt_model_delta_l hZ hz (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 ..)
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      sc_seq_index_sat_l (ZF.modelsKP hZF) hZ hz, fn]
    constructor
    · intro h A hA
      obtain ⟨K, hK⟩ := h ⟨A, hA⟩
      exact ⟨K.val, K.property, fun f hf => (hK.1 ⟨f, hf⟩).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩⟩, hK.2⟩
    · intro h A
      obtain ⟨K, hK, spec, small⟩ := h A.val A.property
      exact ⟨⟨K, hK⟩, fun f => (spec f.val f.property).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩⟩, small⟩
  let nz : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have transfer := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ nz ny φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩ ⟨fun _ => ⟨ω, hωY⟩, fun _ => ⟨ω, hωY⟩⟩ (fun _ => hωq)
  have interpret Z U c (hZ : M.TransitiveSet Z) (hωZ : M.mem ω Z)
      (hc : Smem_d I c Z U) (theory : Sc_theory_d I ω Z U) (hz : Nonempty {x // M.mem x Z}) :
      Sc_sequences_d I ω Z ↔ Formula.satisfies
        (⟨fun _ => ⟨ω, hωZ⟩, fun _ => ⟨ω, hωZ⟩⟩ : Env (rt_model_l Z hz) 1) φ := by
    rw [read Z hZ hωZ hz]
    constructor
    · intro source A hA
      obtain ⟨K, hK, spec⟩ := source.space A hA
      exact ⟨K, hK, fun f _ => (spec f).trans (exists_congr fun n => and_congr_right fun _ =>
        ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩), fun μ e hμ he => source.index A K μ e hA hK hμ he spec⟩
    · intro target
      have full A K (hA : M.mem A Z) (hK : M.mem K Z)
          (spec : ∀ f, M.mem f Z → (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) : Fseq_space_d I ω A K := by
        intro f
        constructor
        · intro hf
          obtain ⟨n, hn, hf⟩ := (spec f (hZ K hK f hf)).mp hf
          exact ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hf⟩
        · rintro ⟨n, hnω, hf⟩
          have fn := fn0_of_function_l (ZF.modelsKP hZF) hf
          exact (spec f (sc_finite_function_l hZF hω hZ hc theory hωZ (hZ A hA) hnω fn)).mpr ⟨n, hnω, fn⟩
      refine ⟨fun A hA => ?_, fun A K μ e hA _ hμ he hK hw idx => ?_⟩
      · obtain ⟨K, hk, spec, _⟩ := target A hA
        exact ⟨K, hk, full A K hA hk spec⟩
      · obtain ⟨L, hl, spec, bound⟩ := target A hA
        exact hZF.1.eq_of_same_members L K (fun f => (full A L hA hl spec f).trans (hK f).symm) ▸ bound μ e hμ he hw idx
  exact (interpret X R c hX hωX hm tx nz).trans (transfer.trans (interpret Y S d hY hωY hn ty ny).symm)


theorem Sc_sequences_d.small_l {ω c X R A K : M.Domain} (h : Sc_sequences_d I ω X)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hωX : M.mem ω X) (hA : M.mem A X) (hK : M.mem K X) (seq : Fseq_space_d I ω A K)
    (small : Sc_small_d X A) : Sc_small_d X K := by
  obtain ⟨μ, e, hμ, he, hw, idx⟩ := sc_infinite_index_l hZF hω hX hm theory hωX hA small
  obtain ⟨f, hf, hi⟩ := h.index A K μ e hA hK hμ he seq hw idx
  exact ⟨μ, f, hμ, hf, hi⟩

theorem sc_h_sequences_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) :
    Sc_sequences_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H := by
  let hZF := ZFC.models_zf_l hZFC
  refine ⟨fun _ => ZFC.h_fseq_l hZFC hω hχ hωχ hH, fun A K μ e _ hK hμ _ seq hw idx => ?_⟩
  obtain ⟨f, hf⟩ := ZF.fseq_ordinal_bound_l (kp_pair_l (ZF.modelsKP hZF)) hZF hω idx.ordinal hw (idx.bound_l (ZF.modelsKP hZF)) seq
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hH hK
    (hf.1.mono_target_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.h_transitive_l (kp_pair_l (ZF.modelsKP hZF)) hZF hH μ hμ)), Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal hf⟩

theorem sc_v_sequences_l {ω δ V : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hωδ : M.mem ω δ) (hV : V_d I δ V) : Sc_sequences_d I ω V := by
  have hωV := ZF.v_ordinal_mem_l I hZF hV hωδ
  refine ⟨fun A hA => ?_, fun A K μ e _ hK hμ _ seq hw idx => ?_⟩
  · obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω A
    exact ⟨K, ZF.v_fseq_mem_l I hZF hV hδ hω hωV hA hK, hK⟩
  · obtain ⟨q, hq⟩ := ZF.fseq_ordinal_bound_l I hZF hω idx.ordinal hw (idx.bound_l (ZF.modelsKP hZF)) seq
    obtain ⟨Y, hY, hKY, hμY⟩ := ZF.v_joint_bound_l I hZF hV hK hμ
    have hqV := ZF.v_relation_mem_l I hZF hV hδ hY (fun p hp =>
      (fn0_of_function_l (ZF.modelsKP hZF) hq.1).1 p hp |>.elim fun a ha => ha.2.elim fun b hb =>
        ⟨a, hKY a ha.1, b, hμY b hb.1, hb.2⟩)
    exact ⟨q, hqV, Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal hq⟩

end YesMetaZFC.SetTheory.Internal
