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
  small : ∀ A K, M.mem A X → M.mem K X → Fseq_space_d I ω A K → Sc_small_d X A → Sc_small_d X K

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_sequences_forward_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (source : Sc_sequences_d I ω X) (theory : Sc_theory_d I ω Y S) : Sc_sequences_d I ω Y := by
  have hωq := hq.omega_l I hZF hω hX hY hm hn hωX
  have hωY := hq.1.1.output_mem_of_pairMember hωq
  -- 固定句子 ∀A ∃K ∀f (f∈K ↔ ∃n∈ω，f:n→A) 覆盖目标中的全部字母表。
  let φ : Formula 1 1 := .forallE (.existsE (.conj (.forallE (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1)))))
      (.imp (sc_small_m (.bound 1)) (sc_small_m .newest))))
  have read Z (hZ : M.TransitiveSet Z) (hωZ : M.mem ω Z) (hz : Nonempty {x // M.mem x Z}) :
      Formula.satisfies (⟨fun _ => ⟨ω, hωZ⟩, fun _ => ⟨ω, hωZ⟩⟩ : Env (rt_model_l Z hz) 1) φ ↔
        ∀ A, M.mem A Z → ∃ K, M.mem K Z ∧ (∀ f, M.mem f Z →
          (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) ∧ (Sc_small_d Z A → Sc_small_d Z K) := by
    have fn (ρ : Env (rt_model_l Z hz) 5) : Formula.satisfies ρ (fn0_m .newest (.bound 3) (.bound 1)) ↔
        Fn0_d (ρ.bound 0).val (ρ.bound 3).val (ρ.bound 1).val :=
      (rt_model_delta_l hZ hz (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 ..)
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_imp_iff, sc_small_sat_l (ZF.modelsKP hZF) hZ hz, fn]
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
  have target := (read Y hY hωY ny).mp (transfer.mp ((read X hX hωX nz).mpr (fun A hA => by
    obtain ⟨K, hK, spec⟩ := source.space A hA
    exact ⟨K, hK, fun f _ => (spec f).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩), source.small A K hA hK spec⟩)))
  have full A K (hA : M.mem A Y) (hK : M.mem K Y)
      (spec : ∀ f, M.mem f Y → (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f)) : Fseq_space_d I ω A K := by
    intro f
    constructor
    · intro hf
      obtain ⟨n, hn, hf⟩ := (spec f (hY K hK f hf)).mp hf
      exact ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hf⟩
    · rintro ⟨n, hnω, hf⟩
      have fn := fn0_of_function_l (ZF.modelsKP hZF) hf
      exact (spec f (sc_finite_function_l hZF hω hY hn theory hωY (hY A hA) hnω fn)).mpr ⟨n, hnω, fn⟩
  refine ⟨fun A hA => ?_, fun A K hA _ hK small => ?_⟩
  · obtain ⟨K, hk, spec, _⟩ := target A hA
    exact ⟨K, hk, full A K hA hk spec⟩
  · obtain ⟨L, hl, spec, bound⟩ := target A hA
    exact hZF.1.eq_of_same_members L K (fun f => (full A L hA hl spec f).trans (hK f).symm) ▸ bound small

theorem sc_h_sequences_l (hZFC : M.Models ZFC) {ω χ H : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) :
    Sc_sequences_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω H :=
  ⟨fun _ => ZFC.h_fseq_l hZFC hω hχ hωχ hH,
    fun _ _ _ hK _ _ => sc_h_small_l hZFC hω hχ hωχ hH hK⟩

theorem sc_v_sequences_l {ω δ V : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hωδ : M.mem ω δ) (hV : V_d I δ V) : Sc_sequences_d I ω V := by
  have hωV := ZF.v_ordinal_mem_l I hZF hV hωδ
  refine ⟨fun A hA => ?_, fun A K _ hK seq small => ?_⟩
  · obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω A
    exact ⟨K, ZF.v_fseq_mem_l I hZF hV hδ hω hωV hA hK, hK⟩
  · obtain ⟨μ, f, hμ, _, idx⟩ := small
    have hμδ := ZF.v_ordinal_height_l hZF hV idx.ordinal hμ
    obtain ⟨ν, hν, hn, bound, _⟩ := ZF.common_cardinal_l I hZF hδ.1 hωδ hμδ hμδ
    obtain ⟨g, hg⟩ := bound
    obtain ⟨e, he⟩ := idx.bound_l (ZF.modelsKP hZF)
    obtain ⟨q, hq⟩ := ZF.fseq_bound_l I hZF hω hn (ZF.exists_compositionInjection hZF I he hg) seq
    have hνV := ZF.v_ordinal_mem_l I hZF hV hν
    obtain ⟨Y, hY, hKY, hνY⟩ := ZF.v_joint_bound_l I hZF hV hK hνV
    have hqV := ZF.v_relation_mem_l I hZF hV hδ hY (fun p hp =>
      (fn0_of_function_l (ZF.modelsKP hZF) hq.1).1 p hp |>.elim fun a ha => ha.2.elim fun b hb =>
        ⟨a, hKY a ha.1, b, hνY b hb.1, hb.2⟩)
    exact ⟨ν, q, hνV, hqV, Sc_index_d.of_injection_l (ZF.modelsKP hZF) hn.1.1 hq⟩

end YesMetaZFC.SetTheory.Internal
